/* =========================================================
   XSpace BIO (ESP32 + AFE4490 + AD8232 + MLX90614)
   - SpO2, R, Frecuencia Cardíaca (FC), PTT, FR y TEMPERATURA
   - PPG o ECG se pueden graficar por Aurora (seleccionable)
   - Fs fijo = 250 Hz
   ========================================================= */

#include <Arduino.h>
#include <XSpaceBioV10.h>
#include <XSpaceIoT.h>
#include <math.h>

// ---------- Nuevas librerías para MLX90614 ----------
#include <Wire.h>
#include <Adafruit_MLX90614.h>
// ----------------------------------------------------

#define USE_AURORA 0 // 1 para enviar datos a Aurora, 0 para desactivar
#if USE_AURORA
   const char* WIFI_SSID 	= "Diego";
   const char* WIFI_PSWD 	= "diego079";
   const char* AURORA_IP 	= "10.89.116.212";
   const uint16_t AURORA_PORT = 15600; 		// Debe coincidir con Aurora
   const uint32_t UDP_PERIOD_MS = 20; 		// ~50 Hz para gráfica
#endif

// -------- Selección de señal para graficar en Aurora --------
enum GraphSignal { ECG, PPG };
GraphSignal GRAFICA = PPG; // por defecto PPG

// -------- Muestreo y ventanas PPG --------
const uint16_t FS 		 = 250; 	// Hz (ECG y PPG sincronizados)
const float 	ALPHA_DC = 0.99f; 	// EMA para DC (seguimiento lento)

// Ventanas definidas en SEGUNDOS (se escalan con Fs)
const float WIN_RMS_SEC = 2.0f; 	// 2 s para RMS
const float WIN_REF_SEC = 5.0f; 	// 5 s para referencia de R

const int WIN_RMS = (int)(WIN_RMS_SEC * FS); 	// muestras
const int WIN_REF = (int)(WIN_REF_SEC * FS); 	// muestras

const uint32_t REPORT_INTERVAL_MS 	= 1000; 	// SpO2/R/FC cada 1 s
const uint32_t PTT_REPORT_INTERVAL_MS = 10000; 	// PTT cada 10 s
const uint32_t TEMP_REPORT_MS         = 5000;   // Reporte de Temperatura cada 5 s
const uint32_t JSON_REPORT_INTERVAL_MS = 15000; // Reporte JSON cada 15 s

// -------- Límites / protecciones ----- 
const float SAT_THRESH = 8.3e6f; 	// saturación cruda
const float MIN_SIGNAL = 10.0f; 	// umbral mínimo de AC_rms

// -------- LEDs ---------- 
const uint8_t LED_IR_PCT 	= 60;
const uint8_t LED_RED_PCT = 60;

// -------- Objetos ---------- 
XSEthernet 		XSerial;
XSpaceBioV10Board MyBoard;
// Objeto MLX90614
Adafruit_MLX90614 mlx = Adafruit_MLX90614(); 

// -------- Variables Globales de Estado y Resultados --------
float last_temp_C = NAN; // Temperatura
float last_FR = NAN; // Frecuencia Respiratoria (FR)
float last_P_sistolica = NAN; // Presión Sistólica
float last_P_diastolica = NAN; // Presión Diastólica
float lastPTT 	= NAN; 		// último PTT en segundos

// -------- Estados PPG ---------- 
float dc_red = 0.0f, dc_ir = 0.0f;
float buf_r[WIN_RMS], buf_i[WIN_RMS];
int 	idx_rms = 0, filled_rms = 0;
float sumsq_r = 0.0f, sumsq_i = 0.0f;
float buf_R[WIN_REF];
int 	idx_ref = 0, filled_ref = 0;

// -------- Filtro LPF (IIR 1er orden) para PPG -------- 
const float FC_LPF = 8.0f; 	// Hz (ajusta 5–10 Hz)
float alpha_lp 	 = 0.0f; 	// se calcula en setup()
float y_lpf_ir 	 = 0.0f; 	// salida del filtro (estado)

// Coeficientes para cálculo de SpO2
float A_SPO2 = -38.64635211f;
float B_SPO2 = 120.0373378f;

inline float clamp_pos(float x) { return (x > 1e-12f) ? x : 1e-12f; }

// -------- Lógica de estabilidad -------- 
const int NUM_MEASUREMENTS = 5;
float spo2_values[NUM_MEASUREMENTS];
float r_values[NUM_MEASUREMENTS];
int 	n_valid_spo2 = 0;
bool stable_R = false;
unsigned long last_stable_R_time = 0;

// -------- Variables para FC (a partir de ECG) --------
const double THRESHOLD_HR 		= 2.10; 	// ajusta según amplitud ECG
const unsigned long REFRACTORY_MS = 300; 		// 300 ms ~ 200 lpm

double lastECGVoltage 	= 0.0;
bool 	wasAboveThreshold = false;
unsigned long lastBeatTime = 0;
unsigned long prevBeatTime = 0; 
double lastBPM = 0.0; // Frecuencia Cardíaca (FC)

// -------- Variables para PTT (ECG + PPG) --------
const unsigned long PPG_SEARCH_MIN_MS = 50; 	// empezar a buscar pulso PPG 50 ms después del R
const unsigned long PPG_SEARCH_MAX_MS = 400; 	// dejar de buscar a los 400 ms

bool 			waitingPPG 		= false;
float 		ppg_peak_value 	= -1e9f;
unsigned long ppg_peak_time_ms 	= 0;

double ptt_sum 	= 0.0; 		// acumulador para promedio 10 s
unsigned long ptt_count = 0; 	// número de PTT válidos en la ventana

// Coeficientes de la regresión lineal para estimar la presión arterial
const float a_systolic = 10.03;
const float b_systolic = 118.44;
const float a_diastolic = -203.70;
const float b_diastolic = 146.47;

// --------------------------------------------------------
// ------------- VARIABLES PARA FR ------------------
// --------------------------------------------------------

// Decimación para señales respiratorias (para reducir carga de CPU)
const int RESP_FS = 25; 			// frecuencia efectiva para FR (Hz)
const int DECIM_FACTOR = FS / RESP_FS; 	// = 10
const int FR_WIN = 5 * RESP_FS; 		// 5 s ventana -> 125 muestras

float fr_buf_am[FR_WIN];
float fr_buf_bw[FR_WIN];
float fr_buf_fm[FR_WIN];
int fr_idx = 0;
int fr_filled = 0;
int decim_counter = 0;

// buffer temporal para cálculo de FM (RR)
float rr_last = NAN;
unsigned long last_FR_time = 0;
const uint32_t FR_REPORT_MS = 5000; // reportar cada 5 s
unsigned long last_fr_report = 0;

// --------------------------------------------------------
// FUNCIONES AUXILIARES
// --------------------------------------------------------

float calculate_average(const float values[], int length) {
	if (length <= 0) return NAN;
	float sum = 0.0f;
	for (int i = 0; i < length; i++) sum += values[i];
	return sum / (float)length;
}

void min_max_array(const float values[], int length, float &vmin, float &vmax) {
	vmin = 	1e9f;
	vmax = -1e9f;
	for (int i = 0; i < length; i++) {
		if (values[i] < vmin) vmin = values[i];
		if (values[i] > vmax) vmax = values[i];
	}
}
void pushRMS(float ac_r, float ac_i) {
	float oldr = buf_r[idx_rms], oldi = buf_i[idx_rms];
	if (filled_rms < WIN_RMS) {
		buf_r[idx_rms] = ac_r; 	buf_i[idx_rms] = ac_i;
		sumsq_r += ac_r * ac_r; sumsq_i += ac_i * ac_i;
		filled_rms++;
	} else {
		sumsq_r += ac_r * ac_r - oldr * oldr;
		sumsq_i += ac_i * ac_i - oldi * oldi;
		buf_r[idx_rms] = ac_r; 	buf_i[idx_rms] = ac_i;
	}
	idx_rms = (idx_rms + 1) % WIN_RMS;
}

void pushR(float R) {
	if (!isnan(R)) {
		buf_R[idx_ref] = R;
		if (filled_ref < WIN_REF) filled_ref++;
		idx_ref = (idx_ref + 1) % WIN_REF;
	}
}

float meanRref() {
	if (!filled_ref) return NAN;
	double s = 0.0;
	for (int k = 0; k < filled_ref; ++k) s += buf_R[k];
	return (float)(s / filled_ref);
}

void resetBuffers() {
	sumsq_r = sumsq_i = 0.0f;
	filled_rms = 0; idx_rms = 0;
	filled_ref = 0; idx_ref = 0;
}

// --------------------------------------------------------
// FUNCIONES FR
// --------------------------------------------------------

// empujar muestras decimadas (AM,BW,FM)
void pushRespiratorySignals(float am, float bw, float fm) {
	fr_buf_am[fr_idx] = am;
	fr_buf_bw[fr_idx] = bw;
	fr_buf_fm[fr_idx] = fm;
	if (fr_filled < FR_WIN) fr_filled++;
	fr_idx = (fr_idx + 1) % FR_WIN;
}

// Estimador simple de frecuencia dominante (DFT naive). Usa fs = RESP_FS.
float estimateRespFreq(const float *x, int N) {
	if (N < 8) return NAN;
	float fs = (float)RESP_FS;
	float best_f = NAN;
	float best_p = -1e30f;

	// k representa índice de frecuencia: f = k * fs / N
	for (int k = 1; k < N/2; ++k) {
		float freq = (float)k * fs / (float)N;
		// rango respiratorio plausible (0.08 - 0.8 Hz) -> 5 - 48 bpm, ajustable
		if (freq < 0.08f || freq > 0.8f) continue;

		float re = 0.0f, im = 0.0f;
		for (int n = 0; n < N; ++n) {
			float ang = -2.0f * 3.14159265f * (float)k * (float)n / (float)N;
			re += x[n] * cosf(ang);
			im += x[n] * sinf(ang);
		}
		float power = re*re + im*im;
		if (power > best_p) {
			best_p = power;
			best_f = freq;
		}
	}
	return best_f;
}

// fusion simple de las tres estimaciones (AM,BW,FM)
float compute_FR_hz() {
	if (fr_filled < FR_WIN) return NAN;

	float am_arr[FR_WIN], bw_arr[FR_WIN], fm_arr[FR_WIN];
	// copiar buffers en orden (fr_idx es circular)
	int start = (fr_idx + FR_WIN - fr_filled) % FR_WIN;
	for (int i = 0; i < fr_filled; ++i) {
		int idx = (start + i) % FR_WIN;
		am_arr[i] = fr_buf_am[idx];
		bw_arr[i] = fr_buf_bw[idx];
		fm_arr[i] = fr_buf_fm[idx];
	}
	int N = fr_filled;

	float f_am = estimateRespFreq(am_arr, N);
	float f_bw = estimateRespFreq(bw_arr, N);
	float f_fm = estimateRespFreq(fm_arr, N);

	int count = 0;
	float sum = 0.0f;
	if (!isnan(f_am)) { sum += f_am; count++; }
	if (!isnan(f_bw)) { sum += f_bw; count++; }
	if (!isnan(f_fm)) { sum += f_fm; count++; }

	if (count == 0) return NAN;
	return sum / (float)count;
}

// --------------------------------------------------------
// SETUP
// --------------------------------------------------------

void setup() {
	Serial.begin(115200);
	Serial.println();
	Serial.println("Inicializando placa y sensores...");

	// 1) Inicializar placa y AFE/ECG
	MyBoard.init();
	MyBoard.AFE4490_init(CS_AFE4490, PWDN_AFE4490);

	// 2) Configurar LEDs del AFE (una sola vez)
	MyBoard.AFE4490_Led_intesity(LED_IR_PCT, LED_RED_PCT);

	// 3) ECG activo desde el inicio
	MyBoard.AD8232_Wake(AD8232_XS1);

	// 4) Inicializar MLX90614 (Temperatura)
	Serial.print("Inicializando MLX90614 (Temperatura)... ");
	if (!mlx.begin()) {
		Serial.println("¡ERROR! No se encontró MLX90614. Revise cableado I2C.");
	} else {
		Serial.println("OK");
	}

	// 5) Semilla DC PPG
	dc_red 	= (float)MyBoard.AFE4490_GetRED();
	dc_ir 	= (float)MyBoard.AFE4490_GetIR();
	y_lpf_ir = 0.0f;

	// 6) Coeficiente LPF depende de Fs
	alpha_lp = 1.0f - expf(-2.0f * 3.14159265f * FC_LPF / (float)FS);

	// 7) Bootstrap DC PPG (ventana corta inicial)
	for (int k = 0; k < 150; ++k) { 	// ~0.6 s a 250 Hz
		float r0 = (float)MyBoard.AFE4490_GetRED();
		float i0 = (float)MyBoard.AFE4490_GetIR();
		dc_red = 0.95f * dc_red + 0.05f * r0;
		dc_ir 	= 0.95f * dc_ir 	+ 0.05f * i0;
		delay(1000 / FS);
	}

	Serial.println("Sensores y LEDs listos.");

	// 8) Contador visible de arranque (5 s)
	for (int i = 5; i > 0; --i) {
		Serial.print("Esperando inicio... ");
		Serial.println(i);
		delay(1000);
	}

	// 9) WiFi + Aurora (después del conteo)
#if USE_AURORA
	XSerial.Wifi_init(WIFI_SSID, WIFI_PSWD);
	XSerial.UDP_Connect(AURORA_IP, AURORA_PORT);
#endif

	Serial.println("# Reporte cada 1s: SpO2, R y FC.");
	Serial.println("# Reporte cada 5s: FR y Tc.");
    Serial.println("# REPORTE JSON cada 15s al Monitor Serial.");
}
// --------------------------------------------------------

void loop() {
	static uint32_t last_report_ms 			= 0; 	// para SpO2/R/FC cada 1 s
	static uint32_t last_valid_ms 			= 0; 	// resetear buffers si no hay señal PPG
	static uint32_t last_ptt_report_ms 	= 0; 	// PTT cada 10 s
	static uint32_t last_fr_report 			= 0; 	// FR cada 5 s
	static uint32_t last_temp_report_ms = 0; 	// Reporte de Temperatura
	static uint32_t last_json_report_ms = 0; 	// NUEVO: Timer para JSON
#if USE_AURORA
	static uint32_t last_udp_ms 			= 0; 	// envío continuo a Aurora
#endif

	unsigned long now_ms = millis();

	// ---------- LECTURA LENTA DE TEMPERATURA (Tc) ----------
	if (now_ms - last_temp_report_ms >= TEMP_REPORT_MS) {
		last_temp_C = mlx.readObjectTempC(); 
		last_temp_report_ms = now_ms;
	}
	// -------------------------------------------------------


	// ---------- ECG: lectura y cálculo de FC ----------
	double ecg_v = MyBoard.AD8232_GetVoltage(AD8232_XS1);

	bool above = (ecg_v > THRESHOLD_HR);

	if (above && !wasAboveThreshold) {
		// detección de R-peak
		if (lastBeatTime == 0 || (now_ms - lastBeatTime) > REFRACTORY_MS) {
			if (lastBeatTime != 0) {
				unsigned long rr = now_ms - lastBeatTime;
				double bpm = 60000.0 / (double)rr;

				if (lastBPM == 0.0) {
					lastBPM = bpm;
				} else {
					lastBPM = 0.7 * lastBPM + 0.3 * bpm; 	// suavizado
				}
			}
			// --- actualizamos prevBeatTime MÍNIMO
			prevBeatTime = lastBeatTime;
			lastBeatTime = now_ms;

			// ----- iniciar búsqueda de pulso PPG para PTT -----
			waitingPPG 		= true;
			ppg_peak_value 	= -1e9f;
			ppg_peak_time_ms = 0;
		}
	}
	wasAboveThreshold = above;
	lastECGVoltage 		= ecg_v;

	// ---------- PPG: cálculo de R y SpO2 ----------
	float red = (float)MyBoard.AFE4490_GetRED();
	float ir 	= (float)MyBoard.AFE4490_GetIR();

	if (fabsf(red) > SAT_THRESH || fabsf(ir) > SAT_THRESH) {
		delay(1000 / FS);
		return;
	}

	dc_red = ALPHA_DC * dc_red + (1.0f - ALPHA_DC) * red;
	dc_ir 	= ALPHA_DC * dc_ir 	+ (1.0f - ALPHA_DC) * ir;

	float ac_r = red - dc_red;
	float ac_i = ir 	- dc_ir;

	// RMS para R
	pushRMS(ac_r, ac_i);
	float ac_r_rms = (filled_rms > 0) ? sqrtf(fmaxf(sumsq_r / filled_rms, 0.0f)) : 0.0f;
	float ac_i_rms = (filled_rms > 0) ? sqrtf(fmaxf(sumsq_i / filled_rms, 0.0f)) : 0.0f;

	bool signal_ok = (ac_i_rms > MIN_SIGNAL && ac_r_rms > MIN_SIGNAL);

	float R = NAN;
	if (signal_ok && dc_red > 1.0f && dc_ir > 1.0f) {
		float n_red = ac_r_rms / clamp_pos(dc_red);
		float n_ir 	= ac_i_rms / clamp_pos(dc_ir);
		R = n_red / n_ir;

		if (isfinite(R)) {
			pushR(R);
			last_valid_ms = now_ms;
		}
	}

	if (now_ms - last_valid_ms > 15000) {
		resetBuffers();
		stable_R 			= false;
		n_valid_spo2 	= 0;
	}

	float Ravg 	= meanRref();
	float SpO2 	= NAN;
	bool 	have_spo2_now = (!isnan(Ravg));

	if (have_spo2_now) {
		SpO2 = B_SPO2 + A_SPO2 * Ravg;
		if (SpO2 < 70.0f) 	SpO2 = 70.0f;
		if (SpO2 > 100.0f) SpO2 = 100.0f;
	}

	if (have_spo2_now && isfinite(SpO2) && isfinite(Ravg)) {
		if (n_valid_spo2 < NUM_MEASUREMENTS) {
			spo2_values[n_valid_spo2] = SpO2;
			r_values[n_valid_spo2] 	= Ravg;
			n_valid_spo2++;
		} else {
			for (int i = 0; i < NUM_MEASUREMENTS - 1; i++) {
				spo2_values[i] = spo2_values[i+1];
				r_values[i] 	= r_values[i+1];
			}
			spo2_values[NUM_MEASUREMENTS - 1] = SpO2;
			r_values[NUM_MEASUREMENTS - 1] 	= Ravg;
		}
	}

	if (n_valid_spo2 == NUM_MEASUREMENTS) {
		float r_min, r_max;
		min_max_array(r_values, NUM_MEASUREMENTS, r_min, r_max);
		if (fabsf(r_max - r_min) < 1.0f) {
			stable_R = true;
			last_stable_R_time = now_ms;
		}
	}

	float spo2_to_print = SpO2;
	float R_to_print 		= R;

	// ---------- Filtro LPF para PPG (para PTT y gráfica) ----------
	y_lpf_ir += alpha_lp * (ac_i - y_lpf_ir);

	// --------- DECIMACIÓN PARA FR --------------
	decim_counter++;
	if (decim_counter >= DECIM_FACTOR) {
		decim_counter = 0;

		// Señales respiratorias decimadas:
		float resp_am = fabsf(ac_i); 	// AM: magnitud AC del IR
		float resp_bw = dc_ir; 		// BW: componente DC lenta
		float resp_fm = NAN;

		if (prevBeatTime != 0 && lastBeatTime != 0 && lastBeatTime > prevBeatTime) {
			float rr_sec = (float)(lastBeatTime - prevBeatTime) / 1000.0f;
			static float rr_prev = NAN;
			if (isnan(rr_prev)) rr_prev = rr_sec;
			resp_fm = rr_sec - rr_prev; 		// variaciones RR
			rr_prev = rr_sec;
		}

		float norm_am = resp_am;
		float norm_bw = resp_bw;
		if (norm_am == 0.0f) norm_am = 1e-6f;
		if (norm_bw == 0.0f) norm_bw = 1e-6f;

		if (!isnan(resp_fm)) resp_fm *= 10.0f;

		pushRespiratorySignals(norm_am, norm_bw, resp_fm);
	}

	// ---------- Cálculo de PTT ----------
	if (waitingPPG && lastBeatTime != 0) {
		unsigned long dt = now_ms - lastBeatTime;

		// ventana donde buscamos el pico del pulso PPG
		if (dt >= PPG_SEARCH_MIN_MS && dt <= PPG_SEARCH_MAX_MS) {
			if (y_lpf_ir > ppg_peak_value) {
				ppg_peak_value 	= y_lpf_ir;
				ppg_peak_time_ms = now_ms;
			}
		}

		// termina la ventana de búsqueda
		if (dt > PPG_SEARCH_MAX_MS) {
			if (ppg_peak_time_ms > 0) {
				float ptt = (ppg_peak_time_ms - lastBeatTime) / 1000.0f; 	// en segundos
				lastPTT = ptt;
				ptt_sum += ptt;
				ptt_count++;
			}
			waitingPPG = false;
		}
	}

	// ---------- Reporte cada 1 segundo: SpO2, R y FC (Monitor Serial) ----------
	if (now_ms - last_report_ms >= REPORT_INTERVAL_MS) {
		Serial.print("SpO2 = ");
		Serial.print(round(spo2_to_print), 2);
		Serial.print(", R = ");
		Serial.print(R_to_print, 6);
		Serial.print(", FC = ");
		Serial.print(round(lastBPM));
		Serial.println(" bpm");
		last_report_ms = now_ms;
	}

	// ---------- Cálculo y Reporte FR y Tc (Temperatura) cada 5 segundos ----------
	if (now_ms - last_fr_report >= FR_REPORT_MS) {
		float fr_hz = compute_FR_hz();
		
		Serial.print("FR = ");
		if (!isnan(fr_hz)) {
			float fr_bpm = fr_hz * 60.0f;
			last_FR = fr_bpm; // Guarda en global
			last_FR_time = now_ms;
			Serial.print(fr_bpm, 2);
			Serial.print(" rpm");
		} else {
			last_FR = NAN;
			Serial.print("NaN rpm");
		}

		// Impresión de Temperatura (Tc)
		Serial.print(", Tc = ");
		if (isnan(last_temp_C)) {
			Serial.println("NaN *C");
		} else {
			Serial.print(last_temp_C, 2); 
			Serial.println("*C");
		}

		last_fr_report = now_ms;
	}

	// ---------- Cálculo y Reporte PTT promedio y presión arterial cada 10 segundos ----------
	if (now_ms - last_ptt_report_ms >= PTT_REPORT_INTERVAL_MS) {
		if (ptt_count > 0) {
			float ptt_avg = (float)(ptt_sum / (double)ptt_count);
			
			// Cálculo de la presión arterial
			last_P_sistolica = round(a_systolic * ptt_avg + b_systolic); // Guarda en global
			last_P_diastolica = round(a_diastolic * ptt_avg + b_diastolic); // Guarda en global
			
			// Imprimir PTT y presión arterial (Monitor Serial)
			Serial.print("PTT_avg_10s = ");
			Serial.print(ptt_avg, 4);
			Serial.print(" s, ");
			Serial.print("P_sistólica = ");
			Serial.print(last_P_sistolica);
			Serial.print(" mmHg, ");
			Serial.print("P_diastólica = ");
			Serial.print(last_P_diastolica);
			Serial.println(" mmHg");
		} else {
            last_P_sistolica = NAN;
            last_P_diastolica = NAN;
			Serial.println("PTT_avg_10s = NaN, P_sistólica = NaN, P_diastólica = NaN");
		}
		// reiniciar acumuladores
		ptt_sum 	= 0.0;
		ptt_count = 0;
		last_ptt_report_ms = now_ms;
	}

    // ---------- REPORTE CONSOLIDADO JSON CADA 15 SEGUNDOS (Monitor Serial) ----------
    if (now_ms - last_json_report_ms >= JSON_REPORT_INTERVAL_MS) {
        last_json_report_ms = now_ms;

        // Formatear el JSON usando String() y c_str() para asegurar la precisión de los flotantes
        char jsonBuffer[128];
        
        // Uso de String() para manejar flotantes con precisión en snprintf
        int len = snprintf(
            jsonBuffer, sizeof(jsonBuffer),
            "{\"Psist\":%s,\"Pdiast\":%s,\"FC\":%s,\"FR\":%s,\"SpO2\":%s,\"Tc\":%s}",
            isnan(last_P_sistolica) ? "null" : String(round(last_P_sistolica)).c_str(),
            isnan(last_P_diastolica) ? "null" : String(round(last_P_diastolica)).c_str(),
            isnan(round(lastBPM)) ? "null" : String((float)round(lastBPM)).c_str(), // lastBPM es double, casteamos a float
            isnan(last_FR) ? "null" : String(round(last_FR)).c_str(),
            isnan(round(spo2_to_print)) ? "null" : String(round(spo2_to_print)).c_str(),
            isnan(last_temp_C) ? "null" : String(last_temp_C, 1).c_str()
        );
        
        // El reporte JSON se envía al Monitor Serial
        Serial.print("JSON_REPORT: ");
        Serial.println(jsonBuffer);
    }
    // ---------------------------------------------------------------------------------


	// ---------- Señal para graficar en Aurora (ECG o PPG) ----------
#if USE_AURORA
	uint32_t now_udp = now_ms;

	if (now_udp - last_udp_ms >= UDP_PERIOD_MS) {
		float valueToSend;

		if (GRAFICA == PPG) {
			valueToSend = y_lpf_ir; 		// PPG filtrada
		} else {
			valueToSend = (float)ecg_v; 	// ECG en voltios
		}

		if (isfinite(valueToSend) && fabsf(valueToSend) < SAT_THRESH) {
			char out[24];
			snprintf(out, sizeof(out), "%.3f", valueToSend);
			XSerial.println(out); // Envía a Aurora
		}
		last_udp_ms = now_udp;
	}
#endif

	// ---------- Ritmo de muestreo ----------
	delay(1000 / FS); 	// ~4 ms → 250 Hz
}