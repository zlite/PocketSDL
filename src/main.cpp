#include <Arduino.h>
#include <WiFi.h>
#include <AsyncTCP.h>
#include <ESPAsyncWebServer.h>
#include <ESPmDNS.h>
#include <Wire.h>
#include <math.h>
#include <Preferences.h>
#include <Adafruit_NeoPixel.h>
#include <Adafruit_AS7343.h>

// ── Hardware ──────────────────────────────────────────────────────────────────
#define NEOPIXEL_PIN   0
#define NEOPIXEL_POWER 2
#define LED_BRIGHTNESS 200

#ifndef WIFI_SSID
#define WIFI_SSID "YOUR_WIFI_SSID"
#endif

#ifndef WIFI_PASS
#define WIFI_PASS "YOUR_WIFI_PASSWORD"
#endif

static const char WIFI_SSID_VALUE[] = WIFI_SSID;
static const char WIFI_PASS_VALUE[] = WIFI_PASS;

Adafruit_NeoPixel pixel(1, NEOPIXEL_PIN, NEO_GRB + NEO_KHZ800);
Adafruit_AS7343   as7343;
AsyncWebServer    server(80);
Preferences       prefs;

static uint8_t ledR=0, ledG=0, ledB=0;
static bool    sensorOK=false;
static String  wifiSSID;
static String  wifiPass;

void setLED(uint8_t r, uint8_t g, uint8_t b){
  ledR=r; ledG=g; ledB=b;
  pixel.setPixelColor(0, pixel.Color(r,g,b)); pixel.show();
}

// ── Channel layout (18-ch mode) ───────────────────────────────────────────────
//  0:FZ/450  1:FY/555  2:FXL/600  3:NIR/855  4,5:CLR0
//  6:F2/425  7:F3/475  8:F4/515   9:F6/640   10,11:CLR1
// 12:F1/405 13:F7/690 14:F8/745  15:F5/550   16,17:CLR2
#define NUM_CH 18
static const int   SPEC_CH[] = {12,6,0,7,8,15,1,2,9,13};
static const int   N_SPEC    = 10;
static const float SPEC_WL[] = {405,425,450,475,515,550,555,600,640,690};

// LED spectral weights (Gaussian, R~635nm G~528nm B~455nm)
static const float W_R[NUM_CH]={0.00f,0.11f,0.68f,0.00f,0,0,0.00f,0.00f,0.00f,1.00f,0,0,0.00f,0.39f,0.02f,0.10f,0,0};
static const float W_G[NUM_CH]={0.08f,0.74f,0.12f,0.00f,0,0,0.01f,0.32f,0.93f,0.01f,0,0,0.00f,0.00f,0.00f,0.82f,0,0};
static const float W_B[NUM_CH]={0.98f,0.01f,0.00f,0.00f,0,0,0.49f,0.73f,0.06f,0.00f,0,0,0.14f,0.00f,0.00f,0.01f,0,0};

// ── Buffers ───────────────────────────────────────────────────────────────────
struct Reading { uint8_t r,g,b; uint16_t ch[NUM_CH]; };
static const int LOG_MAX=120; static Reading logBuf[LOG_MAX];
static int logHead=0, logCount=0;

struct Thought { uint8_t r,g,b; float score; bool improved; char msg[96]; };
static const int TH_MAX=50; static Thought thBuf[TH_MAX];
static int thHead=0, thCount=0;

static const int SCORE_MAX=200; static float scoreHist[SCORE_MAX];
static float acceptedScoreHist[SCORE_MAX];
static int scoreHead=0, scoreLen=0;
static int sensorReadFailures=0;

static String jsonEscape(const char* src);
static void setStateMessage(const char* msg);
static void stopExperiment(const char* msg, bool turnLedOff);
static bool hasCompileTimeWiFiCreds();
static bool loadStoredWiFiCreds();
static bool saveStoredWiFiCreds(const String& ssid, const String& pass);
static String readSerialLine(bool echoInput = true);
static bool promptForWiFiCreds();
static void connectWiFi();
static void startMdns();
static bool parseJsonFloat(const String& body, const char* key, float& valueOut);
static String buildStatusJson();
static String buildScoresJson();
static String buildThoughtsJson();
static String buildLogJson();
static String buildSnapshotJson(bool includeLog);
static bool getRequestInt(AsyncWebServerRequest* request, const char* key, int& valueOut);
static bool getRequestFloat(AsyncWebServerRequest* request, const char* key, float& valueOut);
static bool getRequestString(AsyncWebServerRequest* request, const char* key, String& valueOut);
static bool getRequestRgb(AsyncWebServerRequest* request, uint8_t& r, uint8_t& g, uint8_t& b);

void pushScore(float s){
  int idx=scoreHead%SCORE_MAX;
  scoreHist[idx]=s;
  acceptedScoreHist[idx]=-1.0f;
  scoreHead++;
  if(scoreLen<SCORE_MAX)scoreLen++;
}
void pushAcceptedScore(float s){
  int idx=(scoreHead-1+SCORE_MAX)%SCORE_MAX;
  acceptedScoreHist[idx]=s;
}

void addThought(uint8_t r,uint8_t g,uint8_t b,float sc,bool imp,const char* msg){
  Thought& t=thBuf[thHead%TH_MAX]; t.r=r;t.g=g;t.b=b;t.score=sc;t.improved=imp;
  strncpy(t.msg,msg,95); t.msg[95]='\0'; thHead++; if(thCount<TH_MAX)thCount++;
  Serial.printf("[SDL] %s\n",msg);
}

// ── Spectral helpers ──────────────────────────────────────────────────────────
static float recTgtSpec[NUM_CH]={};   // raw target spectrum (sum-normalised in scoring)
static float ambSpec[NUM_CH]={};      // unused — kept for future reference
static uint8_t recTgtR=255, recTgtG=165, recTgtB=0;

static bool isSaturated(const uint16_t* buf){
  for(int i=0;i<N_SPEC;i++) if(buf[SPEC_CH[i]]>60000) return true;
  return false;
}

// Score: 1 - L2 distance between sum-normalised spectra (probability distributions).
// Ambient (dark frame) is subtracted before normalisation so room light doesn't corrupt shape.
// sqrtf(l2) ranges 0 (identical shape) to sqrt(2) (orthogonal), mapped to 0–100%.
float computeScore(const uint16_t* meas){
  if(isSaturated(meas)) return 0.0f;
  float m[N_SPEC], t[N_SPEC];
  float msum=0, tsum=0;
  for(int i=0;i<N_SPEC;i++){
    int ci=SPEC_CH[i];
    m[i]=max(0.0f,(float)meas[ci]-ambSpec[ci]);
    t[i]=recTgtSpec[ci];
    msum+=m[i]; tsum+=t[i];
  }
  if(msum<1.0f||tsum<1.0f) return 0.0f;
  // Luminance penalty: a dim colour that has the right hue shape still scores low.
  // sqrtf keeps it gentle — 50% brightness → 71% penalty, 25% → 50%.
  float lumPenalty = msum < tsum ? sqrtf(msum/tsum) : 1.0f;
  float l2=0;
  for(int i=0;i<N_SPEC;i++){
    float diff=m[i]/msum - t[i]/tsum;
    l2+=diff*diff;
  }
  // Denominator 0.45 calibrated so a random colour averages ~50%; a true match scores ~90%+.
  return max(0.0f,(1.0f - sqrtf(l2)/0.45f)*100.0f) * lumPenalty;
}

void genTargetSpectrum(uint8_t r,uint8_t g,uint8_t b){
  float rf=r/255.0f,gf=g/255.0f,bf=b/255.0f;
  for(int i=0;i<NUM_CH;i++) recTgtSpec[i]=rf*W_R[i]+gf*W_G[i]+bf*W_B[i];
}

// Gaussian random (Box-Muller)
float gaussRand(){
  float u1=max(1e-6f,(float)random(1,1000000)/1000000.0f);
  float u2=(float)random(0,1000000)/1000000.0f;
  return sqrtf(-2.0f*logf(u1))*cosf(2.0f*M_PI*u2);
}

// ── Algorithm state ───────────────────────────────────────────────────────────
enum Alg { ALG_NONE=0, ALG_SPSA, ALG_BAYES, ALG_THOMPSON, ALG_CMAES };
static Alg   alg=ALG_NONE;
static bool  running=false, settling=false;
static uint32_t nextMs=0;
static uint32_t settleMs=200, pauseMs=30;

static float spsaInitH=40.0f, spsaInitA=60.0f;
static int   spsaRestartPatience=40;
static float boKappaInit=3.0f;
static int   boCandidateCount=80;
static float tsBwInit=0.25f;
static int   tsCandidateCount=80;
static float cmaSigmaInit=32.0f;
static int   cmaMuActive=3;

static uint8_t  bestR=128,bestG=128,bestB=128;
static float    bestScore=-1.0f;
static int      totalIter=0;
static int      evalCount=0;
static uint32_t runStartMs=0;
static int32_t  hit90Ms=-1;
static bool     converged=false;
static int      calibPhase=0;  // 0=running, 1=dark reading, 2=target reading
static float    lastScore=0.0f;
static char     stateMsg[100]="Set a target color and press Search.";

static String jsonEscape(const char* src){
  String out;
  if(!src) return out;
  while(*src){
    char c=*src++;
    switch(c){
      case '\\': out+="\\\\"; break;
      case '"':  out+="\\\""; break;
      case '\n': out+="\\n"; break;
      case '\r': out+="\\r"; break;
      case '\t': out+="\\t"; break;
      default:
        if((uint8_t)c >= 0x20) out += c;
        break;
    }
  }
  return out;
}

static void setStateMessage(const char* msg){
  if(!msg){
    stateMsg[0]='\0';
    return;
  }
  strncpy(stateMsg,msg,sizeof(stateMsg)-1);
  stateMsg[sizeof(stateMsg)-1]='\0';
}

static void stopExperiment(const char* msg, bool turnLedOff){
  running=false;
  settling=false;
  calibPhase=0;
  if(msg) setStateMessage(msg);
  if(turnLedOff) setLED(0,0,0);
}

static bool hasCompileTimeWiFiCreds(){
  return strcmp(WIFI_SSID_VALUE,"YOUR_WIFI_SSID")!=0;
}

static bool loadStoredWiFiCreds(){
  if(!prefs.begin("wifi", true)) return false;
  wifiSSID = prefs.getString("ssid", "");
  wifiPass = prefs.getString("pass", "");
  prefs.end();
  return wifiSSID.length() > 0;
}

static bool saveStoredWiFiCreds(const String& ssid, const String& pass){
  if(!prefs.begin("wifi", false)) return false;
  bool ok = prefs.putString("ssid", ssid) > 0;
  prefs.putString("pass", pass);
  prefs.end();
  return ok;
}

static String readSerialLine(bool echoInput){
  String line;
  while(true){
    while(!Serial.available()) delay(10);
    char c = (char)Serial.read();
    if(c == '\r') continue;
    if(c == '\n'){
      if(echoInput) Serial.println();
      break;
    }
    if(c == '\b' || c == 127){
      if(line.length() > 0){
        line.remove(line.length() - 1);
        if(echoInput) Serial.print("\b \b");
      }
      continue;
    }
    if((uint8_t)c < 0x20) continue;
    line += c;
    if(echoInput) Serial.print(c);
  }
  return line;
}

static bool promptForWiFiCreds(){
  Serial.println();
  Serial.println("WiFi credentials not found.");
  Serial.println("Enter them in the serial monitor and press Enter.");
  while(true){
    Serial.print("SSID: ");
    wifiSSID = readSerialLine();
    if(wifiSSID.length() > 0) break;
    Serial.println("SSID cannot be empty.");
  }
  Serial.print("Password (leave blank for open network): ");
  wifiPass = readSerialLine();
  if(!saveStoredWiFiCreds(wifiSSID, wifiPass)){
    Serial.println("WARN: failed to save WiFi credentials to NVS.");
  } else {
    Serial.println("Saved WiFi credentials.");
  }
  return true;
}

static void connectWiFi(){
  if(hasCompileTimeWiFiCreds()){
    wifiSSID = WIFI_SSID_VALUE;
    wifiPass = WIFI_PASS_VALUE;
  } else if(!loadStoredWiFiCreds()){
    promptForWiFiCreds();
  }

  if(wifiSSID.length() == 0){
    Serial.println("WiFi disabled: no credentials available.");
    setStateMessage("WiFi disabled: enter credentials in Serial.");
    return;
  }

  WiFi.begin(wifiSSID.c_str(), wifiPass.c_str());
  Serial.print("Connecting to ");
  Serial.print(wifiSSID);
  Serial.print(" ");
  setLED(0,0,60);
  int tries=0;
  while(WiFi.status()!=WL_CONNECTED&&tries++<40){delay(500);Serial.print(".");}
  if(WiFi.status()==WL_CONNECTED){
    startMdns();
    setLED(0,60,0);delay(1200);setLED(0,0,0);
  } else {
    Serial.println("\nWiFi failed");
    setStateMessage("WiFi connection failed. Reboot to re-enter credentials in Serial.");
    setLED(60,0,0);delay(2000);setLED(0,0,0);
  }
}

static void startMdns(){
  const char* hostName = "sdl";
  if(MDNS.begin(hostName)){
    MDNS.addService("http", "tcp", 80);
    Serial.println("\nOpen: http://" + String(hostName) + ".local or http://" + WiFi.localIP().toString());
    setStateMessage("WiFi connected at http://sdl.local");
  } else {
    Serial.println("\nOpen: http://" + WiFi.localIP().toString());
    Serial.println("WARN: mDNS failed to start; use the IP address instead.");
    setStateMessage("WiFi connected (mDNS unavailable).");
  }
}

void updateBest(uint8_t r,uint8_t g,uint8_t b,float sc,const char* alg_name){
  bool imp=(sc>bestScore);
  if(imp){ bestScore=sc; bestR=r; bestG=g; bestB=b; }
  if(hit90Ms < 0 && imp && bestScore >= 90.0f && runStartMs > 0){
    hit90Ms = (int32_t)(millis() - runStartMs);
  }
  char msg[100];
  snprintf(msg,99,"%s step %d: rgb(%d,%d,%d) score=%.1f%s",
    alg_name,totalIter,r,g,b,sc,imp?" ↑ BETTER":"");
  setStateMessage(msg);
  addThought(r,g,b,sc,imp,msg);
  pushScore(sc);
  pushAcceptedScore(sc);
  totalIter++;
  if(bestScore>95.0f){
    converged=true;
    snprintf(msg,99,"CONVERGED — Recipe: R=%d%% G=%d%% B=%d%% (score=%.1f%%)",
      (int)(bestR/2.55f),(int)(bestG/2.55f),(int)(bestB/2.55f),bestScore);
    setStateMessage(msg);
    addThought(bestR,bestG,bestB,bestScore,true,msg);
    running=false; setLED(bestR,bestG,bestB);
  } else if(evalCount>=400){
    converged=false;
    snprintf(msg,99,"BUDGET REACHED — Recipe: R=%d%% G=%d%% B=%d%% (score=%.1f%%)",
      (int)(bestR/2.55f),(int)(bestG/2.55f),(int)(bestB/2.55f),bestScore);
    setStateMessage(msg);
    addThought(bestR,bestG,bestB,bestScore,false,msg);
    running=false; setLED(bestR,bestG,bestB);
  }
}

void resetAll(){
  logHead=logCount=0; thHead=thCount=0; scoreHead=scoreLen=0;
  bestScore=-1.0f; bestR=bestG=bestB=128; totalIter=0; converged=false;
  evalCount=0;
  runStartMs=0;
  hit90Ms=-1;
  lastScore=0.0f;
  sensorReadFailures=0;
}

// ── Algorithm 1: SPSA Gradient Descent ───────────────────────────────────────
// Simultaneous perturbation — 2 measurements per gradient estimate
static float   spRf=128,spGf=128,spBf=128; // float to accumulate sub-unit steps
static int8_t  spDelta[3]={1,1,1};
static float   spScorePlus=0;
static float   spH=40.0f, spA=60.0f;
static int     spPhase=0, spK=0, spNoImprov=0;

void initSPSA(){
  spRf=random(256); spGf=random(256); spBf=random(256);
  spH=spsaInitH; spA=spsaInitA; spPhase=0; spK=0; spNoImprov=0;
}
// 3 phases per gradient step: probe+, probe-, evaluate updated position
void stepSPSA(){
  if(spPhase==0){
    for(int d=0;d<3;d++) spDelta[d]=(random(2)*2-1);
    setLED((uint8_t)constrain((int)(spRf+spH*spDelta[0]),0,255),
           (uint8_t)constrain((int)(spGf+spH*spDelta[1]),0,255),
           (uint8_t)constrain((int)(spBf+spH*spDelta[2]),0,255));
  } else if(spPhase==1){
    setLED((uint8_t)constrain((int)(spRf-spH*spDelta[0]),0,255),
           (uint8_t)constrain((int)(spGf-spH*spDelta[1]),0,255),
           (uint8_t)constrain((int)(spBf-spH*spDelta[2]),0,255));
  } else { // phase 2: evaluate the actual updated position
    setLED((uint8_t)constrain((int)spRf,0,255),
           (uint8_t)constrain((int)spGf,0,255),
           (uint8_t)constrain((int)spBf,0,255));
  }
}
void afterSPSA(const Reading& rd, float sc){
  if(spPhase==0){ spScorePlus=sc; pushScore(sc); spPhase=1; return; }
  if(spPhase==1){
    float diff=(spScorePlus-sc)/(2.0f*spH);
    float ak=spA/powf(spK+1+10,0.602f);
    spRf=constrain(spRf+ak*diff*(float)spDelta[0],0.0f,255.0f);
    spGf=constrain(spGf+ak*diff*(float)spDelta[1],0.0f,255.0f);
    spBf=constrain(spBf+ak*diff*(float)spDelta[2],0.0f,255.0f);
    spH=max(spH*0.995f,6.0f); spK++;
    pushScore(sc); spPhase=2; return;
  }
  // Phase 2: sc is the score at the updated position
  float prevBest=bestScore;
  updateBest((uint8_t)spRf,(uint8_t)spGf,(uint8_t)spBf,sc,"GD-SPSA");
  if(sc>prevBest+0.5f) spNoImprov=0; else spNoImprov++;
  if(!converged && spNoImprov>spsaRestartPatience){
    // Stuck in local optimum — restart from new random position
    addThought(spRf,spGf,spBf,sc,false,"SPSA stuck, restarting random...");
    spRf=random(256); spGf=random(256); spBf=random(256);
    spH=spsaInitH; spK=0; spNoImprov=0;
  }
  spPhase=0;
}

// ── Algorithm 2: Bayesian Optimisation (IDW-UCB) ──────────────────────────────
static const int BO_MAX=60;
struct BOObs { float r,g,b,score; };
static BOObs   boHist[BO_MAX]; static int boLen=0;
static float   boKappa=3.0f;

void initBO(){
  boLen=0; boKappa=boKappaInit;
  setLED(random(256),random(256),random(256)); // start random
}
float boIDW(float r,float g,float b, float* varOut){
  int nObs=min(boLen,BO_MAX);
  float wsum=0,wmean=0,wvar=0;
  for(int i=0;i<nObs;i++){
    float dr=(r-boHist[i].r)/255.0f, dg=(g-boHist[i].g)/255.0f, db=(b-boHist[i].b)/255.0f;
    float d2=dr*dr+dg*dg+db*db;
    float w=1.0f/(d2+1e-4f);
    wsum+=w; wmean+=w*boHist[i].score;
  }
  if(wsum<1e-9f){ *varOut=50.0f*50.0f; return 50.0f; }
  float mean=wmean/wsum;
  for(int i=0;i<nObs;i++){
    float dr=(r-boHist[i].r)/255.0f, dg=(g-boHist[i].g)/255.0f, db=(b-boHist[i].b)/255.0f;
    float d2=dr*dr+dg*dg+db*db; float w=1.0f/(d2+1e-4f);
    float diff=boHist[i].score-mean; wvar+=w*diff*diff;
  }
  *varOut=wvar/wsum; return mean;
}
void stepBO(){
  if(boLen<2){ setLED(random(256),random(256),random(256)); return; }
  // Sample 80 candidates, pick highest UCB
  uint8_t bR=bestR,bG=bestG,bB=bestB; float bAcq=-1e9;
  for(int k=0;k<boCandidateCount;k++){
    uint8_t cr=random(256),cg=random(256),cb=random(256);
    float v; float m=boIDW(cr,cg,cb,&v);
    float acq=m+boKappa*sqrtf(v);
    if(acq>bAcq){ bAcq=acq; bR=cr; bG=cg; bB=cb; }
  }
  setLED(bR,bG,bB);
}
void afterBO(const Reading& rd, float sc){
  if(boLen<BO_MAX){ boHist[boLen++]={(float)ledR,(float)ledG,(float)ledB,sc}; }
  else { boHist[boLen%BO_MAX]={(float)ledR,(float)ledG,(float)ledB,sc}; boLen++; }
  boKappa=max(boKappa*0.995f,0.5f); // decay exploration
  updateBest(ledR,ledG,ledB,sc,"BO");
}

// ── Algorithm 3: Thompson Sampling ───────────────────────────────────────────
static const int TS_MAX=60;
struct TSObs { float r,g,b,score; };
static TSObs   tsHist[TS_MAX]; static int tsLen=0;
static float   tsBW=0.25f; // kernel bandwidth

void initTS(){ tsLen=0; tsBW=tsBwInit; setLED(random(256),random(256),random(256)); }
void stepTS(){
  if(tsLen<3){ setLED(random(256),random(256),random(256)); return; }
  int nObs=min(tsLen,TS_MAX);
  uint8_t bR=bestR,bG=bestG,bB=bestB; float bSamp=-1e9;
  for(int k=0;k<tsCandidateCount;k++){
    uint8_t cr=random(256),cg=random(256),cb=random(256);
    // Gaussian kernel posterior
    float wsum=0,wmean=0,wvar=0;
    for(int i=0;i<nObs;i++){
      float dr=(cr-tsHist[i].r)/255.0f,dg=(cg-tsHist[i].g)/255.0f,db=(cb-tsHist[i].b)/255.0f;
      float w=expf(-(dr*dr+dg*dg+db*db)/(2.0f*tsBW*tsBW));
      wsum+=w; wmean+=w*tsHist[i].score;
    }
    float mean=(wsum>1e-9f)?wmean/wsum:50.0f;
    for(int i=0;i<nObs;i++){
      float dr=(cr-tsHist[i].r)/255.0f,dg=(cg-tsHist[i].g)/255.0f,db=(cb-tsHist[i].b)/255.0f;
      float w=expf(-(dr*dr+dg*dg+db*db)/(2.0f*tsBW*tsBW));
      float diff=tsHist[i].score-mean; wvar+=w*diff*diff;
    }
    float std=sqrtf((wsum>1e-9f?wvar/wsum:400.0f)+4.0f);
    float samp=mean+gaussRand()*std; // Thompson sample
    if(samp>bSamp){ bSamp=samp; bR=cr; bG=cg; bB=cb; }
  }
  setLED(bR,bG,bB);
}
void afterTS(const Reading& rd, float sc){
  int idx=tsLen<TS_MAX?tsLen:tsLen%TS_MAX;
  tsHist[idx]={(float)ledR,(float)ledG,(float)ledB,sc}; tsLen++;
  tsBW=max(tsBW*0.997f,0.05f);
  updateBest(ledR,ledG,ledB,sc,"TS");
}

// ── Algorithm 4: CMA-ES (diagonal covariance) ─────────────────────────────────
static const int CMA_LAM=6;
static float cmaM[3]={128,128,128};
static float cmaSig=32.0f;
static float cmaSD[3]={1.0f,1.0f,1.0f}; // per-dim scale (diagonal sqrt(C))
static float cmaPS[3]={0,0,0};  // evolution path
static uint8_t cmaOff[CMA_LAM][3]; static float cmaOffSc[CMA_LAM];
static int cmaPhase=0, cmaGen=0;
static const float CMA_CSig=0.3f, CMA_DSig=1.0f;
static const float CMA_CC=0.4f,   CMA_C1=0.2f;

void initCMA(){
  cmaM[0]=random(256); cmaM[1]=random(256); cmaM[2]=random(256); // start random
  cmaSig=cmaSigmaInit; cmaSD[0]=cmaSD[1]=cmaSD[2]=1.0f;
  cmaPS[0]=cmaPS[1]=cmaPS[2]=0; cmaPhase=0; cmaGen=0;
  // Generate first generation
  for(int k=0;k<CMA_LAM;k++)
    for(int d=0;d<3;d++)
      cmaOff[k][d]=(uint8_t)constrain((int)(cmaM[d]+cmaSig*cmaSD[d]*gaussRand()),0,255);
}
void stepCMA(){ setLED(cmaOff[cmaPhase][0],cmaOff[cmaPhase][1],cmaOff[cmaPhase][2]); }
void afterCMA(const Reading& rd, float sc){
  cmaOffSc[cmaPhase]=sc;
  pushScore(sc); // keep chart live during generation
  cmaPhase++;
  if(cmaPhase<CMA_LAM) return; // still evaluating generation

  // ── Update ──
  // Sort offspring by score (descending)
  int rank[CMA_LAM]; for(int i=0;i<CMA_LAM;i++) rank[i]=i;
  for(int i=0;i<CMA_LAM-1;i++) for(int j=i+1;j<CMA_LAM;j++)
    if(cmaOffSc[rank[j]]>cmaOffSc[rank[i]]){int t=rank[i];rank[i]=rank[j];rank[j]=t;}

  // Weighted mean of top-mu offspring
  float wNew[3]={0,0,0};
  for(int i=0;i<cmaMuActive;i++){
    float w=1.0f/(i+1); // simple 1/rank weights
    for(int d=0;d<3;d++) wNew[d]+=w*(float)cmaOff[rank[i]][d];
  }
  float wsum=0; for(int i=0;i<cmaMuActive;i++) wsum+=1.0f/(i+1);
  float step[3];
  for(int d=0;d<3;d++){ wNew[d]/=wsum; step[d]=(wNew[d]-cmaM[d])/(cmaSig*cmaSD[d]); cmaM[d]=wNew[d]; }

  // Update evolution path and per-dim std
  for(int d=0;d<3;d++){
    cmaPS[d]=(1-CMA_CSig)*cmaPS[d]+sqrtf(CMA_CSig*(2-CMA_CSig)*cmaMuActive)*step[d];
    cmaSD[d]=cmaSD[d]*expf(CMA_C1/2*(cmaPS[d]*cmaPS[d]-1));
    cmaSD[d]=constrain(cmaSD[d],0.1f,5.0f);
  }
  cmaSig=max(cmaSig*expf(CMA_CSig/CMA_DSig*(sqrtf(cmaPS[0]*cmaPS[0]+cmaPS[1]*cmaPS[1]+cmaPS[2]*cmaPS[2])/1.73f-1)),2.0f);

  // Report best of generation
  updateBest(cmaOff[rank[0]][0],cmaOff[rank[0]][1],cmaOff[rank[0]][2],cmaOffSc[rank[0]],"CMA-ES");
  cmaGen++;

  // Generate next generation
  for(int k=0;k<CMA_LAM;k++)
    for(int d=0;d<3;d++)
      cmaOff[k][d]=(uint8_t)constrain((int)(cmaM[d]+cmaSig*cmaSD[d]*gaussRand()),0,255);
  cmaPhase=0;
}

// ── Request helpers ───────────────────────────────────────────────────────────
static int skipWs(const String& body, int idx){
  while(idx<body.length() && isspace((unsigned char)body[idx])) idx++;
  return idx;
}

static bool parseJsonString(const String& body, const char* key, String& valueOut){
  String needle = "\"" + String(key) + "\"";
  int keyPos = body.indexOf(needle);
  if(keyPos < 0) return false;
  int colon = body.indexOf(':', keyPos + needle.length());
  if(colon < 0) return false;
  int start = skipWs(body, colon + 1);
  if(start >= body.length() || body[start] != '"') return false;
  start++;
  int end = start;
  while(end < body.length()){
    if(body[end] == '"' && body[end - 1] != '\\') break;
    end++;
  }
  if(end >= body.length()) return false;
  valueOut = body.substring(start, end);
  return true;
}

static bool parseJsonInt(const String& body, const char* key, int& valueOut){
  String needle = "\"" + String(key) + "\"";
  int keyPos = body.indexOf(needle);
  if(keyPos < 0) return false;
  int colon = body.indexOf(':', keyPos + needle.length());
  if(colon < 0) return false;
  int start = skipWs(body, colon + 1);
  if(start >= body.length()) return false;
  int end = start;
  if(body[end] == '-') end++;
  bool sawDigit=false;
  while(end < body.length() && isdigit((unsigned char)body[end])){
    sawDigit=true;
    end++;
  }
  if(!sawDigit) return false;
  valueOut = body.substring(start, end).toInt();
  return true;
}

static bool parseJsonFloat(const String& body, const char* key, float& valueOut){
  String needle = "\"" + String(key) + "\"";
  int keyPos = body.indexOf(needle);
  if(keyPos < 0) return false;
  int colon = body.indexOf(':', keyPos + needle.length());
  if(colon < 0) return false;
  int start = skipWs(body, colon + 1);
  if(start >= body.length()) return false;
  int end = start;
  if(body[end] == '-') end++;
  bool sawDigit=false, sawDot=false;
  while(end < body.length()){
    char c = body[end];
    if(isdigit((unsigned char)c)){ sawDigit=true; end++; continue; }
    if(c == '.' && !sawDot){ sawDot=true; end++; continue; }
    break;
  }
  if(!sawDigit) return false;
  valueOut = body.substring(start, end).toFloat();
  return true;
}

static bool parseRgbRequest(const String& body, uint8_t& r, uint8_t& g, uint8_t& b){
  int ri=0, gi=0, bi=0;
  if(!parseJsonInt(body,"r",ri) || !parseJsonInt(body,"g",gi) || !parseJsonInt(body,"b",bi)) return false;
  if(ri<0 || ri>255 || gi<0 || gi>255 || bi<0 || bi>255) return false;
  r=(uint8_t)ri;
  g=(uint8_t)gi;
  b=(uint8_t)bi;
  return true;
}

// ── HTML ──────────────────────────────────────────────────────────────────────
static const char HTML[] = R"HTML(
<!DOCTYPE html><html lang="en">
<head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>SDL Color Lab</title>
<style>
:root{--bg:#0d0f18;--card:#161923;--bd:#252838;--acc:#7c6fff;--tx:#dde;--dim:#666;--red:#e05;--grn:#0c6;--blu:#38f}
*{box-sizing:border-box;margin:0;padding:0}
body{background:var(--bg);color:var(--tx);font-family:'Segoe UI',sans-serif;padding:16px}
h1{text-align:center;font-size:1.25rem;letter-spacing:3px;color:#fff;text-transform:uppercase;margin-bottom:2px}
.sub{text-align:center;color:var(--dim);font-size:.75rem;margin-bottom:16px}
.tabs{display:flex;gap:6px;max-width:980px;margin:0 auto 12px;border-bottom:1px solid var(--bd);padding-bottom:6px}
.tab{padding:5px 16px;border-radius:6px 6px 0 0;cursor:pointer;font-size:.8rem;color:var(--dim);border:1px solid transparent;border-bottom:none}
.tab.active{background:var(--card);color:#fff;border-color:var(--bd)}
.page{display:none;max-width:980px;margin:0 auto}
.page.active{display:grid;grid-template-columns:300px 1fr;gap:12px}
@media(max-width:680px){.page.active{grid-template-columns:1fr}}
.card{background:var(--card);border-radius:10px;padding:14px;border:1px solid var(--bd)}
h2{font-size:.68rem;text-transform:uppercase;letter-spacing:1.5px;color:var(--dim);margin-bottom:10px}
input[type=color]{width:42px;height:32px;border:none;border-radius:5px;cursor:pointer;padding:0;background:none}
input[type=text]{flex:1;background:#1e2130;border:1px solid var(--bd);color:var(--tx);border-radius:6px;padding:6px 9px;font-size:.8rem}
input[type=text]:focus{outline:1px solid var(--acc)}
.row{display:flex;gap:7px;align-items:center;margin-bottom:8px}
button{border:none;border-radius:7px;padding:7px 16px;font-size:.8rem;font-weight:600;cursor:pointer;transition:background .2s}
.btn-go{background:var(--acc);color:#fff}.btn-go:hover{background:#5f52e8}.btn-go:disabled{background:#2a2d3a;color:#555;cursor:default}
.btn-stop{background:#922;color:#fff}.btn-stop:hover{background:#b33}.btn-stop:disabled{background:#2a2d3a;color:#555;cursor:default}
.btn-cal{background:#2a3040;color:#aab;border:1px solid var(--bd)}.btn-cal:hover{background:#353a50;color:#fff}.btn-cal:disabled{background:#1a1d28;color:#444;cursor:default}
.dot{width:8px;height:8px;border-radius:50%;display:inline-block}
.dot-idle{background:#333}.dot-run{background:#0c6;animation:pulse 1s infinite}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.3}}
/* Swatch */
.sw-lg{width:100%;height:52px;border-radius:7px;border:1px solid var(--bd);margin-bottom:6px}
.rgb-lbl{font-size:.72rem;color:var(--dim);text-align:center;font-family:monospace;margin-bottom:8px}
/* Alg cards */
.alg-grid{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin-bottom:10px}
.alg{border:2px solid var(--bd);border-radius:7px;padding:8px 10px;cursor:pointer;transition:all .15s}
.alg:hover{border-color:#4a4870}.alg.active{border-color:var(--acc);background:#1c1840}
.alg .nm{font-weight:600;font-size:.78rem}.alg .ds{font-size:.67rem;color:var(--dim);margin-top:3px;line-height:1.4}
.tune-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.tune-shell{display:none;margin-top:10px}
.tune-shell.open{display:block}
.tune-group{display:none;grid-column:1/-1}
.tune-group.active{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.tune-field{background:#111520;border:1px solid var(--bd);border-radius:8px;padding:8px}
.tune-field.wide{grid-column:1/-1}
.tune-field label{display:block;font-size:.62rem;letter-spacing:1px;text-transform:uppercase;color:var(--dim);margin-bottom:5px}
.tune-field input{width:100%;background:#1e2130;border:1px solid var(--bd);color:var(--tx);border-radius:6px;padding:6px 8px;font-size:.78rem}
.tune-field .hint{font-size:.64rem;line-height:1.35;color:#8790b3;margin-top:5px}
.tune-actions{display:flex;justify-content:space-between;align-items:center;margin-top:8px}
.btn-subtle{background:#1a1d28;color:#cdd1e5;border:1px solid var(--bd);padding:6px 10px}
.btn-subtle:hover{background:#242938}
/* Hyp bars */
.ch-row{display:flex;align-items:center;gap:7px;margin-bottom:5px}
.ch-lbl{font-size:.72rem;font-weight:700;width:10px}
.ch-lbl.r{color:var(--red)}.ch-lbl.g{color:var(--grn)}.ch-lbl.b{color:var(--blu)}
.track{flex:1;background:#1a1d28;border-radius:3px;height:9px;overflow:hidden}
.fill{height:100%;border-radius:3px;transition:width .4s}
.fill.r{background:var(--red)}.fill.g{background:var(--grn)}.fill.b{background:var(--blu)}
.pct{font-size:.72rem;font-family:monospace;width:32px;text-align:right;color:var(--dim)}
.stats{display:flex;gap:6px;margin:8px 0}
.stat{flex:1;background:#111520;border-radius:7px;padding:7px;text-align:center}
.stat .v{font-size:1rem;font-weight:700;color:var(--acc);display:block;font-variant-numeric:tabular-nums}
.stat .l{font-size:.62rem;color:var(--dim);text-transform:uppercase;letter-spacing:1px}
.msg{font-size:.72rem;color:var(--dim);margin:7px 0;padding:5px 8px;background:#111520;border-radius:5px;border-left:3px solid var(--acc);min-height:30px;line-height:1.5}
.msg.ok{border-left-color:#0c6;color:#9fd}.msg.done{border-left-color:#ffd700;color:#ffd700}
/* Think log */
.tlog{max-height:240px;overflow-y:auto;font-size:.7rem;font-family:monospace}
.tl{display:flex;gap:7px;align-items:flex-start;padding:6px 0;border-bottom:1px solid #111520}
.td{width:8px;height:8px;border-radius:50%;flex-shrink:0;margin-top:4px}
.tt{color:var(--dim);line-height:1.45;flex:1}.tt.imp{color:#9fd}
.tl-tag{display:inline-block;font-size:.58rem;letter-spacing:1px;text-transform:uppercase;border:1px solid var(--bd);border-radius:999px;padding:1px 6px;margin-right:6px;color:#9aa0bd;background:#111520}
.tl-tag.imp{border-color:#145;color:#9fd;background:#0d1b22}
/* Right column */
.rcol{display:flex;flex-direction:column;gap:12px}
.guide{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:10px}
@media(max-width:680px){.guide{grid-template-columns:1fr}}
.guide-box{background:#111520;border:1px solid var(--bd);border-radius:8px;padding:9px 10px}
.guide-k{font-size:.58rem;letter-spacing:1px;text-transform:uppercase;color:var(--dim);margin-bottom:4px}
.guide-v{font-size:.76rem;line-height:1.45;color:#eef}
.alg-hint{margin-top:8px;padding:8px 10px;background:linear-gradient(180deg,#121528,#0f1220);border:1px solid var(--bd);border-radius:8px}
.alg-hint .nm{font-size:.76rem;font-weight:700;color:#fff;margin-bottom:4px}
.alg-hint .ds{font-size:.68rem;line-height:1.45;color:#aeb4d0}
canvas{width:100%;display:block;border-radius:5px}
.leg{display:flex;gap:14px;font-size:.7rem;color:var(--dim);margin-bottom:6px;align-items:center}
.leg-sq{display:inline-block;width:11px;height:11px;border-radius:2px;vertical-align:middle;margin-right:3px}
/* Raw bars */
.bars{display:flex;align-items:flex-end;gap:2px;height:80px}
.bw{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px}
.rawb{width:100%;border-radius:2px 2px 0 0;min-height:1px;transition:height .3s}
.bl{font-size:7px;color:var(--dim);writing-mode:vertical-rl;transform:rotate(180deg);height:22px}
/* Explore tab */
.exp-page{display:none;max-width:980px;margin:0 auto}
.exp-page.active{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:680px){.exp-page.active{grid-template-columns:1fr}}
.full{grid-column:1/-1}
table{width:100%;border-collapse:collapse;font-size:.7rem}
th{color:var(--dim);text-align:right;padding:3px 5px;border-bottom:1px solid var(--bd);font-weight:400}
th:nth-child(-n+5){text-align:left}
td{padding:3px 5px;border-bottom:1px solid #111520;font-family:monospace;text-align:right}
td:nth-child(-n+5){text-align:left}
.sc{display:inline-block;width:9px;height:9px;border-radius:2px;vertical-align:middle}
</style></head>
<body>
<h1>SDL Color Lab</h1>
<div class="sub">Self-Driving Lab &mdash; ESP32 Feather V2 + AS7343</div>
<div class="tabs">
  <div class="tab active" onclick="showTab('recipe',this)">Recipe Search</div>
  <div class="tab" onclick="showTab('explore',this)">Explore</div>
</div>

<!-- ═══ RECIPE TAB ═══ -->
<div class="page active" id="tab-recipe">
  <div style="display:flex;flex-direction:column;gap:12px">

    <!-- 1. Target -->
    <div class="card">
      <h2>1 — Target Color</h2>
      <div class="row">
        <input type="color" id="colorPicker" value="#ffa500" oninput="syncPicker(this)">
        <input type="text"  id="colorText" value="orange" placeholder="orange, #ff8000, rgb(255,128,0)">
        <button class="btn-go" onclick="applyTarget()">Set</button>
      </div>
      <div class="sw-lg" id="tgtSw" style="background:#ffa500"></div>
      <div class="rgb-lbl" id="tgtRGB">rgb(255, 165, 0)</div>
    </div>

    <!-- 2. Algorithm -->
    <div class="card">
      <h2>2 — Algorithm</h2>
      <div class="alg-grid">
        <div class="alg active" data-alg="spsa" onclick="selAlg(this)">
          <div class="nm">Gradient Descent</div>
          <div class="ds">SPSA: estimates gradient with 2 probes per step. Fast near maxima.</div>
        </div>
        <div class="alg" data-alg="bayes" onclick="selAlg(this)">
          <div class="nm">Bayesian Optimisation</div>
          <div class="ds">IDW-UCB surrogate. Balances exploration and exploitation.</div>
        </div>
        <div class="alg" data-alg="thompson" onclick="selAlg(this)">
          <div class="nm">Thompson Sampling</div>
          <div class="ds">Samples from posterior belief. Probabilistic exploration.</div>
        </div>
        <div class="alg" data-alg="cmaes" onclick="selAlg(this)">
          <div class="nm">CMA-ES</div>
          <div class="ds">Evolves a population. Adapts search geometry each generation.</div>
        </div>
      </div>
      <div class="row">
        <button class="btn-go"   id="btnSearch" onclick="startSearch()" disabled>&#9654; Search</button>
        <button class="btn-stop" id="btnStop2"  onclick="stopExp()"    disabled>&#9632; Stop</button>
        <span class="dot dot-idle" id="dot2" style="margin-left:4px"></span>
      </div>
    </div>

    <div class="card">
      <h2>2B - Advanced Tuning</h2>
      <div class="tune-actions" style="margin-top:0;margin-bottom:8px">
        <span style="font-size:.66rem;color:var(--dim)">Tune search speed, exploration, and restart behavior.</span>
        <button class="btn-subtle" id="tuneToggle" onclick="toggleTuning()">Expand</button>
      </div>
      <div class="tune-shell" id="tuneShell">
      <div class="tune-grid">
        <div class="tune-field">
          <label for="tSettle">Settle Time (ms)</label>
          <input id="tSettle" type="number" min="50" max="1000" step="10" value="200">
          <div class="hint">Lower is faster, higher is steadier.</div>
        </div>
        <div class="tune-field">
          <label for="tPause">Pause Time (ms)</label>
          <input id="tPause" type="number" min="0" max="500" step="5" value="30">
          <div class="hint">Extra idle time between experiments.</div>
        </div>
        <div class="tune-group active" data-tune="spsa">
          <div class="tune-field">
            <label for="tSpsaH">SPSA Step Size</label>
            <input id="tSpsaH" type="number" min="2" max="120" step="1" value="40">
            <div class="hint">How far each plus/minus probe jumps.</div>
          </div>
          <div class="tune-field">
            <label for="tSpsaA">SPSA Learning Rate</label>
            <input id="tSpsaA" type="number" min="5" max="150" step="1" value="60">
            <div class="hint">How aggressively it moves after estimating a slope.</div>
          </div>
          <div class="tune-field wide">
            <label for="tSpsaRestart">SPSA Restart Patience</label>
            <input id="tSpsaRestart" type="number" min="5" max="120" step="1" value="40">
            <div class="hint">Steps without meaningful improvement before a random restart.</div>
          </div>
        </div>
        <div class="tune-group" data-tune="bayes">
          <div class="tune-field">
            <label for="tBoKappa">BO Exploration Weight</label>
            <input id="tBoKappa" type="number" min="0.2" max="8" step="0.1" value="3.0">
            <div class="hint">Higher values reward uncertainty more strongly.</div>
          </div>
          <div class="tune-field">
            <label for="tBoCand">BO Candidate Count</label>
            <input id="tBoCand" type="number" min="16" max="160" step="4" value="80">
            <div class="hint">More samples improve decisions but cost time.</div>
          </div>
        </div>
        <div class="tune-group" data-tune="thompson">
          <div class="tune-field">
            <label for="tTsBw">TS Bandwidth</label>
            <input id="tTsBw" type="number" min="0.05" max="0.8" step="0.01" value="0.25">
            <div class="hint">Smaller values stay local; larger values smooth more.</div>
          </div>
          <div class="tune-field">
            <label for="tTsCand">TS Candidate Count</label>
            <input id="tTsCand" type="number" min="16" max="160" step="4" value="80">
            <div class="hint">More hypothetical draws make each choice more selective.</div>
          </div>
        </div>
        <div class="tune-group" data-tune="cmaes">
          <div class="tune-field">
            <label for="tCmaSig">CMA Initial Sigma</label>
            <input id="tCmaSig" type="number" min="4" max="96" step="1" value="32">
            <div class="hint">Initial search spread for each generation.</div>
          </div>
          <div class="tune-field">
            <label for="tCmaMu">CMA Elite Count</label>
            <input id="tCmaMu" type="number" min="1" max="6" step="1" value="3">
            <div class="hint">How many top candidates shape the next generation.</div>
          </div>
        </div>
      </div>
      <div class="tune-actions">
        <span style="font-size:.64rem;color:var(--dim)">These settings apply when you press Search.</span>
        <button class="btn-subtle" onclick="resetTuning()">Reset Defaults</button>
      </div>
      </div>
    </div>

    <!-- 3. Hypothesis -->
    <div class="card">
      <h2>3 — Current Experiment &amp; Hypothesis</h2>
      <div class="row" style="margin-bottom:6px;gap:10px">
        <div style="display:flex;flex-direction:column;align-items:center;gap:4px;flex-shrink:0">
          <div style="width:56px;height:56px;border-radius:8px;border:1px solid var(--bd)" id="hypSw"></div>
          <span style="font-size:.6rem;color:var(--dim);text-align:center">Current<br>Probe</span>
        </div>
        <div style="flex:1">
          <div class="ch-row"><span class="ch-lbl r">R</span><div class="track"><div class="fill r" id="fR" style="width:0%"></div></div><span class="pct" id="pR">0%</span></div>
          <div class="ch-row"><span class="ch-lbl g">G</span><div class="track"><div class="fill g" id="fG" style="width:0%"></div></div><span class="pct" id="pG">0%</span></div>
          <div class="ch-row"><span class="ch-lbl b">B</span><div class="track"><div class="fill b" id="fB" style="width:0%"></div></div><span class="pct" id="pB">0%</span></div>
        </div>
        <div style="display:flex;flex-direction:column;align-items:center;gap:4px;flex-shrink:0">
          <div style="width:56px;height:56px;border-radius:8px;border:2px solid #0c6" id="bestSw"></div>
          <span style="font-size:.6rem;color:#0c6;text-align:center">Best<br>Found</span>
        </div>
      </div>
      <div class="stats" style="display:grid;grid-template-columns:1fr 1fr;gap:6px">
        <div class="stat"><span class="v" id="sIter">0</span><span class="l">Decision Steps</span></div>
        <div class="stat"><span class="v" id="sEvals">0</span><span class="l">Evaluations</span></div>
        <div class="stat"><span class="v" id="sScore" style="color:#0c6">&#8212;</span><span class="l">Best Score</span></div>
        <div class="stat"><span class="v" id="sElapsed">&#8212;</span><span class="l">Elapsed</span></div>
        <div class="stat"><span class="v" id="sHit90">Not yet</span><span class="l">Reached 90% At</span></div>
        <div class="stat"><span class="v" id="sSensor">&#8212;</span><span class="l">Sensor</span></div>
      </div>
      <div class="row" style="margin-top:4px">
        <button class="btn-cal" id="btnCal" onclick="doCalibrate()">&#9680; Auto-Gain</button>
        <span id="calStatus" style="font-size:.7rem;color:var(--dim);margin-left:6px"></span>
      </div>
      <div class="msg" id="sMsg">Set a target and choose an algorithm.</div>
    </div>

    <!-- 4. Thinking log -->
    <div class="card">
      <h2>4 — Thinking Log</h2>
      <div class="tlog" id="tlog"><div style="color:var(--dim)">Experiments will appear here&hellip;</div></div>
    </div>
  </div>

  <!-- Right column -->
  <div class="rcol">
    <div class="card">
      <h2>Spectral Fingerprint</h2>
      <div class="leg">
        <span><span class="leg-sq" style="background:#fff;opacity:.5;border:1px solid #aaa"></span>Target (normalised)</span>
        <span><span class="leg-sq" style="background:#7c6fff"></span>Measured (normalised)</span>
      </div>
      <canvas id="specCv" height="210"></canvas>
    </div>
    <div class="card">
      <h2>Match Score over Iterations</h2>
      <canvas id="scoreCv" height="130"></canvas>
      <div class="guide">
        <div class="guide-box">
          <div class="guide-k">What It Is Doing</div>
          <div class="guide-v" id="algPhase">Choose a target and start a search.</div>
        </div>
        <div class="guide-box">
          <div class="guide-k">Why This Move</div>
          <div class="guide-v" id="algWhy">The panel will explain whether the algorithm is exploring, refining, or locking onto a better recipe.</div>
        </div>
      </div>
      <div class="alg-hint">
        <div class="nm" id="algName">Gradient Descent</div>
        <div class="ds" id="algDesc">Tests paired nudges around the current color to estimate which RGB direction improves the score fastest.</div>
      </div>
    </div>
  </div>
</div>

<!-- ═══ EXPLORE TAB ═══ -->
<div class="exp-page" id="tab-explore">
  <div class="card">
    <h2>Raw Sensor (18 channels)</h2>
    <div class="bars" id="rawBars"></div>
    <div class="stats" style="margin-top:10px">
      <div class="stat"><span class="v" id="eCount">0</span><span class="l">Readings</span></div>
      <div class="stat"><span class="v" id="eSensor">&#8212;</span><span class="l">Sensor</span></div>
    </div>
  </div>
  <div class="card full">
    <h2>Recent Readings</h2>
    <table><thead><tr><th>#</th><th>Color</th><th>R</th><th>G</th><th>B</th>
      <th>405</th><th>425</th><th>450</th><th>475</th><th>515</th><th>550</th><th>600</th><th>640</th><th>690</th><th>Clr</th>
    </tr></thead><tbody id="logTb"></tbody></table>
  </div>
</div>

<script>
// ── Spectral metadata ─────────────────────────────────────────────────────────
const SPEC_IDX=[12,6,0,7,8,15,1,2,9,13];
const SPEC_WL =[405,425,450,475,515,550,555,600,640,690];
const SPEC_COL=['#8800ff','#5500ff','#0055ff','#0099ff','#00cc44','#aacc00','#cccc00','#ff7700','#ff2200','#cc0000'];
const CH_COL  =['#6600CC','#99CC00','#FF7700','#888','#bbb','#999','#4400FF','#0044FF','#00BB00','#FF2200','#bbb','#999','#9900FF','#CC0000','#880000','#CCEE00','#bbb','#999'];
const CH_LBL  =['450','555','600','NIR','Cl','Cl','425','475','515','640','Cl','Cl','405','690','745','550','Cl','Cl'];

// LED spectral weights (mirror of C++)
const W_R=[0,0.11,0.68,0,0,0,0,0,0,1,0,0,0,0.39,0.02,0.10,0,0];
const W_G=[0.08,0.74,0.12,0,0,0,0.01,0.32,0.93,0.01,0,0,0,0,0,0.82,0,0];
const W_B=[0.98,0.01,0,0,0,0,0.49,0.73,0.06,0,0,0,0.14,0,0,0.01,0,0];
function genTargetSpec(r,g,b){ const rf=r/255,gf=g/255,bf=b/255; return W_R.map((_,i)=>rf*W_R[i]+gf*W_G[i]+bf*W_B[i]); }

// ── Tab switching ─────────────────────────────────────────────────────────────
function showTab(n,el){
  activeTab=n;
  document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active')); el.classList.add('active');
  document.querySelectorAll('.page,.exp-page').forEach(p=>p.classList.remove('active'));
  document.getElementById('tab-'+n).classList.add('active');
}

// ── Color input ───────────────────────────────────────────────────────────────
let targetRGB={r:255,g:165,b:0}; let targetSpec=genTargetSpec(255,165,0);
function parseColor(s){ const c=document.createElement('canvas').getContext('2d'); c.fillStyle='#000'; c.fillStyle=s.trim(); const h=c.fillStyle; if(h[0]==='#'&&h.length===7) return{r:parseInt(h.slice(1,3),16),g:parseInt(h.slice(3,5),16),b:parseInt(h.slice(5,7),16),hex:h}; return null; }
function syncPicker(el){ document.getElementById('colorText').value=el.value; }
function applyTarget(){
  const c=parseColor(document.getElementById('colorText').value||document.getElementById('colorPicker').value);
  if(!c){alert('Could not parse color. Try: teal, #3a9, or rgb(0,128,128)');return;}
  targetRGB=c; targetSpec=genTargetSpec(c.r,c.g,c.b);
  document.getElementById('tgtSw').style.background=c.hex;
  document.getElementById('tgtRGB').textContent=`rgb(${c.r}, ${c.g}, ${c.b})`;
  document.getElementById('colorPicker').value=c.hex;
  document.getElementById('btnSearch').disabled=false;
  document.getElementById('sMsg').textContent=`Target set: rgb(${c.r},${c.g},${c.b}) — choose algorithm and press Search.`;
  drawSpectra(null, null);
}

// ── Algorithm selection ───────────────────────────────────────────────────────
const ALG_META={
  spsa:{
    name:'Gradient Descent',
    desc:'Tests paired nudges around the current color to estimate which RGB direction improves the score fastest.'
  },
  bayes:{
    name:'Bayesian Optimisation',
    desc:'Builds a lightweight model of the color landscape, then probes places that look promising or still uncertain.'
  },
  thompson:{
    name:'Thompson Sampling',
    desc:'Acts on sampled beliefs about the best next color, so it naturally alternates between curiosity and confidence.'
  },
  cmaes:{
    name:'CMA-ES',
    desc:'Tries a population of candidate colors, keeps the stronger ones, and reshapes the search region generation by generation.'
  }
};
const TUNING_DEFAULTS={
  settle:200,
  pause:30,
  spsaH:40,
  spsaA:60,
  spsaRestart:40,
  boKappa:3.0,
  boCand:80,
  tsBw:0.25,
  tsCand:80,
  cmaSig:32,
  cmaMu:3
};
let curAlg='spsa';
let latestThoughts=[];
let latestStatus=null;
let hasRunStarted=false;
let tuningOpen=false;
function setTuningVisibility(){
  document.querySelectorAll('.tune-group').forEach(g=>g.classList.toggle('active',g.dataset.tune===curAlg));
}
function toggleTuning(forceOpen){
  if(typeof forceOpen === 'boolean') tuningOpen=forceOpen;
  else tuningOpen=!tuningOpen;
  const shell=document.getElementById('tuneShell');
  const btn=document.getElementById('tuneToggle');
  if(shell) shell.classList.toggle('open',tuningOpen);
  if(btn) btn.textContent=tuningOpen?'Collapse':'Expand';
}
function resetTuning(){
  document.getElementById('tSettle').value=TUNING_DEFAULTS.settle;
  document.getElementById('tPause').value=TUNING_DEFAULTS.pause;
  document.getElementById('tSpsaH').value=TUNING_DEFAULTS.spsaH;
  document.getElementById('tSpsaA').value=TUNING_DEFAULTS.spsaA;
  document.getElementById('tSpsaRestart').value=TUNING_DEFAULTS.spsaRestart;
  document.getElementById('tBoKappa').value=TUNING_DEFAULTS.boKappa.toFixed(1);
  document.getElementById('tBoCand').value=TUNING_DEFAULTS.boCand;
  document.getElementById('tTsBw').value=TUNING_DEFAULTS.tsBw.toFixed(2);
  document.getElementById('tTsCand').value=TUNING_DEFAULTS.tsCand;
  document.getElementById('tCmaSig').value=TUNING_DEFAULTS.cmaSig;
  document.getElementById('tCmaMu').value=TUNING_DEFAULTS.cmaMu;
  setTuningVisibility();
}
function getTuningPayload(){
  return {
    settle_ms:parseInt(document.getElementById('tSettle').value,10),
    pause_ms:parseInt(document.getElementById('tPause').value,10),
    spsa_h:parseFloat(document.getElementById('tSpsaH').value),
    spsa_a:parseFloat(document.getElementById('tSpsaA').value),
    spsa_restart:parseInt(document.getElementById('tSpsaRestart').value,10),
    bo_kappa:parseFloat(document.getElementById('tBoKappa').value),
    bo_candidates:parseInt(document.getElementById('tBoCand').value,10),
    ts_bw:parseFloat(document.getElementById('tTsBw').value),
    ts_candidates:parseInt(document.getElementById('tTsCand').value,10),
    cma_sigma:parseFloat(document.getElementById('tCmaSig').value),
    cma_mu:parseInt(document.getElementById('tCmaMu').value,10)
  };
}
function selAlg(el){
  document.querySelectorAll('.alg').forEach(a=>a.classList.remove('active')); el.classList.add('active');
  curAlg=el.dataset.alg;
  setTuningVisibility();
  renderAlgNarrative();
}

// ── Recipe search ─────────────────────────────────────────────────────────────
let poll=null, scoreHistory=[];
let pollBusy=false, auxBusy=false, pollTick=0;
let activeTab='recipe';
let lastThoughtKey='';
async function startSearch(){
  const {r,g,b}=targetRGB;
  const res=await fetch('/start',{method:'POST',
    headers:{'Content-Type':'application/x-www-form-urlencoded;charset=UTF-8'},
    body:new URLSearchParams({algorithm:curAlg,r,g,b,...getTuningPayload()})});
  if(!res.ok)return;
  scoreHistory=[];
  latestThoughts=[];
  latestStatus=null;
  hasRunStarted=true;
  lastTH=0;
  lastThoughtKey='';
  document.getElementById('tlog').innerHTML='<div style="color:var(--dim)">Search started. First experiments will appear here&hellip;</div>';
  document.getElementById('btnSearch').disabled=true;
  document.getElementById('btnStop2').disabled=false;
  document.getElementById('dot2').className='dot dot-run';
  pollBusy=false; auxBusy=false; pollTick=0;
  renderAlgNarrative();
  poll=setInterval(doPoll,800);
}
async function stopExp(){ await fetch('/stop',{method:'POST'}); endPoll(); }
async function doCalibrate(){
  const btn=document.getElementById('btnCal');
  const st=document.getElementById('calStatus');
  btn.disabled=true; btn.textContent='Calibrating…';
  st.textContent='LED flashing white — hold still'; st.style.color='#fa0';
  try{
    const d=await(await fetch('/calibrate',{method:'POST'})).json();
    st.textContent='Gain set to '+d.gainLabel; st.style.color='#0c6';
  }catch(e){ st.textContent='Failed'; st.style.color='#e33'; }
  btn.disabled=false; btn.textContent='⬛ Auto-Gain';
  btn.textContent='\u9680 Auto-Gain';
}
function endPoll(){
  clearInterval(poll);poll=null;
  document.getElementById('btnSearch').disabled=false;
  document.getElementById('btnStop2').disabled=false;
  document.getElementById('dot2').className='dot dot-idle';
  renderAlgNarrative();
}
function formatDuration(ms){
  if(ms == null || ms < 0) return '—';
  if(ms < 10000) return (ms/1000).toFixed(1)+'s';
  return (ms/1000).toFixed(0)+'s';
}
function formatHit90(ms){
  if(ms == null || ms < 0) return 'Not yet';
  return formatDuration(ms);
}
async function doPoll(){
  if(pollBusy) return;
  pollBusy=true;
  try{
    const snap=await(await fetch(activeTab === 'explore' ? '/snapshot?log=1' : '/snapshot')).json();
    latestStatus=snap.status;
    updateUI(snap.status); if(!snap.status.running) endPoll();
    renderScores(snap.scores || []);
    renderThoughts(snap.thoughts || []);
    if(snap.log) renderLogRows(snap.log);
  }catch(e){}
  finally{ pollBusy=false; }
}
const ALG_NAME={spsa:'GD',bayes:'BO',thompson:'TS',cmaes:'CMA-ES'};
function updateUI(d){
  const rec=d.recipe; if(!rec) return;
  // Current probe swatch — updates every step so you can see the algorithm exploring
  document.getElementById('hypSw').style.background=`rgb(${d.led.r},${d.led.g},${d.led.b})`;
  // Best-found swatch — updates only on improvement
  document.getElementById('bestSw').style.background=`rgb(${rec.bestR},${rec.bestG},${rec.bestB})`;
  const pr=Math.round(d.led.r/2.55),pg=Math.round(d.led.g/2.55),pb=Math.round(d.led.b/2.55);
  ['R','G','B'].forEach((c,i)=>{
    const v=[pr,pg,pb][i];
    document.getElementById('f'+c).style.width=v+'%';
    document.getElementById('p'+c).textContent=v+'%';
  });
  document.getElementById('sIter').textContent=rec.iter;
  document.getElementById('sEvals').textContent=rec.evals ?? 0;
  document.getElementById('sScore').textContent=rec.bestScore>=0?rec.bestScore.toFixed(1)+'%':'—';
  document.getElementById('sElapsed').textContent=formatDuration(rec.elapsedMs);
  document.getElementById('sHit90').textContent=formatHit90(rec.hit90Ms);
  const se=document.getElementById('sSensor');
  se.textContent=d.sensor?'OK':'ERR'; se.style.color=d.sensor?'#0c6':'#e33';
  const msgEl=document.getElementById('sMsg');
  msgEl.textContent=rec.msg;
  msgEl.className='msg'+(rec.converged?' done':rec.bestScore>70?' ok':'');
  renderAlgNarrative(d);
  // Update raw bars
  if(d.channels){
    const mx=Math.max(...d.channels,1);
    d.channels.forEach((v,i)=>{const el=document.getElementById('rb'+i);if(el)el.style.height=Math.round(v/mx*100)+'%';});
    document.getElementById('eCount').textContent=d.count;
    drawSpectra(d.channels, d.lastScore);
  }
}

function getAlgorithmKeyFromStatus(d){
  if(d && typeof d.algorithm === 'number'){
    return {1:'spsa',2:'bayes',3:'thompson',4:'cmaes'}[d.algorithm] || curAlg;
  }
  return curAlg;
}

function getLatestThought(){
  return latestThoughts.length ? latestThoughts[latestThoughts.length-1] : null;
}

function renderAlgNarrative(d){
  d=d || latestStatus;
  const algKey=getAlgorithmKeyFromStatus(d);
  const meta=ALG_META[algKey] || ALG_META.spsa;
  document.getElementById('algName').textContent=meta.name;
  document.getElementById('algDesc').textContent=meta.desc;

  let phase='Choose a target and start a search.';
  let why='The panel will explain whether the algorithm is exploring, refining, or locking onto a better recipe.';

  if(d){
    const rec=d.recipe || {};
    const msg=(rec.msg || '').toLowerCase();
    const latest=allScores.length ? allScores[allScores.length-1] : null;
    const prev=allScores.length > 1 ? allScores[allScores.length-2] : null;
    const delta=(latest != null && prev != null) ? latest - prev : null;
    const thought=getLatestThought();

    if(!d.running && rec.iter===0){
      phase='Ready to search. The next run will first measure ambient light before it begins testing candidate colors.';
      why='That dark-frame baseline keeps the score focused on the LED spectrum instead of room lighting.';
    } else if(msg.includes('dark frame')){
      phase='Measuring the dark frame so the score reflects LED color rather than ambient light.';
      why='This baseline is subtracted from later readings, which makes the comparisons much more honest.';
    } else if(msg.includes('random start')){
      phase='Seeding the search with an initial guess before the algorithm begins steering toward better colors.';
      why='A starting probe gives the algorithm its first local evidence about which RGB directions look promising.';
    } else if(rec.converged){
      phase=`Locked onto a strong recipe at ${rec.bestScore.toFixed(1)}%. The LED is now showing the best color found.`;
      why='The run hit the score threshold, so it stopped early and kept the strongest recipe it found.';
    } else if(msg.includes('budget reached')){
      phase=`Search budget exhausted at ${rec.bestScore.toFixed(1)}%. The LED is showing the best recipe found within the allowed evaluations.`;
      why='This run stopped because it used up its measurement budget, not because it crossed the high-quality score threshold.';
    } else if(d.running){
      if(algKey==='spsa'){
        phase='Comparing tiny paired RGB nudges to estimate which direction climbs the score fastest.';
        why=delta != null && delta > 0
          ? `The last move improved the score by ${delta.toFixed(1)} points, so Gradient Descent is pushing harder in that direction.`
          : 'If a local nudge does not help, the next step pivots and samples a different slope around the current color.';
      } else if(algKey==='bayes'){
        phase='Balancing model confidence against uncertainty, so it can revisit strong regions without ignoring unexplored ones.';
        why=thought && thought.improved
          ? 'A recent improvement sharpens the model around that neighborhood, which changes where the next informative probes land.'
          : 'Bayesian Optimisation sometimes spends a step learning the landscape, not just chasing the current best guess.';
      } else if(algKey==='thompson'){
        phase='Sampling one plausible version of the hidden color landscape, then probing where that imagined landscape says to go next.';
        why=thought && thought.improved
          ? 'That improved sample boosts confidence around nearby colors while still leaving room for some randomness.'
          : 'Thompson Sampling keeps healthy uncertainty alive, which helps it escape early guesses that only looked good by chance.';
      } else if(algKey==='cmaes'){
        phase='Trying a generation of candidate colors, then reshaping the search cloud around whichever ones performed best.';
        why=thought && thought.improved
          ? 'A strong offspring pulls the next generation toward that region and can also tighten or stretch the search spread.'
          : 'CMA-ES learns the useful search geometry, so it can zoom along productive RGB directions instead of shrinking evenly.';
      }

      if(rec.bestScore >= 0 && latest != null){
        phase += ` Current probe: ${latest.toFixed(1)}%. Best so far: ${rec.bestScore.toFixed(1)}%.`;
        why += ` The current gap to the best-known recipe is ${(rec.bestScore - latest).toFixed(1)} points.`;
      }
    } else if(rec.iter > 0){
      phase=`Search paused after ${rec.iter} steps with a best score of ${rec.bestScore.toFixed(1)}%.`;
      why='The score curve and thinking log now show whether the search had started refining near the answer or was still exploring broadly.';
    }
  } else if(hasRunStarted){
    phase='Waiting for the next live search update...';
    why='The most recent measurements are being collected before the explanation panel refreshes.';
  }

  document.getElementById('algPhase').textContent=phase;
  document.getElementById('algWhy').textContent=why;
}

// ── Spectral fingerprint ──────────────────────────────────────────────────────
// Target and measured are on completely different scales — normalize independently
function drawSpectra(measured, score){
  const cv=document.getElementById('specCv');
  cv.width=cv.offsetWidth||420;
  const ctx=cv.getContext('2d');
  const W=cv.width,H=cv.height,PL=6,PR=6,PT=18,PB=26,n=SPEC_IDX.length;
  const bW=Math.floor((W-PL-PR)/n), chartH=H-PT-PB;
  ctx.clearRect(0,0,W,H);

  // Independent normalization
  let mxT=1e-9;
  for(let i=0;i<n;i++) mxT=Math.max(mxT,targetSpec[SPEC_IDX[i]]);
  let mxM=1;
  if(measured) for(let i=0;i<n;i++) mxM=Math.max(mxM,measured[SPEC_IDX[i]]);

  for(let i=0;i<n;i++){
    const ci=SPEC_IDX[i];
    const x=PL+i*bW;
    const tH=Math.max(1,Math.round(targetSpec[ci]/mxT*chartH));
    // 1. Target fill (subtle background)
    ctx.fillStyle='rgba(220,220,220,0.10)';
    ctx.fillRect(x+1,PT+chartH-tH,bW-2,tH);
    // 2. Measured bar — narrower so gray outline will frame it
    if(measured){
      const mH=Math.max(1,Math.round(measured[ci]/mxM*chartH));
      ctx.fillStyle=SPEC_COL[i];
      ctx.fillRect(x+4,PT+chartH-mH,bW-8,mH);
    }
    // 3. Target outline drawn ON TOP — always visible regardless of bar height
    ctx.strokeStyle='rgba(200,200,200,0.75)';
    ctx.lineWidth=1.5;
    ctx.strokeRect(x+1.5,PT+chartH-tH+0.5,bW-3,tH-1);
    // Wavelength label
    ctx.fillStyle='#444'; ctx.font='9px monospace'; ctx.textAlign='center';
    ctx.fillText(SPEC_WL[i],x+bW/2,H-6);
  }

  // Score overlay — top right
  if(measured && score != null){
    const sc=parseFloat(score);
    const col=sc>80?'#0c6':sc>50?'#fa0':'#e55';
    ctx.font='bold 13px monospace'; ctx.textAlign='right';
    ctx.fillStyle='rgba(13,15,24,0.7)';
    ctx.fillRect(W-82,2,80,16);
    ctx.fillStyle=col;
    ctx.fillText('Score: '+sc.toFixed(1)+'%',W-4,14);
  }
}

// ── Score plot (ascending) ────────────────────────────────────────────────────
let allScores=[], acceptedScores=[];
function renderScores(scores){
  if(Array.isArray(scores)){
    allScores=scores;
    acceptedScores=scores.slice();
  }else{
    allScores=Array.isArray(scores?.all)?scores.all:[];
    acceptedScores=Array.isArray(scores?.accepted)?scores.accepted:[];
  }
  drawScoreChart();
  renderAlgNarrative();
}
function drawScoreChart(){
  const cv=document.getElementById('scoreCv');
  cv.width=cv.offsetWidth||420;
  const ctx=cv.getContext('2d');
  const W=cv.width,H=cv.height;
  const PL=30,PR=10,PT=14,PB=22; // left room for y-axis labels, bottom for x-axis
  const cW=W-PL-PR, cH=H-PT-PB;
  ctx.clearRect(0,0,W,H);
  if(allScores.length<2){
    ctx.fillStyle='#333'; ctx.font='10px monospace'; ctx.textAlign='center';
    ctx.fillText('Waiting for data…',W/2,H/2); return;
  }

  // Y-axis grid lines + labels
  ctx.strokeStyle='#1e2130'; ctx.lineWidth=1;
  [0,25,50,75,100].forEach(v=>{
    const y=PT+cH-(v/100)*cH;
    ctx.beginPath(); ctx.moveTo(PL,y); ctx.lineTo(PL+cW,y); ctx.stroke();
    ctx.fillStyle=v===0?'#222':'#444'; ctx.font='8px monospace'; ctx.textAlign='right';
    ctx.fillText(v+'%',PL-3,y+3);
  });

  // X-axis label
  ctx.fillStyle='#444'; ctx.font='8px monospace'; ctx.textAlign='center';
  ctx.fillText('← Iteration →',PL+cW/2,H-4);

  // Y-axis label (rotated)
  ctx.save(); ctx.translate(9,PT+cH/2); ctx.rotate(-Math.PI/2);
  ctx.fillStyle='#444'; ctx.font='8px monospace'; ctx.textAlign='center';
  ctx.fillText('Score %',0,0); ctx.restore();

  // All measured scores
  const n=allScores.length;
  ctx.strokeStyle='rgba(0,255,153,0.35)'; ctx.lineWidth=1.5;
  ctx.beginPath();
  allScores.forEach((v,i)=>{
    const x=PL+(n===1?cW/2:i/(n-1)*cW);
    const y=PT+cH-(v/100)*cH;
    i===0?ctx.moveTo(x,y):ctx.lineTo(x,y);
  });
  ctx.stroke();

  // Accepted path
  let acceptedCount=0;
  ctx.strokeStyle='#0c6'; ctx.lineWidth=2.2;
  ctx.beginPath();
  acceptedScores.forEach((v,i)=>{
    if(v == null || v < 0) return;
    const x=PL+(n===1?cW/2:i/(n-1)*cW);
    const y=PT+cH-(v/100)*cH;
    if(acceptedCount===0) ctx.moveTo(x,y);
    else ctx.lineTo(x,y);
    acceptedCount++;
  });
  if(acceptedCount>0) ctx.stroke();
  ctx.fillStyle='#0c6';
  acceptedScores.forEach((v,i)=>{
    if(v == null || v < 0) return;
    const x=PL+(n===1?cW/2:i/(n-1)*cW);
    const y=PT+cH-(v/100)*cH;
    ctx.beginPath();
    ctx.arc(x,y,2.2,0,Math.PI*2);
    ctx.fill();
  });

  // Current score dot (last point)
  const last=allScores[n-1];
  const lx=PL+cW, ly=PT+cH-(last/100)*cH;
  ctx.beginPath(); ctx.arc(lx,ly,4,0,Math.PI*2);
  ctx.fillStyle='#fff'; ctx.fill();
  ctx.fillStyle='#aaa'; ctx.font='9px monospace'; ctx.textAlign='right';
  ctx.fillText(last.toFixed(1)+'%',lx-7,ly-5);

  // Best score labels + legend
  const probeBest=Math.max(...allScores);
  const acceptedOnly=acceptedScores.filter(v=>v != null && v >= 0);
  const acceptedBest=acceptedOnly.length?Math.max(...acceptedOnly):null;
  ctx.fillStyle='#0c6'; ctx.font='bold 10px monospace'; ctx.textAlign='left';
  if(acceptedBest != null) ctx.fillText('Accepted Best: '+acceptedBest.toFixed(1)+'%',PL+2,PT+10);
  ctx.fillStyle='rgba(0,255,153,0.55)';
  ctx.fillText('Probe Peak: '+probeBest.toFixed(1)+'%',PL+2,PT+22);

  ctx.textAlign='right';
  ctx.font='9px monospace';
  ctx.fillStyle='rgba(0,255,153,0.35)';
  ctx.fillRect(W-132,PT-2,10,2);
  ctx.fillText('All measurements',W-10,PT+1);
  ctx.fillStyle='#0c6';
  ctx.fillRect(W-132,PT+10,10,2);
  ctx.fillText('Accepted path',W-10,PT+13);
}

// ── Thinking log ─────────────────────────────────────────────────────────────
let lastTH=0;
function renderThoughts(d){
  latestThoughts=d;
  const tail=d.length ? d[d.length-1] : null;
  const key=tail ? `${d.length}:${tail.msg}:${tail.score}:${tail.r},${tail.g},${tail.b}` : '0';
  if(key===lastThoughtKey) return;
  lastThoughtKey=key;
  lastTH=d.length;
  const el=document.getElementById('tlog'); el.innerHTML='';
  [...d].reverse().forEach(t=>{
    const row=document.createElement('div'); row.className='tl';
    const dot=document.createElement('span'); dot.className='td';
    dot.style.background=`rgb(${t.r},${t.g},${t.b})`;
    dot.style.boxShadow=t.improved?'0 0 3px #0c6':'none';
    const txt=document.createElement('span'); txt.className='tt'+(t.improved?' imp':'');
    const tag=document.createElement('span');
    tag.className='tl-tag'+(t.improved?' imp':'');
    tag.textContent=t.msg.includes('CONVERGED')?'locked':(t.msg.includes('BUDGET REACHED')?'budget':(t.improved?'better':'probe'));
    txt.appendChild(tag);
    txt.appendChild(document.createTextNode(t.msg));
    row.appendChild(dot); row.appendChild(txt); el.appendChild(row);
  });
  renderAlgNarrative();
}

// ── Explore log ───────────────────────────────────────────────────────────────
function renderLogRows(rows){
  const tb=document.getElementById('logTb'); tb.innerHTML='';
  rows.slice(-12).reverse().forEach((row,i)=>{
    const tr=document.createElement('tr');
    const cells=[rows.length-i,`<span class="sc" style="background:rgb(${row.r},${row.g},${row.b})"></span>`,
      row.r,row.g,row.b,row.ch[12],row.ch[6],row.ch[0],row.ch[7],row.ch[8],row.ch[15],row.ch[2],row.ch[9],row.ch[13],row.ch[4]];
    tr.innerHTML=cells.map(v=>`<td>${v}</td>`).join('');
    tr.style.background=`rgba(${row.r},${row.g},${row.b},0.06)`; tb.appendChild(tr);
  });
  document.getElementById('eCount').textContent=rows.length;
  const se=document.getElementById('eSensor');
  se.textContent=document.getElementById('sSensor').textContent;
  se.style.color=document.getElementById('sSensor').style.color;
}

// ── Build raw bars ────────────────────────────────────────────────────────────
const rb=document.getElementById('rawBars');
for(let i=0;i<18;i++) rb.innerHTML+=`<div class="bw"><div class="rawb" id="rb${i}" style="background:${CH_COL[i]};height:0%"></div><div class="bl">${CH_LBL[i]}</div></div>`;

// ── Init ──────────────────────────────────────────────────────────────────────
const tlogCard=document.getElementById('tlog').closest('.card');
const rightCol=document.querySelector('.rcol');
if(tlogCard && rightCol) rightCol.appendChild(tlogCard);
resetTuning();
applyTarget();
renderAlgNarrative();
doPoll();
setInterval(()=>{if(!poll)doPoll();},3000);
</script>
</body></html>
)HTML";

// ── Web handlers ──────────────────────────────────────────────────────────────
int runAutoGain(); // defined in Setup section below
void handleRoot(AsyncWebServerRequest* request){ request->send(200,"text/html",HTML); }

static String buildStatusJson(){
  uint32_t elapsedMs = runStartMs > 0 ? (millis() - runStartMs) : 0;
  String j="{";
  j.reserve(384);
  j+="\"running\":"+String(running?"true":"false")+",";
  j+="\"lastScore\":"+String(lastScore,1)+",";
  j+="\"sensor\":"+String(sensorOK?"true":"false")+",";
  j+="\"algorithm\":"+String((int)alg)+",";
  j+="\"count\":"+String(logCount)+",";
  j+="\"led\":{\"r\":"+String(ledR)+",\"g\":"+String(ledG)+",\"b\":"+String(ledB)+"},";
  j+="\"channels\":[";
  if(logCount>0){const Reading& rd=logBuf[(logHead-1+LOG_MAX)%LOG_MAX];for(int i=0;i<NUM_CH;i++){j+=String(rd.ch[i]);if(i<NUM_CH-1)j+=",";}}
  else{for(int i=0;i<NUM_CH;i++){j+="0";if(i<NUM_CH-1)j+=",";}}
  j+="],\"recipe\":{";
  j+="\"bestR\":"+String(bestR)+",\"bestG\":"+String(bestG)+",\"bestB\":"+String(bestB)+",";
  j+="\"bestScore\":"+String(bestScore,1)+",";
  j+="\"iter\":"+String(totalIter)+",";
  j+="\"evals\":"+String(evalCount)+",";
  j+="\"elapsedMs\":"+String(elapsedMs)+",";
  j+="\"hit90Ms\":"+String(hit90Ms)+",";
  j+="\"converged\":"+String(converged?"true":"false")+",";
  j+="\"msg\":\""+jsonEscape(stateMsg)+"\"";
  j+="}}";
  return j;
}

void handleStart(AsyncWebServerRequest* request){
  if(!sensorOK){
    request->send(503,"application/json","{\"error\":\"sensor unavailable\"}");
    return;
  }
  String algStr;
  uint8_t reqR=0, reqG=0, reqB=0;
  if(!getRequestString(request,"algorithm",algStr)){
    request->send(400,"application/json","{\"error\":\"missing algorithm\"}");
    return;
  }
  if(!getRequestRgb(request,reqR,reqG,reqB)){
    request->send(400,"application/json","{\"error\":\"invalid rgb\"}");
    return;
  }
  int reqSettle=0, reqPause=0, reqSpsaRestart=0, reqBoCand=0, reqTsCand=0, reqCmaMu=0;
  float reqSpsaH=0, reqSpsaA=0, reqBoKappa=0, reqTsBw=0, reqCmaSig=0;
  if(getRequestInt(request,"settle_ms",reqSettle)) settleMs = (uint32_t)constrain(reqSettle, 50, 1000);
  if(getRequestInt(request,"pause_ms",reqPause)) pauseMs = (uint32_t)constrain(reqPause, 0, 500);
  if(getRequestFloat(request,"spsa_h",reqSpsaH)) spsaInitH = constrain(reqSpsaH, 2.0f, 120.0f);
  if(getRequestFloat(request,"spsa_a",reqSpsaA)) spsaInitA = constrain(reqSpsaA, 5.0f, 150.0f);
  if(getRequestInt(request,"spsa_restart",reqSpsaRestart)) spsaRestartPatience = constrain(reqSpsaRestart, 5, 120);
  if(getRequestFloat(request,"bo_kappa",reqBoKappa)) boKappaInit = constrain(reqBoKappa, 0.2f, 8.0f);
  if(getRequestInt(request,"bo_candidates",reqBoCand)) boCandidateCount = constrain(reqBoCand, 16, 160);
  if(getRequestFloat(request,"ts_bw",reqTsBw)) tsBwInit = constrain(reqTsBw, 0.05f, 0.8f);
  if(getRequestInt(request,"ts_candidates",reqTsCand)) tsCandidateCount = constrain(reqTsCand, 16, 160);
  if(getRequestFloat(request,"cma_sigma",reqCmaSig)) cmaSigmaInit = constrain(reqCmaSig, 4.0f, 96.0f);
  if(getRequestInt(request,"cma_mu",reqCmaMu)) cmaMuActive = constrain(reqCmaMu, 1, CMA_LAM);
  recTgtR=reqR; recTgtG=reqG; recTgtB=reqB;
  resetAll();
  runStartMs=millis();
  if     (algStr=="spsa")    { alg=ALG_SPSA;    }
  else if(algStr=="bayes")   { alg=ALG_BAYES;   }
  else if(algStr=="thompson"){ alg=ALG_THOMPSON; }
  else if(algStr=="cmaes")   { alg=ALG_CMAES;   }
  else{ request->send(400,"application/json","{\"error\":\"unknown algorithm\"}"); return; }
  // Two-step calibration: (1) dark frame with LED off, (2) target color with LED on.
  // Subtracting the dark frame removes ambient light's spectral signature from scoring.
  genTargetSpectrum(recTgtR,recTgtG,recTgtB); // synthetic fallback if sensor fails
  calibPhase=1;
  setLED(0,0,0); // LED off for dark frame
  setStateMessage("Calibrating: reading dark frame...");
  running=true; settling=true; nextMs=millis()+settleMs;
  request->send(200,"application/json","{\"ok\":true}");
}

void handleStop(AsyncWebServerRequest* request){
  alg=ALG_NONE;
  stopExperiment("Stopped by user.", true);
  request->send(200,"application/json","{\"ok\":true}");
}

void handleCalibrate(AsyncWebServerRequest* request){
  if(!sensorOK){
    request->send(503,"application/json","{\"error\":\"sensor unavailable\"}");
    return;
  }
  int g=runAutoGain();
  // Map index to approximate multiplier for display
  const char* labels[]={"0.5","1","2","4","8","16","32","64","128","256","512"};
  char msg[60]; snprintf(msg,59,"{\"ok\":true,\"gainIdx\":%d,\"gainLabel\":\"%sX\"}",g,g<11?labels[g]:"?");
  request->send(200,"application/json",msg);
}

static String buildLogJson(){
  int total=min(logCount,16);
  int start=(logCount<=LOG_MAX)?max(0,logHead-total):(logHead-total+LOG_MAX)%LOG_MAX;
  String j="[";
  j.reserve(1800);
  for(int i=0;i<total;i++){
    const Reading& rd=logBuf[(start+i)%LOG_MAX]; if(i>0)j+=",";
    j+="{\"r\":"+String(rd.r)+",\"g\":"+String(rd.g)+",\"b\":"+String(rd.b)+",\"ch\":[";
    for(int c=0;c<NUM_CH;c++){j+=String(rd.ch[c]);if(c<NUM_CH-1)j+=",";}
    j+="]}";
  }
  j+="]";
  return j;
}

static String buildThoughtsJson(){
  int total=min(thCount,20);
  int start=(thCount<=TH_MAX)?max(0,thHead-total):(thHead-total+TH_MAX)%TH_MAX;
  String j="[";
  j.reserve(2400);
  for(int i=0;i<total;i++){
    const Thought& t=thBuf[(start+i)%TH_MAX]; if(i>0)j+=",";
    j+="{\"r\":"+String(t.r)+",\"g\":"+String(t.g)+",\"b\":"+String(t.b)+
       ",\"score\":"+String(t.score,1)+",\"improved\":"+String(t.improved?"true":"false")+
       ",\"msg\":\""+jsonEscape(t.msg)+"\"}";
  }
  j+="]";
  return j;
}

static String buildScoresJson(){
  int total=min(scoreLen,SCORE_MAX);
  int start=(scoreLen<=SCORE_MAX)?max(0,scoreHead-total):(scoreHead-total+SCORE_MAX)%SCORE_MAX;
  String j="{\"all\":[";
  j.reserve(3200);
  for(int i=0;i<total;i++){
    j+=String(scoreHist[(start+i)%SCORE_MAX],1);
    if(i<total-1)j+=",";
  }
  j+="],\"accepted\":[";
  for(int i=0;i<total;i++){
    float v=acceptedScoreHist[(start+i)%SCORE_MAX];
    if(v < 0.0f) j+="null";
    else j+=String(v,1);
    if(i<total-1)j+=",";
  }
  j+="]}";
  return j;
}

static String buildSnapshotJson(bool includeLog){
  String j="{\"status\":";
  j.reserve(includeLog ? 5600 : 3800);
  j += buildStatusJson();
  j += ",\"scores\":";
  j += buildScoresJson();
  j += ",\"thoughts\":";
  j += buildThoughtsJson();
  if(includeLog){
    j += ",\"log\":";
    j += buildLogJson();
  }
  j += "}";
  return j;
}

static bool getRequestInt(AsyncWebServerRequest* request, const char* key, int& valueOut){
  const AsyncWebParameter* p = request->getParam(key, true);
  if(!p) p = request->getParam(key);
  if(!p) return false;
  valueOut = p->value().toInt();
  return true;
}

static bool getRequestFloat(AsyncWebServerRequest* request, const char* key, float& valueOut){
  const AsyncWebParameter* p = request->getParam(key, true);
  if(!p) p = request->getParam(key);
  if(!p) return false;
  valueOut = p->value().toFloat();
  return true;
}

static bool getRequestString(AsyncWebServerRequest* request, const char* key, String& valueOut){
  const AsyncWebParameter* p = request->getParam(key, true);
  if(!p) p = request->getParam(key);
  if(!p) return false;
  valueOut = p->value();
  return true;
}

static bool getRequestRgb(AsyncWebServerRequest* request, uint8_t& r, uint8_t& g, uint8_t& b){
  int ri=0, gi=0, bi=0;
  if(!getRequestInt(request,"r",ri) || !getRequestInt(request,"g",gi) || !getRequestInt(request,"b",bi)) return false;
  if(ri<0 || ri>255 || gi<0 || gi>255 || bi<0 || bi>255) return false;
  r=(uint8_t)ri; g=(uint8_t)gi; b=(uint8_t)bi;
  return true;
}

// ── Auto-gain ─────────────────────────────────────────────────────────────────
// Flashes white, steps gain until brightest SPEC channel is 8k–40k (no saturation).
// Returns the gain index that was selected.
// Gain enum: 0=0.5x 1=1x 2=2x 3=4x 4=8x 5=16x 6=32x 7=64x 8=128x 9=256x 10=512x
void handleStatus(AsyncWebServerRequest* request){ request->send(200,"application/json",buildStatusJson()); }
void handleLog(AsyncWebServerRequest* request){ request->send(200,"application/json",buildLogJson()); }
void handleThoughts(AsyncWebServerRequest* request){ request->send(200,"application/json",buildThoughtsJson()); }
void handleScores(AsyncWebServerRequest* request){ request->send(200,"application/json",buildScoresJson()); }
void handleSnapshot(AsyncWebServerRequest* request){ request->send(200,"application/json",buildSnapshotJson(request->hasParam("log"))); }

static int currentGainIdx=4;
int runAutoGain(){
  if(!sensorOK) return currentGainIdx;
  running=false; // pause any experiment
  int gIdx=4; // start at 8X — work up only if signal is too weak
  as7343.setGain((as7343_gain_t)gIdx);
  setLED(200,200,200); delay(400);
  for(int att=0;att<10;att++){
    uint16_t tb[NUM_CH]={};
    if(!as7343.readAllChannels(tb)) break;
    uint16_t mx=0;
    for(int i=0;i<N_SPEC;i++) mx=max(mx,tb[SPEC_CH[i]]);
    Serial.printf("Gain idx=%d max=%u\n",gIdx,mx);
    if(mx>40000 && gIdx>0){ gIdx--; as7343.setGain((as7343_gain_t)gIdx); delay(200); }
    else if(mx<5000  && gIdx<10){ gIdx++; as7343.setGain((as7343_gain_t)gIdx); delay(200); }
    else break;
  }
  setLED(0,0,0);
  currentGainIdx=gIdx;
  Serial.printf("Auto-gain complete: idx=%d\n",gIdx);
  return gIdx;
}

// ── Setup ─────────────────────────────────────────────────────────────────────
void setup(){
  Serial.begin(115200); delay(300);
  randomSeed((uint32_t)esp_random());
  pinMode(NEOPIXEL_POWER,OUTPUT); digitalWrite(NEOPIXEL_POWER,HIGH);
  pixel.begin(); pixel.setBrightness(LED_BRIGHTNESS); pixel.show();
  Wire.begin();
  if(!as7343.begin()){
    Serial.println("ERROR: AS7343 not found"); sensorOK=false;
    for(int i=0;i<6;i++){setLED(255,0,0);delay(200);setLED(255,255,255);delay(200);}
    setLED(0,0,0);
  } else {
    sensorOK=true;
    as7343.setATIME(29); as7343.setASTEP(599);
    runAutoGain();
  }
  connectWiFi();
  server.on("/",         HTTP_GET,  handleRoot);
  server.on("/status",   HTTP_GET,  handleStatus);
  server.on("/snapshot", HTTP_GET,  handleSnapshot);
  server.on("/log",      HTTP_GET,  handleLog);
  server.on("/thoughts", HTTP_GET,  handleThoughts);
  server.on("/scores",   HTTP_GET,  handleScores);
  server.on("/start",    HTTP_POST, handleStart);
  server.on("/stop",     HTTP_POST, handleStop);
  server.on("/calibrate",HTTP_POST, handleCalibrate);
  server.begin(); Serial.println("Server started.");
}

// ── Loop ──────────────────────────────────────────────────────────────────────
void loop(){
  if(!running) return;
  if(!sensorOK){
    stopExperiment("Sensor unavailable. Search cannot run.", true);
    return;
  }
  uint32_t now=millis(); if(now<nextMs) return;
  if(!settling){
    if(calibPhase!=0){ settling=true; nextMs=now+settleMs; return; } // wait for calibration
    switch(alg){
      case ALG_SPSA:     stepSPSA();    break;
      case ALG_BAYES:    stepBO();      break;
      case ALG_THOMPSON: stepTS();      break;
      case ALG_CMAES:    stepCMA();     break;
      default: break;
    }
    settling=true; nextMs=now+settleMs;
  } else {
    uint16_t buf[NUM_CH]={};
    if(as7343.readAllChannels(buf)){
      sensorReadFailures=0;
      if(calibPhase==1){
        // Dark frame: LED off — store ambient spectrum then light the target color.
        for(int i=0;i<NUM_CH;i++) ambSpec[i]=(float)buf[i];
        calibPhase=2;
        setLED(recTgtR,recTgtG,recTgtB);
        char msg[100];
        snprintf(msg,sizeof(msg),"Calibrating: reading target rgb(%d,%d,%d)...",recTgtR,recTgtG,recTgtB);
        setStateMessage(msg);
        settling=true; nextMs=now+settleMs;
        return;
      }
      if(calibPhase==2){
        // Target frame: subtract ambient so only LED contribution is stored.
        if(isSaturated(buf)){
          if(currentGainIdx>0){
            currentGainIdx--;
            as7343.setGain((as7343_gain_t)currentGainIdx);
            Serial.printf("Calib saturated, reducing gain to idx=%d\n",currentGainIdx);
            setStateMessage("Calibration saturated, reducing sensor gain...");
            settling=true; nextMs=now+settleMs;
            return;
          }
          stopExperiment("Calibration saturated at minimum gain. Lower LED brightness or move the sensor back.", true);
          return;
        }
        for(int i=0;i<NUM_CH;i++) recTgtSpec[i]=max(0.0f,(float)buf[i]-ambSpec[i]);
        calibPhase=0;
        setStateMessage("Calibrated. Searching from random start...");
        switch(alg){
          case ALG_SPSA:     initSPSA();    break;
          case ALG_BAYES:    initBO();      break;
          case ALG_THOMPSON: initTS();      break;
          case ALG_CMAES:    initCMA();     break;
          default: break;
        }
        settling=false; nextMs=now+pauseMs;
        return;
      }
      int idx=logHead%LOG_MAX;
      Reading& rd=logBuf[idx]; rd.r=ledR;rd.g=ledG;rd.b=ledB;
      memcpy(rd.ch,buf,sizeof(rd.ch)); logHead++; if(logCount<LOG_MAX)logCount++;
      evalCount++;
      float sc=computeScore(buf);
      lastScore=sc;
      switch(alg){
        case ALG_SPSA:     afterSPSA(rd,sc);    break;
        case ALG_BAYES:    afterBO(rd,sc);      break;
        case ALG_THOMPSON: afterTS(rd,sc);      break;
        case ALG_CMAES:    afterCMA(rd,sc);     break;
        default: break;
      }
    } else {
      sensorReadFailures++;
      Serial.printf("WARN: readAllChannels failed (%d)\n",sensorReadFailures);
      if(sensorReadFailures >= 5){
        stopExperiment("Repeated sensor read failures. Check wiring/power and recalibrate.", true);
        return;
      }
    }
    settling=false; nextMs=now+pauseMs;
  }
}
