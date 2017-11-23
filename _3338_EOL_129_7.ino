#include <EEPROMex.h>
#include <EEPROMVar.h>
#include <FiniteStateMachine.h>
#include <AccelStepper.h> // stepper library with acceleration
#include <elapsedMillis.h>
#include <digitalWriteFast.h>

//Things that may need changing
float ver = 129.7; // version id
// 4 stopping message only sent if verbose turned on
// 5 open gripper in abort
// 6 stepper home - retry on home failure
// 7 fix for hang on startup with door open

int commsTime = 5000; // maximum time allowed for comms in milliseconds
int tareTime = 10000; // max time for taring in milliseconds

const int homeSpeed = 500; // homing speed in mm/s
const int travelSpeed = 5500; // normal linear speed for production mm/s
const int testSpeed = 100; //speed for motions during tests mm/s
const int acceleration = 8000; // mm/s/s

int preCapRemove = 110; // position not yet in contact with cap or trigger - overwritten by eeprom
const int touchCapLoad = -2; // load when touched cap to detect ready to stop.running
const float capRemoveDist = 2.5;// move up before close collet to grip cap
const int extraCapRemove = 10;
const int upLimitLoad = 3500; // load peak to indicate cap pulling started
const int capLoadDrop = 2000; // amount current reading is under moving average to indicate removal in mN
const int overRun = 10; // number of load readings to give after cap removal detected

int triggerPos = 112; // trigger point start position - overwritten by eeprom
float pushMove = 1.6; // distance to push trigger
const int limitWeight = 50;// max difference between subsequent balance readings to indicate end of stream
const int triggerLimitLoad = 3500;// load peak to indicate trigger push started in mN
const int startWeight = 50; // weight of dispense to register as a start in mg
const int readTime = 10; // min delay between balance reads
const int trigLoadDrop = 1000; //amount force falls by to indicate triggeringf
const int trigGrad = 180; // limit on gradient to indicate trigger event.
const byte numLoadReadings = 5;  //number of readings for moving average
long peakLoad; // peak seen during trigger pushing
const int retryPercent = 60; // if load is still above this 100ms after trigger detection, was false trigger, so retry

int upPos = 3; // distance from up limit/home to return to
int downPos = 110; // max down distance - overwritten by eeprom
int startPos = 110; // position for pre-trigger
int intermedPos = 50; // position to use between cap remove and actuate
const int penDrop = 2; // amount to drop pen to shake off drip

const int messageInterval = 100; //minimum message send interval (ms)

const long maxLoad = 45000; //maximum allowed load in millinewtons

int verifyPos = 88; //position for pre-touch of verify weight - overwritten by eeprom
const byte verifyMove = 8; // movement to lift verify weight
const float verifyReleaseLoad = 0.2; // load to release weight on putdown

const int moveDuration = 30; // seconds for initial movements

const byte LGdeBounce = 10; //number of loops through code to register light guard changes

//********************

boolean verbose = false;

volatile boolean timerTrigger = false; // trigger for output to timer, volatile so can be use in ISR
volatile unsigned long timeStart, timeEnd;

// Pin arrangement
// Inputs
const byte streamSensor = 2;         // Keyence stream sensor pin D2
const byte stopIsOut = 36;
const byte stopIsBack = 12;
const byte carriageAtTest = 11;
const byte carriageAtDiscard = 10;
const byte carriageAtReject = 30;
const byte nestIsOpen = 34;
const byte nestIsClosed = 32;
const byte penGripperIsOpen = 52;
const byte penGripperIsClosed = 50;
const byte lightGuardIsOk = 3;
const byte temp1 = 3;
const byte estopIsOk = 6;
const byte negLoadLimit = 4; // this is high when active
const byte posLoadLimit = 5; // this is high when active
const byte stepperUpLimit = 22; // note these limits work high = obscured, reverse of all others !
const byte stepperDownLimit = 24;
const byte containerIsPresent = 48;
const byte scrapIsPresent = 63;
const byte penIsPresent = 46;
byte inputArray[] = {
  2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 22, 24, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52
};
byte inputStateArray[sizeof(inputArray) / sizeof(byte)];


// Outputs
const byte signalOut = 53;  // green signal light
const byte startTimer = 51;        // timer start signal
const byte gateTimer = 41;         // timer gate signal
const byte resetTimer = 45;        // timer reset signal
const byte RS485On = 54;
const byte zeroShift = 49;        // keyence unit zero shift
const byte moveCarriageToTest = 39;
const byte moveCarriageToDiscard = 37;
const byte moveStopOut = 43;
const byte moveStopBack = 47;
const byte openCollet = 31;
const byte closeCollet = 35;
const byte openPenGripper = 33;
const byte closePenGripper = 27;
const byte openNest = 29;
const byte closeNest = 25;
const byte stepperDir = 28;
const byte stepperStep = 26;
byte outputArray[] = {
  23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53
};
byte outputStateArray[sizeof(outputArray) / sizeof(byte)];

const int thisAddress = 0x9;
const int StepperDriveAddress = 0x8;

// actions
const byte check = 0;
const byte swap = 0;
const byte open = 1;
const byte close = 2;
const byte test = 1;
const byte discard = 2;
const byte reject = 3;
const byte setTravel = 2;
const byte setTest = 3;
const byte setRemove = 6;
const byte setVerify = 5;

int resetPulse = 100;  // length of reset pulse for timer
unsigned long MMdelta = 0L; // allows timings to be carried out from start of test ratehr than myMillis()
unsigned long dispenseEnd, moveEnd, resetEnd, nominalTimerEnd, timeoutTimerEnd, startEnd, errorEnd;
unsigned long commsEnd, balanceCommsEnd, loadCommsEnd, commsEnd2, deBounceEnd, shiftEnd, sysTimeoutEnd; // variables for end of things
unsigned long timeTaken, usedTime, timeStamp, testTimerStart;
byte tempHeadPos[10];

uint32_t nominalTimeout = 70;  // nominal timeout value in tenths of a second - updated with value from PC
int weightChange = 10; // change in weight to detect dose completion in mg - updated from PC
int doseTimeout; // timeout in sec
int doseTime, doseWeight;

byte a, b; //bytes for i2c instruction and response
char i2cbuffer[8]; //buffer for received values
long val = 0; // received value

uint32_t timeTrigger = 0L;
volatile unsigned long now;

boolean nomEnd = false; //nominal timer is finished

boolean priorityStatus;
int maxTimeout = 15000; // maximum test time in milliseconds - updated with info from pc
byte mainRunState = 0; //indicator of position in running order
byte verifyRestartState = 0;
byte abortRestartState = 0;
byte restartState = 0; // used to maintain state when light guard interrupted
byte abortRunState = 0;
byte verifyRunState = 0;
byte startRunState = 0;
boolean timeoutEnd = false;
byte minPause = 30; // minimum pause between zero shifts
int maxPause = 2000; // maximum pause between zero shifts
int maxDelay = 3000; //max for microsecond delay between transmit and enable changeover
byte minDelay = 10;
byte startPulse = 40; // length of start pulse (ms)
int initialise, addressInit, addressTimer, addressShift, addressDelay;
int addressPreCapRemove, addressCapRemoveDist, addressTriggerPos, addressPushMove;
int addressUpPos, addressDownPos, addressStartPos, addressMaxTimer, addressVerifyPos;
int addressIntermedPos, addressWeightChange;

byte horPos = 0; //horizontal head position becasue pasing in paramaters is a pain the bum
byte deBounceTime = 100; // pause to allow input debouncing (ms)
long shiftPause = 30; // pause between zeroshift if idle
int delayMicros = 2000;// delay for comms enable line - set to 2000 after testing at 1500 and 3000.
int cylMove = 5000; // milliseconds for cylinder movements to complete
int stepperMax = 20000; // milliseconds for stepper movement
byte LGcounter = LGdeBounce;
byte nestState = swap;
byte colletState = swap;
byte penGripState = swap;
byte stopState = 0;
byte horState = 0;
byte loadReadState = 0;
byte balanceReadState = 0;
boolean endComm, devicePass, pass, go, startTimerOnce, deBounce, doShift, changes, chksumRead, newWeightAvail, newLoadAvail, lightGuardSent, overloadSent;
boolean serialOn, lastPenIsPresent, loadNoOpState, balanceNoOpState, capRemoved, removalInProgress, triggerInProgress, normal, readFlag;
boolean rejectCap, touchedCap, triggered, dispenseStarted, lastLightGuardIsOk, lastContainerIsPresent, lastEstopIsOk;
boolean restart = 0;
boolean verifyRestart = 0;
boolean writeNow, errorRestart, touchDown, verifyCancel, verifyWeightUp, penIn;
boolean temp2, temp3;
boolean checkRequest = false; // indicates that HMI has requested a position update
boolean needleMeasure; // indicates a request for needle measure
boolean gated = false;
boolean verifyState = false; // indicates wether verify weight is in or not
boolean lightGuardStatus = HIGH;
boolean abortStop = false;
//boolean TEMP1=false;
byte errorState = 0; // indication of where the error occurred.
byte errorActive = 0; // indicates when error is active
/* 1=comms timeout,
  2=no pen placed
  3=start without pen,
  4=not configured
  5=unexpected stepper things,
  6=no container or scrap,
  7= timer value oor,
  8= no air,
  10= nest move timeout,
  11= pen grip timeout,
  12= collet timeout,
  13= horizontal move timeout
  14= stop timeout
  15= balanceread fail
  16= load read fail
  17= cap not found
  18= no cap removal trigger
  20= light guard broken during timing
  21= stepper timeout
  30=system timeout
  40 = overload or axis limit
*/
byte readPCSerial; // mini state machine sequence in mainNoOp

// stepper stuff
int stepperState = 1;
int fullStroke = 250; // full stroke length in mm
byte stepperStatus;
boolean homing = false;
int conversion = 125; // steps per mm
int tempSpeed, moveSpeed;
long headPos, restartHeadPos;
boolean stepperIsActive = false;
boolean homed = false;

// things to do with timer comms
const byte timerMessageLength = 30; // size of timerBuffer for returned message from timer
int timerReceivedMessage; // length of returned message
byte count = 0; //counter for length of message received
byte timerBuffer[timerMessageLength]; //will hold incoming message
boolean commsFailed;
byte retries = 0; // counts number of comms retries
int failWhy = 0; // indicates step of comms that failed
byte maxretries = 3; // maximum number of comms retries
boolean ended = false;
boolean configured = true; //NOTE - need to check where the config comes from !
float timerValue;
float maxTimerValue = 50; // maximum value allowed - anyhitng larger is an error.
//                  =  STX   NODE  NODE  SUB   SUB   SID   MRC   MRC   SRC   SRC    VARTYPE    START START START START BIT   BIT   NUM   NUM   NUM   NUM   ETX  chksum
byte timerMessage[] = {
  0x02, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x31, 0x30, 0x31, 0x43, 0x30, 0x30, 0x30, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x31, 0x03, 0x41
};
byte chksum, chksum2, chksumtemp, scrap;
byte index;

// things to do with Wire comms
//int wireReadTimeout = 250; //i2c timeout in ms

// things to do with PC serial comms
int messageTime = 1000; // interval between actuator messages
char incomingChar, command, balanceResponse;
char currentState[15];
const int numPar = 8; // number of parameters in a command string
int parameters[numPar];
byte testSeq = 0; // indicates progress of test cycle
char testStatus = 'A'; // indicates progress of stream measurment
int readNum = 1; // start new set of readings
unsigned long testStart = 0; // saves test start time
unsigned long finishTime;
//char commands[]="SCTARUNWMJLKGHPVXYZ";
char commands[] = "SCTABZRUNWwMJLKGHPVXncE";

// things to do with balance comms
boolean balanceError = false;
//byte tareReturnState=0; //allows tare funtion to return to correct state to prevent duplication of function
//byte actuatorReturnState = 0;// 0 = noop1, 1=waitforup, 2=
char balanceBuffer[30]; // receive buffer
long weight = 0;
long calcWeight = 0;
int prevWeight = 0;
long weightTotal = 0; // for moving average
byte balanceReceivedMessage = 0; // length of received mesage
//char chb = ' ';
byte balanceState = 1; // simple state machine in balance taring
const byte numBalanceReadings = 5;  //number of readings for moving average
long balanceReadings[numBalanceReadings] = {
  0
};
long averageWeight = 0;
long previousAvWt = 0;
boolean dispenseFinished = false;
byte balanceIndex = 0;
unsigned long getNextData = 0;

// things to do with load comms
boolean loadError = false;
char loadBuffer[20];
float load = 0;
float lastLoad = 0;
long averageLoad = 0;
long lastAvLoad = 0;
long gradient = 0; // gradient of average load, used to indicate triggering
long milliLoad;
unsigned long lastTimestamp, timestamp;
int finishedCount;
long loadReadings[numLoadReadings] = {
  0
};
byte loadIndex = 0;
byte loadReceivedMessage = 0;
char chl = ' ';
byte loadState = 1; // simple state machine in load cell taring
long loadTotal = 0;

/** state definition */
//StateMachine states

// maint functions
State configSys = State(configSysEnter, configSysUpdate, configSysExit);
State getReadings = State(getReadingsEnter, getReadingsUpdate, getReadingsExit);
State actuateNest = State(actuateNestEnter, actuateNestUpdate, actuateNestExit);
State actuateGripper = State(actuateGripEnter, actuateGripUpdate, actuateGripExit);
State actuateStop = State(actuateStopEnter, actuateStopUpdate, actuateStopExit);
State actuateCollet = State(actuateColletEnter, actuateColletUpdate, actuateColletExit);
State headMoveVer = State(headMoveVerEnter, headMoveVerUpdate, headMoveVerExit);
State headMoveHor = State(headMoveHorEnter, headMoveHorUpdate, headMoveHorExit);
State tare = State(tareEnter, tareUpdate, tareExit);
State tareFail = State(tareFailEnter, tareFailUpdate, tareFailExit);

State mainNoOp = State(mainNoOpEnter, mainNoOpUpdate, mainNoOpExit); //no operation
State startTest = State(startTestEnter, startTestUpdate, startTestExit);
State waitForSafety = State(waitForSafetyUpdate);
State lowerToCap = State(lowerToCapEnter, lowerToCapUpdate, lowerToCapExit);
State verifyRelease = State(verifyReleaseEnter, verifyReleaseUpdate, verifyReleaseExit);
State smallMoveUp = State(smallMoveUpEnter, smallMoveUpUpdate, smallMoveUpExit);
State removeCap = State(removeCapEnter, removeCapUpdate, removeCapExit);
State ready = State(readyEnter, readyUpdate, readyExit); // state ready for timer trigger, enter = turn on light and set message, ready = send reset pulse to timer
State retryReady = State(retryReadyUpdate); // go to this and immediately bounce back to ready to retry after false trigger
State timing = State(timingEnter, timingUpdate, timingExit);
State waitForDispenseEnd = State(waitForDispenseEndEnter, waitForDispenseEndUpdate, waitForDispenseEndExit);
State gate = State(gateEnter, gateUpdate, gateExit);
State retry = State(retryUpdate);
State commsDead = State(commsDeadUpdate);
State reset = State(resetEnter, resetUpdate, resetExit);
State waitForUnclamp = State(waitForUnclampEnter, waitForUnclampUpdate, waitForUnclampExit);
State waitForNeedle = State(waitForNeedleEnter, waitForNeedleUpdate, waitForNeedleExit);
State waitForNeedleReturn = State(waitForNeedleReturnEnter, waitForNeedleReturnUpdate, waitForNeedleReturnExit);
State waitForPenRemove = State(waitForPenRemoveEnter, waitForPenRemoveUpdate, waitForPenRemoveExit);
State dispenseOver = State(dispenseOverEnter, dispenseOverUpdate, dispenseOverExit);
State temp = State(tempUpdate);
State homeStepperState = State(homeStepperStateEnter, homeStepperStateUpdate, homeStepperStateExit);
State nullState = State(nullStateUpdate);

State error = State(errorUpdate);
State timerValueError = State(timerValueErrorUpdate);

// timeout states (nominal time)
State nomTimerNoOp = State(nomTimerNoOpEnter, nomTimerNoOpUpdate, nomTimerNoOpExit); //no operation
State nomTimer = State(nomTimeEnter, nomTimeUpdate, nomTimeExit); // overall timeout check status

//timeout states (max time)
State maxTimerNoOp = State(maxTimerNoOpEnter, maxTimerNoOpUpdate, maxTimerNoOpExit); //no operation
State maxTimer = State(maxTimerEnter, maxTimerUpdate, maxTimerExit);

//timeout states (max time)
State sysTimerNoOp = State(sysTimerNoOpEnter, sysTimerNoOpUpdate, sysTimerNoOpExit); //no operation
State sysTimer = State(sysTimerEnter, sysTimerUpdate, sysTimerExit);

// balance read states
State balanceNoOp = State(balanceNoOpEnter, balanceNoOpUpdate, balanceNoOpExit);
State balanceRead = State(balanceReadEnter, balanceReadUpdate, balanceReadExit);

//Load cell read states
State loadNoOp = State(loadNoOpEnter, loadNoOpUpdate, loadNoOpExit);
State loadRead = State(loadReadEnter, loadReadUpdate, loadReadExit);


FSM mainStateMachine = FSM(mainNoOp); //initialize state machine, start in state: mainNoOp
FSM nominalTimer = FSM(nomTimerNoOp); // initialise timer state machine, start in TimerNoOp
FSM timeoutTimer = FSM(maxTimerNoOp);
FSM sysTimeout = FSM(sysTimerNoOp);
FSM balanceMachine = FSM(balanceNoOp);
FSM loadMachine = FSM(loadNoOp);

char buffer[30];    // temporary buffer for string transfer

AccelStepper stepper1(1, stepperStep, stepperDir); // 1 choice for step/dir

//LiquidCrystal_I2C lcd(0x27,16,2);  // set the LCD address to 0x27 for a 16 chars and 2 line display

//Button penPresent = Button(penIsPresent,PULLUP);

elapsedMillis messageTimeElapsed;
elapsedMillis actuatorTimeout;
elapsedMillis stepperTimeout;
elapsedMillis tareTimeout;
elapsedMillis serialPrint;
elapsedMillis tempTimer;
elapsedMillis emptyTimer;
elapsedMillis wfnTimer;
elapsedMillis balanceTimeout;
elapsedMillis loadTimeout;
elapsedMillis wireReadTime;
elapsedMillis serialTime;
elapsedMillis readTimer;
elapsedMillis sysTimerElapsed;

void setup() {
  Serial.begin(19200, SERIAL_8N1);  // serial used for PC comms through USB
  Serial.print("*v");
  Serial.println(ver);
  if (verbose)Serial.println("Hello World!");
  if (verbose)Serial.print("Version ");
  if (verbose)Serial.println(ver);
  while (Serial.available()) Serial.read();
  Serial1.begin(9600, SERIAL_7E2); // serial 1 used for comms with timer through RS485
  Serial2.println("Hello 1");
  Serial2.begin(19200, SERIAL_8N1); // serial 2 used for comms with balance
  Serial2.println("ON"); // wake up balance
  Serial3.begin(38400, SERIAL_8N1); // serial 3 used for comms with force meter
  Serial3.println("Hello 3");
  //  Wire.begin(thisAddress);
  //  Wire.onReceive(receiveEvent);
  stepper1.setCurrentPosition(0);
  stepper1.setAcceleration(acceleration); // acceleration is not reset

  /*  lcd.init();                      // initialize the lcd & turn on backlight
    lcd.backlight();

    lcd.clear();
    lcd.print("GB Innomech");
    lcd.setCursor(0,1);
    lcd.print("Project 3338");
    //  delay(1000);
    lcd.setCursor(0,1);
    lcd.print("Version       ");
    lcd.setCursor(9,1);
    lcd.print(ver);
    //  delay(1000);
    lcd.setCursor(0,1);
    lcd.print("EOL tester      ");
    //delay(1000);*/


  GetEepromAddresses(); // set up eeprom addresses for all saved stuff
  // check that eeprom has some values in
  initialise = EEPROM.readInt(addressInit);

  // if it has values then read the values back. If not, write standard values
  if ( initialise == 3338) {
    ReadEeprom();
  }
  else {
    initialise = 3338;
    EEPROM.updateInt(addressInit, initialise);
    WriteToEeprom();
  }

  attachInterrupt(0, timerGo, CHANGE); // trigger signal from thru-beam sensor on D2

  pinMode(streamSensor, INPUT);
  //  pinMode(colletIsClosed,INPUT);
  pinMode(stopIsOut, INPUT_PULLUP);
  pinMode(stopIsBack, INPUT);
  pinMode(carriageAtTest, INPUT);
  pinMode(carriageAtDiscard, INPUT);
  pinMode(carriageAtReject, INPUT);
  pinMode(nestIsOpen, INPUT);
  pinMode(nestIsClosed, INPUT);
  pinMode(penGripperIsOpen, INPUT);
  pinMode(penGripperIsClosed, INPUT);
  pinMode(lightGuardIsOk, INPUT);
  pinMode(estopIsOk, INPUT);
  pinMode(stepperUpLimit, INPUT);
  pinMode(stepperDownLimit, INPUT);
  pinMode(containerIsPresent, INPUT);
  pinMode(scrapIsPresent, INPUT);
  pinMode(negLoadLimit, INPUT_PULLUP);
  pinMode(posLoadLimit, INPUT_PULLUP);

  pinMode(signalOut, OUTPUT);
  pinMode(startTimer, OUTPUT);
  pinMode(gateTimer, OUTPUT);
  pinMode(resetTimer, OUTPUT);
  pinMode(resetTimer, OUTPUT);
  pinMode(zeroShift, OUTPUT);
  pinMode(moveCarriageToTest, OUTPUT);
  pinMode(moveCarriageToDiscard, OUTPUT);
  pinMode(moveStopOut, OUTPUT);
  pinMode(moveStopBack, OUTPUT);
  pinMode(openCollet, OUTPUT);
  pinMode(closeCollet, OUTPUT);
  pinMode(openPenGripper, OUTPUT);
  pinMode(closePenGripper, OUTPUT);
  pinMode(openNest, OUTPUT);
  pinMode(closeNest, OUTPUT);
  pinMode(RS485On, OUTPUT);

  stepperIsActive = true;
  stepperTimeout = 0;

  messageTimeElapsed = 0;
  actuatorTimeout = 0;

  if (digitalRead(stepperUpLimit) == HIGH) {
    stepper1.move(-2000);
    while (stepper1.distanceToGo() != 0) {
      stepper1.run();
    }
  }
  digitalWrite(moveStopOut, HIGH);
  digitalWrite(closeCollet, HIGH);
  digitalWrite(closePenGripper, HIGH);
  digitalWrite(closeNest, HIGH);
  delay (500);
  digitalWrite(moveStopOut, LOW);
  digitalWrite(closeCollet, LOW);
  digitalWrite(closePenGripper, LOW);
  digitalWrite(closeNest, LOW);
  digitalWrite(moveStopBack, HIGH);
  digitalWrite(openCollet, HIGH);
  digitalWrite(openPenGripper, HIGH);
  digitalWrite(openNest, HIGH);
  digitalWrite(moveCarriageToTest, HIGH);
  digitalWrite(moveCarriageToDiscard, LOW);

  startRunState = 1;
  if (verbose)Serial.print("startstate");
  if (verbose)Serial.println(startRunState);
  nextState();

  overloadSent = false;
  lightGuardSent = false;
  MMdelta = myMillis();
} // end of setup


void loop() {
  boolean finish;
  mainStateMachine.update(); // this line makes the state machine 'tick' for timer reaedings
  nominalTimer.update(); // tick for overall maximum timer
  timeoutTimer.update();
  balanceMachine.update();
  loadMachine.update();
  sysTimeout.update();

  if (lightGuardStatus != digitalReadFast(3)) { // compare light guard recorded status with read
    if (lightGuardStatus == HIGH) { // light guard status indicates alreaedy obscured, (but read indicates not)
      if (LGcounter > 0) --LGcounter; // decrement counter if above 0
      else {
        lightGuardStatus = LOW; // change lightguardstatus if counter reaches zero
        Serial.println("LG ok");
        //       errorState=22;
        //       errorActive=false;
        //       sendError(errorState,errorActive);
      }
    }
    else { // therefore lightguardstatus must be low
      if (LGcounter < LGdeBounce) ++LGcounter; // increment counter if less than debounce value
      else {
        lightGuardStatus = HIGH; //change status to show obscured if value reached
        Serial.println("LG open");
        //        errorState=22;
        //        errorActive=true;
        //        sendError(errorState,errorActive);
      }
    }
  }

  //  messageMachine.update();
  if (serialOn && serialPrint > 4000) { // if maintenance serial printing is on , and over 4 seconds since last print
    if (verbose) printInputs();
    if (changes) printChanged();
    if (verbose) printOutputs();
    serialPrint = 0; // reset timer for next loop
  }
  /* if (serialPrint > 4000){ // if maintenance serial printing is on , and over 4 seconds since last print
    Serial.print("RS ");
    Serial.println(restart);
    Serial.print("LG stat");
    Serial.print(lightGuardStatus);
    serialPrint=0; // reset timer for next loop
    }*/
  if (digitalReadFast(3) == HIGH && homed) {
    homed = false;
    //    Serial.println("Need Home");
  }
  if (stepperIsActive) {
    if (digitalReadFast(6) && !errorActive) { // estop pressed
      Serial.println("estop press");
      //      errorState=22;
      //      errorActive=true;
      //      sendError(errorState,errorActive);
      mainRunState = 0;
      if (!abortRunState) {
        abortRunState = 1;
        nextState();
      }
      if (!digitalReadFast(6) && errorActive) { // estop released
        Serial.println("estop release");
        //      errorState=22;
        //      errorActive=false;
        //      sendError(errorState,errorActive);
      }
    }
    else if ((!homing && digitalReadFast(22) == HIGH) || digitalReadFast(4) == HIGH ||  digitalReadFast(5) == HIGH || (!homing && digitalReadFast(24) == HIGH)) { // kill stepper moves if exess force or limit
      stepper1.stop();
      abortStop = true;
      if (!overloadSent) {
        errorState = 40; // indicates stepper fail through limits or overload
        errorActive = true;
        sendError(errorState, errorActive);
        overloadSent = true; // this means its only sent once
        mainRunState = 0;
        if (!abortRunState) {
          abortRunState = 1;
          nextState();
        }
      }
    }
    if (lightGuardStatus == HIGH && restart == false && moveSpeed == setTravel) { // if safety not OK, travel speed move and not already waiting for restart
      if (verbose)Serial.println("stopping");
      if (mainRunState > 0 && !homing) {
        restartState = mainRunState - 3;
        verifyRestartState = 0;
        homed = false;
        finish = true;
      }//All travel moves should be preceeded by null and home, so jump back to this on restart
      else if (abortRunState > 0) {
        abortRestartState = 1;
        finish = true;
      }
      else if (verifyRunState > 0 && verifyRunState < 20) {
        verifyRestartState = 1;
        finish = true;
      } // indicates restarting a verify state during pickup
      else if (verifyRunState > 20) {
        verifyRestartState = 1;
        finish = true;
      } //verify restart during putdown
      //      else if (mainRunState>0 && homing) {restartState = mainRunState - 2; Serial.println("Homing");homed=false;}//if already homing
      else if (mainRunState > 0 && homing && !lightGuardSent) { // cancel if homing
        Serial.println("lg open");
        errorState = 20;
        errorActive = true;
        sendError(errorState, errorActive);
        lightGuardSent = true; // this means its only sent once
        mainRunState = 0;
        sysTimeout.transitionTo(sysTimerNoOp);
        while (digitalReadFast(3) == HIGH) {
          delay(1);
        };// wait until light guard is clear before abort takes place
        if (!abortRunState) {
          abortRunState = 1;
          Serial.println("1");
          nextState();
        }
        finish = false;
      }
      if (finish) {
        Serial.print("rs ");
        Serial.println(restartState);
        stepper1.stop();
        abortStop = true;
        homed = false;
        restart = true;
        Serial.println("rs true");
      }
    }
    else if (lightGuardStatus == HIGH && verifyRestart == false && moveSpeed == setVerify) { // if safety not OK, travel verify speed move and not already waiting for restart
      resetLoad();
      if (verbose)Serial.println("stopping verify");
      mainStateMachine.transitionTo(mainNoOp); // crash out of routine.
      //      mainStateMachine.immediateTransitionTo(mainNoOp); // crash out of routine.
      sysTimeout.transitionTo(sysTimerNoOp); // stop timeout timer
      stepper1.stop();
      abortStop = true;
      homed = false;
      verifyRestart = true;
      Serial.println("verify rs");
    }
    else if (lightGuardStatus == HIGH && restart == false && !lightGuardSent) { // all other speeds cause error message and test abandon
      errorState = 20;
      errorActive = true;
      sendError(errorState, errorActive);
      lightGuardSent = true; // this means its only sent once
      mainStateMachine.transitionTo(mainNoOp); // crash out of routine.
      //      mainStateMachine.immediateTransitionTo(mainNoOp); // crash out of routine.
      mainRunState = 0;
      sysTimeout.transitionTo(sysTimerNoOp);
      while (digitalReadFast(3) == HIGH) {
        delay(1);
      };// wait until light guard is clear before abort takes place
      if (!abortRunState) {
        abortRunState = 1;
        Serial.println("2");
        nextState();
      }
    }

    else if (lightGuardStatus == LOW && lightGuardSent) lightGuardSent = false; // reset sent flag on lightguard clear

    if (errorState == 40 && errorActive) {
      if (digitalReadFast(4) == LOW && digitalReadFast(5) == LOW && digitalReadFast(22) == LOW && digitalReadFast(24) == LOW) { // limits and overload now OK
        errorState = 40;
        errorActive = false;
        overloadSent = false;
        sendError(errorState, errorActive);
        //        TEMP1=false;
      }
    }
  }
  if (lightGuardStatus == LOW && restart == true) { // safety OK again, and restart requested
    Serial.println("restarting travel");
    abortStop = false;
    lightGuardSent = false;
    restart = false;
    stepperIsActive = true;
    if (verifyRestartState == 1) verifyRunState = 1;
    else if (verifyRestartState == 2) verifyRunState = 24; // skip to homing at end of sequence.
    else if (abortRestartState) {
      abortRunState = 1;
      Serial.println("restart in abort");
      errorState = 20;
      errorActive = true;
      sendError(errorState, errorActive);
    }
    else {
      mainRunState = restartState;
      Serial.print("rs in state ");
      Serial.println(restartState);
      homed = false;
    }
    testTimerStart = myMillis(); // crude reset of test start time to reset systimer - its only used in the timeout, so doesn't affect the test.
    if (!verifyRunState) sysTimeout.transitionTo(sysTimer);
    homed = false;
    nextState(); // should restart in homing routine
  }
  else if (lightGuardStatus == LOW && verifyRestart == true) { // safety OK again, and restart requested after verify stop
    Serial.println("restarting verify");
    abortStop = false;
    lightGuardSent = false;
    verifyRestart = false;
    verifyCancel = true;
    stepperIsActive = true;
    verifyRunState = 20;
    homed = false;
    nextState();
  }
  stepper1.run();
} // end of loop


//  ************** FSM states ***********

void mainNoOpEnter() { // main FSM noOp
  if (!restart) stepperIsActive = false;
  if (verbose) Serial.println("mainNoOp");
  readPCSerial = 1;
  //  lcd.clear();
  //  lcd.print("NoOp");
  command = '0';
  for (byte i = 0; i < numPar; i++)parameters[i] = 0;
  //  memset(parameters,0,sizeof(parameters)/sizeof(int));
  endComm = false;
  mainRunState = 0;
  //  abortRunState=0;
  verifyRunState = 0;
  digitalWriteFast(53, HIGH); // turn on green light
  digitalWriteFast(zeroShift, HIGH); // zero shift off
  shiftEnd = myMillis() + (shiftPause * 1000); // set time for next zero shift if not used
  emptyTimer = 0;
}

void mainNoOpUpdate() {  //noOperation
  if ((long)(myMillis() - shiftEnd) >= 0) { // check for timing of end of shift pause
    digitalWriteFast(zeroShift, LOW); //zero shift on
    delay (10);
    digitalWriteFast(zeroShift, HIGH); // zero shift off
    shiftEnd = myMillis() + (shiftPause * 1000);
  }
  readIncoming();
  if (endComm) {
    //if (verbose) Serial.println("switch");
    switch (command) { // select a Serial command to leave noOp
      case 'S': //status request
        //      lcd.clear();
        //      lcd.print("sendstatus");
        if (verbose) Serial.println("sendstatus");
        //      tim=1;
        sendStatus();
        break;
      case 'C': //config
        mainStateMachine.transitionTo(configSys);
        break;
      case 'R': //tare balance and load cell
        mainStateMachine.transitionTo(tare);
        break;
      case 'T': //initiate test
        if (digitalReadFast(penIsPresent) == LOW) {
          weight = 0;
          abortStop = false;
          testSeq = 0;
          testStatus = 'A';
          penIn = true;
          sendTestStatus();
          mainRunState = 1;
          digitalWriteFast(zeroShift, LOW); //zero shift on
          delay (10);
          digitalWriteFast(zeroShift, HIGH); // zero shift off
          testTimerStart = myMillis();
          nomEnd = false;
          if (errorActive) {
            errorActive = 0;
            sendError(errorState, errorActive);
            errorState = 0;
          }
          sysTimeout.transitionTo(sysTimer);
          nextState();
          digitalWriteFast(resetTimer, HIGH);
          //        balanceMachine.transitionTo(balanceRead);
        }
        else {
          errorState = 3;
          sendError(errorState, 1);
          mainRunState = 0;
          if (!abortRunState) abortRunState = 1; // if not currently running abort procedure, start it now
          Serial.println("3");
          nextState();
        }
        break;
      case 'N': // needle measure stuff
        needleMeasure = true;
        //      tim=2;
        sendStatus();
        break;
      case 'n': // needle measure stuff return
        needleMeasure = false;
        //      tim=3;
        sendStatus();
        break;
      case 'W': //Test weight sequence
        verifyRunState = 1;
        verifyNextState();
        break;
      case 'w': // put down test weight
        verifyRunState = 20;
        verifyNextState();
        break;
      case 'M': //pass balance and load reading
        mainStateMachine.transitionTo(getReadings);
        break;
      case 'K':
        { // actuators
          switch (parameters[0]) {
            case 1:
              mainStateMachine.transitionTo(actuateNest);
              nestState = parameters[1];
              break;
            case 2:
              penGripState = parameters[1];
              mainStateMachine.transitionTo(actuateGripper);
              break;
            case 3:
              mainStateMachine.transitionTo(actuateCollet);
              colletState = parameters[1];
              break;
            case 4:
              mainStateMachine.transitionTo(actuateStop);
              break;
          }
          break;
        }
      case 'c':
        mainStateMachine.transitionTo(actuateNest);
        nestState = swap;
        break;
      case 'U':
        mainStateMachine.transitionTo(actuateNest);
        nestState = parameters[1];
        break;
      case 'H': //Head move up/down
        switch (parameters[0]) {
          case 0: //check
            if (headPos <= upPos) Serial.println("*h1"); // indicate is up
            else Serial.println("*h2"); // indicate is down
            break;
          case 1: //up to top
            headPos = upPos * conversion; // set position for movement
            if (verbose)Serial.print("moving to ");
            if (verbose)Serial.println(headPos);
            moveSpeed = setTravel;
            mainStateMachine.transitionTo(headMoveVer);
            break;
          case 2: //down to pre cap remove
            headPos = preCapRemove * conversion; // set position for movement
            if (verbose)Serial.print("moving to ");
            if (verbose)Serial.println(headPos);
            moveSpeed = setTravel;
            mainStateMachine.transitionTo(headMoveVer);
            break;
          case 3: //down to pre trigger
            headPos = triggerPos * conversion; // set position for movement
            if (verbose)Serial.print("moving to ");
            if (verbose)Serial.println(headPos);
            moveSpeed = setTravel;
            mainStateMachine.transitionTo(headMoveVer);
            break;
          case 4: // jog down
            if (parameters[1] > 0) headPos += (parameters[1] * conversion); // down by parameter value
            else headPos += conversion; // drop by 1mm
            stepper1.setMaxSpeed(travelSpeed);
            stepperIsActive = true;
            stepper1.moveTo(-headPos);
            while (stepper1.distanceToGo() != 0) {
              stepper1.run();
            };
            stepperIsActive = false;
            break;
          case 5: // jog up by 1mm
            if (parameters[1] > 0) headPos -= (parameters[1] * conversion); // down by parameter value
            else headPos -= conversion; // drop by 1mm
            stepper1.setMaxSpeed(travelSpeed);
            stepperIsActive = true;
            stepper1.moveTo(-headPos);
            while (stepper1.distanceToGo() != 0) {
              stepper1.run();
            };
            stepperIsActive = false;
            break;
          case 6: //set preCapRemove
            if (parameters[1] == 1) { // 1= change value, otherwise just report
              preCapRemove = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("PreCapRemove = ");
            Serial.println(preCapRemove);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 7: //set verifyPos
            if (parameters[1] == 1) {
              verifyPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("VerifyPos = ");
            Serial.println(verifyPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 8: // set triggerPos
            if (parameters[1] == 1) {
              triggerPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("TriggerPos = ");
            Serial.println(triggerPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 9: // set upPos
            if (parameters[1] == 1) {
              upPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("UpPos = ");
            Serial.println(upPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 10: // set downPos
            if (parameters[1] == 1) {
              downPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("DownPos = ");
            Serial.println(downPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 11: // set startPos
            if (parameters[1] == 1) {
              startPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("StartPos = ");
            Serial.println(startPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
          case 12: // set intermediate pos
            if (parameters[1] == 1) {
              intermedPos = headPos / conversion;
              WriteToEeprom();
            }
            Serial.print("IntermediatePos = ");
            Serial.println(intermedPos);
            Serial.print("HeadPos = ");
            Serial.println(headPos / conversion);
            break;
        }
        break;
      case 'P': //Head move left/right
        horPos = parameters[0];
        mainStateMachine.transitionTo(headMoveHor);
        break;
      case 'V': //Send version num
        Serial.print("*v");
        Serial.println(ver);
        break;
      case 'X': // request for status
        Serial.print("*x");
        if (digitalReadFast(nestIsOpen) == LOW) Serial.print(0);
        else if (digitalReadFast(nestIsClosed) == LOW) Serial.print(1);
        else Serial.print(2);
        Serial.print(',');
        if (digitalReadFast(penGripperIsOpen) == LOW) Serial.print(0);
        else if (digitalReadFast(penGripperIsClosed) == LOW) Serial.print(1);
        else Serial.print(2);
        Serial.print(',');
        if (colletState == open) Serial.print(0);
        else if (colletState == close) Serial.print(1);
        else Serial.print(2);
        Serial.print(',');
        if (digitalReadFast(stopIsBack) == LOW) Serial.print(0);
        else if (digitalReadFast(stopIsOut) == LOW) Serial.print(1);
        else Serial.print(2);
        Serial.print(',');
        if (digitalReadFast(carriageAtTest) == LOW) Serial.print(0);
        else if (digitalReadFast(carriageAtDiscard) == LOW) Serial.print(1);
        else if (digitalReadFast(carriageAtReject) == LOW) Serial.print(2);
        else Serial.print(3);
        Serial.print(',');
        //      Serial.print(int(stepper1.currentPosition()/conversion));
        //      Serial.print(',');
        if (int(-stepper1.currentPosition() / conversion) > upPos - 2 && int(-stepper1.currentPosition() / conversion) < upPos + 2) Serial.print(0);
        else if (int(-stepper1.currentPosition() / conversion) > preCapRemove - 2 && int(-stepper1.currentPosition() / conversion) < preCapRemove + 2)Serial.print(1);
        else if (int(-stepper1.currentPosition() / conversion) > triggerPos - 2 && int(-stepper1.currentPosition() / conversion) < triggerPos + 2) Serial.print(2);
        else Serial.print(3);
        Serial.println();
        //      Serial.println(int(-stepper1.currentPosition()/conversion));

        if (errorActive) { // reset errors
          abortStop = false;
          errorActive = 0;
          sendError(errorState, errorActive);
          errorState = 0;
          //sent=false; // reset error sent flag so new messages can be sent
        }
        break;
      case 'A': // maintenace function to turn on serial reporting on inputs
        serialOn = (serialOn) ? false : true; //if (serialOn) serialOn = false; else serialOn=true;
        break;
      case 'B': // maintenance function to switch individual outputs
        digitalWriteFast (parameters[0], parameters[1]);
        if (verbose) Serial.println();
        if (verbose) Serial.print("*y");
        if (verbose) Serial.print(parameters[0]);
        if (verbose) Serial.print(',');
        if (verbose) Serial.println(parameters[1]);
        break;
      case 'Z': // maintenance function to turn on serial chatter
        if (parameters[0] ==  0) verbose = (verbose) ? false : true;
        else changes = (changes) ? false : true;
        break;
      default:
        while (Serial.available()) Serial.read();
        readPCSerial = 1;
        endComm = false;
        break;
    }
    //command = '0'; // reset command to prevent further actions
    // if (verbose) Serial.println("switch finished");
    while (Serial.available()) Serial.read();
    readPCSerial = 1;
    endComm = false;
  }

  boolean check = digitalReadFast(penIsPresent);
  if (check != lastPenIsPresent) { //if pen has just been placed or removed
    lastPenIsPresent = check;
    //    tim=4;
    sendStatus();//things to do if pen placed or removed COULD AUTO START IF NEEDED - use if (penPresert.isPressed()) {mainRunState =1; nextState()}here
  }

  /*  check = digitalReadFast(3);
    if (check != temp2){
    temp2=check;
    tim=5;
    sendStatus();
    }*/

  check = digitalRead(lightGuardIsOk);
  if (check != lastLightGuardIsOk) { //if pen has just been placed or removed
    lastLightGuardIsOk = check;
    //    tim=5;
    sendStatus();
  }
  /*    if(check == lastLightGuardIsOk && counter > 0){
    counter++;
    }
    else if (check != lastLightGuardIsOk){
    if (counter == 0) counter=1;
    else counter--;
    }
    // If the Input has shown the same value for long enough let's switch it
    if(counter >= debounce_count){
    lastLightGuardIsOk = check;
    counter = 0;
    tim=5;
    sendStatus();
    }*/
  /*  if (check != lastLightGuardIsOk){//if safety has just cleared or obscured
    tempTimer=0;
    change=true;
    lightDebounce = check;
    }
    if check = (lightDebounce && tempTimer>20)
    lastLightGuardIsOk = check;
    tim=5;
    sendStatus();
    }*/
  if (!check) digitalWriteFast(resetTimer, HIGH); // if light guard broken then reset timer to preven unexpected runaway.

  check = digitalReadFast(containerIsPresent);
  if (check != lastContainerIsPresent) { //if container has been removed or replaced
    lastContainerIsPresent = check;
    //    tim=6;
    sendStatus();
  }

  if (!lastPenIsPresent && !lastLightGuardIsOk && tempTimer > 100) { // if pen in, light guard OK and timer over 0.1 sec
    sendStatus();
    tempTimer = 0;
  }
  /*  if (sysTimerElapsed>500) {
    sendStatus();
    sysTimerElapsed=0;
    }*/
  if (emptyTimer > 2000) { // send t0 message every half second if ready for new pen.
    Serial.println("*t00,A,0,0,0,0");
    emptyTimer = 0;
  }
}

void mainNoOpExit() {
}

//******************************************************
void configSysEnter() {
  //  lcd.clear();
  //  lcd.print("ConfigSys");
  if (verbose) Serial.println("config");
}

void configSysUpdate() {

  nominalTimeout = parameters[0];
  weightChange = parameters[1];
  maxTimeout = parameters[3];
  WriteToEeprom();
  mainStateMachine.transitionTo(mainNoOp);
}

void configSysExit() {
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
  configured = true; // configuration complete
}

//******************************************************
void getReadingsEnter() {
  // if (verbose) Serial.println("getreadingsenter");
  balanceMachine.transitionTo(balanceRead);
  loadMachine.transitionTo(loadRead);
  //  lcd.clear();
  //  lcd.print("GetReadings");
  newWeightAvail = false;
  newLoadAvail = false;
}

void getReadingsUpdate() {
  //  if (newWeightAvail == true ){ // readings available from balance and load cell
  //    Serial.println("weight avail");}
  //  if (newLoadAvail ==true){ // readings available from balance and load cell
  //    Serial.println("load avail");}
  if (newWeightAvail == true && newLoadAvail == true) { // readings available from balance and load cell
    Serial.print("*t00,A,0,0,"); // start of response, seq step, status not normal, reading number, timestamp
    Serial.print(load, 1);
    Serial.print(',');
    Serial.println(float(weight) / 10000, 4);
    if (!running()) mainStateMachine.transitionTo(mainNoOp);
    else nextState();
  }
  if (loadError or balanceError) {
    errorState = 15;
    sendError(errorState, 1);
    Serial.println("*t00,A,0,0,0,0"); // start of response, seq step, status not normal, reading number, timestamp
    balanceMachine.transitionTo(balanceNoOp);
    loadMachine.transitionTo(loadNoOp);
    if (!running()) mainStateMachine.transitionTo(mainNoOp);
    else nextState();
  }
  // need timeout transition here ?
  //  Serial.write(0x0D); // send cr terminator
}

void getReadingsExit() {
  // if (verbose) Serial.println("getreadingsexit");
  //  memset(parameters,0,sizeof(parameters)/sizeof(int)); // zero all parameters
}


//******************************************************
void actuateNestEnter() {
  // if (verbose) Serial.println("actuatenest");
  if (nestState == swap) {
    if (digitalReadFast(nestIsOpen) == LOW) nestState = close; // if is open, call for closed
    else nestState = open; //vice versa
  }
  if (nestState == open) nestMoveOpen();
  if (nestState == close)nestMoveClose();
  //  lcd.clear();
  //  lcd.print("ActuateNest");
  //delay(1000);
  actuatorTimeout = 0;
  load = 0;
  //  weight=0;
  loadMachine.transitionTo(loadRead);
  if (!running()) balanceMachine.transitionTo(balanceRead);
}

void actuateNestUpdate() {
  if (tempTimer > messageTime && !running()) { // send progress messages
    sendActuatorStatus(parameters[0], 1, digitalReadFast(openNest), digitalReadFast(nestIsClosed), digitalReadFast(nestIsOpen), weight, load);
    tempTimer = 0;
    loadMachine.transitionTo(loadRead);
    balanceMachine.transitionTo(balanceRead);
  }
  if ((nestState == open && digitalReadFast(nestIsOpen) == LOW) || (nestState == close && digitalReadFast(nestIsClosed) == LOW)) { // move finished
    if (running()) nextState(); // if running a cycle,
    else mainStateMachine.transitionTo(mainNoOp);
  }
  else if (actuatorTimeout > cylMove) { // timeout
    errorState = 10;//
    sendError(errorState, 1);
    mainRunState = 0;
    testSeq = 13; // indicates clamping failed
    if (mainRunState > 0)sendTestStatus();
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("1");
    } // if not currently running abort procedure, start it now
    if (!running())mainStateMachine.transitionTo(mainNoOp);
    nextState();
    //    mainStateMachine.transitionTo(mainNoOp); // check for cylinder move timeout and return to noOp
  }
}

void actuateNestExit() {
  if (!running()) sendStatus();
  if (testSeq == 2) {
    testSeq = 3;
    sendTestStatus();
  }

  if (!running()) sendActuatorStatus(parameters[0], 0, digitalReadFast(openNest), digitalReadFast(nestIsClosed), digitalReadFast(nestIsOpen), float(weight) / 10000, load);
  // if (verbose) Serial.println("actuatenestexit");
  for (byte i = 0; i < numPar; i++)parameters[i] = 0;
}

//******************************************************
void actuateGripEnter() {
  if (penGripState == swap) {
    // if (verbose) Serial.println("SWAPPING"); //0=swap, 1=open, 2=close
    if (digitalReadFast(penGripperIsOpen) == LOW) penGripState = close; // if is open, call for closed
    else penGripState = open; //vice versa
  }
  if (penGripState == open)penGripMoveOpen();
  if (penGripState == close)penGripMoveClose();
  //  lcd.clear();
  //  lcd.print("ActuateGripper");
  //delay(1000);
  actuatorTimeout = 0;
  /*  if (verbose) {
    Serial.println("actuategrip");
    Serial.print("pengripstate = ");
    Serial.println(penGripState);
    }*/
  loadMachine.transitionTo(loadRead);
  if (!running()) balanceMachine.transitionTo(balanceRead);
  load = 0;
  //  weight=0;
}

void actuateGripUpdate() {
  if (tempTimer > messageTime && !running()) {
    sendActuatorStatus(parameters[0], 1, digitalReadFast(openPenGripper), digitalReadFast(penGripperIsClosed), digitalReadFast(penGripperIsOpen), weight, load);
    tempTimer = 0;
    loadMachine.transitionTo(loadRead);
    balanceMachine.transitionTo(balanceRead);
  }
  if ((penGripState == open && digitalReadFast(penGripperIsOpen) == LOW) || (penGripState == close && digitalReadFast(penGripperIsClosed) == LOW)) {
    if (!running()) { // maint function
      //      sendStatus(); //if gripper open valve is on and gripper is open, or closed and closed, sed stus and transition
      mainStateMachine.transitionTo(mainNoOp);
    }
    else {
      nextState();
    }
  }
  else if (actuatorTimeout > cylMove) {
    errorState = 11;//
    sendError(errorState, 1);
    mainRunState = 0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("5");
    }// if not currently running abort procedure, start it now
    if (!running())mainStateMachine.transitionTo(mainNoOp);
    nextState();
  }
}

void actuateGripExit() {
  if (!running()) sendActuatorStatus(parameters[0], 0, digitalReadFast(openPenGripper), digitalReadFast(penGripperIsClosed), digitalReadFast(penGripperIsOpen), float(weight) / 10000, load);
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
  //  if (!running()) sendStatus();
}

//******************************************************
void actuateStopEnter() {
  if (digitalReadFast(stopIsOut) == LOW) {
    stopMoveBack(); // if is out, call for back
    Serial.println("move back");
  }
  else {
    stopMoveOut(); //vice versa
    Serial.println("move out");
  }
  actuatorTimeout = 0;
  loadMachine.transitionTo(loadRead);
  if (!running()) balanceMachine.transitionTo(balanceRead);
  load = 0;
  //  weight=0;
}

void actuateStopUpdate() {
  if (tempTimer > messageTime && !running()) {
    sendActuatorStatus(parameters[0], 1, digitalReadFast(moveStopOut), digitalReadFast(stopIsOut), digitalReadFast(stopIsBack), float(weight) / 10000, load);
    tempTimer = 0;
    loadMachine.transitionTo(loadRead);
    balanceMachine.transitionTo(balanceRead);
  }
  if ((digitalReadFast(moveStopOut) == HIGH && digitalReadFast(stopIsOut) == LOW) || (digitalReadFast(moveStopBack) == HIGH && digitalReadFast(stopIsBack) == LOW)) { // stop motion is complete
    mainStateMachine.transitionTo(mainNoOp);
    //    if (!running()) sendStatus();
  }
  else if (actuatorTimeout > cylMove) {
    errorState = 14;//
    sendError(errorState, 1);
    stopMoveBack();
    mainRunState = 0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("6");
    }
    if (!running())mainStateMachine.transitionTo(mainNoOp);
    nextState();
  }
}

void actuateStopExit() {
  if (!running()) sendActuatorStatus(parameters[0], 0, digitalReadFast(moveStopOut), digitalReadFast(stopIsOut), digitalReadFast(stopIsBack), float(weight) / 10000, load);
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
  //  if (!running()) sendStatus();
}

//******************************************************
void actuateColletEnter() {
  if (colletState == swap) {
    if (digitalReadFast(closeCollet) == HIGH) {
      colletState = open; //if is closed, call for open
      // if (verbose) Serial.println("opening");
    }
    else {
      colletState = close; //vice versa
      // if (verbose) Serial.println("closing");
    }
  }
  if (colletState == open)colletMoveOpen();
  if (colletState == close)colletMoveClose();
  moveEnd = myMillis() + cylMove;
  //lcd.clear();
  //lcd.print("ActuateCollet");
  //delay(1000);
  actuatorTimeout = 0;
  // if (verbose) Serial.println("actuatecollet");
  load = 0;
  //  weight=0;
  loadMachine.transitionTo(loadRead);
  if (!running()) balanceMachine.transitionTo(balanceRead);
}

void actuateColletUpdate() {
  if (tempTimer > messageTime && !running()) {
    sendActuatorStatus(parameters[0], 1, digitalReadFast(openCollet), 0, 0, float(weight) / 10000, load);
    tempTimer = 0;
    loadMachine.transitionTo(loadRead);
    balanceMachine.transitionTo(balanceRead);
  }
  if (actuatorTimeout > 500) {
    if (!running()) {
      //      sendStatus(); //if gripper open valve is on and gripper is open, or closed and closed, sed stus and transition
      mainStateMachine.transitionTo(mainNoOp);
    }
    else nextState();
  }
}

void actuateColletExit() {
  if (!running()) sendActuatorStatus(parameters[0], 0, digitalReadFast(openCollet), colletState, !colletState, float(weight) / 10000, load);
  //  for (byte k =0;k<numPar;k++) parameters[k]=0; // zero all parameters
  //  if (!running()) sendStatus();
}

//******************************************************
void headMoveVerEnter() { // NEEDS CHECK FOR HOMED FIRST ?
  if (verbose) Serial.println("headMoveVer");
  //lcd.clear();
  //lcd.print("HeadmoveVer");
  stepperIsActive = true;
  stepper1.setMaxSpeed(travelSpeed); // set to travel speed to cover most of distance quickly
  stepper1.moveTo(-headPos);
  //  loadMachine.transitionTo(loadRead);
  //  balanceMachine.transitionTo(balanceRead);
}

void headMoveVerUpdate() {
  if (stepper1.distanceToGo() == 0 && !restart && !abortStop) {
    if (running()) nextState();
    else mainStateMachine.transitionTo(mainNoOp);
  }
}

void headMoveVerExit() {
  if (!running() && headPos > upPos) sendHeadStatus(parameters[0], 1, 0, digitalReadFast(stepperUpLimit), digitalReadFast(stepperDownLimit), float(weight) / 10000, load);
  else if (!running() && headPos <= upPos) sendHeadStatus(parameters[0], 1, 0, 1, digitalReadFast(stepperDownLimit), float(weight) / 10000, load);
  stepperIsActive = false;
  for (byte i = 0; i < numPar; i++)parameters[i] = 0;
  //  memset(parameters,0,sizeof(parameters)/sizeof(int)); // zero all parameters
}

//******************************************************
void headMoveHorEnter() {
  horState = 0;
  actuatorTimeout = 0;
  if (running()) {
    parameters[0] = horPos;
  }
  //  Serial.print("par=");
  //  Serial.println(parameters[0]);
  switch (parameters[0]) {
    case 0: // no parameter - stay put and request status update only
      //    if (verbose) Serial.println("check");
      //lcd.clear();
      //lcd.print("Check");
      if (digitalReadFast(carriageAtTest) == LOW) parameters[0] = test;
      else if (digitalReadFast(carriageAtDiscard) == LOW) parameters[0] = discard;
      else if (digitalReadFast(carriageAtReject) == LOW) parameters[0] = reject;
      horState = 99;
      break;
    case 1: // move to test position
      //    if (verbose) Serial.println("test");
      //lcd.clear();
      //lcd.print("Test");
      if (digitalReadFast(carriageAtTest) == LOW) { // if already at test
        horState = 99; // move complete
        //       if (verbose) Serial.println("AT TEST");
      }
      else if (digitalReadFast(carriageAtReject) == LOW) { // if at reject, need to simply move to test
        horState = 10;
        //       if (verbose) Serial.println("AT REJECT");
      }
      else { // anywhere else need to check stop is back, and move to test
        horState = 20;
        //       if (verbose) Serial.println("AT DISCARD");
      }
      break;
    case 2: // move to discard position
      // if (verbose) Serial.println("discard");
      //lcd.clear();
      //lcd.print("Discard");
      if (digitalReadFast(carriageAtReject) == LOW) { // if at reject, move left until off sensor, retract stop and move to discard
        horState = 40;
        //       if (verbose) Serial.println("AT REJECT");
      }
      else if (digitalReadFast(carriageAtDiscard) == LOW) { // if already at discard
        // if (verbose) Serial.println("AT DISCARD");
        horState = 99;
      }
      else { // anywhere else, check stop is back and move to discard
        horState = 30;
        //       if (verbose) Serial.println("AT TEST");
      }
      break;
    case 3: // move to reject position
      //     if (verbose) Serial.println("reject");
      //lcd.clear();
      //lcd.print("Reject");
      if (digitalReadFast(carriageAtDiscard) == LOW) { // if at test, check stop is out and move toward discard
        // if (verbose) Serial.println("AT DISCARD");
        horState = 60;
      }
      else if (digitalReadFast(carriageAtReject) == LOW) { // if already at reject
        horState = 99;
        //       if (verbose) Serial.println("AT REJECT");
      }
      else { // anywhere else, check stop back, move left to test, check stop out, move toward discard
        horState = 50;
        //       if (verbose) Serial.println("AT TEST");
      }
      break;
  }
  //   if (verbose) Serial.println("headmovehor");
  //   if (verbose) Serial.print("horState= ");
  //   if (verbose) Serial.println(horState);
  if (headPos < upPos) {
    horState = 99;
    mainRunState = 0;
    if (!abortRunState) {
      errorState = 13;
      errorActive = 1;
      sendError(errorState, errorActive);
      errorActive = 0;
      abortRunState = 1;
      Serial.println("7");
      nextState();
    }
    //Serial.println("Can't go sideways");
    loadMachine.transitionTo(loadRead);
    if (!running()) balanceMachine.transitionTo(balanceRead);
  }
}

void headMoveHorUpdate() {
  if (tempTimer > messageTime && !running()) {
    sendCarriageStatus(parameters[0], 1, digitalReadFast(moveCarriageToTest), digitalReadFast(carriageAtTest), digitalReadFast(carriageAtDiscard), digitalReadFast(carriageAtReject), float(weight) / 10000, load);
    tempTimer = 0;
    loadMachine.transitionTo(loadRead);
    balanceMachine.transitionTo(balanceRead);
  }
  //  if (verbose) Serial.println("headmoveupdate");
  //  if (verbose) Serial.print("horState= ");
  //  if (verbose) Serial.println(horState);
  switch (horState) {
    case 0:
      {
        horState = 99;
        break;
      }
    case 10:
      { //move toward test
        headMoveTowardTest();
        horState = 11;
        break;
      }
    case 11:
      { // wait for move to test complete
        if (digitalReadFast(carriageAtTest) == LOW) horState = 99;
        break;
      }
    case 20:
      { // move from discard to test, stop back first
        // if (verbose) Serial.println("case 20");
        stopMoveBack();
        //lcd.setCursor(0,1);
        //lcd.print("stop back       ");
        horState = 21;
        break;
      }
    case 21:
      { // when stop is back, move to test
        if (digitalReadFast(stopIsBack) == LOW) horState = 10;
        break;
      }
    case 30:
      { //move test to discard, start by moving stop back
        stopMoveBack();
        //lcd.setCursor(0,1);
        //lcd.print("stop back       ");
        horState = 31;
        break;
      }
    case 31:
      { //check stop move finished
        if (digitalReadFast(stopIsBack) == LOW) horState = 32;
        break;
      }
    case 32:
      { // move carriage to discard
        headMoveTowardDiscard();
        //lcd.setCursor(0,1);
        //lcd.print("head to discard       ");
        horState = 33;
        break;
      }
    case 33:
      { // wait for move complete
        if (digitalReadFast(carriageAtDiscard) == LOW) horState = 99;
        break;
      }
    case 40:
      { // if at reject, move towards test until off sensor, retract stop and move to discard
        headMoveTowardTest();
        //lcd.setCursor(0,1);
        //lcd.print("head to test        ");
        horState = 41;
        break;
      }
    case 41:
      { //check for off reject sensor
        if (digitalReadFast(carriageAtReject) == HIGH) horState = 30;
        break;
      }
    case 50:
      { // if at test, check stop is out and move to reject
        stopMoveOut();
        //lcd.setCursor(0,1);
        //lcd.print("stop out         ");
        horState = 51;
        break;
      }
    case 51:
      { // wait until stop is out
        if (digitalReadFast(stopIsOut) == LOW) horState = 52;
        break;
      }
    case 52:
      { // move carriage towards discard
        headMoveTowardDiscard();
        //lcd.setCursor(0,1);
        //lcd.print("head to discard");
        horState = 53;
        break;
      }
    case 53:
      { // wait until at reject
        if (digitalReadFast(carriageAtReject) == LOW) horState = 99;
        break;
      }
    case 60:
      { // if at discard, check stop back, move left to test, check stop out, move toward discard
        stopMoveBack();
        //lcd.setCursor(0,1);
        //lcd.print("stop back         ");
        horState = 61;
        break;
      }
    case 61:
      { // wait until stop is back
        if (digitalReadFast(stopIsBack) == LOW) horState = 62;
        break;
      }
    case 62:
      { //move to test
        headMoveTowardTest();
        //lcd.setCursor(0,1);
        //lcd.print("head to test     ");
        horState = 63;
        break;
      }
    case 63:
      {
        if (digitalReadFast(carriageAtTest) == LOW) horState = 50;
        break;
      }
    case 99:
      { // return as required
        if (running())nextState(); //running, not maint
        else mainStateMachine.transitionTo(mainNoOp);
        break;
      }
  }
  if (actuatorTimeout > cylMove) {
    if (startRunState) {
      errorState = 8; // no air pressure is likely cause
      Serial.println("air fail");
      errorRestart = 1; //indicates that on error correction the system should begin the start sequence again
      mainStateMachine.transitionTo(mainNoOp);
    }
    else {
      errorState = 13;
      Serial.println("clamp fail");
      if (verbose) Serial.println("horiz failed");
      mainRunState = 0;
      if (!abortRunState) {
        abortRunState = 1;
        Serial.println("8");
      }// if not currently running abort procedure, start it now
      nextState();
    }
    errorActive = 1;
    sendError(errorState, errorActive);
    //    mainStateMachine.transitionTo(mainNoOp); // check for cylinder move timeout and return to noOp
  }
  //  if (verbose) Serial.print("case = ");
  //  if (verbose) Serial.println(horState);
}

void headMoveHorExit() {
  if (!running()) {
    //    Serial.print("*p");
    //    Serial.println(parameters[0]);
    sendCarriageStatus(parameters[0], 0, digitalReadFast(moveCarriageToTest), digitalReadFast(carriageAtTest), digitalReadFast(carriageAtDiscard), digitalReadFast(carriageAtReject), float(weight) / 10000, load);
  }
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
  if (verbose) Serial.println("head move hor exit");
}

//********************************************                                                                                                                                                                                                    ew**********
void tareEnter() { //
  //Balance stuff

  Serial2.println("IP"); // kills any continuous print that might be happening to stop data flow
  delay(50); // small pause to allow reading to arrive
  while (Serial2.available()) Serial2.read(); //empty buffer of rubbish
  Serial2.println('T'); // send tare command

  // Load cell stuff
  Serial3.write(0x13); // XOFF kills any continuous print that might be happening to stop data flow
  delay(50);
  while (Serial3.available()) Serial3.read(); //empty buffer of rubbish
  Serial3.println("ZA0"); // send tare off command


  commsEnd = myMillis() + (tareTime);
  loadError = false;
  balanceError = false; // reset error flag
  balanceState = 1;
  loadState = 1;
  if (testSeq > 5) {
    testSeq = 7; //running, not maint mode
    sendTestStatus();
  }
  //lcd.clear();
  //lcd.print("Tare");
  if (verbose) Serial.println("tare");
  tareTimeout = 0;
}

void tareUpdate() {
  if (balanceState == 1 && Serial2.available() >= 3) { // state 1 is waiting for OK to return on command sent
    //    if (verbose) Serial.println("balancestate 1");
    char c = ' ';
    while (c != 'O' && Serial2.available()) {
      c = Serial2.read();
      //      if (verbose) Serial.print("char ");
      //      if (verbose) Serial.println(c);
    }
    if (c != 'O') balanceError = true; //anything other than OK! from balance is error, no data = -1, OR timeout fail
    else balanceState = 2; // move on to check for progress
  }
  else if (balanceState == 2) { // state 2 is send print on stable command whch waits for tare completion
    //    if (verbose) Serial.println("balancestate 2");
    Serial2.println("P");
    balanceState = 3;
  }
  else if (balanceState == 3) { // state 3 is waiting for result returned
    //    if (verbose) Serial.println("balancestate 3");
    if (Serial2.available() >= 8) { // more than 8 data bits indicates a returned reading and successful tare
      while (Serial2.available()) Serial2.read(); //empty buffer of rubbish
      balanceState = 4;
      //      if (verbose) Serial.println("balancestate 4");
    }
    /*  else {
      balanceError = true; // indicate timeout
      if (verbose) Serial.println("balanceerror");
      }
    */
  }
  if (loadState == 1 && Serial3.available() > 1) {
    // if (verbose) Serial.println("loadstate =1");
    char c;
    if (verbose) Serial.println(c);
    while (Serial3.available() && c != '*') {
      c = Serial3.read();
    }
    if ( c != '*' /*|| (long)(myMillis() - commsEnd) >=0*/) {
      loadError = true; //anything other than * is wrong
      if (verbose) Serial.println("loadError");
    }
    else {
      while (Serial3.available()) Serial3.read(); //empty out rubbish
      Serial3.println("ZA1"); // send tare on command
      loadState = 2;
      if (verbose) Serial.println("LOAD untared");
    }
  }
  else if (loadState == 2 && Serial3.available() > 0) {
    // if (verbose) Serial.println("loadstate =2");
    if (Serial3.read() != '*' /*|| (long)(myMillis() - commsEnd) >=0*/) {
      loadError = true; //anything other than
      if (verbose) Serial.println("loadError");
    }
    else {
      while (Serial3.available()) Serial3.read(); //empty out rubbish
      loadState = 4;
      if (verbose) Serial.println("LOAD tared");
    }
  }
  if (balanceState == 4 && loadState == 4) { // satisfactory taring
    if (running()) {
      if (testSeq > 5) {
        testSeq = 9; // taring succeeded
        sendTestStatus();
      }
      nextState();
    }
    else mainStateMachine.transitionTo(mainNoOp);
  }

  if ((tareTimeout > tareTime) || balanceError || loadError) {
    if (balanceError) Serial.println("balanceErrror");
    if (loadError) Serial.println("loadError");
    if (tareTimeout > tareTime) {
      Serial.print("tareTimeout = ");
      Serial.println(tareTimeout);
    }
    if (testSeq > 5) {
      testSeq = 8; // taring failed
      sendTestStatus();
    }
    mainStateMachine.transitionTo(tareFail);
  }
}

void tareExit() {
  while (Serial2.available())Serial2.read();// dump rubbish from buffer
  while (Serial3.available())Serial3.read();
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
}

//****************************************
void tareFailEnter() {
  //lcd.clear();
  //lcd.print("TareFail");
  //delay(1000);
  command = '0';
  //  Serial.println("tarefail");
}

void tareFailUpdate() {
  /*  readIncoming();
    if (endComm && (command == 'R')){
    mainStateMachine.transitionTo(tare);
    }
    else{ // abort
    mainRunState=0; // cancel main run
    if (!abortRunState) abortRunState=1; // if not currently running abort procedure, start it now
    nextState();
    }*/
  nextState();
}

void tareFailExit() {
}
//******************************************************
void startTestEnter() {
  errorState = 0;
  readNum = 0; // reset sequence number of reading
  //  mainRunState=0; // reset running state, just in case
  pass = false; // indicate device is a fail
  if (configured == true) {
    testSeq = 1;
    dispenseStarted = false;
    testStatus = 'A'; // no stream yet
    sendTestStatus();
    readNum = 1; // start new set of readings
    testStart = myMillis(); // log start time
    nomEnd = false;
    load = 0; // reset load
    weight = 0; // reset weight
    prevWeight = weight;
    balanceReceivedMessage = 0;
    for (byte i = 0; i < numBalanceReadings; i++)balanceReadings[i] = 0;
    averageWeight = 0;
    //    calcWeight=0;
    previousAvWt = 0;
    dispenseEnd = 0;
    timeStart = 0;
    timeEnd = 0;
    rejectCap = false;
    needleMeasure = false;
    triggerInProgress = false;
    touchedCap = false;
    priorityStatus = false;
  }
  else {
    mainStateMachine.transitionTo(mainNoOp);
    errorState = 4;
    sendError(errorState, 1);
  }
  //  messageMachine.transitionTo(messageSend); // start sending out messages
  //lcd.clear();
  //lcd.print("StartTest");
  //delay(1000);
  if (verbose) Serial.println("starttest");
}

void startTestUpdate() {
  if (digitalReadFast(penIsPresent) == LOW) { // pen in nest
    if (digitalReadFast(containerIsPresent) == LOW /*&& digitalReadFast(scrapIsPresent)==LOW*/) { // container and scrap present, waiting to start
      testSeq = 1;
      sendTestStatus();
      //      mainRunState=1; //set ready for first test state
      nextState(); // call first test state
    }
    else {
      mainStateMachine.transitionTo(mainNoOp);
      errorState = 6;
      sendError(errorState, 1);
      mainRunState = 0; // cancel main run
      if (!abortRunState) {
        abortRunState = 1;
        Serial.println("9");
      }// if not currently running abort procedure, start it now
      nextState();
    }
  }
  else { // no pen yet - will stay in this state until a pen is inserted - should it listen for an abort ?
    testSeq = 0; // waiting to start, pen in nest
    sendTestStatus();
  }
}

void startTestExit() {
  testSeq = 2;
  sendTestStatus();
  for (byte k = 0; k < numPar; k++) parameters[k] = 0; // zero all parameters
}

//******************************************************
void waitForSafetyUpdate() {
  if (digitalReadFast(lightGuardIsOk) == LOW) { // does this wait for safety rest need timeout ?
    nextState();
    testSeq = 1; // step = clamping
    if (running()) sendStatus();
  }
}

//************************************************************

void lowerToCapEnter() {
  stepperIsActive = true;
  stepper1.setMaxSpeed(testSpeed);
  stepper1.moveTo(-headPos);
  loadMachine.transitionTo(loadRead);
  //  newLoadAvail =true;
  loadNoOpState = true; // indicates that load machine is in noOp state
  load = 0; // double check that load is zeroed out before starting
  averageLoad = 0;
  for (byte i = 0; i < numLoadReadings; i++)loadReadings[i] = 0;
  touchedCap = false;
}

void lowerToCapUpdate() {
  if (newLoadAvail && errorState != 16 && loadNoOpState) { // keep on getting new load info if load already reported - read as quickly as possible
    newLoadAvail = false;
    loadMachine.transitionTo(loadRead);
  }
  if (errorState == 16) {
    mainRunState = 0; // stop main run state
    sendError(16, 1);
    errorState = 0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("10");
    }
    nextState();
  }

  if (touchedCap) {
    stepper1.stop();
    loadMachine.transitionTo(loadNoOp);
    delay(10);
    if (verbose)Serial.print("touched cap");
    nextState();
  }
  /*  else if (a==10) {// end of move*/
  else if (stepper1.currentPosition() == -headPos) { // end of movement reached
    //    Serial.println("failed lower find cap");
    mainRunState = 0; // stop main run state
    errorState = 17;
    errorActive = 1;
    sendError(errorState, errorActive);
    sysTimeoutEnd += 10000; // add ten seconds to timer to accommodate longer pull
    //    errorState=0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("11");
    }
    nextState();
  }
}

void lowerToCapExit() {
  testSeq = 4; // start of cap removal
  if (mainRunState > 0) sendTestStatus();
  stepperIsActive = false;
}

//******************************************************
void verifyReleaseEnter() {
  //  Serial.println("vr");
  stepperIsActive = true;
  stepper1.setMaxSpeed(testSpeed);
  stepper1.moveTo(-headPos);
  loadMachine.transitionTo(loadRead);
  newLoadAvail = false;

  for (byte i = 0; i < numLoadReadings; i++)loadReadings[i] = 0;
  touchDown = false;
}

void verifyReleaseUpdate() {
  if (newLoadAvail && errorState != 16 && loadNoOpState) { // keep on getting new load info if load already reported - read as quickly as possible
    newLoadAvail = false;
    loadMachine.transitionTo(loadRead);
  }

  if (touchDown || (load < touchCapLoad)) { //if touched down or already pushing down onto cap xxx
    stepper1.stop();
    loadMachine.transitionTo(loadNoOp);
    delay(10);
    if (verbose)Serial.print("touched cap");
    nextState(); // only skip on to next state if cancel is true, otherwise just put it down.
  }
}

void verifyReleaseExit() {
  stepperIsActive = false;
}

//******************************************************
void smallMoveUpEnter() {
  // if (verbose) Serial.println("smallmoveup");
  stepperIsActive = true;
  headPos = int(((capRemoveDist * 10) * conversion) / 10); // multiply and divide by 10 to accomodate tenths of mm
  stepper1.setMaxSpeed(travelSpeed);
  stepper1.move(headPos);
}

void smallMoveUpUpdate() {
  if (stepper1.distanceToGo() == 0 && !restart && !abortStop) nextState();
  /*  if (a==99){
    errorState =5;
    sendError(errorState,1);//stepper Error
    //lcd.clear();
    //lcd.print("stepper error");
    if (verbose) Serial.println("stepper error");
    mainRunState=0; // stop main run state
    if (!abortRunState) abortRunState=1;
    nextState();
    }*/
}
void smallMoveUpExit() {
  testSeq = 4;
  if (mainRunState > 0) sendTestStatus();
}

//******************************************************
void removeCapEnter() {
  stepperIsActive = true;
  stepper1.setMaxSpeed(testSpeed);
  stepper1.moveTo(-headPos);
  newLoadAvail = true;
  averageLoad = 0;
  loadTotal = 0;
  loadIndex = 0;
  for (byte i = 0; i < numLoadReadings; i++)loadReadings[i] = 0;
  load = 0; // double check that load is zeroed out before starting
  capRemoved = false; //reset cap removed flag
  removalInProgress = false;
  finishedCount = 0; // reset finished counter as a double check - should be reset in loadread when count is finished
}

void removeCapUpdate() {
  if (newLoadAvail && errorState != 16 && loadNoOpState/* && messageTimeElapsed > messageInterval/2*/) { // keep on getting new load info if load already reported - read as quickly as possible
    newLoadAvail = false;
    loadMachine.transitionTo(loadRead);
    sendTestStatus();
    //    messageTimeElapsed-=messageInterval;
  }
  if (errorState == 16) {
    mainRunState = 0; // stop main run state
    sendError(16, 1);
    errorState = 0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("12");
    }
    nextState();
  }
  if (load > maxLoad || -load > maxLoad) {
    stepper1.stop();
    Serial.println("maxload exceeded");
    loadMachine.transitionTo(loadNoOp);
    mainStateMachine.transitionTo(mainNoOp);
  }
  if (capRemoved || (stepper1.distanceToGo() == 0 && !abortStop)) {
    if (capRemoved) Serial.println("Cap Rem");
    else Serial.println("excess movement");
    stepper1.stop();
    loadMachine.transitionTo(loadNoOp);
    testSeq = 5;
    sendTestStatus();
    delay(10);
    nextState();
  }
}

void removeCapExit() {
  testSeq = 6; // cap removal stroke completed
  sendTestStatus();
  stepperIsActive = false;
  removalInProgress = false;
}

//******************************************************
void homeStepperStateEnter() { //
  stepperIsActive = true;
  stepperTimeout = 0;
  stepperState = 1;
  homing = true;
  //  homed=false;
  //restart = false;
  Serial.println("homing enter");
}

void homeStepperStateUpdate() {
  if (homed) {
    stepperState = 6;
    if (serialTime > 500) {
      serialTime = 0;
      Serial.println("already homed");
    }
  }
  switch (stepperState) {
    case -1: // error state
      if (verbose)Serial.println("homing error");
      //NEED ABORT HERE
      stepperState = 1; // used to be zero, but that probably caused hang
      break;
    case 1: // stepperState = 1, determine necessary move and initiate
      if (serialTime > 500) {
        serialTime = 0;
        Serial.println("case ss=1");
      }
      stepper1.setMaxSpeed(travelSpeed); // set to travel speed to cover most of distance quickly
      if (digitalReadFast(stepperUpLimit) == HIGH) { //check for already on upper limit
        Serial.println("upperlimit");
        stepper1.move(-1 * conversion);
        if (verbose)Serial.println("small move down");
        while (stepper1.distanceToGo() != 0 /*&& !restart /*&& !abortStop*/) {
          stepper1.run();
          delay(1);
          if (serialTime > 500) {
            serialTime = 0;
            Serial.println("moving");
          }
        };
        //stepperState=2;
      }
      else {
        Serial.println("standard home");
        stepper1.moveTo(fullStroke * conversion); // initiate movement for full stroke upwards
        if (lightGuardStatus == LOW) {
          stepperState = 3; // dont move on unless light guard is clear/safety OK
          if (errorState == 22 && errorActive){
            errorActive = false;
            sendError(errorState, errorActive);
          }
        }
        else {
          if (lightGuardSent == false) {
            errorState = 22;
            errorActive = true;
            sendError(errorState, errorActive);
            lightGuardSent=true;
          }
        }
      }
      break;
    /*  case 2: // stepperState = 2, wait for small downward move to get off limit sw, and then initiate short down move
      if (digitalReadFast(stepperUpLimit==LOW)) {
      if (verbose)Serial.println("off limit");
      stepper1.stop();
      stepper1.setCurrentPosition(0);
      stepperState=4;
      stepper1.moveTo(-200); // small move down
      }
      else if (serialTime>500) {serialTime=0; Serial.println("case ss=2");}
      break;*/
    case 3: // stepperState = 3, wait for up movement to reach limit, and then initiaite a small move down
      if (stepper1.distanceToGo() == 0 && !restart && !abortStop) {
        stepperState = -1; // end of movement reached before up limt triggered
        Serial.println("home fail");
      }
      if (digitalReadFast(stepperUpLimit) == HIGH) { // upper limit signal triggered
        stepper1.stop();
        stepper1.setCurrentPosition(0);
        stepper1.moveTo(-250); //small move downwards
        stepperState++; // upper limit reached, making down movement, now need to wait
        Serial.println("Limit reached");
      }
      else if (serialTime > 500) {
        serialTime = 0;
        Serial.println("case ss=3");
      }
      break;
    case 4:
      if (stepper1.distanceToGo() == 0 && !abortStop) { // abort is dealt with elsewhere
        if (verbose)Serial.println("distance reached");
        stepper1.setMaxSpeed(homeSpeed); // set to home speed to provide accuracy
        stepper1.moveTo(250); //small move up
        stepperState++;
      }
      else if (serialTime > 500) {
        serialTime = 0;
        Serial.println("case ss=4");
      }
      break;
    case 5: // stepperState = 5, wait until back up slowly
      if (digitalReadFast(stepperUpLimit) == HIGH) { // upper limit signal triggered
        stepper1.stop();
        if (verbose)Serial.println("limit reached");
        if (verbose)Serial.println("moving down 2mm");
        stepper1.setCurrentPosition(0);
        stepper1.setMaxSpeed(travelSpeed); // return to speed used before homing
        stepper1.moveTo(-2 * conversion); // small movement down to get off limit sensor
        stepperState ++;
      }
      else if (serialTime > 500) {
        serialTime = 0;
        Serial.println("case ss=5");
      }
      break;
    case 6:
      if (stepper1.distanceToGo() == 0 /*&& !abortStop*/) {
        Serial.println("finished");
        headPos = upPos * conversion; // reset to up just to make sure
        //      if (restart && verifyRestart) nextState(); else {stepperState=1; Serial.println("restart home");}
        nextState();
        stepperIsActive = false;
        stepperState = 0; // no op state
        homing = false;
      }
      else if (serialTime > 500) {
        serialTime = 0;
        Serial.println("case ss=6");
      }
      break;
  }
}

void homeStepperStateExit() {
  stepperIsActive = false;
  homing = false;
  homed = true;
  // if (verbose) Serial.println("home stepper exit");
}
//*************************************************************************************

// ready : enter from preparefortrigger, exit to timing (timing transition triggered in ISR)
void readyEnter() {
  headPos = downPos * conversion;
  stepperIsActive = true;
  stepper1.setMaxSpeed(testSpeed);
  stepper1.moveTo(-headPos);
  timerTrigger = true; // timerTrigger flag indicates status of timing, high = ready for timing
  gated = false; // indication that timer has not been held
  //  newLoadAvail =true;
  normal = true; // indicates normal run, false = retry after false trigger
  averageLoad = 0;
  loadTotal = 0;
  loadIndex = 0;
  loadMachine.transitionTo(loadRead);
  //  loadNoOpState=true; // indicates that load machine is in noOp state
  load = 0; // double check that load is zeroed out before starting
  //  weight=0;
  testSeq = 10;
  sendTestStatus();
  timeoutEnd = false;
  triggered = false;
  nomEnd = false;
  triggerInProgress = false;
  digitalWriteFast(resetTimer, LOW);
  dispenseStarted = false;
  dispenseFinished = false;
}

void readyUpdate() { // wait for transition to timing - triggered in ISR by stream sensor
  if (loadNoOpState && testStatus != 'Z') { // keep on getting new load info if waiting for trigger - read as quickly as possible.
    //Stop reading when triggered and waiting for stream start to prevent race condition with maxtimer producing zeros
    newLoadAvail = false;
    loadMachine.transitionTo(loadRead);
    sendTestStatus(); // this sends repeatedly if in teststatus z, waiting for trigger
  }
  /*  if (stepper1.distanceToGo()==0 && !triggered) {//Shouldn't get to end of move without trigger, but distance to go is also zero on 'stop'
    testStatus='N';
    sendTestStatus();
    mainRunState=40; // stop main run state
    nextState();
    }*/

  if (triggered && (myMillis() - timeTrigger > 100)) { // if triggered and still in ready, waiting for stream start 100ms after triggering
    if (long(abs(milliLoad)) > peakLoad * retryPercent / 100L) { //use absolute value to avoid faffing with signs
      //Things to do if load has not fallen back to less than retry percent. If it has then trigger was good, and carry on waiting for stream.
      triggered = false; // reset triggered flag
      timeTrigger = 0; // re-zero triggered time stamp
      normal = false; // used to skip maxtimerexit state contents
      timeoutTimer.transitionTo(maxTimerNoOp); // kill max timer to reset 15s timer. (normal = false) prevents maxtimerexit actions
      //      mainStateMachine.transitionTo(retryReady); // bounce out and back to come back to
      stepper1.moveTo(-headPos); // restart stepper with same setup as before
      Serial.println("retry triggering");
    }
  }

  if (timeoutEnd) nextState(); // jump out if maxtimer timed out
}

void readyExit() { // exit triggered by ISR
  if (normal) {
    if (!abortRunState) {
      stepper1.stop(); // do not want to stop if abort is active, as this cancels the home
      stepperIsActive = false;
      testSeq = 11;
    }
  }
  stepper1.stop();

  timerTrigger = false;
}

//*************************************************************************************

// retryReady : called if false trigger detected, so ready activities can be restarted

void retryReadyUpdate() {
  mainStateMachine.transitionTo(ready);
}

//*************************************************************************************

// timing : enter from ready, exit to wait for dispense end - could be triggered by nominal timer state machine
void timingEnter() {
  digitalWriteFast(startTimer, HIGH) // just in case ISR didn't work
  testStatus = 'B'; // stream sensed
  nominalTimer.transitionTo(nomTimer); // start nominal check timer
  timeoutTimer.transitionTo(maxTimer); // start timeout check timer if not already started by trigger
  startEnd = myMillis() + startPulse;
  deBounceEnd = myMillis() + deBounceTime;
  boolean startTimerOnce = false;
  //balanceMachine.transitionTo(balanceRead);// now in max timer state
  load = 0; // zero out load, as only weight important now.
}

void timingUpdate() {
  if (((long)(myMillis() - startEnd) >= 0) && (startTimerOnce == false)) { // check for timing of end of start pulse
    digitalWriteFast(startTimer, LOW); // end of start pulse for omron timer unit
    startTimerOnce = true; // make sure timer is only started once !
  }
  if ((long)(myMillis() - deBounceEnd) >= 0) { // wait for debounce of input - is this a good thing ?
    deBounce = true;
  }
  //sit and wait in this bit until timing is done - state change is initiated in ISR

  //  NEED A CHECK FOR LIGHT GUARD BROKEN ?

  if (digitalReadFast(3) == HIGH) { // light guard broken or lower door opened
    errorState = 20;
    errorActive = 1;
    sendError(errorState, errorActive);
    //    errorState=0;
    mainRunState = 0;
    if (!abortRunState) {
      abortRunState = 1;
      Serial.println("1");
    }// if not currently running abort procedure, start it now
    nextState();
    //  mainStateMachine.transitionTo(error)
  }
  if (digitalReadFast(2) == HIGH && deBounce == true) { // double check on steam sensor in case interrput doesn't catch falling edge
    if (timeEnd == 0) {
      timeEnd = myMillis();
      digitalWriteFast(gateTimer, HIGH); // turn on gate to hold reading
    }
    nextState();
  }
  /*  if (errorState == 15){ // abort due to balance error ? Should this just continue ?
    mainRunState=0; // stop main run state
    sendError(15,1);
    if (!abortRunState) abortRunState=1;
    nextState();
    }*/
}

void timingExit() {
  deBounce = false;
  if (testStatus == 'B' || testStatus == 'Z' || testStatus == 'J' ) {
    testStatus = 'C'; // stream complete
    Serial.println("stat c");
    priorityStatus = true; // make sure this gets sent and not overwritten
  }
  sendTestStatus(); // Removed to eliminate 'kink' in graph.
  gated = true;
  Serial.println("gated");
  digitalWriteFast(gateTimer, HIGH); // set gate for omron timer to hold reading - should already be set in ISR
  retries = 0; // reset comms retries to zero
}

//******************************************************
void waitForDispenseEndEnter() {
  //  Serial.println("waitfordispenseend");
  balanceMachine.transitionTo(balanceRead);
}

void waitForDispenseEndUpdate() { // transition out of here triggered in nomTimerEnd
  /*  if (newWeightAvail && errorState!=15 && balanceNoOpState){ // keep on getting new balance info
    newWeightAvail=false;
    balanceMachine.transitionTo(balanceRead);
    sendTestStatus();
    }
    else if (errorState==15){
    balanceMachine.transitionTo(balanceRead);
    errorState=0;
    }*/
}

void waitForDispenseEndExit() {
  mainRunState++; // increment run state pointer
  needleMeasure = false;
}

//*************************************************************************************

void gateEnter() { // read out timer value for passing to PC.
  //  Serial.println("gate enter");
  commsFailed = false;
  digitalWriteFast(startTimer, LOW);
  while (Serial1.available()) scrap = Serial1.read(); // empty serial buffer
  for (byte i = 0; i < timerMessageLength; i++) timerBuffer[i] = '0';
  //  memset(timerBuffer,0,sizeof(timerBuffer));// reset timerBuffer ready for incoming time data
  //  for (int z=0;z<messageLength;z++) buffer[z]=0;// reset buffer ready for incoming time data

  byte c;
  digitalWriteFast(RS485On, HIGH); //turn on write enable
  chksum = 0;
  for (int i = 1; i <= sizeof(timerMessage); i++) chksum ^= timerMessage[i]; // calculate rs485 message checksum
  Serial1.write(timerMessage, sizeof(timerMessage));
  //  Serial1.write(chksum);
  // wait for transmit complete
  Serial1.flush();
  //  UCSR0A=UCSR0A |(1 << TXC0);
  //  while (!(UCSR0A & (1 << UDRE0)))  // Wait for empty transmit buffer
  //  UCSR0A |= 1 << TXC0;  // mark transmission not complete
  //  while (!(UCSR0A & (1 << TXC0))) // Wait for the transmission to complete
  delayMicroseconds (uint32_t(delayMicros)); // simple method is crude, but doesn't hang
  digitalWriteFast(RS485On, LOW); //turn off write enable
  for (int i = 1; i < 5; i++) Serial1.read(); //empty out read buffer of reflected characters
  commsEnd = myMillis() + (commsTime);

  //  Read timer value

  while (Serial1.available() <= 5) { // wait for a good chunk of data to be available
    if ((long)(myMillis() - commsEnd) >= 0) { // jump out of waiting loop if insufficient data received in time - should comms retry ?
      commsFailed = true;
      failWhy = 1;
      break;
    }
  }
  /*  int z;
    while( z <5){ // attempt to remove rubbish and first start character to remove reflected transmitted message
    if (Serial1.available()){
    c = Serial1.read();
    z++;
    }
    }*/

  if (commsFailed == false) {
    do { // loop for start character
      if (Serial1.available()) {
        c = Serial1.read();
      }
      if ((long)(myMillis() - commsEnd) >= 0) { // jump out of waiting loop if start char not received in time - should comms retry ?
        commsFailed = true;
        failWhy = 2;
        break;
      }
    }
    while (c != 0x02);
  }

  if (commsFailed == false) {
    timerReceivedMessage = 1; // reset length of message
    do {
      if ((long)(myMillis() - commsEnd) >= 0) { // jump out of loop if insufficient data received in time - should comms retry ?
        commsFailed = true;
        failWhy = 3;
        break;
      }
      if (Serial1.available()) { //if buffer has data
        c = Serial1.read();
        timerBuffer[timerReceivedMessage] = c;//Store data in an array
        timerReceivedMessage++; // variable incremented (ends up at one more than number of bytes received as includes end char byte)
      }
    }
    while (c != 0x03 && timerReceivedMessage < 50 && ((long)(myMillis() - commsEnd) <= 0)); // wait for end character or 40 characters received
  }
  if (commsFailed == false) {
    chksum2 = 0;
    chksumRead = false;
    do {
      if (Serial1.available()) { //if buffer has data
        chksum2 = Serial1.read(); // next character should be checksum
        chksumRead = true;
      }
    }
    while (chksumRead == false);

    chksumtemp = 0; // reset chksumtemp before calculation
    for (int i = 1; i <= timerReceivedMessage - 2; i++) chksumtemp ^= timerBuffer[i]; // calculate rs485 message checksum on received message, message length -2 to remove stop char and received chksum
    if (chksumtemp == chksum2 || 1) { // check for good data received - chksum not yet working, so forced out - perhaps now working - needed zeroing before use?
      timerValue = (hex2dec(timerBuffer[22]) + (hex2dec(timerBuffer[21]) * 16) + (hex2dec(timerBuffer[20]) * 256) + (hex2dec(timerBuffer[19]) * 4096));
      timerValue = (timerValue / 100);
      //      Serial.println(timerValue);
      //NOTE - timer sends value in 100ths of a second
    }
    else {
      // things to do if comms checksum fails - retry perhaps ?
      commsFailed = true;
      failWhy = 4;
    }
  }
  while (Serial1.available()) Serial1.read(); // empty serial buffer

  if ((timerValue > maxTimerValue) && (retries <= maxretries)) {
    timerValue = 0;
    mainStateMachine.immediateTransitionTo(retry);
  }
  else if ((timerValue > maxTimerValue) && (retries > maxretries)) {
    mainStateMachine.immediateTransitionTo(timerValueError);
  }
}

void gateUpdate() {
  if ((commsFailed == true) && (retries < maxretries)) { // have another comms attempt
    mainStateMachine.transitionTo(retry);
    commsFail(retries, failWhy);
  }
  else if ((commsFailed == true) && (retries >= maxretries)) { // too many comms attempts
    mainStateMachine.transitionTo(commsDead);
  }
  else mainStateMachine.transitionTo(reset);
}

void gateExit() {
  commsFailed = false;
  //  gated = false;
  digitalWriteFast(startTimer, LOW);
  digitalWriteFast(resetTimer, LOW);
  digitalWriteFast(zeroShift, HIGH); //turn zero shift signal off
  while (Serial1.available()) scrap = Serial1.read(); // empty serial buffer
}


//*************************************************************************************

void retryUpdate() {
  commsFailed = false;
  while (Serial1.available()) scrap = Serial1.read(); // empty serial buffer
  for (byte i = 0; i < timerMessageLength; i++) timerBuffer[i] = '0';
  //  memset(timerBuffer,0,sizeof(timerBuffer));// reset timerBuffer ready for incoming time data
  mainStateMachine.transitionTo(gate);
  retries += 1;
}

//*************************************************************************************

void timerValueErrorUpdate() {

  errorState = 7;
  errorActive = 1;
  sendError(errorState, errorActive); //ERROR in TIMER VALUE
  //  errorState=0;

  //  mainStateMachine.transitionTo(reset);
}
//*************************************************************************************

void commsDeadUpdate() {

  errorState = 1;
  sendError(errorState, 1); //stepper Error
  errorState = 0;
  //ERROR IN COMMS

  commsFailed = false; // reset ready for next comms attempt
  retries = 0;

  delay(2000);
  mainStateMachine.transitionTo(mainNoOp);
}

//**************************************************************************************
void resetEnter() {
  //  Serial.println("reset");
  digitalWriteFast(startTimer, LOW);
  delay(50);
  digitalWriteFast(resetTimer, HIGH);
  if (doShift == true) digitalWriteFast(zeroShift, LOW); //turn zero shift signal on
  delay(50);
  resetEnd = myMillis() + resetPulse;
}

void resetUpdate() {
  if ((long(myMillis() - resetEnd) >= 0) && ended == true) { //check for reset pulse complete and test timeout over
    ended = false;
    digitalWriteFast(resetTimer, LOW);
    digitalWriteFast(zeroShift, HIGH); // zero shift off
    //    Serial.println("*s1,1,1,1,1");
    mainRunState = 28; // this is an attempt to catch an error. Should jump to dispenseover
    nextState();
  }
  /*  if (tempTimer>500){
    Serial.println("here");
    tempTimer=0;
    }*/
}

void resetExit() {
  //  Serial.println("resetexit");
  digitalWriteFast(resetTimer, LOW);
  digitalWriteFast(zeroShift, HIGH); // zero shift off
  digitalWriteFast(startTimer, LOW);
  digitalWriteFast(gateTimer, LOW);
  timerTrigger = false;
}

//******************************************************
void dispenseOverEnter() {
  stepperIsActive = true;
  headPos = intermedPos * conversion;
  //  headPos = upPos*conversion;
  stepper1.setMaxSpeed(travelSpeed);
  stepper1.moveTo(-headPos);

  if (timeStart + timeEnd == 0) timerValue = 0;
  //else timerValue=float(timeEnd-timeStart)/1000; // ONLY WHILE TIMER DISCONNECTED

  float dispenseTimeValue;
  if (timeStart == 0) { // if no start of continuous registered
    Serial.println("didn't start");
    if (timeoutEnd) {
      Serial.println("timeout");
      dispenseTimeValue = maxTimeout; // if reached max timeout timer, set to maxtimeout
    }
    else dispenseTimeValue = 0; // if dispense registered finished based on weight, record as zero.
  }
  else if (dispenseEnd == 0) { // if no end of weight rise registered
    Serial.println("no disp end time");
    dispenseTimeValue = maxTimeout; // note maxTimeout is in seconds
    sysTimeoutEnd += 10000; // add on some extra because the failed to finish will have taken longer
  }
  else if (long(dispenseEnd) < long(timeStart)) {// trap any possibililty of negative outcome, and set to 15 seconds
    Serial.println("negative");
    dispenseTimeValue = maxTimeout;
  }
  else dispenseTimeValue = float(dispenseEnd - timeStart) / 1000;

  Serial.print("ts ");
  Serial.print(timeStart);
  Serial.print(",");
  Serial.print("te ");
  Serial.print(timeEnd);
  Serial.print(",");
  Serial.print("de ");
  Serial.println(dispenseEnd);

  Serial.print("*d");
  Serial.print(timerValue); // send continuous stream time
  Serial.print(',');
  /*  Serial.print(dispenseEnd);
    Serial.print(',');
    Serial.print(timeStart);
    Serial.print(',');*/
  Serial.println(dispenseTimeValue); // send dispense time in seconds and tenths of seconds
  //  Serial.println(float(dispenseEnd-timeStart)/1000,1); // send in seconds and tenths of seconds
  timerValue = 0;
  //  ended=true;
  //  Serial.println("dispenseover");
}

void dispenseOverUpdate() { //
  if (stepper1.distanceToGo() == 0 && !restart && !abortStop) nextState();
}

void dispenseOverExit() {
}


//*******************************************************
void waitForNeedleEnter() {
  //  Serial.println("wfn");
  command = '0';
  for (byte i = 0; i < numPar; i++)parameters[i] = 0;
  wfnTimer = 0;
  readFlag = false;
  newWeightAvail = false;
  balanceMachine.transitionTo(balanceRead);
  needleMeasure = false;
}

void waitForNeedleUpdate() {
  if (balanceNoOpState) {
    balanceMachine.transitionTo(balanceRead);
    sendTestStatus();
    //Serial.println("get weight again");
  }
  if (wfnTimer > 2000 && !readFlag && newWeightAvail) {
    testSeq = 12;
    Serial.print("*t");
    Serial.print(testSeq);
    Serial.print(",");
    Serial.print(testStatus);
    Serial.print(",");
    Serial.print(readNum);
    Serial.print(",");
    Serial.print(finishTime - testStart);
    Serial.print(",");
    Serial.print(load, 1);
    Serial.print(",");
    Serial.println(float(weight) / 10000, 5);
    readFlag = true;
    sendStatus();
  }
  if (readFlag) {
    readIncoming();
  }
  if (command == 'N') {
    needleMeasure = true;
    sendStatus();
    nextState();
  }
  else {
  }//error conditions
  newWeightAvail = false;
}

void waitForNeedleExit() {
  //Serial.println("wfn exit");
}
//*******************************************************
void waitForNeedleReturnEnter() {
  //  Serial.println("wfnr");
  command = '0';
  for (byte i = 0; i < numPar; i++)parameters[i] = 0;
  //  memset(parameters,0,sizeof(parameters)/sizeof(int));
  endComm = false;
  tempTimer = 0;
}

void waitForNeedleReturnUpdate() {
  readIncoming();
  if (tempTimer > 500) { // keep sending status
    sendStatus();
    tempTimer = 0;
  }
  if ( command == 'n' /*|| command =='U'*/) { // there seems to be some confusion about whether the n command is captured correctly, so U might appear first.
    needleMeasure = false;
    sendStatus();
    nextState();
  }
}

void waitForNeedleReturnExit() {
  //  Serial.println("wfnr ex");
}
//*******************************************************
void waitForUnclampEnter() {
  Serial.println("wfu");
  if (command != 'U') { // iff command is not already U, clear up ready to read
    command = '0';
    for (byte i = 0; i < numPar; i++)parameters[i] = 0;
    //  memset(parameters,0,sizeof(parameters)/sizeof(int));
    endComm = false;
  }
}

void waitForUnclampUpdate() {
  if (command != 'U') readIncoming();
  if (endComm && (command == 'U' || command == 'S')) {
    if (parameters[0] == 0) {
      devicePass = true; // keep hold of pen and move head to collect it
      nextState();
    }
    else {
      devicePass = false;
      mainRunState = 60; // jump to things to do if pen fail
      nextState();
    }
  }
}

void waitForUnclampExit() {
}
//******************************************************
void nomTimerNoOpEnter() {
  if (verbose) Serial.println("nomtimernoop");
}

void nomTimerNoOpUpdate() { // timeout check noOp

}


void nomTimerNoOpExit() {
}
//*************************************************************************************

void nomTimeEnter() {
  if (!triggered) timeTrigger = myMillis(); // if interrupt triggers before trigger load readings report
  nominalTimerEnd = timeTrigger + (uint32_t(nominalTimeout) * uint32_t(100)); //nb  nominaltimeout is in tenths
  if (verbose) Serial.println("nomtimer");
  nomEnd = false;
}

void nomTimeUpdate() {
  if (long(myMillis() - nominalTimerEnd) >= 0) { //nominal timer is completed
    nomEnd = true;
    nominalTimer.transitionTo(nomTimerNoOp);
    Serial.println(nominalTimeout);
  }
  if (gated && dispenseFinished) { // stream finished and weight increase stopped
    nominalTimer.transitionTo(nomTimerNoOp); // early finish
  }
}

void nomTimeExit() {
  sendTestStatus();
  finishTime = myMillis();
}

//*************************************************************************************
void maxTimerNoOpEnter() {
  //  if (verbose) Serial.println("max timer noop");
}
void maxTimerNoOpUpdate() {
}
void maxTimerNoOpExit() {
}
//*************************************************************************************
void maxTimerEnter() {
  timeoutTimerEnd = timeTrigger + (uint32_t(maxTimeout) * uint32_t(1000)); // end of timetout, note maxtimeout is in seconds
  Serial.print("maxtime ");
  Serial.println(timeoutTimerEnd);
  for (byte i = 0; i < numBalanceReadings; i++) balanceBuffer[i] = '0';
  //  if (verbose) {Serial.println("max timer ");}
  dispenseStarted = false;
  averageWeight = 0;
  previousAvWt = 0;
  weightTotal = 0;
  balanceIndex = 0;

  balanceMachine.transitionTo(balanceRead);
}

void maxTimerUpdate() {
  if (newWeightAvail && errorState != 15 && balanceNoOpState && readTimer > readTime && testStatus != 'E') { // keep on getting new weight info if weight already reported - read as quickly as possible
    newWeightAvail = false;
    balanceMachine.transitionTo(balanceRead);
    loadMachine.transitionTo(loadRead);
    readTimer = 0;
    Serial.println("mt");
    sendTestStatus();
//    if (priorityStatus) {
//      priorityStatus = false; // cancel the priority ststus as the message has been sent
//      Serial.println("ps");
//    }
  }
  else if (errorState == 15) {
    balanceMachine.transitionTo(balanceRead);
    sendError(errorState, 0);
    errorState = 0;
  }
  else if (errorState == 16) {
    balanceMachine.transitionTo(loadRead);
    sendError(errorState, 0);
    errorState = 0;
  }

  //************ This is the bit that evaluates what teststatus code to give the reading

  if (!priorityStatus) { // don't change the code letter if there is a priority status to send - wait until it has been sent

    if (dispenseFinished && testStatus == 'C') { // try to make sure a D is sent after a C
      testStatus = 'D';
      priorityStatus = true; // don't ignore this status code until its sent
    }
    else if (!nomEnd) { // if 7s is not yet finished
      if (gated && dispenseFinished && testStatus == 'D') { // things to do if continuous stream now ended and dose ended
        testStatus = 'E'; // only show E if 7s not yet expired
        sendTestStatus();
        timeoutTimer.transitionTo(maxTimerNoOp);
      }
      /*      else if (!gated && dispenseFinished && testStatus != 'D'){ // if under 7s, stream not finished and dose ended
              testStatus='J';
            }*/
    }
    else { // if 7s is finished
      if (!gated && !dispenseFinished) { // if over 7s, continuous not finished, dispense not finished
        testStatus = 'G';
      }
      else if (gated && !dispenseFinished) { // if over 7s, continuous has finished, but dispense not finished
        testStatus = 'F';
      }
      else if (!gated && dispenseFinished) { // if over 7s, dose ended, stream end not detected - droplet on tip ?
        testStatus = 'K';
      }
    }

    if (long(myMillis() - timeoutTimerEnd) >= 0) { // end of timeout timer
      timeoutEnd = true;
      Serial.println("timed out");
      if (testStatus == 'A' || testStatus == 'Z') testStatus = 'X'; // stream didn't start
      else if (!dispenseFinished && !gated) testStatus = 'Y'; //max timer ended, dose not ended, stream end not detected - very slow dispense ?
      else if (!dispenseFinished) testStatus = 'H'; // max timer ended, dose end not detected
      sendTestStatus();
      timeoutTimer.transitionTo(maxTimerNoOp);
    }
  }
}

void maxTimerExit() {
  if (normal) { //if normal process, not restart after false trigger
    finishTime = myMillis();
    mainStateMachine.transitionTo(gate);
    ended = true;
    if (testStatus == 'Z') nextState(); // pen not fired, so timing wont happen
  }
  else {
    normal = true; // reset to normal process after skipping previous code on retry
    Serial.println("Restart");
  }
}
//*************************************************************************************
void sysTimerNoOpEnter() {
}

void sysTimerNoOpUpdate() {
}

void sysTimerNoOpExit() {
}

//************************************************************************

void sysTimerEnter() {
  sysTimeoutEnd = testTimerStart + (long(moveDuration) * 1000);
  sysTimerElapsed = 0;
  writeNow = true;
}

void sysTimerUpdate() {
  if (sysTimerElapsed > 500 && writeNow) {
    /*    Serial.print("ste ");
      Serial.println(sysTimeoutEnd);
      Serial.print("mi");
      Serial.println(myMillis());*/
    digitalWriteFast(53, HIGH); // flash green light
    writeNow = false;
  }
  if (sysTimerElapsed > 1000) {
    digitalWriteFast(53, LOW); // 53 is green light
    sysTimerElapsed = 0;
    writeNow = true;
  }
  if (long(myMillis() - sysTimeoutEnd) >= 0) { //if over system Timeout time, abort and send error
    mainRunState = 0;
    abortRunState = 1;
    errorState = 30;
    sendError(errorState, 1);
    nextState();
    sysTimeout.transitionTo(sysTimerNoOp);
    timeoutTimer.transitionTo(maxTimerNoOp);
  }
}

void sysTimerExit() {
  digitalWriteFast(53, LOW); // 53 is green light
}

//*************************************************************************************
void balanceNoOpEnter() {
  balanceNoOpState = true;
}
void balanceNoOpUpdate() {
}
void balanceNoOpExit() {
  balanceNoOpState = false;
}
//*************************************************************************************
void balanceReadEnter() {
  while (Serial2.available()) Serial2.read(); // empty buffer
  Serial2.println("IP"); // Have to assume that no continuous print is happening
  //  balanceCommsEnd = myMillis() + (commsTime);
  balanceError = false; // reset error flag
  prevWeight = weight;
  //  calcWeight  = 0;
  balanceReceivedMessage = 0;
  balanceReadState = 0;
  //  for (byte i=0;i<numBalanceReadings;i++)balanceReadings[i]=0;
  //  memset(balanceBuffer,0,sizeof(balanceBuffer)/sizeof(char));// reset balanceBuffer ready for incoming time data
  //  if (verbose) Serial.println("balanceread");
  balanceTimeout = 0;
  /*if (errorState==15){
    errorActive=0;
    sendError(errorState,errorActive);
    errorState=0;
    }*/
}

void balanceReadUpdate() {
  if (balanceTimeout >= commsTime) { // jump out of waiting loop if insufficient data received in time - should comms retry ?
    if (verbose) Serial.print("timeout ");
    if (verbose) Serial.println(balanceTimeout);
    if (verbose) Serial.print("commsTime");
    if (verbose) Serial.println(commsTime);
    if (verbose) Serial.println("balance timed out");
    balanceError = true;
    weight = 0; // default to 0
    newWeightAvail = true;
    errorState = 15;
    errorActive = 1;
    sendError(errorState, errorActive);
    balanceMachine.transitionTo(balanceNoOp);
  }
  else {
    if (Serial2.available() >= 8 && balanceReadState == 0) balanceReadState = 1; //wait for incoming data
    if (balanceReadState == 1) {
      //      if (verbose) Serial.println("balanceReadState = 1");
      if (balanceReceivedMessage < 20) { // end char not received in time. if this state executed too many times before noop, received message will be > 20
        char chb = Serial2.read();
        //if (verbose) Serial.print("chb");
        //Serial.println(weight);
        //Serial.println(chb);
        if (chb != 0x0D) {
          balanceBuffer[balanceReceivedMessage++] = chb; // if not cr add character to buffer array and then increment the array pointer
          //if (chb=='-') weight = -weight;
          //if (chb >= 48 && incomingChar <= 57){
          //  weight *= 10;
          //  weight += (chb - 48);
          //}
        }
        else { // cr received
          calcWeight = long(atof(balanceBuffer) * 10000); // convert char array to float
          //Serial.println(weight);
          //          if (weight > (prevWeight*2)) weight=prevWeight; // remove spurious large readings
          newWeightAvail = true;
          if (errorState == 15 && errorActive == 1) { // send error corrected message
            errorState = 15;
            errorActive = 0;
            sendError(errorState, errorActive);
          }
          //          if (verbose) Serial.print("weight = ");
          //Serial.println(weight);
          tempTimer = 0;
          balanceReadState = 2;
        }
      }
      else { // check for exit due to lack of end char
        balanceError = true;
        errorState = 15;
        sendError(errorState, 1);
        //weight = 0; // default to 0
        tempTimer = 0;
        balanceReadState = 2;
      }
    }
    if (balanceReadState == 2 && tempTimer > 10) { // wait 10ms before exiting to ensuer that all crap is recieved and then dumped
      balanceMachine.transitionTo(balanceNoOp);
      while (Serial2.available()) Serial2.read(); // empty buffer
      newWeightAvail = true;
    }
  }
}

void balanceReadExit() {
  weight = calcWeight;
  //  Serial.println(weightTotal);
  //  Serial.println(balanceReadings[balanceIndex]);
  weightTotal = weightTotal - balanceReadings[balanceIndex]; // subtract current array value from weightTotal
  //  Serial.println(weightTotal);
  balanceReadings[balanceIndex] = weight;   // write in new value to array to overwrite previous
  //  Serial.println(weight);
  weightTotal = weightTotal + balanceReadings[balanceIndex]; // add value to the weightTotal:
  //  Serial.println(weightTotal);
  balanceIndex++;                      // advance to the next position in the array:

  // if we're at the end of the array...
  if (balanceIndex >= numBalanceReadings) balanceIndex = 0;    // ...wrap around to the beginning:

  // calculate the average:
  previousAvWt = averageWeight;
  averageWeight = weightTotal / numBalanceReadings;
  //    Serial.print("av ");
  //    Serial.println(averageWeight);

  if (running() && !dispenseFinished) { // if process is running and dispense is not finished - don't update if needle shaking
    if (averageWeight > startWeight && testSeq > 6) dispenseStarted = true; // only allow dispense started if at good point in test sequence

    if ((averageWeight - previousAvWt) < (weightChange / 2) && dispenseStarted) { // weight stopped increasing
      dispenseFinished = true;
      timerTrigger = false; // make sure timer can't be triggered after dispense finished
      Serial.println("dispense finished");
      dispenseEnd = myMillis();
      if (testStatus == 'C' || testStatus == 'Z' || testStatus == 'J') { // only allow transition on to D if stream has stopped
        testStatus = 'D'; // update status if normal dispense - not if over 7s as status would be F or G
        Serial.println("stat D");
        priorityStatus = true; // make sure this gets sent and not overwritten
        sendTestStatus();
      }
    }
    //    readNum++;// now incremented in sendteststatus
  }
}

//*************************************************************************************
void loadNoOpEnter() {
  //  if (verbose) Serial.print("load NoOp");
  loadNoOpState = true;
}
void loadNoOpUpdate() {
}
void loadNoOpExit() {
  loadNoOpState = false;
}
//*************************************************************************************
void loadReadEnter() {
  //  Serial3.write(0x13); // XOFF kills any continuous print that might be happening to stop data flow
  while (Serial3.available()) Serial3.read(); // empty buffer
  Serial3.println("PI"); //
  //  loadCommsEnd = myMillis() + (commsTime);
  loadError = false; // reset error flag
  load  = 0;
  loadReceivedMessage = 0;
  loadReadState = 0;
  //  for (byte i=0;i<numLoadReadings;i++)loadReadings[i]=0;
  //  memset(loadBuffer,0,sizeof(loadBuffer)/sizeof(char));// reset loadBuffer ready for incoming time data
  //  if (verbose) Serial.println("load read");
  loadTimeout = 0;
  //  errorState=0;
}

void loadReadUpdate() {
  if (loadTimeout >= commsTime) { // jump out of waiting loop if insufficient data received in time - should comms retry ?
    //    Serial.println("timeout");
    loadError = true;
    //    errorState = 16;
    errorActive = 1;
    load = 0;
    loadTimeout = 0;
    loadMachine.transitionTo(loadNoOp);
    //    errorState=50; //temporary for debug purpose
    //    sendError(errorState,1); // temporarily commented out due to excessive errors !
    //    errorState=0;
    if (verbose)Serial.println("load error");
  }
  else {
    if (Serial3.available() >= 10 && loadReadState == 0) loadReadState = 1; //wait for incoming data
    switch (loadReadState) {
      case 1:
        {
          char chl = Serial3.read();
          if (chl == '*') {
            loadReadState = 2;
          }
          break;
        }
      case 2:
        {
          char c = Serial3.read();
          if (c != '\0')loadBuffer[loadReceivedMessage++] = c;
          else {
            load = atof(loadBuffer); // convert char array to float
            if (triggered && load == 0) load = lastLoad; // remove zeroes after triggering
            if (triggerInProgress && load == 0) load = lastLoad; // kill spurious zeros in output stream;
            loadReadState = 0;
            loadMachine.transitionTo(loadNoOp);
            if (errorState == 16 && errorActive == 1) { // send error corrected mesage on next successful read, and clear error
              errorActive = 0;
              sendError(errorState, errorActive);
              errorState = 0;
            }
            if (load > (maxLoad * 1000) || -load > (maxLoad * 1000)) {
              stepper1.stop();
              abortStop = true;
              Serial.println("maxload exceeded");
              mainStateMachine.transitionTo(mainNoOp);
              errorState = 19;
              errorActive = 1;
              sendError(errorState, errorActive);
            }
          }
          break;
        }
    }
  }
}

void loadReadExit() {
  delay(5);
  loadTotal = loadTotal - loadReadings[loadIndex];  // subtract current array value from loadTotal
  milliLoad = long(load * 1000); // convert to millinewtons
  loadReadings[loadIndex] = milliLoad;   // write in new value to array to overwrite previous, convert N value to mN to use integersqw
  loadTotal = loadTotal + loadReadings[loadIndex];  // add value to the loadTotal:
  loadIndex++;                      // advance to the next position in the array:
  // if we're at the end of the array...
  if (loadIndex >= numLoadReadings) loadIndex = 0;    // ...wrap around to the beginning:

  //save the last average
  lastAvLoad = averageLoad;

  if (abs(milliLoad) > peakLoad) peakLoad = abs(milliLoad); // keep increasing peakload to capture highest value. use abs value to avoidfaffinf with signs

  if (triggered && load != 0) lastLoad = load; // remove zeroes from data once triggereing has happened
  lastTimestamp = timestamp;
  // calculate the average:
  averageLoad = loadTotal / numLoadReadings;
  timestamp = myMillis();
  gradient = ((averageLoad * 10) - (lastAvLoad * 10)) / long(timestamp - lastTimestamp);

  if (mainStateMachine.isInState(verifyRelease)) {
    if (load < verifyReleaseLoad && averageLoad < int(verifyReleaseLoad * 1000)) {
      touchDown = true;
      Serial.println("touchdown ver");
    }
  }

  if (mainStateMachine.isInState(lowerToCap)) {
    if (averageLoad < (touchCapLoad * 1000)) {
      touchedCap = true;
      Serial.println("touchdown cap");
    }
  }

  if (mainStateMachine.isInState(removeCap)) {
    if ((averageLoad > (upLimitLoad)) && !removalInProgress && finishedCount < 1) {
      removalInProgress = true;
      Serial.println("cap in progress");
    }
    if (removalInProgress && (milliLoad < (capLoadDrop))) { //check that load has risen, and now dropped back below threshold
      finishedCount = 1;
      Serial.println("cap trigger");
      removalInProgress = false;
    }
    if (finishedCount > 0) {
      if (milliLoad > capLoadDrop && finishedCount > 1) finishedCount--; // dont increment if load has risen back up
      finishedCount++; // increment count to gaterh post event readings
      Serial.print("fin cnt ");
      Serial.println(finishedCount);
    }
    if (finishedCount > overRun) {
      //      Serial.println("counting");
      finishedCount = 0;
      capRemoved = true;
      Serial.println("Cap removed");
    }
  }

  if (mainStateMachine.isInState(ready)) { // loads will be recorded negative
    if ((-averageLoad > (triggerLimitLoad)) && !triggerInProgress) { //
      triggerInProgress = true;
      //      testStatus='Q';// temporary to indicate progress
    }
    if ((gradient > trigGrad && triggerInProgress)) { // ||(abs(averageLoad)<((peakLoad*retryPercent)/100))){
      // add in capture for triggering occurring in 100ms stationary period of false trigger,along with gradient based detection
      //    if (triggerInProgress && (-averageLoad + milliLoad) > (trigLoadDrop)) { //load has dropped back - simple load drop test does not work
      triggered = true;
      timeTrigger = myMillis();
      timeoutTimer.transitionTo(maxTimer); // start timeout check timer
      if (testStatus == 'A') testStatus = 'Z'; //only set to z if at A. IE not already triggered
      stepper1.stop();
      sendTestStatus();
    }
  }
  newLoadAvail = true;
}

//*************************************************************************************
void messageNoOpEnter() {
}

void messageNoOpUpdate() {
}

void messageNoOpExit() {
}

// ***********************************************************************
void waitForPenRemoveEnter() {
  tempTimer = 0;
}

void waitForPenRemoveUpdate() {
  if (digitalRead(penIsPresent) == HIGH) nextState();
  if (tempTimer > 500) { // keep sending status
    sendStatus();
    tempTimer = 0;
  }
}

void waitForPenRemoveExit() {
}
// ***********************************************************************

void tempUpdate() {
}

//*************************************************************************************

void errorUpdate() {
  // error actions
}

void nullStateUpdate() {
  nextState();
}


// ************* ISR ******************

// ISR triggered on trigger pin state change - timerTrigger indicates current status

void timerGo() { // interrupt service routine to send output to timer on thru beam trigger if apprioriate
  if (timerTrigger == true) { // In ready state, waiting for trigger, so initiate start pulse
    digitalWriteFast(51, HIGH); // turn on start pulse
    timeStart = myMillis(); //save start of time pulse
    mainStateMachine.transitionTo(timing);    // transition to timing wait state
    timerTrigger = false;
  }
  else if ((digitalReadFast(32) == LOW) && (digitalReadFast(48) == LOW) && deBounce == true) { // check for cup, clamp and debounce time - prevent activity during startup
    digitalWriteFast(41, HIGH); // turn on gate to hold reading
    timeEnd = myMillis();
    mainStateMachine.transitionTo(waitForDispenseEnd);    // transition to waitForDispenseEnd state to wait until dose/nominal/timeout timer is on
    mainRunState ++;
  }
}

/*void receiveEvent(int howMany){
  wireReadTime=0;
  if (verbose) Serial.print("resp ");
  a = Wire.read(); // read instruction first
  if (verbose) Serial.print(a,DEC);
  byte i=0; // loop counter
  while (Wire.available() > 0){
  i2cbuffer[i] = Wire.read();
  if (verbose) Serial.print("byte ");
  if (verbose) Serial.println(i2cbuffer[i++], DEC);
  if (wireReadTime > wireReadTimeout){
  a=-1;
  break;
  }
  }
  val = atol(i2cbuffer);
  if (verbose) Serial.print(" val ");
  if (verbose) Serial.println(val);
  }*/
//***************** sub routines ******************

void GetEepromAddresses() { //
  // eeprom variables etc for storage
  if (verbose) Serial.println("Get eeprom addresses");
  addressInit = EEPROM.getAddress(sizeof(int));
  addressTimer = EEPROM.getAddress(sizeof(int));
  addressShift = EEPROM.getAddress(sizeof(long));
  addressDelay = EEPROM.getAddress(sizeof(int));
  addressPreCapRemove = EEPROM.getAddress(sizeof(int));
  addressCapRemoveDist = EEPROM.getAddress(sizeof(int));
  addressTriggerPos = EEPROM.getAddress(sizeof(int));
  addressPushMove = EEPROM.getAddress(sizeof(float));
  addressUpPos = EEPROM.getAddress(sizeof(int));
  addressDownPos = EEPROM.getAddress(sizeof(int));
  addressStartPos = EEPROM.getAddress(sizeof(int));
  addressMaxTimer = EEPROM.getAddress(sizeof(int));
  addressVerifyPos = EEPROM.getAddress(sizeof(int));
  addressIntermedPos = EEPROM.getAddress(sizeof(int));
  addressWeightChange = EEPROM.getAddress(sizeof(int));
}

void WriteToEeprom() {
  // write to eeprom
  if (verbose) Serial.println("write to eeprom");
  EEPROM.updateInt(addressTimer, nominalTimeout);
  EEPROM.updateLong(addressShift, shiftPause);
  EEPROM.updateInt(addressDelay, delayMicros);
  EEPROM.updateInt (addressPreCapRemove, preCapRemove);
  EEPROM.updateInt (addressCapRemoveDist, capRemoveDist);
  EEPROM.updateInt (addressTriggerPos, triggerPos);
  EEPROM.updateFloat (addressPushMove, pushMove);
  EEPROM.updateInt (addressUpPos, upPos);
  EEPROM.updateInt (addressDownPos, downPos);
  EEPROM.updateInt (addressStartPos, startPos);
  EEPROM.updateInt (addressMaxTimer, maxTimeout);
  EEPROM.updateInt (addressVerifyPos, verifyPos);
  EEPROM.updateInt (addressIntermedPos, intermedPos);
  EEPROM.updateInt (addressWeightChange, weightChange);
}

void ReadEeprom() {
  // load setup from EEPROM
  if (verbose) Serial.println("read eeprom");
  //  nominalTimeout = EEPROM.readInt(addressTimer);
  shiftPause = EEPROM.readLong(addressShift);
  delayMicros = EEPROM.readInt(addressDelay);
  preCapRemove = EEPROM.readInt(addressPreCapRemove);
  //  capRemoveDist = EEPROM.readInt(addressCapRemoveDist);
  triggerPos = EEPROM.readInt(addressTriggerPos);
  pushMove = EEPROM.readFloat(addressPushMove);
  upPos = EEPROM.readInt(addressUpPos);
  downPos = EEPROM.readInt(addressDownPos);
  startPos = EEPROM.readInt(addressStartPos);
  maxTimeout = EEPROM.readInt(addressMaxTimer);
  verifyPos = EEPROM.readInt(addressVerifyPos);
  intermedPos = EEPROM.readInt(addressIntermedPos);
  //  weightChange= EEPROM.readInt(addressWeightChange);
}

// ************************************************************

void clearTimerBuffer() {
  for (byte i = 0; i < timerMessageLength; i++) timerBuffer[i] = '0';
  //  memset(timerBuffer,0,sizeof(timerBuffer)/sizeof(char));// reset timerBuffer ready for incoming time data
}

void commsFail(int tries, int why) {
  commsFailed = true;
  clearTimerBuffer(); // delete partial message
}

byte hex2dec(byte hexVal) {
  if (hexVal >= 0x30 && hexVal <= 0x39) {
    return hexVal - 0x30;
  }
  else {
    return hexVal - 0x40 + 9;
  }
}

//******************** sendstatus ********************

void sendStatus() {
  Serial.print("*s"); // start of response
  if (penIn == HIGH) Serial.print("1,"); // if running a test, must be pen in
  else if (digitalReadFast(penIsPresent) == LOW) Serial.print("1,"); //pen is in
  else Serial.print("0,");
  if (digitalReadFast(lightGuardIsOk) == LOW) Serial.print("1,"); // light curtain clear
  else Serial.print("0,");
  if (digitalReadFast(nestIsClosed) == LOW) Serial.print("1,"); // clamp closed
  else Serial.print("0,");
  if (digitalReadFast(containerIsPresent) == LOW) Serial.print("1,"); // container placed
  else Serial.print("0,");
  //  Serial.print(",");
  //  Serial.print(tim);
  if (needleMeasure) Serial.println("1");
  else Serial.println("0");


  //Serial.write(0x0D); // send cr terminator - println should send termination
}

void sendTestStatus() {
  if (testSeq != 12) {
    Serial.print("*t");
    Serial.print(testSeq);
    Serial.print(",");
    Serial.print(testStatus);
    Serial.print(",");
    Serial.print(readNum);
    Serial.print(",");
    Serial.print(myMillis() - testStart);
    Serial.print(",");
    if (testSeq == 'B') Serial.print(averageLoad, 1);
    else Serial.print(load, 1);
    Serial.print(",");
    //  Serial.print(float(weight)/10000,4);
    //  Serial.print(",");
    //  Serial.println(gradient);
    Serial.println(float(weight) / 10000, 4);
    //  if (weight == 0) Serial.println(float(averageWeight)/10000,4);
    //  else Serial.println(float(weight)/10000,4);
    if (testSeq >= 11) readNum++;
  }
    if (priorityStatus) {
    priorityStatus = false; // cancel the priority ststus as the message has been sent
    Serial.println("ps");
  }
}

void sendActuatorStatus(byte actuator, byte progress, byte valve, byte one, byte two, float weight, float load) {
  Serial.print("*k");
  Serial.print(actuator);
  Serial.print(",");
  Serial.print(progress);
  Serial.print(",");
  Serial.print(valve);
  Serial.print(",");
  Serial.print(two);
  Serial.print(",");
  Serial.print(one);
  Serial.print(",");
  Serial.print(float(weight) / 10000, 4);
  Serial.print(",");
  Serial.println(load, 1);
}

void sendCarriageStatus(byte dir, byte progress, byte valve, byte one, byte two, byte three, float weight, float load) {
  Serial.print("*p");
  Serial.print(dir);
  Serial.print(",");
  Serial.print(progress);
  Serial.print(",");
  Serial.print(valve);
  Serial.print(",");
  Serial.print(one);
  Serial.print(",");
  Serial.print(two);
  Serial.print(",");
  Serial.print(three);
  Serial.print(",");
  Serial.print(float(weight) / 10000, 4);
  Serial.print(",");
  Serial.println(load, 1);
}

void sendHeadStatus(byte pos, byte progress, byte valve, byte one, byte two, float weight, float load) {
  Serial.print("*h");
  Serial.print(pos);
  Serial.print(",");
  Serial.print(progress);
  Serial.print(",");
  Serial.print(valve);
  Serial.print(",");
  Serial.print(one);
  Serial.print(",");
  Serial.print(two);
  Serial.print(",");
  Serial.print(float(weight) / 10000, 4);
  Serial.print(",");
  Serial.println(load, 1);
}

void headMoveTowardTest() {
  digitalWriteFast(moveCarriageToTest, HIGH);
  digitalWriteFast(moveCarriageToDiscard, LOW);
}

void headMoveTowardDiscard() {
  digitalWriteFast(moveCarriageToTest, LOW);
  digitalWriteFast(moveCarriageToDiscard, HIGH);
}

void stopMoveBack() {
  digitalWriteFast(moveStopBack, HIGH);
  digitalWriteFast(moveStopOut, LOW);
}

void stopMoveOut() {
  digitalWriteFast(moveStopBack, LOW);
  digitalWriteFast(moveStopOut, HIGH);
}

void colletMoveClose() {
  digitalWriteFast(closeCollet, 1); // turn on close collet valve
  digitalWriteFast(openCollet, 0); // turn off open collet valve
}

void colletMoveOpen() {
  digitalWriteFast(closeCollet, 0); // turn off close collet valve
  digitalWriteFast(openCollet, 1); // turn on open collet valve
}

void penGripMoveOpen() {
  digitalWriteFast(openPenGripper, 1); // turn on open gripper valve
  digitalWriteFast(closePenGripper, 0); // turn off close gripper valve
}

void penGripMoveClose() {
  digitalWriteFast(openPenGripper, 0); // turn off open gripper valve
  digitalWriteFast(closePenGripper, 1); // turn on close gripper valve
}

void nestMoveOpen() {
  digitalWriteFast(openNest, 1); // turn on open nest valve
  digitalWriteFast(closeNest, 0); // turn off close nest valve
}

void nestMoveClose() {
  digitalWriteFast(openNest, 0); // turn off open nest valve
  digitalWriteFast(closeNest, 1); // turn on close nest valve
}

//*************************************************************************************
void readIncoming() {
  //  if (verbose) Serial.println("read incoming");
  //if (verbose) Serial.print("ReadPCSerial = ");
  //if (verbose) Serial.println(readPCSerial);
  checkRequest = true;
  switch (readPCSerial) {
    case 1:
      if (Serial.available() > 1) {
        readPCSerial = 2; // something arrived from PC
      }
      break;
    case 2:
      {
        char c;
        while (c != '*' && Serial.available()) {
          c = Serial.read();
          if (verbose) Serial.println(c);
        }
        if (c == '*') { // check for correct start command
          if (verbose) Serial.println("OK");
          for (byte i = 0; i < numPar; i++)parameters[i] = 0;
          //      memset(parameters,0,sizeof(parameters)/sizeof(int));
          commsEnd = myMillis() + (commsTime);
          //      if (verbose) Serial.print("commsEnd = ");
          //      if (verbose) Serial.println(commsEnd);
          readPCSerial = 3;
        }
        else {
          readPCSerial = 99; // error state
          while (Serial.available()) {
            char c = Serial.read();
            //Serial.println(c);
          }
          if (verbose) Serial.println("wrong start");
          if (verbose) Serial.println(myMillis());
        }
        break;
      }
    case 3:
      if (Serial.available()) { // wait for next character to be available
        readPCSerial = 4;
      }
      else {
        if ((long)(myMillis() - commsEnd) >= 0) { // jump out of waiting loop if insufficient data received in time - should comms retry ?
          commsFailed = true;
          readPCSerial = 99;
          if (verbose) Serial.println("short on data");
          errorState = 1; // 1=comms timeout
          sendError(errorState, 1);
          failWhy = 1;
          break;
        }
      }
      break;
    case 4:
      {
        command = Serial.read(); // read command letter
        if (findCommand(commands, sizeof(commands) / sizeof(char), command)) { // if command is in array
          //lcd.clear();
          if (verbose) Serial.println(command);
          int i = 0;
          endComm = false; // detect end of command string
          while (!endComm && !commsFailed) { // keep looping to read all info
            if (Serial.available() > 0) { // check serial data available
              incomingChar = Serial.read(); // read next part
              if (incomingChar >= 48 && incomingChar <= 57) { // if is numeric
                checkRequest = false;
                if (verbose) Serial.print("number ");
                if (verbose) Serial.print(incomingChar);
                if (verbose) Serial.print(' ');
                if (verbose) Serial.println(incomingChar, HEX);
                parameters[i] = parameters[i] * 10;
                parameters[i] = parameters[i] + (incomingChar - '0');
                if (verbose) Serial.print("par ");
                if (verbose) Serial.print(i);
                if (verbose) Serial.print(" = ");
                if (verbose) Serial.println(parameters[i]);
              }
              else if (incomingChar == ',') {
                if (verbose) Serial.print("parameter ");
                if (verbose) Serial.print(i);
                if (verbose) Serial.print(" = ");
                if (verbose) Serial.println(parameters[i]);
                i++;
                checkRequest = false;
              }  // check for comma separator and increment to next parameter
              //            else if (incomingChar == '\r'){ // end of line character
              else if (incomingChar == '\n') { // end of line character
                if (verbose) Serial.println("endcomm");
                endComm = true; // check for CR at end of command string and end loop
                readPCSerial = 100;
                if (command == 'E') { // what if need start do-over ? qqq
                  Serial.print("*e");
                  Serial.print(parameters[0]);
                  Serial.println(",0");
                  errorState = 0;
                  errorActive = 0;
                  if (errorRestart) {
                    startRunState = 1; // begin the startup sequence at step 1, as failure was down to air pressure
                    errorRestart = false;
                    abortRunState = 0;
                    mainRunState = 0;
                    verifyRunState = 0;
                    nextState();
                  }
                  if (!running() && parameters[0] == 0 && !verifyWeightUp) {
                    mainStateMachine.transitionTo(homeStepperState);
                    headPos = upPos;
                    homed = false;
                    Serial.println("homing");
                  }
                }
                if (i == 0) checkRequest = true; // if no parameters, is a request for a status update
                else checkRequest = false;
              }
              //else {}//ERROR CONDITION
            }// end of if avaialble
            if ((long)(myMillis() - commsEnd) >= 0) { // jump out of waiting loop if insufficient data received in time - should comms retry ?
              if (verbose) Serial.print("millis= ");
              if (verbose) Serial.println(myMillis());
              commsFailed = true;
              errorState = 1;
              if (verbose) Serial.println("error");
              //            errorState= x // serial comms with PC fail
              errorState = 51; // temporary value for debug
              sendError(errorState, 1);
              failWhy = 1;
              //lcd.clear();
              //lcd.print("commsfail");
              readPCSerial = 99;
              if (verbose) Serial.println("timeout");
              break;
            } // end of if comms timeout
          } // end of while(!endComm) loop
        } // end of if command is in array
        else {
          if (verbose) Serial.println("command error");
          readPCSerial = 99;
        }
        break;
      }
    case 99:
      delay(20);
      //    while (Serial.available()) Serial.read();
      readPCSerial = 1;
      //things to do if comms error from PC
      break;
    case 100:
      readPCSerial = 1; // reset state flag for next time
      delay(20);
      //while (Serial.available()) Serial.read(); // empty out buffer

      break;
  }
}


void nextState() {
  //  if (verbose) Serial.println("nextstate");
  if (abortRunState > 0) {
    //    if (verbose) Serial.println("nextAbortState");
    abortNextState();
  }
  else if (mainRunState > 0) {
    //if (verbose) {
    Serial.print("nextMainState ");
    Serial.println(mainRunState);
    //}
    mainNextState();
  }
  else if (verifyRunState > 0) {
    //Serial.println("nextVerifyState");
    verifyNextState();
  }
  else if (startRunState > 0) {
    if (verbose) Serial.println("nextStartState");
    startNextState();
  }
  else mainStateMachine.transitionTo(mainNoOp);
}

boolean running() {
  //  if (verbose) Serial.print("running = ");
  if (mainRunState + abortRunState + verifyRunState + startRunState > 0) {
    return true;
    //    if (verbose) Serial.println("TRUE");checkRequest=false;
    //    Serial.println("TRUE");
    checkRequest = false;
  }
  else {
    return false;
    //    if (verbose) Serial.println("FALSE");
    //    Serial.println("FALSE");
  }
}

void sendError(byte error, byte errorActive) {
  if (verbose) Serial.println("senderror");
  Serial.print("*e"); // start of error message
  Serial.print(error); //
  Serial.print(",");
  Serial.println(errorActive);
}

boolean findCommand(char a[], byte num_elements, char value) {
  int i;
  for (i = 0; i < num_elements; i++) {
    if (a[i] == command) {
      return (true); /* it was found */
    }
  }
  return (false); /* if it was not found */
}

void printInputs() {
  Serial.println("Inputs");
  for (int i = 0; i < (sizeof(inputArray) / sizeof(byte)); i++) {
    Serial.print(inputArray[i]);
    Serial.print('=');
    Serial.print(digitalReadFast(inputArray[i]));
    Serial.print(',');
    if ((i + 1) % 8 == 0) Serial.println();
  }
  Serial.println();
}

void printChanged() {
  Serial.println("Changed");
  for (int i = 0; i < (sizeof(inputArray) / sizeof(byte)); i++) {
    if (digitalReadFast(inputArray[i]) != inputStateArray[i]) {
      Serial.print(inputArray[i]);
      Serial.print('=');
      Serial.print(digitalReadFast(inputArray[i]));
      Serial.print(',');
      inputStateArray[i] = digitalReadFast(inputArray[i]);
    }
    if ((i + 1) % 8 == 0) Serial.println();
  }
  Serial.println();
  for (int i = 0; i < (sizeof(outputArray) / sizeof(byte)); i++) {
    if (digitalReadFast(outputArray[i]) != outputStateArray[i]) {
      Serial.print(outputArray[i]);
      Serial.print('=');
      Serial.print(digitalReadFast(outputArray[i]));
      Serial.print(',');
      outputStateArray[i] = digitalReadFast(outputArray[i]);
    }
    if ((i + 1) % 8 == 0) Serial.println();
  }
  Serial.println();
}

void printOutputs() {
  Serial.println("Outputs");
  for (int i = 0; i < (sizeof(outputArray) / sizeof(byte)); i++) {
    Serial.print(outputArray[i]);
    Serial.print('=');
    Serial.print(digitalReadFast(outputArray[i]));
    Serial.print(',');
    if ((i + 1) % 8 == 0) Serial.println();
  }
  Serial.println();
}

void resetLoad() {
  averageLoad = 0;
  loadIndex = 0;
  loadTotal = 0;
  for (byte i = 0; i < numLoadReadings; i++)loadReadings[i] = 0;
  //    memset(loadReadings,0,sizeof(loadReadings)/sizeof(long));
}

void resetWeight() {
  averageWeight = 0;
  balanceIndex = 0;
  weightTotal = 0;
  for (byte i = 0; i < numBalanceReadings; i++)balanceReadings[i] = 0;
  //    memset(loadReadings,0,sizeof(loadReadings)/sizeof(long));
}

//*****************************************************

void verifyNextState() {
  penIn = false;
  Serial.print("verifyRunState = ");
  Serial.println(verifyRunState);
  switch (verifyRunState) {
    case  0:
      mainStateMachine.transitionTo(mainNoOp);
      break;
    case  1:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      horPos = test;
      parameters[0] = test;
      verifyState = true;
      break; // double check is in test position
    case  2:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      break; // check collet is open
    case  3:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = close;
      break; // close nest
    case 4:
      stepperIsActive = false;
      if (digitalRead(negLoadLimit) == LOW && digitalRead(posLoadLimit) == LOW) { //Only Tare if not on load limit - causes problems otherwise
        mainStateMachine.transitionTo(tare);
      }
      break;
    case 5:
      mainStateMachine.transitionTo(nullState);
      break;
    case 6:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 7: // move down to pretrigger position ready to grab part
      mainStateMachine.transitionTo(headMoveVer);
      headPos = verifyPos * conversion;
      moveSpeed = setTravel;
      break;
    case 8:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      break; // close nest
    case 9:  //move down to touch cap at test speed
      resetLoad();
      mainStateMachine.transitionTo(lowerToCap);
      averageLoad = 0;
      loadIndex = 0;
      for (byte i = 0; i < numLoadReadings; i++)loadReadings[i] = 0;
      //    memset(loadReadings,0,sizeof(loadReadings)/sizeof(long));
      headPos = downPos * conversion;
      //    moveSpeed=setTravel;
      moveSpeed = setTest;
      break;
    case  10:
      mainStateMachine.transitionTo(smallMoveUp);
      moveSpeed = 4;
      break;
    case  11:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = close;
      break; // close collet to grab
    case 12:
      mainStateMachine.transitionTo(nullState);
      break;
    case 13:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case  14:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = -(stepper1.currentPosition() + (verifyMove * conversion)); //pick verify weight up
      moveSpeed = setVerify;
      break; // move up to lift test part
    case  15:
      stepperIsActive = false;
      verifyWeightUp = true;
      mainStateMachine.transitionTo(mainNoOp);
      sendStatus();
      break;


    case 20:
      /*    mainStateMachine.transitionTo(homeStepperState);
        break;
        case 21: */
      //    resetLoad();
      mainStateMachine.transitionTo(verifyRelease); // put verify weight down
      headPos = downPos * conversion;
      moveSpeed = setVerify;
      verifyRunState++; // skip a step
      break; // move down to release
    case 22:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      break; // open collet
    case 23:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = close;
      break; // close nest
    case 24:
      mainStateMachine.transitionTo(nullState);
      break;
    case 25:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 26:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = upPos * conversion;
      moveSpeed = setTravel;
      break; // move up
    case 27:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      verifyState = false;
      break; // open nest
    case 28:
      stepperIsActive = false;
      mainStateMachine.transitionTo(mainNoOp);
      verifyRunState = -1; // kill any further states
      verifyRestart = false;
      verifyRestartState = 0;
      verifyWeightUp = false;
      break;
  }
  verifyRunState ++;
}

//******************************************************************************

void abortNextState() {
  if (verbose) Serial.println("abort");
  Serial.print("abortRunState = ");
  Serial.println(abortRunState);
  switch (abortRunState) {
    case  0:
      mainStateMachine.transitionTo(mainNoOp);
      break;

    case  1:
      timeoutTimer.transitionTo(maxTimerNoOp); // crash stop reporting of data if running a process timer
      //    mainStateMachine.immediateTransitionTo(mainNoOp); // crash stop main routine to prevent any further changes
      mainStateMachine.transitionTo(mainNoOp); // crash out of routine.
    case 2:
      stepperIsActive = false;
      mainRunState = 0;
      restart = false;
      testSeq = 0;
      testStatus = 'A';
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      Serial.println("zero");
      break; // open collet to drop cap
    case  3:
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      break;
    case 4:
      homed = false;
      sysTimeout.transitionTo(sysTimerNoOp);
      mainStateMachine.transitionTo(homeStepperState);
      moveSpeed = setTravel;
      headPos = upPos * conversion;
      Serial.println("one");
      break;
    case  5:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = upPos * conversion;
      Serial.println("two");
      break;
    case  6:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      break; // open gripper to discard pen
    case  7:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      horPos = test;
      parameters[0] = test;
      checkRequest = false;
      if (verbose)Serial.print("send to ");
      if (verbose)Serial.println(parameters[0]);
      Serial.println("four");
      break; // move to cap discard
    case  8:
      penIn = false;
      stepperIsActive = false;
      openNest;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      sysTimeout.transitionTo(sysTimerNoOp);
      break;// request nest open and move to nest actuation state
    case 9:
      stepperIsActive = false;
      Serial.println("wfpr");
      mainStateMachine.transitionTo(waitForPenRemove);
      break;
    case 10:
      stepperIsActive = false;
      //    sysTimeout.transitionTo(sysTimerNoOp);
      mainStateMachine.transitionTo(mainNoOp);
      mainRunState = 0;
      abortRunState = -1; // kill any further states
      errorState = 0;
      errorActive = 0;
      sendError(20, errorActive);
      break;
  }
  abortRunState ++;
  while (Serial.available()) Serial.read(); // dump serial data
  Serial.print("next abortstate ");
  Serial.println(abortRunState);
}

//***********************************************************

void startNextState() {
  if (verbose) Serial.println("start");
  Serial.print("startRunState = ");
  Serial.println(startRunState);
  switch (startRunState) {
    case  0:
      penIn = false;
      stepperIsActive = false;
      mainStateMachine.transitionTo(mainNoOp);
      break;
    case  1:
      mainStateMachine.transitionTo(nullState);
      break;
    case 2:
      mainStateMachine.transitionTo(homeStepperState);
      moveSpeed = setTravel;
      headPos = upPos * conversion;
      break;
    case  3:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = close;
      break;// request nest close to test air function
    case  4:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      parameters[0] = test;
      //qqq
      horPos = test;
      //    Serial.println("two");
      break; // move to test
    case  5:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      //    Serial.println("three");
      break; // open collet to drop cap
    case  6:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      openNest;
      //    Serial.println("four");
      break; // close gripper to grab pen
    case 7:
      stepperIsActive = false;
      if (digitalRead(negLoadLimit) == LOW && digitalRead(posLoadLimit) == LOW) { //Only Tare if not on load limit - causes problems otherwise
        mainStateMachine.transitionTo(tare);
      }
      //    Serial.println("five");
      break;
    case  8:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      //    Serial.println("six");
      break;// request nest open and move to nest actuation state
    case 9:
      stepperIsActive = false;
      if (digitalRead(negLoadLimit) == LOW && digitalRead(posLoadLimit) == LOW) { //Only Tare if not on load limit - causes problems otherwise
        mainStateMachine.transitionTo(tare);
      }
      break;
    case 10:
      stepperIsActive = false;
      mainStateMachine.transitionTo(mainNoOp);
      startRunState = -1; // kill any further states
      break;
    case 11:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = upPos * conversion;
      moveSpeed = setTravel;
      break; // move up to top
    case 12:
      stepperIsActive = false;
      mainStateMachine.transitionTo(tare);
      break;
  }
  startRunState ++;
  if (verbose) Serial.print("next startstate ");
  if (verbose) Serial.println(startRunState);
}

//*****************************************************

void mainNextState() {
  switch (mainRunState) {
    case  0:
      stepperIsActive = false;
      mainStateMachine.transitionTo(mainNoOp);
      break;
    case  1:
      stepperIsActive = false;
      mainStateMachine.transitionTo(tare);
      break;
    case  2: // wait for safety circuit to be reset by operator removing hands from light guard
      stepperIsActive = false;
      mainStateMachine.transitionTo(waitForSafety);
      //    balanceMachine.transitionTo(balanceRead);
      break;
    case  3:
      stepperIsActive = false;
      mainStateMachine.transitionTo(startTest);
      //    headMoveTowardTest(); // fire the valves anyway;
      break;
    case  4:// request nest close and move to nest actuation state
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = close;
      sendTestStatus();
      //    mainRunState=17; //temporary to jump to actuate
      break;
    case  5:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      parameters[0] = test;
      //qqq
      horPos = test;
      //    Serial.println("two");
      break; // move to test
    case  6: // open collet to place over cap
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      break;
    case  7:
      mainStateMachine.transitionTo(nullState);
      break;
    case 8:
      mainStateMachine.transitionTo(homeStepperState);
      //    balanceMachine.transitionTo(balanceRead); // just to straighten out readings if spurious data received
      break;
    case  9:// move down to pretrigger position ready to start test
      mainStateMachine.transitionTo(headMoveVer);
      headPos = preCapRemove * conversion;
      moveSpeed = setTravel;
      mainRunState++;
      break;
    case  10:
      stepperIsActive = false;
      mainStateMachine.transitionTo(tare);
      break;
    case  11:  //move down to grab cap at test speed
      sysTimeoutEnd += 10000; // add 10s to timeout
      resetLoad();
      mainStateMachine.transitionTo(lowerToCap);
      headPos = downPos * conversion;
      //    moveSpeed=setTravel;
      moveSpeed = setTest;
      break;
    case 12:
      mainStateMachine.transitionTo(smallMoveUp);
      moveSpeed = 4;
      break;
    case 13:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = close;
      break; // close collet to grab
    case 14:
      resetLoad();
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(removeCap);
      moveSpeed = setRemove;
      headPos = (preCapRemove * conversion) - (extraCapRemove * conversion); // extra added to ensure cap is removed
      break;
    case 15:
      mainStateMachine.transitionTo(nullState);
      break;
    case 16:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 17:
      mainStateMachine.transitionTo(headMoveVer);
      //    messageMachine.transitionTo(messageNoOp);
      headPos = intermedPos * conversion;
      moveSpeed = setTravel;
      //    TravelFlag=true;
      break; // move up to top
    case 18:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      checkRequest = false;
      if (capRemoved && !rejectCap) {
        horPos = discard;
        parameters[0] = discard;
      } //2=discard
      else {
        horPos = reject;
        parameters[0] = reject;
        //      errorState = 18;
        //      errorActive=1;
        //      sendError(errorState,errorActive);//stepper Error
        //      errorActive=0;
        //      sendError(errorState,errorActive);//stepper Error over
        //      errorState=0;
        rejectCap = true;
      }
      break;
    case 19: // dump cap
      {
        stepperIsActive = false;
        mainStateMachine.transitionTo(actuateCollet);
        colletState = open;
        break;
      } // open collet to drop cap
    case 20: // back to test
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      horPos = test;
      parameters[0] = test ;
      break;
    case 21:
      mainStateMachine.transitionTo(nullState);
      break;
    case 22:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 23:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = triggerPos * conversion;
      moveSpeed = setTravel;
      mainRunState++; // skip over next tare as it may distort readings
      break; // move down to pretrigger position raedy to start test
    case 24:
      stepperIsActive = false;
      if (weight > 0) mainStateMachine.transitionTo(tare);
      break;
    case 25:
      resetLoad();
      resetWeight();
      sysTimeoutEnd += 10000; // add 10s to timeout
      sysTimeoutEnd += (long(maxTimeout) * 1000); // add dispense timer onto timeout
      mainStateMachine.transitionTo(ready);
      moveSpeed = setTest;
      break; // set slow speed and turn on messages
    case 26:
      stepperIsActive = false;
      mainStateMachine.transitionTo(waitForDispenseEnd);
      break;
    case 27:
      stepperIsActive = false;
      mainStateMachine.transitionTo(gate); // will bounce on to reset
      break;
    case 28:
      stepperIsActive = false;
      mainStateMachine.transitionTo(dispenseOver);
      break;
    case 29:
      stepperIsActive = false;
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(headMoveHor);
      horPos = discard;
      parameters[0] = discard ;
      break; // move to discard to collect pen
    case 30:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      break; // check gripper is open
    case 31:
      mainStateMachine.transitionTo(nullState);
      break;
    case 32:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 33:
      mainStateMachine.transitionTo(headMoveVer);
      //sendTestStatus();
      headPos = (downPos - 10) * conversion;
      break;
    case 34:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = close;
      break;
    case 35:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      break;// request nest open and move to nest actuation state
    case 36:
      mainStateMachine.transitionTo(nullState);
      break;
    case 37:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 38:
      mainStateMachine.transitionTo(headMoveVer);
      //sendTestStatus();
      headPos = (downPos - 10 - penDrop) * conversion;
      break;
    case 39:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      break;
    case 40:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = close;
      break;// request nest open and move to nest actuation state
    case 41:
      sysTimeoutEnd += 10000; // add 10s to timeout
      stepperIsActive = false;
      mainStateMachine.transitionTo(waitForNeedle);
      break; // wait for N command and respnd with needle true
    case 42:
      stepperIsActive = false;
      mainStateMachine.transitionTo(waitForNeedleReturn);
      break; // wait for n command and respond with needle false
    case 43:
      stepperIsActive = false;
      mainStateMachine.transitionTo(waitForUnclamp);
      //sysTimeout.transitionTo(sysTimerNoOp);
      break; // wait for unclamp choice
    case 44:
      stepperIsActive = false;
      //sysTimeout.transitionTo(sysTimer);
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(headMoveHor);
      horPos = discard;
      parameters[0] = discard ;
      break; // move to discard to collect pen
    case 45:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      break; // check gripper is open
    case 46:
      mainStateMachine.transitionTo(nullState);
      break;
    case 47:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 48:
      mainStateMachine.transitionTo(headMoveVer);
      testSeq = 16;
      sendTestStatus();
      headPos = downPos * conversion;
      break;
    case 49:
      stepperIsActive = false;
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = close;
      break; // close gripper to grab pen
    case 50:
      stepperIsActive = false;
      penIn = false;
      mainStateMachine.transitionTo(actuateNest);
      nestState = open;
      break;// request nest open and move to nest actuation state
    case 51:
      mainStateMachine.transitionTo(nullState);
      break;
    case 52:
      mainStateMachine.transitionTo(nullState);
      break;
    case 53:
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 54:
      mainStateMachine.transitionTo(headMoveVer);
      headPos = upPos * conversion;
      break;
    case 55:
      stepperIsActive = false;
      sendStatus();
      mainStateMachine.transitionTo(headMoveHor);
      parameters[0] = test ;
      horPos = test;
      break; // move across to test position to put pen in outfeed
    case 56:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateCollet);
      colletState = open;
      break; // open collet ready for next use
    case 57:
      stepperIsActive = false;
      sendStatus();
      mainStateMachine.transitionTo(actuateGripper);
      penGripState = open;
      testSeq = 18;
      sendTestStatus();
      break; // open gripper to release
    case 58:
      stepperIsActive = false;
      Serial.print("*x");
      if (digitalReadFast(nestIsOpen) == LOW) Serial.print(0);
      else if (digitalReadFast(nestIsClosed) == LOW) Serial.print(1);
      else Serial.print(2);
      Serial.print(',');
      if (digitalReadFast(penGripperIsOpen) == LOW) Serial.print(0);
      else if (digitalReadFast(penGripperIsClosed) == LOW) Serial.print(1);
      else Serial.print(2);
      Serial.print(',');
      if (colletState == open) Serial.print(0);
      else if (colletState == close) Serial.print(1);
      else Serial.print(2);
      Serial.print(',');
      if (digitalReadFast(stopIsBack) == LOW) Serial.print(0);
      else if (digitalReadFast(stopIsOut) == LOW) Serial.print(1);
      else Serial.print(2);
      Serial.print(',');
      if (digitalReadFast(carriageAtTest) == LOW) Serial.print(0);
      else if (digitalReadFast(carriageAtDiscard) == LOW) Serial.print(1);
      else if (digitalReadFast(carriageAtReject) == LOW) Serial.print(2);
      else Serial.print(3);
      Serial.print(',');
      //      Serial.print(int(stepper1.currentPosition()/conversion));
      //      Serial.print(',');
      if (int(-stepper1.currentPosition() / conversion) == upPos) Serial.print(0);
      else if (int(-stepper1.currentPosition() / conversion) == preCapRemove)Serial.print(1);
      else if (int(-stepper1.currentPosition() / conversion) == triggerPos)Serial.print(2);
      else Serial.print(3);
      Serial.println();
      sysTimeout.transitionTo(sysTimerNoOp);
      mainStateMachine.transitionTo(getReadings);
      break; // send readings to prompt ready for next pen
    case 59:
      mainStateMachine.transitionTo(mainNoOp);
      mainRunState = -1;
      stepperIsActive = false;
      break;

    case 60:
      mainStateMachine.transitionTo(nullState);
      break;
    case 61:
      mainStateMachine.transitionTo(homeStepperState);
      break;
    case 62: // things to do if failed
      penIn = false;
      sysTimeoutEnd += 10000; // add 10s to timeout
      mainStateMachine.transitionTo(headMoveVer);
      headPos = upPos * conversion;
      testSeq = 16;
      sendTestStatus();
      break;
    case 63:
      stepperIsActive = false;
      mainStateMachine.transitionTo(headMoveHor);
      parameters[0] = test ;
      horPos = test;
      break;
    case 64:
      stepperIsActive = false;
      mainStateMachine.transitionTo(actuateNest);
      testSeq = 18;
      //    Serial.println("check");
      sendTestStatus();
      nestState = open;
      sendStatus();
      break;// pen failed, so just open nest
    case 65:
      stepperIsActive = false;
      Serial.println("wfpr");
      sysTimeout.transitionTo(sysTimerNoOp); // end of timeout
      mainStateMachine.transitionTo(waitForPenRemove);
      break;
    case 66:
      mainStateMachine.transitionTo(getReadings);
      break;
    case 67:
      mainStateMachine.transitionTo(mainNoOp);
      //    sysTimeout.transitionTo(sysTimerNoOp);
      mainRunState = -1; // kill any further states
      stepperIsActive = false;
      break;
  }
  //  Serial.print(mainRunState); Serial.println(" state change finished");
  mainRunState++;
  //  delay(1000);
}

unsigned long myMillis() {
  return millis() - MMdelta; // returns time in ms from mmdelta == millis() reset at start of test
}


