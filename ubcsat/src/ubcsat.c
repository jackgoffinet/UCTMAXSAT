/*

      ##  ##  #####    #####   $$$$$   $$$$   $$$$$$    
      ##  ##  ##  ##  ##      $$      $$  $$    $$      
      ##  ##  #####   ##       $$$$   $$$$$$    $$      
      ##  ##  ##  ##  ##          $$  $$  $$    $$      
       ####   #####    #####  $$$$$   $$  $$    $$      
  ======================================================
  SLS SAT Solver from The University of British Columbia
  ======================================================
  ...Developed by Dave Tompkins (davet [@] cs.ubc.ca)...
  ------------------------------------------------------
  .......consult legal.txt for legal information........
  ......consult revisions.txt for revision history......
  ------------------------------------------------------
  ... project website: http://www.satlib.org/ubcsat ....
  ------------------------------------------------------
  .....e-mail ubcsat-help [@] cs.ubc.ca for support.....
  ------------------------------------------------------

*/

#include "ubcsat.h"

const char sVersion[] = "1.1.0 (Sea to Sky Release)";


void ubcsatsetup(int argc, char *argv[]) {  
  InitSeed();

  SetupUBCSAT();

  AddAlgorithms();
  AddParameters();
  AddReports();
  AddDataTriggers();
  AddReportTriggers();

  AddLocal();
  
  ParseAllParameters(argc,argv);

  ActivateAlgorithmTriggers();
  ActivateReportTriggers();

  RandomSeed(iSeed);

  RunProcedures(PostParameters);

  RunProcedures(ReadInInstance);

  RunProcedures(PostRead);

  RunProcedures(CreateData);
  RunProcedures(CreateStateInfo);
  
  iRun = 0;
  iNumSolutionsFound = 0;
  bTerminateAllRuns = FALSE;

  RunProcedures(PreStart);

  StartTotalClock();
  
  return;
}


int ubcsatrun() {

  iRun++;
  iStep = 0;
  bSolutionFound = FALSE;
  bTerminateRun = FALSE;
  bRestart = TRUE;

  RunProcedures(PreRun);
  StartRunClock();
    
  while ((iStep < iCutoff) && (! bSolutionFound) && (! bTerminateRun)) {

      iStep++;
      iFlipCandidate = 0;

      RunProcedures(PreStep);
      RunProcedures(CheckRestart);

      if (bRestart) {
        RunProcedures(PreInit);
        RunProcedures(InitData);
        RunProcedures(InitStateInfo);
        RunProcedures(PostInit);
        bRestart = FALSE;
      } else {
        RunProcedures(ChooseCandidate);
        RunProcedures(PreFlip);
        RunProcedures(FlipCandidate);
        RunProcedures(UpdateStateInfo);
        RunProcedures(PostFlip);
      }
      
      RunProcedures(PostStep);

      RunProcedures(StepCalculations);

      RunProcedures(CheckTerminate);
    }

  StopRunClock();

  RunProcedures(RunCalculations);
    
  RunProcedures(PostRun);

  if (bSolutionFound) {
    iNumSolutionsFound++;
    if (iNumSolutionsFound == iFind) {
      bTerminateAllRuns = TRUE;
    }
  }
  return 0;
}
  
  
int ubcsatcleanup() {

  StopTotalClock();

  RunProcedures(FinalCalculations);

  RunProcedures(FinalReports);

  CleanExit();

  return(0);
  
}


#ifndef ALTERNATEMAIN

int main(int argc, char *argv[]) {
  int i;  
  ubcsatsetup(argc, argv);
  for (i=0; i<iNumRuns; i++) {
    if (ubcsatrun()) {
      printf("Run %d failed\n",  i);
      fflush(stdout);
      return 1;
    }
  }
  return ubcsatcleanup();
}

#endif


