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

/*  

  AddLocal() is here for you to add your own algorithms, reports, etc... 
  
  this will help to avoid your work being 'clobbered' by future releases of ubcsat
  
  if you've added some features you'd like to see included in the ubcsat package,
  then please send us your files!

*/

void AddWalkSatTabuNoNull();
void PickWalkSatTabuNoNull();

void AddWalkSatUCT();
void PickWalkSatUCT();

void AddRNoveltyUCT();
void PickRNoveltyUCT();
void PickRNoveltyCoreUCT();

void AddNoveltyUCT();
void PickNoveltyUCT();

void AddAgeStat();
void UpdateCurVarAge();


void AddLocal() {

  AddWalkSatUCT();
  AddNoveltyUCT();
  AddWalkSatTabuNoNull();
  AddAgeStat();

}


/***** WALKSAT for UCT *****/

void AddWalkSatUCT() {

  ALGORITHM *pCurAlg;

  pCurAlg = CreateAlgorithm(
    "walksat","uct",FALSE,
    "WALKSAT-UCT: Walksat with a set of immutable variables",
    "Selman, Kautz, Cohen [AAAI 94] (modified)",
    "PickWalkSatUCT",
    "DefaultProceduresUCT,Flip+FalseClauseList,BestFalse",
    "default",
    "default");
  
  
  CopyParameters(pCurAlg,"walksat","",FALSE);

  CreateTrigger("PickWalkSatUCT",
    ChooseCandidate,
    PickWalkSatUCT,
    "",
    "");

}

void PickWalkSatUCT() {
 
  UINT32 i;
  UINT32 j;
  SINT32 iScore;
  UINT32 iClause;
  UINT32 iClauseLen;
  UINT32 iVar;
  LITTYPE *pLit;
  UINT32 *pClause;
  LITTYPE litPick;
  UINT32 iNumOcc;
  UINT32 falseClauses[iNumClauses]; //doesn't include preSat clauses
  int numFalseClauses = 0;

  iNumCandidates = 0;
  iBestScore = iNumClauses;
  
  // If there are unsat clauses ...
  if (iNumFalse) {
  
    // construct <falseClauses>
    for (j=0; j<iNumClauses; j++) {
      if (!preSat[j] && aNumTrueLit[j]==0) {
        falseClauses[numFalseClauses++] = j;
      }
    }
    
    // If there are no false clauses that aren't preSat, terminate the run
    if (!numFalseClauses) {
      bTerminateRun = TRUE;
      closedFlag = TRUE;
      iFlipCandidate = 0;
      return;
    }
    
    // Otherwise, select a false clause uniformly at random from <falseClauses>
    iClause = falseClauses[RandomInt(numFalseClauses)];
    iClauseLen = aClauseLen[iClause];
    
  }
  
  // Otherwise, there are no unsat clauses (shouldn't get here for unsat instances)
  else {
    bTerminateRun = TRUE;
    closedFlag = TRUE;
    iFlipCandidate = 0;
    return;
  }


  // Find a literal to flip
  pLit = pClauseLits[iClause];

  for (j=0;j<iClauseLen;j++) {
    // for WalkSAT variants, it's faster to calculate the score for each literal than to
	// cache the values. Note that in this case, score is just the breakcount[]
 
    iVar = GetVarFromLit(*pLit);
    
    // Don't consider variables that are immutable
    if (!varMutable[iVar]) {
      pLit++;
      continue;
    }
    
    iScore = 0;
    
    iNumOcc = aNumLitOcc[GetNegatedLit(*pLit)];
    pClause = pLitClause[GetNegatedLit(*pLit)];
    
    for (i=0;i<iNumOcc;i++) {
      if (aNumTrueLit[*pClause]==1) {
        iScore++;
      }
      pClause++;
    }

    // build candidate list of best vars
    if (iScore <= iBestScore) {
      if (iScore < iBestScore) {
        iNumCandidates=0;
        iBestScore = iScore;
      }
      aCandidateList[iNumCandidates++] = iVar;
    }

    pLit++;
  }

  // if the best step is a worsening step, then with probability (iWp) randomly choose the
  // literal to flip
  if (iBestScore > 0) {
    if (RandomProb(iWp)) {
      litPick = pClauseLits[iClause][RandomInt(iClauseLen)];
      iFlipCandidate = GetVarFromLit(litPick);
      if (!varMutable[iFlipCandidate]) {
        iFlipCandidate=0;
      }
      return;
    }
  }

  // select flip candidate uniformly from candidate list
  if (iNumCandidates > 1) {
    iFlipCandidate = aCandidateList[RandomInt(iNumCandidates)];
  } else {
    iFlipCandidate = aCandidateList[0];
  }
}



/***** NOVELTY for UCT *****/

void AddNoveltyUCT() {
  
  ALGORITHM *pCurAlg;

  pCurAlg = CreateAlgorithm(
    "novelty","uct",FALSE,
    "Novelty-UCT: Novelty with a set of immutable variables",
    "McAllester, Selman, Kautz [AAAI 97] (modified)",
    "PickNoveltyUCT",
    "DefaultProceduresUCT,Flip+FalseClauseList,VarLastChange,BestFalse",
    "default",
    "default");
  
  CopyParameters(pCurAlg,"novelty","",FALSE);

  CreateTrigger("PickNoveltyUCT",
    ChooseCandidate,
    PickNoveltyUCT,
    "",
    "");
}


void PickNoveltyUCT() {
  
  UINT32 i;
  UINT32 j;
  SINT32 iScore;
  UINT32 iClause;
  UINT32 iClauseLen;
  LITTYPE *pLit;
  UINT32 *pClause;
  UINT32 iNumOcc;
  UINT32 iVar;
  UINT32 iYoungestVar;
  SINT32 iSecondBestScore;
  UINT32 iBestVar=0;
  UINT32 iSecondBestVar=0;
  UINT32 falseClauses[iNumClauses];
  int numFalseClauses = 0;

  iBestScore = iNumClauses;
  iSecondBestScore = iNumClauses;

  // select an unsatisfied clause uniformly at random
  if (iNumFalse) {
    // construct <falseClauses>
    for (j=0; j<iNumClauses; j++) {
      if (!preSat[j] && aNumTrueLit[j]==0)
        falseClauses[numFalseClauses++] = j;
    }
    
    // If there are no false clauses that aren't preSat, terminate the run
    if (!numFalseClauses) {
      bTerminateRun = TRUE;
      closedFlag = TRUE;
      iFlipCandidate = 0;
      return;
    }
      
    iClause = falseClauses[RandomInt(numFalseClauses)];
    iClauseLen = aClauseLen[iClause];
  } else { // shouldn't get here for unsat instances
    iFlipCandidate = 0;
    closedFlag = TRUE;
    return;
  }

  pLit = pClauseLits[iClause];

  iYoungestVar = GetVarFromLit(*pLit);

  // for each literal in the clause
  for (j=0;j<iClauseLen;j++) {
  
    iVar = GetVarFromLit(*pLit);
    if (!varMutable[iVar]) {
      pLit++;
      continue;
    }
    iScore = 0;
    
    iNumOcc = aNumLitOcc[*pLit];
    pClause = pLitClause[*pLit];

    // for each appearance of the literal in a false clause, decrease score by one 
    // (increase makecount)
    for (i=0;i<iNumOcc;i++) {
      if (aNumTrueLit[*pClause]==0) {
        iScore--;
      }
      pClause++;
    }

    // for each appearance of the negated literal in a critially satisfied clause,
    // increase score by one (increase breakcount)
    iNumOcc = aNumLitOcc[GetNegatedLit(*pLit)];
    pClause = pLitClause[GetNegatedLit(*pLit)];
    
    for (i=0;i<iNumOcc;i++) {
      if (aNumTrueLit[*pClause]==1) {
        iScore++;
      }
      pClause++;
    }

    // keep track of which literal was the 'youngest'
    if (aVarLastChange[iVar] > aVarLastChange[iYoungestVar]) {
      iYoungestVar = iVar;
    }

    // keep track of the 'best' and the 'second best' variables, breaking ties by 
    // selecting the younger variables
    if ((iScore < iBestScore) || ((iScore == iBestScore) && (aVarLastChange[iVar] < aVarLastChange[iBestVar]))) {
      iSecondBestVar = iBestVar;
      iBestVar = iVar;
      iSecondBestScore = iBestScore;
      iBestScore = iScore;
    } else if ((iScore < iSecondBestScore) || ((iScore == iSecondBestScore) && (aVarLastChange[iVar] < aVarLastChange[iSecondBestVar]))) {
      iSecondBestVar = iVar;
      iSecondBestScore = iScore;
    }

    pLit++;
  }
  
  iFlipCandidate = iBestVar;

  // if the best is the youngest, select it
  if ((iFlipCandidate != iYoungestVar) || !varMutable[iSecondBestVar]) {
    return;
  }

  // otherwise, choose the second best with probability (novnoise)
  if (RandomProb(iNovNoise)) {
    iFlipCandidate = iSecondBestVar;
  }


}


/***** EXAMPLE 1: Adding a new algorithm variant *****/

void AddWalkSatTabuNoNull() {

  ALGORITHM *pCurAlg;

  pCurAlg = CreateAlgorithm(
    "walksat-tabu","nonull",FALSE,                          /* algorithm name, variant, non-weighted */
    "WALKSAT-TABU-NoNull: WALKSAT-TABU without null flips", /* algorithm description */
    "McAllester, Selman, Kautz [AAAI 97] (modified)",       /* author information */
    "PickWalkSatTabuNoNull",                                /* Heuristic Triggers */
    "",                                                     /* Data Triggers (blank because we'll inherit */
    "default,agemean",                                      /* default parameter (columns) for output (-r out) -- will demo example 2*/
    "default");                                             /* default parameter (stats) for statistics (-r stats) */
  
  InheritDataTriggers(pCurAlg,"walksat-tabu","",FALSE);     /* Copy the data triggers from walksat-tabu */
  
  CopyParameters(pCurAlg,"walksat-tabu","",FALSE);          /* Copy the command line parameters from walksat-tabu */

  CreateTrigger("PickWalkSatTabuNoNull",                    /* Add the new trigger for the heuristic */
    ChooseCandidate,                                        /* Occurs at the event point for choosing flip candidates */
    PickWalkSatTabuNoNull,                                  /* the corresponding function name */
    "",                                                     /* no dependency triggers */
    "");                                                    /* no deactivation triggers */

}

void PickWalkSatTabuNoNull() {
  
  LITTYPE litPick;
  UINT32 iClauseLitNo;

  PickWalkSatTabu();                                              /* Perform regular walksat-tabu step */

  if (iFlipCandidate==0) {                                        /* if null flip then */
    iClauseLitNo = RandomInt(aClauseLen[iWalkSATTabuClause]);     /* choose a # from [0 .. clausesize-1] */
    litPick = pClauseLits[iWalkSATTabuClause][iClauseLitNo];      /* select the literal from the clause */
    iFlipCandidate = GetVarFromLit(litPick);                      /* set iFlipCandidate to the corresponding variable */
  }
}

/***** EXAMPLE 2: Adding a statistic *****/

UINT32 iCurVarAge;    /* variable to store current variable age */

void AddAgeStat() {
                                                                  /* note that UInt refers to the data type of the _source_ */
  AddColumnUInt("agemean",                                        /* name of the column... as in: -r out stdout default,agemean */
    "Mean age of variables when flipped",                         /* description */
    "   Mean",                                                    /* the next 3 columns are the column headers */
    " Age of",                                                    /* they should be the same width as each other */
    "   Vars",                                                    /* and the same width as the.... */
    "%7.1f",                                                      /* format string: Note %f (float) because it's a mean value */
    &iCurVarAge,                                                  /* pointer to location of statistic */
    "UpdateCurVarAge",                                            /* trigger to be activated */
    ColTypeMean);                                                 /* find the mean over all search steps */

  CreateTrigger("UpdateCurVarAge",                                /* add the trigger to update the value */
    PreFlip,
    UpdateCurVarAge,
    "VarLastChange",
    "");

  AddStatCol("agemean",                                           /* column statistic for the -r stats report */
    "MeanAge",                                                    /* prefix for the report */
    "mean+cv+median+min+max",                                     /* default stats to show */
    FALSE);                                                       /* specify TRUE to sort by the steps column (for median, etc.) instead of this column */

}

void UpdateCurVarAge() {
  iCurVarAge = iStep - aVarLastChange[iFlipCandidate];
}

