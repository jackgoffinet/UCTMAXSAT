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




#ifndef UBCSAT

#define UBCSAT

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <signal.h>
#include <sys/signal.h>


#include "ubcsat-limits.h"
#include "ubcsat-types.h"

#include "ubcsat-lit.h"
#include "ubcsat-mem.h"
#include "ubcsat-time.h"
#include "ubcsat-io.h"
#include "ubcsat-internal.h"
#include "ubcsat-globals.h"
#include "ubcsat-triggers.h"

#include "algorithms.h"
#include "reports.h"

#include "mylocal.h"

/* for UCT variants */
#define MAX_NUM_VARS 2500 
#define MAX_NUM_CLAUSES 10000
short varMutable[MAX_NUM_VARS+1];
short preSat[MAX_NUM_CLAUSES];
short alwaysSat[MAX_NUM_CLAUSES];
short bPresatTerminate;
BOOL closedFlag; // used for closing nodes

int bestSoln[MAX_NUM_VARS+1];

#endif

