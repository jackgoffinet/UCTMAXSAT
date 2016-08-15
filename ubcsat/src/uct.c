/* Class implementing UCTMAXSAT, UCT for MaxSAT
 * Leaf node value estimation is performed by short runs of the UBCSAT SLS algorithms
 *
 * The <varMutable> array defined in ubcsat.h tells which variables are mutable and which
 * are not during the SLS runs: varMutable[varNum] = TRUE or FALSE
 *
 * The <preSat> array defined in ubcsat.h tells which clauses have truth values that
 * are determined by the set of immutable variables: preSat[clauseNum] = TRUE or FALSE
 *
 * UCT-compatible variants of the basic UBCSAT algorithms are defined in mylocal.c
 *
 * See "Monte-Carlo Tree Search for the Maximum Satisfiability Problem" by Jack Goffinet
 * and Raghuram Ramanujan, the 22nd International Conference on the Principles and 
 * Practice of Constraint Programming
 *
 *
 * @author Jack Goffinet
 * @author Raghu Ramanujan
 * July 2015 - August 2016
 */

 
#include "ubcsat.h"

const char sVersion[] = "1.1.0 (Sea to Sky Release)";  // UBCSAT version info

// branching factor
#define BF 2

// arm labels
#define LEFT 0   
#define RIGHT 1
#define BOTH 2

// for leaf node value estimation
#define MIN_REWARD 0.0


/* Data structure for UCT search -- maintained for each node in search tree */
typedef struct uctnode {
  double x[BF]; // reward for each arm (this is what is backed up)
  int n[BF]; // number of times each arm has been played
  UINT32 atom; // atom to branch on at this node
  int nextAtom[BF]; // atoms this node's children branch on
  BOOL closed[BF]; // whether each arm is closed
  int depth;  // node depth
  struct uctnode** children; // node children
} uctnode;

/* SLS Algorithm Enum */
typedef enum {WALKSAT, NOVELTY} sls_type;


/* prototype functions */
double playNode(uctnode *node);
short selectMove(uctnode *node);
double estimateReward();
int getNumUnsat(double reward);
void setBranchingAtom();
void setRootNode();
void printMemoryError();
uctnode *getNewNode(uctnode *parent, int armNum);
void createChildren(uctnode *node);
void freeNode(uctnode *node);
void ubcsatsetup(int argc, char *argv[]);
int ubcsatrun();
void ubcsatcleanup();
void setMutable();
void setPreSat();
void printParams();
void printUsageError();
int runUCT();
int runUCTtimed();
void ALARMhandler(int sig);
void performRuns();


/* PARAMS */
int numRuns = 10;
int numIterations = 2000; // number of iterations of UCT to run
double C = 0.02; // exploration bias parameter for UCT
int maxFlips = 500; // upper bound of the number of flips in the SLS playout
double p = 0.0; // noise parameter for SLS algorithm
sls_type slsAlg = WALKSAT; // SLS algorithm used for leaf node value estimation
char *filename; // .cnf filename
BOOL timed = FALSE; // whether each run has a time limit
int runTimeout = 15; // run timeout in seconds -- only applies if timed == TRUE

/* GLOBAL VARIABLES */
int depthLimit; // maximum depth a node may have
uctnode* root; // pointer to root node of UCT search tree
UINT32 nextBranchingAtom; // the next atom to branch on given the current formula
BOOL timeFlag; // used for timeouts
clock_t start, stop; // used for timeouts
BOOL clockStopped; // used for timeouts
double bestReward;
double bestRewardAtTimeout;
int runBestNumFalse;
int iterationNum;


/* Main UCT Method -- Plays the selected node */
double playNode(uctnode *node) {
  double reward;
  short armPlayed;
  
  // Set this node's variable to be immutable
  varMutable[node->atom] = FALSE;
  
  // If neither arm has been played, play them both
  if (node->n[LEFT]==0) {
    node->n[LEFT] = node->n[RIGHT] = 1;
    // play the left arm
    aVarValue[node->atom] = LEFT;
    node->x[LEFT] = estimateReward();
    if (closedFlag) {
      closedFlag=FALSE;
      node->closed[LEFT]=TRUE;
    }
    else {
      node->nextAtom[LEFT] = nextBranchingAtom;
    }
    // then play the right arm
    aVarValue[node->atom] = RIGHT;
    node->x[RIGHT] = estimateReward();
    if (closedFlag) {
      closedFlag=FALSE;
      node->closed[RIGHT]=TRUE;
    }
    else  {
      node->nextAtom[RIGHT] = nextBranchingAtom;
    }
    reward = (node->x[LEFT]+node->x[RIGHT])/2.0;
    armPlayed = BOTH;
    // If the depth limit has been reached, close both arms
    if (node->depth >= depthLimit) {
      node->closed[LEFT] = node->closed[RIGHT] = TRUE;
    }
  }
  
  // If the left arm is closed, play the right
  else if (node->closed[LEFT]) {
    node->n[RIGHT]++;
    aVarValue[node->atom] = RIGHT;
    if (!(node->children)) {
      createChildren(node);
    }
    reward = playNode(node->children[RIGHT]);
    node->x[RIGHT]+=(reward-node->x[RIGHT])/node->n[RIGHT];
    armPlayed = RIGHT;
  }
  
  // If the right arm is closed, play the left
  else if (node->closed[RIGHT]) {
    node->n[LEFT]++;
    aVarValue[node->atom] = LEFT;
    if (!(node->children)) {
      createChildren(node);
    }
    reward = playNode(node->children[LEFT]);
    node->x[LEFT]+=(reward-node->x[LEFT])/node->n[LEFT];
    armPlayed = LEFT;
  }
  
  // Otherwise, play the arm that maximizes its UCB1 score
  else {
    armPlayed = selectMove(node);
    node->n[armPlayed]++;
    aVarValue[node->atom] = armPlayed;
    if (!(node->children)) {
      createChildren(node);
    }
    reward = playNode(node->children[armPlayed]);
    node->x[armPlayed]+=(reward-node->x[armPlayed])/node->n[armPlayed];
  }


  // Then propagate the closed nodes upwards to the root node
  switch (armPlayed) {
      
  case (LEFT):
    if (node->children[LEFT]->closed[LEFT] && node->children[LEFT]->closed[RIGHT])
      node->closed[LEFT] = TRUE;
    break;
          
  case (RIGHT):
    if (node->children[RIGHT]->closed[LEFT] && node->children[RIGHT]->closed[RIGHT])
      node->closed[RIGHT] = TRUE;
    break;

  }
  // Finally, return the reward to propagate it up to the root
  return reward;
}


/* Subroutine in UCT search -- given a node, it decides which child UCT should expand */
short selectMove(uctnode *node) {
  double scoreL, scoreR;
  
  //Calculate the UCB1 scores for the two arms
  scoreL = node->x[LEFT];
  scoreL += C*sqrt(log(node->n[LEFT]+node->n[RIGHT])/ (double) node->n[LEFT]);
  scoreR = node->x[RIGHT];
  scoreR += C*sqrt(log(node->n[LEFT]+node->n[RIGHT])/ (double) node->n[RIGHT]);
  //If they are equal, pick an arm uniformly at random
  if (scoreL==scoreR) {
    return RandomInt(BF);
  }
  //Otherwise, pick the arm with the larger score
  return (scoreR>scoreL);
}


/* Estimates the value of a leaf node by performing SLS */
double estimateReward() {
  double reward;
  
  // First update which clauses are pre-satisfied or pre-unsatisfied
  setPreSat();
  // Then perform SLS using a UBCSAT SLS algorithm ...
  reward = (double) (iNumClauses-ubcsatrun()) / (double) iNumClauses;
  // and take the reward to be the portion of satisfied clauses squared
  reward *= reward;
  // Then determine which atom to branch on next
  if (!closedFlag) {
    setBranchingAtom();
  }
  
  bestReward = (reward>bestReward) ? reward : bestReward;
  return reward;
}


/* Returns the number of unsat clauses given a UCT reward */
int getNumUnsat(double reward) {
  return (int) rint(iNumClauses - iNumClauses*sqrt(reward));
}


/* Sets the next variable to branch on given the current formula.
 * Branching heuristic: A0 */
void setBranchingAtom() {
    UINT32 j, k;
  int bestScore;
  UINT32 bestVars[iNumVars];
  int numBest = 0;
  int varScores[iNumVars+1];
  
  for (j=1; j<=iNumVars; j++) {
    varScores[j]=0;
  }
  
  // Collect the variable scores
  for (j=0; j<iNumClauses; j++) {
    if (preSat[j]) continue; // don't consider preSat clauses
    for (k=0;k<aClauseLen[j];k++) {
      varScores[GetVar(j,k)]++;
    }
  }
  
  // Search for the best score, break ties uniformly at random
  bestScore = -1;
  
  for (j=1; j<=iNumVars; j++) {
    if (!varMutable[j]) continue;
    
    if (varScores[j]>bestScore) {
      bestScore = varScores[j];
      bestVars[0] = j;
      numBest = 1;
    }
    else if (varScores[j]==bestScore) {
      bestVars[numBest++]=j;
    }
  }
  
  if (numBest==0) {
    nextBranchingAtom=0;
  }
  else {
    nextBranchingAtom = bestVars[RandomInt(numBest)];
  }
  
}


/* Sets the root node of the UCT search tree */
void setRootNode() {
  root = malloc(sizeof(uctnode));
  if (!root) printMemoryError();
  root->depth = 0;
  root->x[LEFT] = root->x[RIGHT] = MIN_REWARD;
  root->n[LEFT] = root->n[RIGHT] = 0;
  root->closed[LEFT] = root->closed[RIGHT] = FALSE;
  root->children = NULL;
  setPreSat();
  setBranchingAtom();
  root->atom = nextBranchingAtom;
}


/* Returns a new node */
uctnode *getNewNode(uctnode *parent, int armNum) {
  uctnode *temp; 
  temp = malloc(sizeof(uctnode));
  if (!temp) printMemoryError();
  temp->depth = (parent->depth+1);
  temp->x[LEFT] = temp->x[RIGHT] = MIN_REWARD;
  temp->n[LEFT] = temp->n[RIGHT] = 0;
  temp->closed[LEFT] = temp->closed[RIGHT] = FALSE;
  temp->atom = parent->nextAtom[armNum];
  temp->children = NULL;
  return temp;
}


/* Creates child nodes for a given node */
void createChildren(uctnode *node) {
  int i;
  node->children = malloc(BF * sizeof(uctnode*));
  if (!node->children) printMemoryError();
  for (i=0; i<BF; i++) {
    node->children[i] = getNewNode(node, i);
  }
}


/* Frees the memory of the given node and its children */
void freeNode(uctnode *node) {
  if (node->children) {
    // Free the left child if it exists
    if (node->children[LEFT]) {
      freeNode(node->children[LEFT]);
    }
    // Free the right child if it exists
    if (node->children[RIGHT]) {
      freeNode(node->children[RIGHT]);
    }
  }
  free(node);
}


/* UBCSAT sets up its data structures */
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


/* UBCSAT performs an SLS run, returns the best number of unsat clauses found */
int ubcsatrun() {
  
  int j;
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
      
      if (iBestNumFalse<runBestNumFalse) {
        for (j=1; j<=iNumVars; j++) {
          bestSoln[j]=aVarValue[j];
        }
      }
    }
      
    RunProcedures(PostStep);

    RunProcedures(StepCalculations);

    RunProcedures(CheckTerminate);
  } 

  StopRunClock();

  RunProcedures(RunCalculations);
    
  RunProcedures(PostRun);
   
  return iBestNumFalse;
}


/* UBCSAT cleans up, creates reports */
void ubcsatcleanup() {
  StopTotalClock();
  RunProcedures(FinalCalculations);
  RunProcedures(FinalReports);
  CleanExit();
}


/* Sets <varMutable> array */
void setMutable() {
  int i;
  for (i=0; i<=iNumVars; i++) {
    varMutable[i] = TRUE;
  }
}


/* Sets the <preSat> array */
void setPreSat() {
  // A clause is pre-satisfied if it contains a true immutable literal or all literals
  // are immutable and false.
  
  UINT32 j, k;
  LITTYPE *pLit;
  BOOL clausePresat;
  
  closedFlag = TRUE;
  
  for (j=0; j<iNumClauses; j++) {
    if (alwaysSat[j]) {
      preSat[j] = TRUE;
      continue;
    }
    clausePresat = TRUE;
    pLit = pClauseLits[j];
    
    for (k=0; k<aClauseLen[j]; k++) {
      if (varMutable[GetVarFromLit(*pLit)]) {
        clausePresat = FALSE;
      }
      else if (IsLitTrue(*pLit)) {
        clausePresat = TRUE;
        break;
      }
      pLit++;
    }

    if (clausePresat) {
      preSat[j] = TRUE;
    }
    else {
      preSat[j] = FALSE;
      closedFlag = FALSE;
    }
  }
}


/* Sets the <alwaysSat> array */
void setAlwaysSat() {
  // alwaysSat[j] <-> clause j contains a literal and its negation
  UINT32 j,k,l;
  UINT32 var;
  LITTYPE *pLit, *pLit2;
  BOOL breakFlag = FALSE;
  
  for (j=0; j<iNumClauses; j++) {
    alwaysSat[j] = FALSE;
    pLit = pClauseLits[j];
    
    for (k=0; k<aClauseLen[j]; k++) {
      if (GetLitSign(*pLit)) {
        var=GetVarFromLit(*pLit);
        pLit2=pLit;
        for (l=k+1; l<aClauseLen[j]; l++) {
          if (GetVarFromLit(*pLit2) == var && !GetLitSign(*pLit2)) {
            alwaysSat[j] = TRUE;
            breakFlag = TRUE;
            break;
          }
          pLit2++;
        }
        if (breakFlag) {
          breakFlag = FALSE;
          break;
        }
      }
      pLit++;
    }
    
  }
}


void printParams() {
  printf("Parameters:\n");
  printf("Instance: %s \n", filename);
  printf("UCT runs: %d\n", numRuns);
  printf("UCT iterations per run: %d\n", numIterations);
  printf("UCT C param: %f\n", C);
  printf("UCT branching heuristic: A0\n");
  printf("SLS algorithm: ");
  if (slsAlg==WALKSAT)
    printf("WalkSAT\n");
  else if (slsAlg==NOVELTY)
    printf("Novelty\n");
  printf("SLS max flips: %d\n", maxFlips);
  printf("Total SLS flips per run: %d\n", 2*maxFlips*numIterations);
  printf("SLS noise param: %f\n", p);
  printf("Bandit Algorithm: UCB1\n");
  if (timed) printf("Timeout: %d (s)\n", runTimeout);
  else printf("Timeout: NA\n");
  fflush(stdout);
}


void printMemoryError() {
  printf("\nUnable to allocate memory!\n");
  fflush(stdout);
  exit(1);
}


void printUsageError() {
  printf("\nusage: uct -f filename [-a INT] [-r INT] [-i INT] [-g INT] [-c DOUBLE] \n");
  printf("[-p DOUBLE] [-m INT] [-n DOUBLE] [-b INT] [-t INT] [-o INT]\n\n");
  printf("-flag : <description> (= <default value>)\n");
  printf("-a : SLS algorithm (= WalkSAT) \n");
  printf("    WalkSAT (0) \n");
  printf("    Novelty (1) \n");
  printf("-f : .cnf filename \n");
  printf("-r : number of uct runs (=10) \n");
  printf("-i : maximum number of uct iterations per run (=2000) \n");
  printf("-c : UCT exploration/exploitation parameter (=0.02) \n");
  printf("-m : max flips for each sls run (=500) \n");
  printf("-n : noise param for each sls run (=0.0) \n");
  printf("-t : run timeout in seconds (NA). Iterations should be set accordingly \n\n");
  fflush(stdout);
  exit(1);
}


/* Performs a single untimed UCT run and returns the best number of unsat clauses found */
int runUCT() {
  int i;
  depthLimit = iNumVars-1;
  
  bestReward=MIN_REWARD;
  
  clockStopped = FALSE;
  start = clock();
  /* all variables begin as mutable */
  setMutable();
  /* free the previous tree from memory and initialize a new root node */
  if (root) {
    freeNode(root);
  }
  setRootNode();
  for (i=0; i<numIterations; i++) {
    setMutable();
    playNode(root); 
  }
  fflush(stdout);
  
  return getNumUnsat(bestReward);
}

/* Performs a single timed UCT run and returns the best number of unsat clauses found */
int runUCTtimed() {
  int i=0;
  
  depthLimit = iNumVars-1;
  bestReward=MIN_REWARD;
  iterationNum = 0;
  
  // Install the timeout handler and set the alarm
  signal(SIGALRM, ALARMhandler);
  timeFlag = TRUE;
  alarm(runTimeout);
  
  clockStopped=FALSE;
  start = clock();
  
  // All variables begin as mutable
  setMutable();

  // Free the previous tree from memory and initialize a new root node
  if (root)
    freeNode(root);
  setRootNode();
  
  while (timeFlag) {
    iterationNum++;
    setMutable();
    playNode(root); 
    if (++i == numIterations) {
      printf("Fatal Error: increase number of iterations!\n");
      fflush(stdout);
      exit(1);
    }
  }
  
  return getNumUnsat(bestRewardAtTimeout);
}


/* Handles timeout signals */
void  ALARMhandler(int sig)
{
  bestRewardAtTimeout = bestReward;
  timeFlag = FALSE;
  signal(SIGALRM, SIG_IGN);
}


/* Performs UCT runs and prints the results to stdout */
void performRuns() {
  int i,j;
  int numUnsat[numRuns];
  
  if (iNumVars>MAX_NUM_VARS || iNumClauses>MAX_NUM_CLAUSES) {
    printf("Fatal Error: increase size of MAX_NUM_VARS or MAX_NUM_CLAUSES\n");
    fflush(stdout);
    exit(1);
  }
  
  setAlwaysSat();
  
  for (i=0; i<numRuns; i++) { 
    for (j=1; j<=iNumVars; j++) {
      bestSoln[j]=RandomInt(2);
    }
    runBestNumFalse = MAX_NUM_CLAUSES+1;
    if (timed) {
      numUnsat[i] = runUCTtimed(); 
    }
    else numUnsat[i] = runUCT();
  }
  
  ubcsatcleanup();
  
  // print results to stdout
  printf("\n*** Best Num Unsat ***\n");
  for (i=0; i<numRuns; i++) {
    printf("Run %d: %d\n", i, numUnsat[i]);
  }
  printf("\n");
  printf("Total Time Elapsed: %f\n\n", fTotalTime);
  printParams();
}



#define COMMAND_LN_LEN 300
#define MAX_ARG_LEN 30
#define MAX_NUM_ARGS 20

/* Mostly command line parsing here */
int main(int argc, char **argv) {
  extern char *optarg;
  extern int optind;
  int i, option;
  BOOL fflag = TRUE;
  char runsstr[MAX_ARG_LEN];
  char cutoffstr[MAX_ARG_LEN];
  char noisestr[MAX_ARG_LEN];
  
  int ubcargc;
  char **ubcargv;
  char ubccommandline[COMMAND_LN_LEN];
  char *token;
  
  while ((option = getopt(argc, argv, "f:c:i:m:r:n:a:t:")) != -1) {
    
    switch (option) {
    
    case 'a':
      if (atoi(optarg)==0)
        slsAlg = WALKSAT;
      else if (atoi(optarg)==1)
        slsAlg = NOVELTY;
      else {
        printf("Fatal Error: Invalid SLS algorithm!");
        printUsageError();
      }
      break;
    
    case 'f':
      fflag = FALSE;
      filename = optarg;
      break;
    	
    case 'r':
      numRuns = atoi(optarg);
      break;
    	
    case 'c':
      C = (double) atof(optarg);
      break;
    	
    case 'i':
      numIterations = atoi(optarg);
      break;
    	
    case 'm':
      maxFlips = atoi(optarg);
      break;
    	
    case 'n':
      p = (double) atof(optarg);
      break;
      
    case 't':
      runTimeout = atoi(optarg);
      timed = TRUE;
      break;
    	
    case '?':
      if (optopt == 'c')
	    fprintf (stderr, "Option -%c requires an argument.\n", optopt);
      else
	    fprintf (stderr,
		 "Unknown option character `\\x%x'.\n",
		 optopt);
      return 1;
    	
    default:
      printf("\nFatal Error: option %c is invalid!\n", option);
      printUsageError();
      return 1;
    }  
  }
  
  if (fflag) {
    printf("\nFatal Error: filename must be specified!\n");
    printUsageError();
  }
   
  
  ubcargv = (char**)malloc(MAX_NUM_ARGS*sizeof(char*));
  for (i=0; i<MAX_NUM_ARGS; i++) {
    ubcargv[i] = malloc(MAX_NUM_ARGS*sizeof(char));
  }
  
  strcpy(ubccommandline, "./ubcsat -alg ");
  if (slsAlg==WALKSAT)
    strcat(ubccommandline, "walksat ");
  else if (slsAlg==NOVELTY)
    strcat(ubccommandline, "novelty ");
  
  strcat(ubccommandline, "-v uct -runs ");
  sprintf(runsstr, "%d ", 2*numIterations*numRuns);
  strcat(ubccommandline, runsstr);
  
  strcat(ubccommandline, "-cutoff ");
  sprintf(cutoffstr, "%d ", maxFlips);
  strcat(ubccommandline, cutoffstr);
  
  if (slsAlg==WALKSAT)
    strcat(ubccommandline, "-wp ");
  else if (slsAlg==NOVELTY)
    strcat(ubccommandline, "-novnoise ");
  sprintf(noisestr, "%f ", p);
  strcat(ubccommandline, noisestr);
  
  strcat(ubccommandline, "-i ");
  strcat(ubccommandline, filename);

  strcat(ubccommandline, " -r stats null -r out null ");
  
  token = strtok(ubccommandline, " ");

  ubcargc = 0;
  i=0;
  while (token) {
    ubcargc++;
    strcpy(ubcargv[i], token);
    token = strtok(NULL, " ");
    i++;
  } 
  
  // Run UCT
  ubcsatsetup(ubcargc,ubcargv);
  
  performRuns();

  return 0;
}