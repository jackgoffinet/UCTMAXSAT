#include "basic_uct.h"
#include <unistd.h>

unsigned long long step;

const int RAND_MAX_INT = 10000000; //used for random number generation


/* UCT PARAMS */
int numRuns = 10;
double C = 0.02; // exploration bias parameter for UCT
int prob = 2000000; // CCLS noise parameter
int maxFlips = 1000; // number of flips in each CCLS run
char *filename; // .cnf filename
int runTimeout = 15; // run timeout in seconds

/* GLOBAL VARIABLES */
uctnode* root; // pointer to root node of UCT search tree
int nextBranchingAtom; // the next atom to branch on given the current formula
short timeFlag; // used for timeouts

clock_t opt_start, opt_stop; // used for finding time to optimal
short clockStopped; // used for finding time to optimal

double bestReward;
unsigned long long bestNumUnsat;
double bestRewardAtTimeout;

int* varScores; //used in setBranchingAtom
int* bestVars; //used in setBranchingAtom

int best_array[MAX_VARS];
int best_array_count;


/* Main UCT Method -- Plays the selected node */
double playNode(uctnode *node) {
  double reward;
  short armPlayed;
  
  // Set this node's variable to be immutable
  varMutable[node->atom] = 0;
  
  // If neither arm has been played, play them both
  if (node->n[LEFT]==0) {
    node->n[LEFT] = node->n[RIGHT] = 1;
    // play the left arm
    cur_soln[node->atom] = LEFT;
    node->x[LEFT] = estimateReward();
    if (closedFlag) {
      closedFlag=0;
      node->closed[LEFT]=1;
    }
    else {
      node->nextAtom[LEFT] = nextBranchingAtom;
    }
    // then play the right arm
    cur_soln[node->atom] = RIGHT;
    node->x[RIGHT] = estimateReward();
    if (closedFlag) {
      closedFlag=0;
      node->closed[RIGHT]=1;
    }
    else {
      node->nextAtom[RIGHT] = nextBranchingAtom;
    }
    reward = (node->x[LEFT]+node->x[RIGHT])/2.0;
    armPlayed = BOTH;
    // If the depth limit has been reached, close both arms
    if (node->depth >= depthLimit) {
      node->closed[LEFT] = node->closed[RIGHT] = 1;
    }
  }
  
  // If the left arm is closed, play the right
  else if (node->closed[LEFT]) {
    node->n[RIGHT]++;
    cur_soln[node->atom] = RIGHT;
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
    cur_soln[node->atom] = LEFT;
    if (!(node->children)) {
      createChildren(node);
    }
    reward = playNode(node->children[LEFT]);
    node->x[LEFT]+=(reward-node->x[LEFT])/node->n[LEFT];
    armPlayed = LEFT;
  }
  
  // Otherwise, play the arm that maximizes its UCB1 score */
  else {
    armPlayed = selectMove(node);
    node->n[armPlayed]++;
    cur_soln[node->atom] = armPlayed;
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
      node->closed[LEFT] = 1;
    break;
          
  case (RIGHT):
    if (node->children[RIGHT]->closed[LEFT] && node->children[RIGHT]->closed[RIGHT])
      node->closed[RIGHT] = 1;
    break;

  }
  // Finally, return the reward to propagate it up to the root
  return reward;
}



/* Subroutine in UCT search -- given a node, it decides which child UCT should expand */
short selectMove(uctnode *node) {
  float scoreL, scoreR;
  
  // Calculate the UCB1 scores for the two arms
  scoreL = node->x[LEFT];
  scoreL += C*sqrt(log(node->n[LEFT]+node->n[RIGHT])/ (float) node->n[LEFT]);
  scoreR = node->x[RIGHT];
  scoreR += C*sqrt(log(node->n[LEFT]+node->n[RIGHT])/ (float) node->n[RIGHT]);
  // If they are equal, pick one uniformly at random
  if (scoreL==scoreR) {
    return rand()%BF;
  }
  // Otherwise, pick the arm with the larger score
  return (scoreR>scoreL);
}


/* Estimates the value of a leaf node by performing SLS */
double estimateReward() {
  double reward;
  
  // Initialize the SLS run
  init(); 
  
  // Perform SLS using a UBCSAT algorithm
  reward = (double) (num_clauses-local_search())/(double)num_clauses;
  
  // Take the reward to be the portion of satisfied clauses squared
  reward *= reward;
  
  // Determine which atom to branch on next
  if (!closedFlag) {
    setBranchingAtom();
  }
  
  bestReward = (reward > bestReward) ? reward : bestReward;
  
  return reward;
}


/* Returns the number of unsat clauses given a UCT reward */
int getNumUnsat(double reward) {
  return (int) rint(num_clauses - num_clauses*sqrt(reward));
}


/* Sets the root node of the UCT search tree */
void setRootNode() {
  root = new uctnode;
  if (!root) printMemoryError();
  root->depth = 0;
  root->x[LEFT] = root->x[RIGHT] = MIN_REWARD;
  root->n[LEFT] = root->n[RIGHT] = 0;
  root->closed[LEFT] = root->closed[RIGHT] = 0;
  root->children = NULL;
  init();
  setBranchingAtom();
  root->atom = nextBranchingAtom;
}


/* Branching heuristic: A0 */
void setBranchingAtom() {
  int j, k;
  int bestScore = -1;
  int numBest = 0;
  
  for (j=0; j<num_vars; j++) {
    varScores[j] = 0;
  }
  // Collect the variable scores
  for (j=0; j<num_clauses; j++) {
    if (preSat[j]) continue; // don't consider preSat clauses
    for (k=0;k<clause_lit_count[j];++k) {
      varScores[clause_lit[j][k].var_num]++;
    }
  }
  // Search for the best score, break ties uniformly at random
  for (j=1; j<=num_vars; j++) {
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
    nextBranchingAtom = bestVars[rand()%numBest];
  }
  
}


/* Returns a new node */
uctnode *getNewNode(uctnode *parent, int armNum) {
  uctnode *temp; 
  temp = new uctnode;
  if (!temp) printMemoryError();
  temp->depth = (parent->depth+1);
  temp->x[LEFT] = temp->x[RIGHT] = MIN_REWARD;
  temp->n[LEFT] = temp->n[RIGHT] = 0;
  temp->closed[LEFT] = temp->closed[RIGHT] = 0;
  temp->atom = parent->nextAtom[armNum];
  temp->children = NULL;
  return temp;
}


/* Creates child nodes for a given node */
void createChildren(uctnode *node) {
  int i;
  node->children = new uctnode*[BF];
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
  delete node->children;
  delete node;
}


/* CCLS method -- picks a variable to flip from an unsatisfied clause */
int pick_var()
{
	int     i,c,v;
	int     best_score=0;
	int		v_score;
	
	if(rand()%RAND_MAX_INT<prob)
	{
		int 
		c = unsat_stack[rand()%unsat_stack_fill_pointer];

		best_array_count=0;
		
		for (i=0; i<clause_lit_count[c]; i++) {
		  v = clause_lit[c][i].var_num;
		  if (varMutable[v]) { // only consider mutable variables
		    best_array[best_array_count++] = v;
		  }
		}
		return best_array[rand()%best_array_count];
	}
	
	best_array_count=0;
	for(i=0; i<unsatvar_stack_fill_pointer; i++)
	{
		v = unsatvar_stack[i];
		if (!varMutable[v]) continue;
		if(conf_change[v]==1)
		{
			best_array[0] = v;
			best_array_count=1;
			best_score = score[v];
			break;
		}
	}
	for(i++; i<unsatvar_stack_fill_pointer; i++)
	{
		v = unsatvar_stack[i];
		if (!varMutable[v]) continue;
		if(conf_change[v]==0)
			continue;
		v_score = score[v];
		if(v_score>best_score)
		{
			best_array[0] = v;
			best_array_count=1;
			best_score = v_score;
		}
		else if(v_score==best_score)
			best_array[best_array_count++] = v;
	}
	
	if(best_array_count>0)
		return best_array[rand()%best_array_count];
	
	c = unsat_stack[rand()%unsat_stack_fill_pointer];
	return clause_lit[c][rand()%clause_lit_count[c]].var_num;
}
 

/* Main CCLS method -- performs local search*/
int local_search()
{
	int flipvar,v,j;
	unsigned long long local_opt_unsat_clause_weight = total_unsat_clause_weight+numPreFalsifiedClauses;

	if(local_opt_unsat_clause_weight<bestNumUnsat)
	{
		
		bestNumUnsat=local_opt_unsat_clause_weight;
		
		for(v=1; v<=num_vars; v++)
			best_soln[v] = cur_soln[v];

	}
	if(total_unsat_clause_weight==0)
	{
		return local_opt_unsat_clause_weight;
	}
	
	for(step=0; step<maxFlips; step++)
	{

		if(total_unsat_clause_weight+numPreFalsifiedClauses<local_opt_unsat_clause_weight)
		{
			local_opt_unsat_clause_weight=total_unsat_clause_weight+numPreFalsifiedClauses;
		    if (local_opt_unsat_clause_weight<bestNumUnsat) {
				bestNumUnsat=local_opt_unsat_clause_weight;
				for(v=1; v<=num_vars; v++)
					best_soln[v] = cur_soln[v];
			}
			
			
		}

		if(total_unsat_clause_weight==0) 
		{
			return local_opt_unsat_clause_weight;
		}

		flipvar = pick_var();

		if (varMutable[flipvar]) {
			flip(flipvar);
		}
	}
	
	return local_opt_unsat_clause_weight+numPreFalsifiedClauses;
}


/* Set <varMutable> array */
void setMutable() {
  int i;
  for (i=1; i<=num_vars; i++) {
    varMutable[i] = 1;
  }
}


/* Performs a single timed UCT run and returns the best number of unsat clauses found */
int runUCTtimed() {
  
  bestReward=MIN_REWARD;
  bestNumUnsat=BIG_LONG;
  
  // Install the timeout handler and set the alarm
  signal(SIGALRM, ALARMhandler);
  timeFlag = 1;
  alarm(runTimeout);
  
  build_neighbor_relation();
  
  clockStopped=0;
  opt_start = clock();
  
  // all variables begin as mutable
  setMutable();

  // initialize the root node
  setRootNode();
  
  while (timeFlag) {
    setMutable();
    playNode(root);
  }
  
  // free memory
  if (root) {
    freeNode(root);
  }
  
  return getNumUnsat(bestRewardAtTimeout);
}


/* Performs UCT runs and prints the results to stdout */
void performRuns() {
  int i;
  int numUnsat[numRuns];
  
  for (i=0; i<numRuns; i++) {
    numUnsat[i] = runUCTtimed();
  }
  
  /* print results to stdout */
  printf("\n*** Best Num Unsat ***\n");
  for (i=0; i<numRuns; i++) {
    printf("Run %d: %d\n", i, numUnsat[i]);
  }
  printf("\n");
  printParams();
}


void printParams() {
  printf("Parameters:\n");
  printf("Instance: %s \n", filename);
  printf("UCT runs: %d\n", numRuns);
  printf("UCT C param: %f\n", C);
  printf("UCT branching heuristic: A0\n");
  printf("SLS algorithm: CCLS14\n");
  printf("SLS max flips: %d\n", maxFlips);
  printf("SLS noise param: %f\n", prob/((double) RAND_MAX_INT));
  printf("Bandit Algorithm: UCB1\n");
  printf("Timeout: %d\n", runTimeout);
  fflush(stdout);
}


void printMemoryError() {
  printf("\nUnable to allocate memory!\n");
  fflush(stdout);
  exit(1);
}


/* Handles timeout signals */
void ALARMhandler(int sig)
{
  timeFlag = 0;
  bestRewardAtTimeout = bestReward;
  signal(SIGALRM, SIG_IGN);
}


void printUsageError() {
  printf("Usage: uct -f filename [-r INT] [-i INT] [-c DOUBLE] [-p DOUBLE] [-m INT] ");
  printf("[-n DOUBLE] [-o INT] [-t INT]\n");
  printf("-flag : <description> (= <default value>)\n");
  printf("-f : .cnf filename \n");
  printf("-r : number of uct runs (=10) \n");
  printf("-i : maximum number of uct iterations per run (=2000) \n");
  printf("-c : UCT exploration/exploitation parameter (=0.02) \n");
  printf("-m : max flips for each sls run (=1000) \n");
  printf("-n : noise param for each sls run (=0.0) \n");
  printf("-t : run timeout in seconds (15)\n\n");
  fflush(stdout);
  exit(1);
}

int main(int argc, char* argv[])
{
	int     seed;
	unsigned long long tries;
	
	extern char *optarg;
    extern int optind;
    int i, option;
    int fflag = 1;
	
	while ((option = getopt(argc, argv, "f:c:m:r:n:t:")) != -1) {
    
      switch (option) {
      
        case 'f':
          if (build_instance(optarg)==0) {
		    printf("c Invalid filename: %s\n", optarg);
		    fflush(stdout);
		    return -1;
	      }
	      filename = optarg;
	      fflag = 0;
          break;
          
        case 't':
          runTimeout = atoi(optarg);
          break;

        case 'r':
          numRuns = atoi(optarg);
          break;
          
        case 'c':
          C = atof(optarg);
          break;
        
        case 'n':
          prob = (int) atof(optarg)*RAND_MAX_INT;
          break;
        
        case 'm':
          maxFlips = atoi(optarg);
          break;
      	
        case '?':
          if (optopt == 'c')
	        fprintf (stderr, "Option -%c requires an argument.\n", optopt);
          else
	        fprintf (stderr, "Unknown option character `\\x%x'.\n", optopt);
            printUsageError();
    	
        default:
          printf("\nFatal Error: option %c is invalid!\n", option);
          printUsageError();
      }  
    }
	
	probtype = NONE;
    
    if (fflag) {
      printf("Fatal Error: filename must be specified!\n");
      printUsageError();
    }
	
    seed = time(0);
	srand(seed);
	
    bestVars = new int[num_vars];
    varScores = new int[num_vars];
    
	// Perform UCT
	performRuns();
	 
	free_memory();

    return 0;
}

