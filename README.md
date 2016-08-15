UCTMAXSAT: Monte-Carlo Tree Search for the Maximum Satisfiability Problem

Code implementing UCTMAXSAT with WalkSAT, Novelty, and CCLS leaf node value estimation.

1) For background see /MCTS_for_MaxSAT.pdf from the 22nd International Conference on the Principles and Practice of Constraint Programming.

2) For WalkSAT and Novelty leaf node value estimation, see /ubcsat. UBCSAT is an SLS SAT solver suite developed by Dave Tompkins. For more information on UBCSAT see /ubcsat/readme.txt. For usage:

$ cd ubcsat
$ make -f Makefile
$ ./uct

3) For CCLS leaf node value estimation, see /ccls. For more information on CCLS, see "CCLS: An Efficient Local Search Algorithm for Weighted Maximum Satisfiability" by Chuan Luo, Shaowei Cai, Wei Wu, Zhong Jie, and Kaile Su in IEEE Trans. on Computers. For usage:

$ cd ccls
$ g++ main_uct.cpp -o uct
$ ./uct