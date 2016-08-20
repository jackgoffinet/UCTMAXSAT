### Monte-Carlo Tree Search for the Maximum Satisfiability Problem

Code implementing `UCTMAXSAT` with `WalkSAT`, `Novelty`, and `CCLS` leaf node value estimation.

1. For details about our algorithm and results, see our paper (the file `MCTS_for_MaxSAT.pdf` in the repo) that was presented at the 22nd International Conference on the Principles and Practice of Constraint Programming (CP 2016).

2. For `WalkSAT` and `Novelty` leaf node value estimation, see `/ubcsat`. [`UBCSAT`](http://ubcsat.dtompkins.com/) is an SLS SAT solver suite developed by Dave Tompkins. To run:

```
$ cd ubcsat
$ make -f Makefile
$ ./uct
```

3. For `CCLS` leaf node value estimation, see `/ccls`. For more information on `CCLS`, see ["CCLS: An Efficient Local Search Algorithm for Weighted Maximum Satisfiability"](http://ieeexplore.ieee.org/xpl/login.jsp?tp=&arnumber=6874523&url=http%3A%2F%2Fieeexplore.ieee.org%2Fxpls%2Fabs_all.jsp%3Farnumber%3D6874523) by Chuan Luo, Shaowei Cai, Wei Wu, Zhong Jie, and Kaile Su in IEEE Trans. on Computers. To run:

```
$ cd ccls
$ g++ main_uct.cpp -o uct
$ ./uct
```
