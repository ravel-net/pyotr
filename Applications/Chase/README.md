The current version does not work for all orderings. The only ordering that always works is dependency [0,1,2,3,4,5] (or optimal from before). For some orderings, the results is sometimes True and sometimes False. This means that there is some bug in our code.

Possible things to try:
1. It's unclear where we want to treat the variables as c_variables and where we want to treat them as text. We need to think about this for all possible dependencies. The in-memory computation converts the Z_table to text, which causes problems in certain tgds. We need clarity on this issue
2. We need to find out exactly in what case the answer is returned False. One possible thing would be to have fixed path instead of random paths, to make the debugging easier
3. There is a dependency which is handled by sql rather than the apply_egd function. Need to look into what it is.

For the future, I think we can either skip computations in database entirely (do everything in memory) or find more efficient methods for computations. Fangping found some sources on the implementation of Chase, perhaps we can utilize them: https://www.southampton.ac.uk/~gk1e17/chaseBench.pdf 