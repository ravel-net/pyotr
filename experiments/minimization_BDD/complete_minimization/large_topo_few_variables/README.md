# Performance

Run on UIUC machine.

## 20% variables, 3 variables in a single loop

Chain topology with loops: 15 - 45 nodes in total, 20% variables, 3 variables in a single loop.

The running time of BDD version vs. Z3 version: 

|size of topo | BDD          |      Z3     |
|-------------|--------------|-------------|
| 15          | 9.929 sec    | 8.876 sec   | 
| 20          | 41.662 sec   | 13.954 sec  |
| 25          |  -           | 23.029 sec  |
| 30          |  -           | 42.265 sec  |
| 35          |  -           | 64.837 sec  |
| 40          |  -           | 104.780 sec |
| 45          |  -           | 176.610 sec |

## 20% variables, 4 variables in a single loop

Chain topology with loops: 15 - 45 nodes in total, 20% variables, 4 variables in a single loop

The running time of BDD version vs. Z3 version: 

|size of topo | BDD          |      Z3     |
|-------------|--------------|-------------|
| 15          | 8.309 sec    | 10.927 sec  |
| 20          |out-of-memory | 47.242 sec  |
| 25          |  -           | 84.010 sec  |
| 30          |  -           | 166.391 sec |
| 35          |  -           | 308.038 sec |
| 40          |  -           | 667.251 sec |
| 45          |  -           | 1011.912 sec|

**Out-of-memory: happend on 20-node chain topology with 4-variables loop, 20% variables in total.** See the system memory record: [`killed_program.txt`](results/killed_program.txt) 