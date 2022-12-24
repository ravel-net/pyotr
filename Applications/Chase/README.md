# The chase

Details for the experiments of the chase on distributed invariants

## Topology
We use a chain topology generated from the largest AS(AS 7018) of **Rocketfuel topologies**: 
1. randomly pick the source and destination nodes on AS 7018 and calculate the shortest path between the source and destination. Using this shortest path as a chain and assigning IP addresses to each node of the path.
2. adding a number of ingress hosts connected to the source node and egress hosts connected to the dest node(equal number of ingress hosts and egress hosts) and assigning IP addresses to each host
3. randomly pick one ingress host and one egress host, then use this pair of IP addresses of two hosts as a block(firewall) which means blocking traffic from the source host to the dest host(e.g., block 10.2->10.4). 
4. Assign rewrite policies at the source and dest nodes(i.e., the first node and the last node of a chain)


## Dependencies
### Rewrite Policies
- \sigma_1(tgd): rewrite source at node 1; 
  
    | **F**                  | **S**  | **D**  | **N** | **X** |
    |:----------------------:|:------:|:------:|:-----:|:-----:|
    | x_f                    | 10.2   | 10.3   | 1     | 2     |
    | _x_f_                  | _10.1_ | _10.3_ | _1_   | _2_   |

- \sigma_1'(egd): the header of flows should be matched before and after rewriting at node 1; 
  
    | **F**       | **S** | **D** | **N** | **X** |
    |:-----------:|:-----:|:-----:|:-----:|:-----:|
    | x_f         | 10.2  | 10.3  | 1     | 2     |
    | y_f         | 10.1  | 10.3  | 1     | 2     |
    | _x_f = y_f_ |       |       |       |       |

- \sigma_2(tgd):  similar to (1);

    | **F**                  | **S**  | **D**  | **N** | **X**  |
    |:----------------------:|:------:|:------:|:-----:|:------:|
    | x_f                    | 10.1   | 10.3   | 2     | 10.3   |
    | _x_f_                  | _10.1_ | _10.4_ | _2_   | _10.4_ |

- \sigma_2'(tgd):  similar to (2);
  
    | **F**       | **S** | **D** | **N** | **X** |
    |:-----------:|:-----:|:-----:|:-----:|:-----:|
    | x_f         | 10.1  | 10.3  | 2     | 10.3  |
    | y_f         | 10.1  | 10.4  | 2     | 10.4  |
    | _x_f = y_f_ |       |       |       |       |

### Dest-based Forwarding Policy
- \sigma_D(egd): destination_based forwarding policy; 
  
    | **F**                           | **S** | **D** | **N** | **X** |
    |:-------------------------------:|:-----:|:-----:|:-----:|:-----:|
    | x_f                             | x_s   | x_d   |       |       |
    | x_f                             | y_s   | y_d   |       |       |
    |    _x_s = y_s_     | /\        | _x_d = y_d_      |       |       |

### Avoiding "black-hole" 
Ensure any newly inserted flow entries are not "black-holed" in the network.

- \sigma_new(tgd): inserting forwarding entries for every newly inserted entry to avoid "black-hole"(i.e., making sure any forwarding entry at node 1, there must exist a matching entry in the next hop).

    | **F** | **S**  | **D** | **N** | **X**    |
    |-------|--------|-------|-------|----------|
    | x_f   | x_s1   | x_d   | x_n   | x_x      |
    | x_f   | x_s2   | x_d   | x_x   | x_next   |
    | _x_f_ | _x_s1_ | _x_d_ | _x_x_ | _x_next_ |

### Firewall Policy

blocking flows whose source is 10.2 and dest is 10.4.
- \sigma_fw(egd) 

    | **F** | **S**  | **D** | **N** | **X**    |
    |-------|--------|-------|-------|----------|
    |       | s      |   d   |       |          |
    | _not_   |_(s=10.2_ | /\    | _d=10.4)_|          |

## Orderings

We set different ordering for applications of dependencies. 

- Optimal: \sigma_D, \sigma_1, \sigma_1', \sigma_2, \sigma_2', \sigma_new, \sigma_fw.
- Random: randomly generate an order of applications of dependencies in every run.
- Specific: randomly generate an order of applications of dependencies and apply dependencies as this order in every run.

Note: Above orderings were used in previous experiment. We may need to think twice for optimal ordering right now(\sigma_D, \sigma_1, \sigma_1', \sigma_new, \sigma_2, \sigma_2', \sigma_fw may be better). 

## The complete process of the chase on the toy example
See [sheet](https://docs.google.com/spreadsheets/d/1eag-hdVJLU3USVnYnF_T9020bt_E_PfJgU2wqJxZcAk/edit?usp=sharing).

## Parameters in experiments

- ordering: see subsection [Orderings](#orderings)
- whitelists for reachability view: `relevant` and `all`
  -  `relevant`: only set partial reachability view that only contains pairs of sourse and dest related to the block, i.e., only checking related hosts.
  -  `all`: put all pairs of ingress and egress hosts in reachability view, i.e., checking all hosts.
  -  adjusted in `gen_gamma_table()`

## Scripts for running experiments

- [`chase.py`](../../Applications/Chase/chase.py) provides the main function for the chase, such as 
  - applying a dependency on the inverse image(`apply_dependecy()`), 
  - generating inverse image(`gen_z()`).
- [`experiments/chase_distributed_invariants/script_chase_distributed_invariants.py`](../../experiments/chase_distributed_invariants/script_chase_distributed_invariants.py) provides functions that 
  - generate dependencies(`gen_dependencies_for_chase_distributed_invariants()`),  
  - generate reachability view(`gen_gamma_table()`)
  - generate tableau query for topology(`gen_E_for_chase_distributed_invariants()`)
  - run the chase with different orderings(`run_chase_distributed_invariants_in_xxx_order()`)
- [`experiments/chase_distributed_invariants/run_script.py`](../../experiments/chase_distributed_invariants/run_script.py) provides scripts that
  - run scalability experiments(`run_scalibility()`)
  - run experiments with different orderings(`run_ordering_strategies()`)

We just adjust code in [`run_script.py`](../../experiments/chase_distributed_invariants/run_script.py) to run experiments with different requirements.

## Note after hotnet submission

**updated: we had fixed all bugs and the chase is working correctly for any orderings**

The current version does not work for all orderings. The only ordering that always works is dependency [0,1,2,3,4,5] (or optimal from before). For some orderings, the results is sometimes True and sometimes False. This means that there is some bug in our code.

Possible things to try:
1. It's unclear where we want to treat the variables as c_variables and where we want to treat them as text. We need to think about this for all possible dependencies. The in-memory computation converts the Z_table to text, which causes problems in certain tgds. We need clarity on this issue
2. We need to find out exactly in what case the answer is returned False. One possible thing would be to have fixed path instead of random paths, to make the debugging easier
3. There is a dependency which is handled by sql rather than the apply_egd function. Need to look into what it is.


For the future, I think we can either skip computations in database entirely (do everything in memory) or find more efficient methods for computations. Fangping found some sources on the implementation of Chase, perhaps we can utilize them: https://www.southampton.ac.uk/~gk1e17/chaseBench.pdf 