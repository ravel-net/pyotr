# collect cost for z3 initialization/checking, BDD construction/checking

Run on 15-node chain topology 80% variables with 4-variable loops.

Run on UIUC machine.

Total running time: **seconds**
|BDD|Z3|
|----|----|
|100.6710|210.6119|

## BDD

Update condition: **seconds**

|operate_BDDs|
|----|
|46.801|

Merge tuples: **seconds**
|operate_BDDs|checking|
|----|----|
|41.1037|0.0001|

refer to [`BDD_components_analyzed.txt`](results/BDD_components_analyzed.txt) and [`BDD_components.txt`](results/BDD_components.txt)

## Z3

Normalization: **seconds**
|initializaiton|checking|
|----|----|
|110.4688|3.1708|

Merge tuples: **seconds**
|initializaiton|checking|
|----|----|
|19.7207|0.0920|

refer to [`Z3_components_analyzed.txt`](results/Z3_components_analyzed.txt) and [`Z3_components.txt`](results/Z3_components.txt)