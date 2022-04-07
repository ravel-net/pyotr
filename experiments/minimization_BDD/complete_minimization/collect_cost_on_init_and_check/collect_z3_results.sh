#!/bin/bash

# cd "results"
# rm "Z3_components_analyzed.txt"
# cd ..
runtimes=1
loops=2
for((size=50;size<=55;size+=5))
do
    python3 exp_minimization_z3.py "$size" "$loops" "$runtimes"
    cd "results"
    python3 analyze.py "$runtimes"
    echo -n "$size $loops $runtimes " >> "Z3_output.txt"
    grep "Total" "Z3_components_analyzed.txt" | awk '{print $2 " " $3 "\n"}' >> "Z3_output.txt"
    rm "Z3_components.txt"
    rm "Z3_components_analyzed.txt"
    cd ..
done