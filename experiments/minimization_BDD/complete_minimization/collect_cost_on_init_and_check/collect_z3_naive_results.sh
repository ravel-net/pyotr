#!/bin/bash
cd "results"
rm "Z3_naive_output.txt" || true
rm "Z3_naive_components.txt" || true
rm "Z3_naive_components_analyzed.txt" || true
cd ..
runtimes=5
loops=2
for((size=10;size<=100;size+=10))
do
    python3 exp_minimization_z3_naive.py "$size" "$loops" "$runtimes"
    cd "results"
    python3 analyze_z3_naive.py "$runtimes"
    echo -n "$size $loops $runtimes " >> "Z3_naive_output.txt"
    grep "Total" "Z3_naive_components_analyzed.txt" | awk '{print $2 " " $3 "\n"}' >> "Z3_naive_output.txt"
    #rm "Z3_naive_components.txt"
    rm "Z3_naive_components_analyzed.txt"
    cd ..
done
cd "results"
rm *minimization_chain* || true
cd ..
