#!/bin/bash
cd "results"
rm "Z3_output.txt" || true
rm "Z3_components.txt" || true
rm "Z3_components_analyzed.txt" || true
cd ..
runtimes=5
loops=2
for((size=10;size<=100;size+=10))
do
    python3 exp_minimization_z3.py "$size" "$loops" "$runtimes"
    cd "results"
    python3 analyze_z3.py "$runtimes"
    echo -n "$size $loops $runtimes " >> "Z3_output.txt"
    grep "Total" "Z3_components_analyzed.txt" | awk '{print $2 " " $3 "\n"}' >> "Z3_output.txt"
    rm "Z3_components.txt"
    rm "Z3_components_analyzed.txt"
    cd ..
done
cd "results"
rm *minimization_chain* || true
cd ..
