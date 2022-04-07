#!/bin/bash
cd "results"
rm "BDD_output.txt" || true
rm "BDD_components.txt" || true
rm "BDD_components_analyzed.txt" || true
cd ..
runtimes=1
loops=2
for((size=500;size<=501;size+=10))
do
    python3 exp_minimization_BDD.py "$size" "$loops" "$runtimes"
    cd "results"
    python3 analyze_BDD.py "$runtimes"
    echo -n "$size $loops $runtimes " >> "BDD_output.txt"
    grep "Total" "BDD_components_analyzed.txt" | awk '{print $2 " " $3 "\n"}' >> "BDD_output.txt"
    rm "BDD_components.txt"
    rm "BDD_components_analyzed.txt"
    cd ..
done
cd "results"
rm *minimization_chain* || true
cd ..
