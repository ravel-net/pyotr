#!/bin/bash
cd "results"
#rm "BDD_output.txt" || true
rm "BDD_components.txt" || true
#rm "BDD_components_analyzed.txt" || true
cd ..
runtimes=5
loops=2
for((size=10;size<=100;size+=10))
do
    python3 exp_minimization_BDD.py "$size" "$loops" "$runtimes"
    cd "results"
    python3 analyze_BDD.py "$runtimes"
    echo -n "$size $loops $runtimes " >> "BDD_output.txt"
    grep "Total" "BDD_components_analyzed.txt" | awk '{print $2 " " $3 "\n"}' >> "BDD_output.txt"
    rm "BDD_components.txt"
    mv "BDD_components_analyzed.txt" "BDD_components_analyzed_$size.txt"
    cd ..
done
cd results
cp "*minimization_chain*" BDD_results/ || true
cd ..
