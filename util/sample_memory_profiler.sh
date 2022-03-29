#!/bin/bash
rm top_output.txt
rm results.txt
python3 group_query_splitjoin_tauto10.py > results.txt &
echo "$!" > top_output.txt
for i in {1..40000}; do sleep 1 && top -b -p "$!" -n1 | tail -1 ; done >> top_output.txt