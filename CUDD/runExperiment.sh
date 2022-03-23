#!/bin/bash
input=$1
python3 encodeCUDD.py "$input" "tmp.txt"
make > /dev/null
./BDD_manager "tmp.txt"