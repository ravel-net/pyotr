#!/bin/bash
input=$1
python3 encodeCUDD.py "$input" "tmp.txt"
make > /dev/null
./convertToBDD "tmp.txt"