#!/bin/bash
input=$1
while IFS= read -r line
do
	output=$(python3 convertToCUDD.py "$line" | tr '\n' ' ')
	sed "s/MODIFY/$output/g" "before.c" > output.c
	make > /dev/null
	./output
  # echo "$output"
done < "$input"