#!/bin/bash
rm top_output.txt
rm results.txt
python3 $1 > results.txt &
# echo "$!" > top_output.txt
top -b -p "$!" -n1 | tail -1 | awk -F " " '{print $6}' > top_output.txt
for (( i=1;i<=$2;i++ ))
do 
	sleep 1
	if ps -p "$!" > /dev/null
	then
		top -b -p "$!" -n1 | tail -1 | awk -F " " '{print $6}' >> top_output.txt
	else
		break
	fi
done
