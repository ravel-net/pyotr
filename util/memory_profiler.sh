#!/bin/bash
rm top_output.txt
rm results.txt
python3 one_big_switch.py > results.txt &
# echo "$!" > top_output.txt
top -b -p "$!" -n1 | tail -1 | awk -F " " '{print $6}' > top_output.txt
for i in {1..20}
do 
	sleep 1
	if ps -p "$!" > /dev/null
	then
		top -b -p "$!" -n1 | tail -1 | awk -F " " '{print $6}' >> top_output.txt
	else
		break
	fi
done
