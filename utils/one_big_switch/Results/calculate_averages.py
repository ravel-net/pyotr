import sys

lengths = [6,7,8,9]
averages = {}
for length in lengths:
	averages[str(length)] = []

filename = sys.argv[1]
with open(filename, 'r') as f:
	lines = f.readlines()
	for line in lines[1:]:
		split = line.split("\t\t")
		if split[0] in averages:
			averages[split[0]].append(float(split[1])) 

with open("stats_" + filename, 'a') as f:
	for length in lengths:
		average = sum(averages[str(length)])/len(averages[str(length)])
		f.write(str(length) + "\t" + str(average) + "\n")