import sys

file_name = sys.argv[1]

f = open(file_name, "r")
lines = f.readlines()
timings = []
for line in lines:
	if "Execution Time:" in line:
		timings.append(float(line.split()[2]))

print(timings)
