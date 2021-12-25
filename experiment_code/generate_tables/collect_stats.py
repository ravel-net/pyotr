file_name = "string_1000.txt"

f = open(file_name, "r")
lines = f.readlines()
timings = []
for line in lines:
	if "Execution Time:" in line:
		timings.append(float(line.split()[2]))

print(timings)