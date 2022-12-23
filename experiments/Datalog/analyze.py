sums = {}
with open("program.log") as f:
	lines = f.readlines()
	for line in lines:
		if "Time" in line:
			data = line.split()
			function = data[1]
			time = float(data[-1])
			if function not in sums:
				sums[function] = []
			sums[function].append(time)

for function in sums:
	if sum(sums[function]) > 0.2: # only print times that take more than 0.2 seconds of the time
		print(function, sum(sums[function]))