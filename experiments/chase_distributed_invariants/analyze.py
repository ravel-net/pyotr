sums = {}
with open("host2_specificOrder_allMode_20221228183303.log") as f:
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
	print(function, sum(sums[function]))