sums = {}
info = []
whitelists = []
with open("host4_randomOrder_allMode_20230101003814.log") as f:
	lines = f.readlines()
	for line in lines:
		if "Numhost" in line:
			data = line.strip()
			info.append(data)
		elif "Whitelist" in line:
			data = line.strip()
			whitelists.append(data)
		elif "Time" in line:
			data = line.split()
			function = data[1]
			time = float(data[-1])
			if function not in sums:
				sums[function] = []
			sums[function].append(time)

for function in sums:
	print(function, sum(sums[function]))

for d in info:
	print(d)

for w in whitelists:
	print(w)