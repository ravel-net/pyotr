
results = {}
with open("result_UDP.txt") as f:
	lines = f.readlines()[1:]
	for line in lines:
		stripped = line.split("|")
		length = int(stripped[1])
		total_time = float(stripped[-1].strip())
		if length not in results:
			results[length] = []
		results[length].append(total_time)

for length in results:
	print(length, sum(results[length])/len(results[length]))