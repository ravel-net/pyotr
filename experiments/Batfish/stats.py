
def calculate_averages(sum):
	f = open("result_NAT_avg.csv", "a")
	f.write("destinations,num_runs,avg_eval_time,avg_snap_time,avg_total_time\n")
	for dest in sums:
		eval_sum = float(sums[dest][0])
		snap_sum = float(sums[dest][1])
		num_runs = int(sums[dest][2])
		avg_eval_time = str(eval_sum/num_runs)
		avg_snap_time = str(snap_sum/num_runs)
		avg_total_time = str(float(avg_eval_time)+float(avg_snap_time))
		f.write("{},{},{},{},{}\n".format(str(dest), str(num_runs), avg_eval_time, avg_snap_time, avg_total_time))


def calculate_sums(fileName = "result_NAT.csv"):
	sums = {}
	with open(fileName) as f:
		lines = f.readlines()[1:]
		for line in lines:
			splitLine = line.split(",")
			num_dest = int(splitLine[3])
			eval_time = float(splitLine[4])
			snap_time = float(splitLine[5])
			if num_dest not in sums:
				sums[num_dest] = [0,0,0]
			sums[num_dest][0] += eval_time
			sums[num_dest][1] += snap_time
			sums[num_dest][2] += 1
	return sums

def total():
	with open("result_NAT.csv") as f:
		f2 = open("result_NAT2.csv", "a")
		lines = f.readlines()
		i = 0
		for line in lines:
			if i == 0:
				f2.write("{}".format(line))
				i += 1
				continue
			splitLine = line.split(",")
			f2.write("{},{},{},{},{},{},{}\n".format(splitLine[0], splitLine[1], splitLine[2], splitLine[3], eval_time*num_dest, snap_time*num_dest, (eval_time+snap_time)*num_dest))

if __name__ == '__main__':
	sums = calculate_sums()
	calculate_averages(sums)