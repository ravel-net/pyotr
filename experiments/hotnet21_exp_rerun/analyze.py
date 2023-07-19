import sys
import os
import numpy as np

def gen_cdf(data):
    sorted_data = np.sort(data)
    cdf_data = 1 * np.arange(len(sorted_data)) / float(len(sorted_data) - 1)
    # print(cdf_data)
    return cdf_data

def gen_cdf_data_file(raw_data, out_filedir, out_filename):
    cdf_data = gen_cdf(raw_data)
    data = np.sort(raw_data)
    try:
        f = open(out_filedir+out_filename, "w")
        for i in range(len(data)):
            row = "{:.4f} {} \n".format(cdf_data[i], data[i])
            f.write(row)
    except ValueError:
        print(ValueError)
    finally:
        f.close()

def analyze(filename, mode='print'):
	sums = {}
	info = []
	whitelists = []
	suspicious = []
	with open(filename) as f:
		lines = f.readlines()
		for line in lines:
			if "Numhost" in line:
				data = line.strip()
				info.append(data)
			elif "Whitelist" in line:
				data = line.strip()
				whitelists.append(data)
			elif "Suspicious" in line:
				data = line.strip()
				suspicious.append(data)
			elif "Time" in line:
				data = line.split()
				items = data[1].split(',')
				function = None
				if len(items) == 1:
					function = items[0]
				else:
					function = items[1]

				time = float(data[-1])
				if function not in sums:
					sums[function] = []
				sums[function].append(time)

	if mode == 'output':
		name = filename.split(".log")[0].split('/')[-1]
		newfile = "summary.log"
		with open(newfile, 'a') as f:
			for function in sums:
				print(function, sum(sums[function]))
				f.write("{} {} {}\n".format(function, sum(sums[function]), name))

			for d in info:
				print(d)
				f.write("{} {}\n".format(d, name))

			for w in whitelists:
				print(w)
				f.write("{} {}\n".format(w, name))

			# raw_data = []
			for s in suspicious:
				# raw_data.append(float(s.split(",")[-1].split(':')[-1]))
				print(s)
				f.write("{} {}\n".format(s, name))
	else:
		for function in sums:
			print(function, sum(sums[function]))

		for d in info:
			print(d)

		for w in whitelists:
			print(w)
		# raw_data = []
		for s in suspicious:
			# raw_data.append(float(s.split(",")[-1].split(':')[-1]))
			print(s)

if __name__ == '__main__':
	input_str = sys.argv[1]
	print(input_str)
	if os.path.exists(os.path.dirname(input_str)):
		# print("yes")
		
		if os.path.isdir(input_str):
			files = []
			for name in os.listdir(input_str):
				if name.endswith('.log'):
					files.append("{}/{}".format(input_str, name))
			for file in files:
				analyze(file, "output")
		else:
			analyze(input_str, "print")
	else:
		print("invalid input")
	