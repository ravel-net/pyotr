import sys
import numpy as np
from os import listdir
from os.path import isfile, join
from copy import deepcopy


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
            row = "{:.4f} {:.4f} \n".format(cdf_data[i], data[i])
            f.write(row)
    except ValueError:
        print(ValueError)
    finally:
        f.close()

def go_over_files(filedir):
	f_avg = open(filedir+"avg.dat", "w")
	row = "avg\tstd\titem\n"
	f_avg.write(row)

	items = ["single_gamma", "chase_policy", "apply_E", "apply_policy", "apply_egd", "apply_tgd"]
	f_items = open(filedir+"items.txt", "w")
	row = "{} {}\n".format("\t".join(items), "filename")
	f_items.write(row)

	for f in listdir(filedir):
		if isfile(join(filedir, f)) and f.endswith('.log'):
			print("processing", join(filedir, f))
			raw_data, suspicous_sums, total_sums = process_file(filedir, f)

			gen_cdf_data_file(raw_data, filedir, "cdf_"+f.split('.')[0]+".dat")

			avg = np.mean(raw_data)
			std = np.std(raw_data)
			row = "{:.4f}\t{:.4f}\t{} \n".format(avg, std, f)
			f_avg.write(row)

			target = get_items_runtime(items, total_sums)
			data = []
			for item in items:
				data.append("{:.4}".format(target[item]))
			row = "{} {}\n".format("\t".join(data), f)
			f_items.write(row)

			f_info = open(filedir+"info_"+f.split('.')[0]+".txt", "w")
			rows = get_items_runtime_for_each_run(items, suspicous_sums)
			f_info.write("\n".join(rows))
			f_info.close()
	f_items.close()
	f_avg.close()

def get_items_runtime(items, sums):
	target = {}
	for item in items:
		for sum_item in sums.keys():
			if item in sum_item:
				if item in target.keys():
					target[item] += sum(sums[sum_item])
				else:
					target[item] = sum(sums[sum_item])
	return target

def get_items_runtime_for_each_run(items, suspicious_sums):
	rows = []
	titles = []
	for suspicous in suspicious_sums.keys():
		target = get_items_runtime(items, suspicious_sums[suspicous])

		
		for item in suspicous.split(","):
			if "Suspicious" in item or ')' in item:
				continue
			
			item_list = item.split(":")
			key = item_list[0].strip()
			value = item_list[1].strip()

			if "TimeForRun" in key:
				target["TimeForRun"] = eval(value)
			else:
				target[key] = eval(value)
		

		if len(titles) == 0:
			titles = list(target.keys())
			rows.append("\t".join(titles))

		data = []
		for item in titles:
			data.append("{:.4f}".format(target[item]))
		rows.append("{}".format("\t".join(data)))
	
	return rows

def process_file(filedir, filename):
	total_sums = {}
	info = []
	whitelists = []
	suspicious = []
	suspicious_sums = {}
	with open(filedir+filename) as f:
		lines = f.readlines()
		sums = {}
		suspicious_flow = None
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
				
				suspicious_flow = data
				if len(sums)!= 0:
					suspicious_sums[suspicious_flow] = deepcopy(sums)
					sums = {}
				
				
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

				if function not in total_sums:
					total_sums[function] = []
				total_sums[function].append(time)
				
		# if len(sums)!= 0:
		# 	suspicious_sums[suspicious_flow] = deepcopy(sums)
			# sums = {}
			# suspicious_flow = data
	# for function in sums:
	# 	print(function, sum(sums[function]))

	# for d in info:
	# 	print(d)

	# for w in whitelists:
	# 	print(w)

	raw_data = []
	for s in suspicious:
		raw_data.append(float(s.split(",")[-1].split(':')[-1])*1000)
		# print(s)

	
	# gen_cdf_data_file(raw_data, filedir, "cdf_"+filename.split('.')[0]+".dat")
	return raw_data, suspicious_sums, total_sums

if __name__ == '__main__':
	go_over_files("./", )
	