import sys
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

if __name__ == '__main__':
	sums = {}
	info = []
	whitelists = []
	suspicious = []
	with open("NumPolicies4_Hosts3ReH2_Orderspecific_Unitpolicy_20230129163447.log") as f:
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

	
	# gen_cdf_data_file(raw_data, "./random_policies", "cdf"+filename.split('.')[0]+".txt")

# ('Merge Right Join  (cost=13112.53..57549.77 rows=2947369 width=160) (actual time=65.568..116.727 rows=196596 loops=1)',), 
# ('  Merge Cond: (u.flowid = t.f)',), ('  ->  Sort  (cost=708.56..728.23 rows=7865 width=96) (actual time=13.762..14.783 rows=16383 loops=1)',), 
# ('        Sort Key: u.flowid',), 
# ('        Sort Method: quicksort  Memory: 1530kB',), 
# ('        ->  Seq Scan on update_src_dst u  (cost=0.00..199.65 rows=7865 width=96) (actual time=0.003..0.716 rows=16383 loops=1)',), 
# ('  ->  Materialize  (cost=12403.97..12778.71 rows=74949 width=96) (actual time=51.802..83.862 rows=196596 loops=1)',), 
# ('        ->  Sort  (cost=12403.97..12591.34 rows=74949 width=96) (actual time=51.801..75.012 rows=196596 loops=1)',), 
# ('              Sort Key: t.f',), ('              Sort Method: external merge  Disk: 6736kB',), 
# ('              ->  Seq Scan on z_random t  (cost=0.00..2492.49 rows=74949 width=96) (actual time=0.003..9.719 rows=196596 loops=1)',), 
# ('Planning Time: 0.048 ms',), 
# ('Execution Time: 193.324 ms',)

# ('Update on z_random  (cost=2.08..6325.21 rows=0 width=0) (actual time=15.109..15.110 rows=0 loops=1)',), 
# ('  ->  Hash Join  (cost=2.08..6325.21 rows=63760 width=190) (actual time=0.092..14.427 rows=996 loops=1)',), 
# ('        Hash Cond: (z_random.f = "*VALUES*".column1)',), 
# ('        ->  Seq Scan on z_random  (cost=0.00..5109.39 rows=153639 width=38) (actual time=0.070..8.909 rows=196596 loops=1)',), 
# ('        ->  Hash  (cost=1.04..1.04 rows=83 width=216) (actual time=0.021..0.021 rows=83 loops=1)',), 
# ('              Buckets: 1024  Batches: 1  Memory Usage: 17kB',), 
# ('              ->  Values Scan on "*VALUES*"  (cost=0.00..1.04 rows=83 width=216) (actual time=0.002..0.015 rows=83 loops=1)',), 
# ('Planning Time: 0.035 ms',), 
# ('Execution Time: 15.117 ms',)