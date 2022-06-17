import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import numpy as np

def cal_mean(filedir, filename, out_file_dir, out_filename):
    f = open(filedir+filename)
    title = None
    list_times = None
    for line in f:
        if "total" in line:
            title = line.strip()
            continue
        times = line.strip().split()

        if list_times is None:
            list_times = []
            for t in times:
                list_times.append([float(t)])
        else:
            for idx, t in enumerate(times):
                list_times[idx].append(float(t))
    f.close()

    list_means = []

    for d in list_times:
        mean = np.mean(d)
        list_means.append(mean)

    

    f = open(out_file_dir+out_filename, "w")
    f.write("{}\n".format(title))
    for d in list_means:
        f.write("{:.4f} ".format(d))
    f.write("\n")
    f.close()

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
    file_dir = './plots/'
    filename = "static.txt"

    raw_data = []
    f = open(file_dir+filename)
    for line in f:
        raw_data.append(float(line.strip()))

    gen_cdf_data_file(raw_data, file_dir, "cdf_static.dat")

    # file_dir  = './results/'
    # filename = "chase_a.txt"
    # out_filename = "cahse_a_mean.txt"

    # cal_mean(file_dir, filename, file_dir, out_filename)

    # filename = "chase_b.txt"
    # out_filename = "cahse_b_mean.txt"

    # cal_mean(file_dir, filename, file_dir, out_filename)

    