import sys
from os.path import dirname, abspath
from turtle import pos

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import numpy as np

def cal_mean_stddev(filedir, filename):
    f = open(filedir+filename)
    runtime_list = []
    for line in f:
        runtime = float(line.strip())
        runtime_list.append(runtime)
    f.close()

    mean = np.mean(runtime_list)
    stddev = np.std(runtime_list)

    f = open(filedir+"data.dat", "a")
    f.write("{} {} {}\n".format(filename, mean, stddev))
    f.close()

def gen_cdf(data):
    sorted_data = np.sort(data)
    cdf_data = 1 * np.arange(len(sorted_data)) / float(len(sorted_data) - 1)
    # print(cdf_data)
    return cdf_data

def gen_data_file(filedir, filename, out_filedir, out_filename):
    f = open(filedir+filename)
    data = []
    for line in f:
        runtime = float(line.strip())
        data.append(runtime)
    f.close()

    cdf_data = gen_cdf(data)
    data = np.sort(data)
    try:
        f = open(out_filedir+out_filename, "w")
        for i in range(len(data)):
            row = "{:.4f} {} \n".format(cdf_data[i], data[i])
            f.write(row)
    except ValueError:
        print(ValueError)
    finally:
        f.close()

def gen_data_file_flash(filedir, filename, out_filedir, out_filename):
    f = open(filedir+filename)
    data = []
    for line in f:
        runtime = float(line.strip())
        print(runtime)
        exit()
        data.append(runtime)
    f.close()

    cdf_data = gen_cdf(data)
    data = np.sort(data)
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
    file_dir  = '../pyotr/experiments/flash/output/'
    out_filedr = "./"
    # AS_num = 7018
    # pick_num = [2, 3, 4]
    # for p in pick_num:
    #     filename = "as_{}_{}.txt".format(AS_num, p)
    #     cal_mean_stddev(file_dir, filename)
    filename = sys.argv[2]
    print(filename)
    exit()

    gen_data_file_flash(file_dir, filename, file_dir, out_filename)


    