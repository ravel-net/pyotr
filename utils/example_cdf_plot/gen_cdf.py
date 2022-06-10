import enum
import numpy as np

import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'new_experiments', 'variable_closure', 'data')
sys.path.append(filename)


def get_data_scalibility(filename, col_index):
    data = []
    with open(filename) as f:
        for line in f:
            cols = line.split()
            
            if len(cols) == 11:
                try:
                    float(cols[col_index])
                    data.append(float(cols[col_index]))
                except ValueError:
                    continue
    print(data)
    return data

def get_total_groups_time(filename):
    data = 0
    with open(filename) as f:
        for line in f:
            if ":" in line or "Total groups running time" in line:
                cols = line.split(":")
            
                try:
                    data = float(cols[1])
                except ValueError:
                    continue
    print(data)
    return data

def gen_cdf(data):
    sorted_data = np.sort(data)
    cdf_data = 1 * np.arange(len(sorted_data)) / float(len(sorted_data) - 1)
    print(cdf_data)
    return cdf_data

def gen_data_file(data, cdf_data, out_filename):
    data = np.sort(data)
    try:
        f = open(out_filename, "w")
        for i in range(len(data)):
            row = "{:.2f} {} \n".format(cdf_data[i], data[i])
            f.write(row)
    except ValueError:
        print(ValueError)
    finally:
        f.close()


if __name__ == '__main__':
    filepath = "../../variable_closure/data/"
    systems = ["faure", "pyotr"]
    # filenames = [
    #     "exp_faure_close_data100.txt", 
    #     "exp_faure_close_data1000.txt", 
    #     "exp_faure_close_data10000.txt",
    #     "exp_pytro_close_data100.txt",
    #     "exp_pytro_close_data1000.txt"
    #     ]
    sizes = [100, 1000, 10000]
    # col_index = [2, 3, -1] # length, data time, total time per group
    # col_name = ["tuples", "data", "totalpergp"]

    # for s in systems:
    #     for size in sizes:
    #         filename = "exp_{}_close_data{}.txt".format(s, size)

    #         for idx, col_idx in enumerate(col_index):
    #             data = get_data_scalibility(filepath+filename, col_idx)

    #             cdf_data = gen_cdf(data)
    #             out_filename = "data/{}_{}_{}.dat".format(s, size, col_name[idx])
    #             gen_data_file(data, cdf_data, out_filename)
    for s in systems:
        data = []
        for size in sizes:
            filename = "exp_{}_close_data{}.txt".format(s, size)
            t = get_total_groups_time(filepath+filename)
            data.append(t)
        cdf_data = gen_cdf(data)
        out_filename = "data/{}_totalgps.dat".format(s)
        gen_data_file(data, cdf_data, out_filename)
    