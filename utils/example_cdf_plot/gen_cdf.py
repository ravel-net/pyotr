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

def extractCol(col_name, filepath):
    data = []
    col_index = 0
    with open(filepath) as f:
        i = 0
        tmp = f.readlines()
        for line in tmp:
            if (i == 0):
                for col in line.split("|"):
                    print(col)
                    if col.strip() == col_name:
                        break
                    col_index += 1
            else:
                data_part = line.split("|")[col_index].strip()
                data.append(float(data_part))
            i += 1
    return data
            # data.append(line.strip())


if __name__ == '__main__':
    filepath = "../../experiments/Batfish/result_UDP.txt"
    data = extractCol("total_time", filepath)
    cdf_data = gen_cdf(data)
    print(cdf_data)
    out_filename = "7018_batfish.dat"
    gen_data_file(data, cdf_data, out_filename)
    # for s in systems:
    #     data = []
    #     for size in sizes:
    #         filename = "exp_{}_close_data{}.txt".format(s, size)
    #         t = get_total_groups_time(filepath+filename)
    #         data.append(t)
    #     cdf_data = gen_cdf(data)
    #     out_filename = "data/{}_totalgps.dat".format(s)
    #     gen_data_file(data, cdf_data, out_filename)
    