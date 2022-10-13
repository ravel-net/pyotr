import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import time
from tqdm import tqdm
from Core.Homomorphism.Datalog.program import DT_Program
from utils.fattree.fattree_generator import Fattree

def test_scalability(runs, k, dst):
    tree = Fattree(k)
    program_str = tree.generate_base_program(dst)

    total_time = 0
    for r in tqdm(range(runs)):

        program = DT_Program(program_str, {"R":["integer", "integer", "integer[]", "integer"]})
        begin = time.time()
        program.minimize()
        end = time.time()

        total_time += end-begin
    
    print("\n*****completion time for k={}: {:.4f}*****".format(k, total_time/runs))
    return total_time/runs
if __name__ == '__main__':
    ks = [4, 8, 16, 32]
    r = 1
    f = open("./scal_results.txt", "w")
    f.write("k avg_time\n")
    for k in ks:
        f = open("./scal_results.txt", "a")
        avg_time = test_scalability(r, k, 'h1')
        f.write("{} {:.4f}\n".format(k, avg_time))
        f.close()