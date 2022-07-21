import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import experiments.faure_link_failure.gen_reachability_table as gen_reachability_table
import experiments.gen_large_tableau.gen_tableau_script as gen_tableau_script

def reachability_link_failure(file_dir, filename, AS_num, pick_num):
    # generate f table
    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)
    fwd_tablename = "fwd_{}".format(AS_num)

    path_links, source, dest = gen_tableau_script.gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)

    r1_time = gen_reachability_table.r1(fwd_tablename, AS_num)
    count, rn_time = gen_reachability_table.rn(fwd_tablename, AS_num)
    r_table, union_time = gen_reachability_table.union(count, AS_num, source, dest)

    gen_reachability_table.clean(count, AS_num)

    check_time = gen_reachability_table.check(r_table, 'Int')
    
    return len(path_links), r1_time, rn_time, union_time, check_time



if __name__ == '__main__':
    file_dir  = '/../../topo/ISP_topo/'
    pick_num = [2]

    AS_num = 7018
    runs = 100
    for p in pick_num:
        filename = "{}_edges.txt".format(AS_num)
        f = open("./results/as_{}_IP_seperate.txt".format(AS_num, p), 'w')
        f.write("len_path r1_time rn_time union_time check_time\n")
        for r in range(runs):
            
            len_path, r1_time, rn_time, union_time, check_time = reachability_link_failure(file_dir, filename, AS_num, p)
            total_time = r1_time + rn_time + union_time + check_time
            f.write("{} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len_path, total_time*1000, r1_time*1000, rn_time*1000, union_time*1000, check_time*1000))
            print("run{}".format(r), "AS_num{}".format(AS_num), "running time:{:.4f}(ms)".format(total_time*1000))
        f.close()





    

