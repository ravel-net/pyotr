import os
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import datetime
import psycopg2
from tqdm import tqdm
import databaseconfig as cfg
import experiments.gen_large_tableau.func_gen_tableau as func_gen_tableau
import experiments.chase_distributed_invariants.script_chase_distributed_invariants as chase_scripts
from utils.logging import timeit

def run_scalibility():
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    # E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
    # while len(path_nodes) > 6:
    #     E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
    # print("path_nodes: ", len(path_nodes), path_nodes)
    # print("symbolic_IP_mapping", symbolic_IP_mapping)
    # print("---------------------------\n")

    runs = 20
    num_hosts_list = [2, 4, 8, 16, 32, 64, 128]
    # for num_hosts in num_hosts_list:
    #     f1 = open("./results/relevant/runtime_hosts{}_rel.txt".format(num_hosts), "w")
    #     f1.write("len(path) ans count_application gen_z check_applicable operation_time query_answer check_answer\n")
    #     print("num_hosts", num_hosts)
    #     for r in tqdm(range(runs)):
    #         E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
            

    #         ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
    #         egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")
    #         # print("ingress_hosts", ingress_hosts)
    #         # print("egress_hosts", egress_hosts)

    #         # generate dependencies
    #         dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)

    #         gamma_attributes = ['f', 'n', 'x', 'condition']
    #         gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    #         gamma_summary = None

    #         Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    #         Z_datatypes = ['text', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure']
        
    #         '''
    #         for `relevant` case
    #         '''
    #         gamma_tablename_relevant = "W_relevant"
    #         Z_tablename_relevant = "Z_relevant"
    #         gamma_summary = chase_scripts.gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, gamma_tablename_relevant, gamma_attributes, gamma_attributes_datatypes, 'relevant')

    #         # Step 1
    #         Z_tuples, gen_z_time = chase_scripts.gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename_relevant, Z_tablename_relevant, Z_attributes, Z_datatypes)
            
    #         #step2 and step3
    #         ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = chase_scripts.run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename_relevant, gamma_summary)
            
    #         f1.write("{} {} {} {} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len(path_nodes), ans, count_application, total_query_times, gen_z_time*1000, total_check_applicable_time*1000, total_operation_time*1000, total_query_answer_time*1000, total_check_answer_time*1000))

    #     f1.close()
    
    for num_hosts in num_hosts_list:
        f2 = open("./results/all/runtime_hosts{}_all.txt".format(num_hosts), "w")
        f2.write("len(path) ans count_application total_queries gen_z check_applicable operation_time query_answer check_answer total_time\n")
        print("num_hosts", num_hosts)
        for r in tqdm(range(runs)):
            E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
           
            ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
            egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")
            # print("ingress_hosts", ingress_hosts)
            # print("egress_hosts", egress_hosts)
            start = time.time()

            # generate dependencies
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)

            gamma_attributes = ['f', 'n', 'x', 'condition']
            gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
            gamma_summary = None

            Z_attributes = ['f', 'src', 'dst', 'n', 'x']
            Z_datatypes = ['text', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure']
        
            '''
            for `all` case
            '''
            gamma_tablename_all = "W_all"
            Z_tablename_all = "Z_all"
            gamma_summary = chase_scripts.gen_gamma_table(block_list, ingress_hosts, egress_hosts, gamma_tablename_all, gamma_attributes, gamma_attributes_datatypes, 'all')

            # Step 1
            Z_tuples, gen_z_time = chase_scripts.gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename_all, Z_tablename_all, Z_attributes, Z_datatypes)
            
            #step2 and step3
            ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = chase_scripts.run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename_all, gamma_summary)

            end = time.time()
            f2.write("{} {} {} {} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len(path_nodes), ans, count_application, total_query_times, gen_z_time*1000, total_check_applicable_time*1000, total_operation_time*1000, total_query_answer_time*1000, total_check_answer_time*1000, (end-start)*1000))
        f2.close()

def run_ordering_strategies():
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
    while len(path_nodes) != 5:
        E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
    # run_scalibility()
    runs = 50
    num_hosts_list = [8, 16, 32]
    for num_hosts in num_hosts_list:
        print("num_hosts", num_hosts)
        case = 'all'
        f1 = open("./ordering_results/optimal/runtime_hosts{}_optimal_{}.txt".format(num_hosts, case), "w")
        f1.write("len(path) ans count_application total_query_times gen_z check_applicable operation_time query_answer check_answer\n")

        f2 = open("./ordering_results/random/runtime_hosts{}_random_{}.txt".format(num_hosts, case), "w")
        f2.write("len(path) ans count_application total_query_times gen_z check_applicable operation_time query_answer check_answer\n")

        f3 = open("./ordering_results/static/runtime_hosts{}_static_{}.txt".format(num_hosts, case), "w")
        f3.write("len(path) ans count_application total_query_times gen_z check_applicable operation_time query_answer check_answer\n")
        for r in tqdm(range(runs)):

            ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
            egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")
            # print("ingress_hosts", ingress_hosts)
            # print("egress_hosts", egress_hosts)

            # generate dependencies
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)

            '''
            get whitelist
            case: relevant, all
            '''
            gamma_attributes = ['f', 'n', 'x', 'condition']
            gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
            gamma_summary = None
            
            Z_attributes = ['f', 'src', 'dst', 'n', 'x']
            Z_datatypes = ['text', 'text', 'text', 'inet_faure', 'inet_faure']
            
            '''
            for `optimal` order
            '''
            gamma_tablename_optimal= "W_optimal"
            Z_tablename_optimal = "Z_optimal"
            # gamma_summary = chase_scripts.gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, gamma_tablename_optimal, gamma_attributes, gamma_attributes_datatypes, "relevant")
            gamma_summary = chase_scripts.gen_gamma_table(block_list, ingress_hosts, egress_hosts, gamma_tablename_optimal, gamma_attributes, gamma_attributes_datatypes, case)

            # Step 1
            print("optimal")
            Z_tuples, gen_z_time = chase_scripts.gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename_optimal, Z_tablename_optimal, Z_attributes, Z_datatypes)
            
            #step2 and step3
            ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = chase_scripts.run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename_optimal, gamma_summary)
            
            f1.write("{} {} {} {} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len(path_nodes), ans, count_application, total_query_times, gen_z_time*1000, total_check_applicable_time*1000, total_operation_time*1000, total_query_answer_time*1000, total_check_answer_time*1000))

            '''
            for `random` order
            '''
            gamma_tablename_random = "W_random"
            Z_tablename_random = "Z_random"
            # gamma_summary = chase_scripts.gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, gamma_tablename_random, gamma_attributes, gamma_attributes_datatypes, "relevant")
            gamma_summary = chase_scripts.gen_gamma_table(block_list, ingress_hosts, egress_hosts, gamma_tablename_random, gamma_attributes, gamma_attributes_datatypes, case)

            # Step 1
            print("random")
            Z_tuples, gen_z_time = chase_scripts.gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename_random, Z_tablename_random, Z_attributes, Z_datatypes)
            
            #step2 and step3
            ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = chase_scripts. run_chase_distributed_invariants_in_random_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename_random, gamma_summary)

            f2.write("{} {} {} {} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len(path_nodes), ans, count_application, total_query_times, gen_z_time*1000, total_check_applicable_time*1000, total_operation_time*1000, total_query_answer_time*1000, total_check_answer_time*1000))

            '''
            for `static` order
            '''
            gamma_tablename_random = "W_static"
            Z_tablename_random = "Z_static"
            # gamma_summary = chase_scripts.gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, gamma_tablename_random, gamma_attributes, gamma_attributes_datatypes, "relevant")
            gamma_summary = chase_scripts.gen_gamma_table(block_list, ingress_hosts, egress_hosts, gamma_tablename_random, gamma_attributes, gamma_attributes_datatypes, case)

            # Step 1
            print("static")
            Z_tuples, gen_z_time = chase_scripts.gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename_random, Z_tablename_random, Z_attributes, Z_datatypes)
            
            #step2 and step3
            ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = chase_scripts.run_chase_distributed_invariants_in_specific_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename_random, gamma_summary)
            # if count_application >= 12:
            #     print("E_tuples = ", E_tuples)
            #     print("path_nodes", path_nodes)
            #     print("symbolic_IP_mapping", symbolic_IP_mapping)
            #     print("block_list", block_list)
            #     print("ingress_hosts", ingress_hosts)
            #     print("egress_hosts", egress_hosts)
            #     print("dependencies = ", dependencies)
            #     exit()
            f3.write("{} {} {} {} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(len(path_nodes), ans, count_application, total_query_times, gen_z_time*1000, total_check_applicable_time*1000, total_operation_time*1000, total_query_answer_time*1000, total_check_answer_time*1000))
            
        f1.close()
        f2.close()
        f3.close()

@timeit
def run_ordering_strategies_new(conn, runs=10, num_hosts_list=[2], random_path=True, ordering_strategy='random', orderings=None, mode='all'):
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    E_tuples, path_nodes, symbolic_IP_mapping = None, None, None
    if not random_path:
        E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(conn, file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)

    for num_hosts in num_hosts_list:
        for r in tqdm(range(runs)):
            if random_path: 
                E_tuples, path_nodes, symbolic_IP_mapping = chase_scripts.gen_E_for_chase_distributed_invariants(conn, file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)

            ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
            egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")

            # generate dependencies
            dependencies, relevant_in_hosts, relevant_out_hosts, block_list = chase_scripts.gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)

            '''
            get whitelist
            '''
            gamma_attributes = ['f', 'n', 'x', 'condition']
            gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
            gamma_summary = None
            gamma_tablename= "W_{}".format(ordering_strategy)
            gamma_summary = chase_scripts.gen_gamma_table(conn, block_list, ingress_hosts, egress_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, mode)

            
            Z_attributes = ['f', 'src', 'dst', 'n', 'x']
            Z_datatypes = ['text', 'text', 'text', 'inet_faure', 'inet_faure']
            Z_tablename = "Z_{}".format(ordering_strategy)
            Z_tuples = chase_scripts.gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
            
            #step2 and step3
            ans = chase_scripts.run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
            
            print('answer', ans)
        
        if os.path.isfile('program.log'):
            os.rename('program.log', 'host{}_{}Order_{}Mode_{}.log'.format(num_hosts, ordering_strategy, mode, datetime.datetime.now().strftime('%Y%m%d%H%M%S')))
if __name__ == '__main__':
    # run_scalibility()
    # run_ordering_strategies()

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    runs=10
    num_hosts_list=[2]
    random_path=True
    ordering_strategy='specific'
    orderings=[0, 1, 2, 6, 3, 4, 5]
    mode='all'

    run_ordering_strategies_new(conn, runs, num_hosts_list, random_path,ordering_strategy, orderings, mode)
