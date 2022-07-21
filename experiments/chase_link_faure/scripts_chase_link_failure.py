import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import psycopg2
from psycopg2.extras import execute_values
import Applications.Chase.chase as chase
import databaseconfig as cfg
import experiments.gen_large_tableau.gen_tableau_script as gen_tableau_script

conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
cursor = conn.cursor()

'''
hard coding, assume location number is value, others are variables. Only one tuple for dependency
#TODO, generilize it
'''
def apply_link_fail_dependency(dependency_tuple, instance_name, bp_next_node, insert_acl):

    location = dependency_tuple[1]
    sql = "select f, '{}', acl from {} where loc = '{}'".format(location, instance_name, location)

    check_begin = time.time()
    cursor.execute(sql)
    check_end = time.time()

    results = cursor.fetchall()
    
    if len(results) == 0:
        print("no affected row!")
        conn.commit()
        return check_end-check_begin, 0
    else:
        inserted_tuples = []
        for tuple in results:
            f = tuple[0]
            acl = tuple[2]

            loc = bp_next_node
            acl.append(insert_acl)

            inserted_tuples.append((f, loc, "{"+", ".join(acl)+"}"))
        insert_begin = time.time()
        insert_sql = "insert into {} values %s".format(instance_name)
        execute_values(cursor, insert_sql, inserted_tuples)
        insert_end = time.time()

        conn.commit()

        return check_end-check_begin, insert_end-insert_begin

def check_is_trivial(data_instance, dependency_summary):
    f = dependency_summary[0]
    loc = dependency_summary[1]
    acl = dependency_summary[2]

    sql = "select * from {} where f = '{}' and loc = '{}' and acl = '{}'".format(data_instance, f, loc, '{'+", ".join(acl)+'}')
    check_begin = time.time()
    cursor.execute(sql)
    check_end = time.time()
    conn.commit()

    if cursor.rowcount > 0:
        print("It is trivial!")
        return True, check_end-check_begin
    else:
        print("It is not trivial!")
        return False, check_end-check_begin

def gen_linkfail_dependency(primary_link, bp_next_node):
    sigma = ('f', primary_link[0], 'acl')
    sigma_bp_next_node = bp_next_node
    sigma_insert_acl = primary_link[0]

    return sigma, sigma_bp_next_node, sigma_insert_acl


def script_chase_link_failure(file_dir, filename, AS_num, pick_num, data_instance_name):
    # generate f table
    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)
    fwd_tablename = "fwd_{}".format(AS_num)

    link_failures_dependencies, sigma3 = gen_tableau_script.gen_dependencies_for_link_failures_chase(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)
    
    print("link_failures_dependencies", link_failures_dependencies)
    print("sigma3", sigma3)

    attributes = ['f', 'loc', 'acl']
    datatypes = ['inet_faure', 'inet_faure', 'text[]']

    chase.load_table(attributes, datatypes, data_instance_name, sigma3["sigma3_tuples"])

    total_check_applicable_time = 0
    total_insert_time = 0
    for dependency in link_failures_dependencies:
        check_applicable_time, insert_time = apply_link_fail_dependency(dependency["dependency_tuple"], data_instance_name, dependency["dependency_bp_next_node"], dependency["dependency_insert_acl"])

        total_check_applicable_time += check_applicable_time
        total_insert_time += insert_time
    
    ans, check_trivial_time = check_is_trivial(data_instance_name, sigma3["sigma3_summary"])

    return ans, total_check_applicable_time, total_insert_time, check_trivial_time
    
        

if __name__ == '__main__':

    # file_dir  = '/../../topo/ISP_topo/'
    # pick_num = 2

    # AS_num = 7018
    # filename = "{}_edges.txt".format(AS_num)
    # data_instance_name = "sigma3"
    # ans, total_check_applicable_time, total_insert_time, check_trivial_time = script_chase_link_failure(file_dir, filename, AS_num, pick_num, data_instance_name)

    # print("Whether is trivial:", ans)
    # print("check applicable time", total_check_applicable_time)
    # print("insert time", total_insert_time)
    # print("check trivial time", check_trivial_time)
    # attributes = ['f', 'loc', 'acl']
    # datatypes = ['int4_faure', 'int4_faure', 'text[]']
    

    # sigma3_instance = [('f', '1', '{}')]
    # sigma3_summary = ['f', '5', ['1', '2']]
    # chase.load_table(attributes, datatypes, "sigma3_a", sigma3_instance)

    # sigma1_a = ('f', '1', 'acl')
    # sigma1_a_bp_next_node = '3'
    # sigma1_a_insert_acl = '1'
    # sigma1_a_check_time, sigma1_a_insert_time = apply_link_fail_dependency(sigma1_a, 'sigma3_a', sigma1_a_bp_next_node, sigma1_a_insert_acl)

    # sigma1_b = ('f', '3', 'acl')
    # sigma1_b_bp_next_node = '5'
    # sigma1_b_insert_acl = '2'
    # sigma1_b_check_time, sigma1_b_insert_time = apply_link_fail_dependency(sigma1_b, 'sigma3_a', sigma1_b_bp_next_node, sigma1_b_insert_acl)

    # ans_a, sigma3_a_check_trivial = check_is_trivial("sigma3_a", sigma3_summary)

    # print("Whether is trivial:", ans_a)
    # print("check applicable time", sigma1_a_check_time+sigma1_b_check_time)
    # print("insert time", sigma1_a_insert_time+sigma1_b_insert_time)
    # print("check trivial time", sigma3_a_check_trivial)

    # sigma3_instance = [('f', '1', '{}')]
    # sigma3_summary = ['f', '4', ['1', '2']]
    # chase.load_table(attributes, datatypes, "sigma3_b", sigma3_instance)

    # sigma1_a = ('f', '1', 'acl')
    # sigma1_a_bp_next_node = '3'
    # sigma1_a_insert_acl = '1'
    # sigma1_a_check_time, sigma1_a_insert_time = apply_link_fail_dependency(sigma1_a, 'sigma3_b', sigma1_a_bp_next_node, sigma1_a_insert_acl)

    # sigma1_b = ('f', '2', 'acl')
    # sigma1_b_bp_next_node = '4'
    # sigma1_b_insert_acl = '2'
    # sigma1_b_check_time, sigma1_b_insert_time = apply_link_fail_dependency(sigma1_b, 'sigma3_b', sigma1_b_bp_next_node, sigma1_b_insert_acl)

    # ans_b, sigma3_b_check_trivial = check_is_trivial("sigma3_b", sigma3_summary)

    # print("Whether is trivial:", ans_b)
    # print("check applicable time", sigma1_a_check_time+sigma1_b_check_time)
    # print("insert time", sigma1_a_insert_time+sigma1_b_insert_time)
    # print("check trivial time", sigma3_b_check_trivial)

    attributes = ['f', 'loc', 'acl']
    datatypes = ['inet_faure', 'inet_faure', 'text[]']

    runs = 100

    f = open("./results/chase_a.txt", 'w')
    f.write("total check_applicable1 check_applicable2 insert_time1 insert_time2 check_trivial\n")
    for r in range(runs):
        sigma3_instance = [('f', '1.0.0.1', '{}')]
        sigma3_summary = ['f', '1.0.0.5', ['1', '2']]
        chase.load_table(attributes, datatypes, "sigma3_a", sigma3_instance)

        sigma1_a = ('f', '1.0.0.1', 'acl')
        sigma1_a_bp_next_node = '1.0.0.3'
        sigma1_a_insert_acl = '1'
        sigma1_a_check_time, sigma1_a_insert_time = apply_link_fail_dependency(sigma1_a, 'sigma3_a', sigma1_a_bp_next_node, sigma1_a_insert_acl)

        sigma2_a = ('f', '1.0.0.3', 'acl')
        sigma2_a_bp_next_node = '1.0.0.5'
        sigma2_a_insert_acl = '2'
        sigma2_a_check_time, sigma2_a_insert_time = apply_link_fail_dependency(sigma2_a, 'sigma3_a', sigma2_a_bp_next_node, sigma2_a_insert_acl)

        ans_a, sigma3_a_check_trivial = check_is_trivial("sigma3_a", sigma3_summary)

        print("Whether is trivial:", ans_a)
        print("check applicable time", sigma1_a_check_time+sigma2_a_check_time)
        print("insert time", sigma1_a_insert_time+sigma2_a_insert_time)
        print("check trivial time", sigma3_a_check_trivial)

        total_time = sigma1_a_check_time+sigma2_a_check_time+sigma1_a_insert_time+sigma2_a_insert_time+sigma3_a_check_trivial
        f.write("{:.4f} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(total_time*1000, sigma1_a_check_time*1000, sigma2_a_check_time*1000, sigma1_a_insert_time*1000, sigma2_a_insert_time*1000, sigma3_a_check_trivial*1000))
    f.close()

    f = open("./results/chase_b.txt", 'w')
    f.write("total check_applicable1 check_applicable2 insert_time1 insert_time2 check_trivial\n")
    for r in range(runs):
        sigma3_instance = [('f', '1.0.0.1', '{}')]
        sigma3_summary = ['f', '1.0.0.4', ['1', '2']]
        chase.load_table(attributes, datatypes, "sigma3_b", sigma3_instance)

        sigma1_b = ('f', '1.0.0.1', 'acl')
        sigma1_b_bp_next_node = '1.0.0.3'
        sigma1_b_insert_acl = '1'
        sigma1_b_check_time, sigma1_b_insert_time = apply_link_fail_dependency(sigma1_b, 'sigma3_b', sigma1_b_bp_next_node, sigma1_b_insert_acl)

        sigma2_b = ('f', '1.0.0.2', 'acl')
        sigma2_b_bp_next_node = '1.0.0.4'
        sigma2_b_insert_acl = '2'
        sigma2_b_check_time, sigma2_b_insert_time = apply_link_fail_dependency(sigma2_b, 'sigma3_b', sigma2_b_bp_next_node, sigma2_b_insert_acl)

        ans_b, sigma3_b_check_trivial = check_is_trivial("sigma3_b", sigma3_summary)

        print("Whether is trivial:", ans_b)
        print("check applicable time", sigma1_b_check_time+sigma2_b_check_time)
        print("insert time", sigma1_b_insert_time+sigma2_b_insert_time)
        print("check trivial time", sigma3_b_check_trivial)

        total_time = sigma1_b_check_time+sigma2_b_check_time+sigma1_b_insert_time+sigma2_b_insert_time+sigma3_b_check_trivial
        f.write("{:.4f} {:.4f} {:.4f} {:.4f} {:.4f} {:.4f}\n".format(total_time*1000, sigma1_b_check_time*1000, sigma2_b_check_time*1000, sigma1_b_insert_time*1000, sigma2_b_insert_time*1000, sigma3_b_check_trivial*1000))
    f.close()