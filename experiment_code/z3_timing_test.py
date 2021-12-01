from unicodedata import name
from z3 import *
from tqdm import tqdm
import psycopg2
import re
import time
from queries_on_r_2 import q6
#from db import DB


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'condition'

#only for q7/q8
def rem_contrad(tablename = 'ans'):
    global part_var
    global part_check
    global part_delete

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    cur.execute('select * from {}'.format(tablename))

    del_cur = conn.cursor()
    num = cur.rowcount
    print("num",num)
    count = 0
    for i in tqdm(range(num)):
        row = cur.fetchone()
        check = process(row[3])
        if check == False:
            delete_begin = time.time()
            sql = "delete from {} where fid = '{}' and source = '{}' and dest = '{}' and cond = '{}'".format(tablename, row[0], row[1], row[2], row[3])
            del_cur.execute(sql)
            part_delete = part_delete + (time.time() - delete_begin)

            count = count + del_cur.rowcount

    print("Part variable average time is: ", part_var / num)
    print("Part check average time is: ", part_check / num)
    print("Part delete average time is: ", part_delete / count)
    print("Part variable total time is: ", part_var)
    print("Part check total time is: ", part_check)
    print("Part delete total time is: ", part_delete)
    print('Total number of rows deleted: ', count)


def process(cond):
    global part_var
    global part_check

    s = Solver()

    var_begin = time.time()
    conds_list = re.findall('\(([^)]+)', cond) # find all conditions in parenthess
    for count, c in enumerate(conds_list):

        if '[' in c:
            conds = re.findall('\[([^\]]+)', cond) # find all conditions in square brakets
            and_list = []
            
            for con in conds:
                var_list, val_list = process_con_or_disjunction(con, ',')
                and_list.append(And([ String(var) == StringVal(val) for var, val in zip(var_list, val_list)]))
            s.add(Or([a for a in and_list]))

        elif  '|' in c:
            var_list, val_list = process_con_or_disjunction(c, '|')
            s.add(Or([String(var) == StringVal(val) for var, val in zip(var_list, val_list)]))

        elif ',' in c:
            var_list, val_list = process_con_or_disjunction(c, ',')
            s.add(And([ String(var) == StringVal(val) for var, val in zip(var_list, val_list)]))
        else:
            strs = c.split('=')
            s.add(String(strs[0]) == StringVal(strs[1]))
    part_var = part_var + (time.time() - var_begin)

    check_begin = time.time()
    result = s.check()
    part_check = part_check + (time.time() - check_begin)

    if result == sat:
        # print(s.model())
        return True
    else:
        return False

def process_con_or_disjunction(cond, delimiter):    
    conds = cond.split(delimiter)

    var_list = []
    val_list = []
    for c in conds:
        strs = c.split('=')
        
        var_list.append(strs[0])
        val_list.append(strs[1])
    return var_list, val_list

if __name__ == '__main__':
    start_time_q6 = time.time()
    q6(r_table='rib1000_r', f_table='f_table_rib1000', output='ans')
    sql_running_time = time.time()-start_time_q6

    part_var = 0
    part_check = 0
    part_delete = 0

    s = time.time()
    rem_contrad(tablename='ans')
    z3_running_time = time.time() - s

    print('sql running time: ', sql_running_time)
    print('z3 running time: ', z3_running_time)
    print('q6 running time: ', sql_running_time + z3_running_time)
