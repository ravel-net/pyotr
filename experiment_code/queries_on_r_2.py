from z3 import *
from tqdm import tqdm
import psycopg2
from psycopg2.extras import execute_values
import re
import time
from remove_contradiction import rem_contrad
from gen_r_table import create_index_source_dest_fid

host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

def q6(r_table = 'rib1000_r', f_table='f_table_rib1000', output='t1_rib1000'):
    """
    q6 in paper that pair-wise reachability under 2-link failure

    @param r_table: the R table
    @param f_table: the F table
    @param output: the table stores the query results
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create ans in database
    cur.execute("DROP TABLE IF EXISTS {} CASCADE;".format(output))
    cur.execute("CREATE TABLE {} ( fid text, source TEXT, dest TEXT, condition TEXT);".format(output))

    # cur.execute("select distinct fid, cond from {} where cond like '%=1%'".format(f_table))
    cur.execute("select distinct fid, condition from {} where mark = 1".format(f_table))

    num = cur.rowcount
    for i in tqdm(range(num)):
        row = cur.fetchone()
        cond_string =  ''.join(row[1])
        #conds_list = re.findall('\(([^)]+)', row[1][0].split(','))
        conds_list = row[1]

        # at least have three protected links
        if len(conds_list) < 3: # no three protected links
            continue
        else:
            x = conds_list[0].split('=')[0]
            y = conds_list[1].split('=')[0]
            z = conds_list[2].split('=')[0]
            
            # x = 1, y = 0, z = 0. x + y + z = 2
            cond = '[{}=1,{}=0,{}=0]'.format(x, y, z)
            # x = 0, y = 0, z = 1. x + y + z = 2
            cond = cond + '|[{}=1,{}=0,{}=0]'.format(z, x, y)
            # x = 0, y = 1, z = 0. x + y + z = 2
            cond = cond + '|[{}=1,{}=0,{}=0]'.format(y, z, x)

            cond = '{'+ cond + '}'

            sel_cur = conn.cursor()
            sel_cur.execute("select fid, source, dest, condition || '{}' from {} where fid = '{}'".format(cond, r_table, row[0]))
            tuples = sel_cur.fetchall()

            sql = 'insert into {} values (%s, %s, %s, %s)'.format(output)
            ins_cur = conn.cursor()
            ins_cur.executemany(sql, tuples)
            # for t in tuples:
            #     ins_cur.execute(sql, t)
            conn.commit()
    conn.close()

# y = 0
def q7(t_table = 't1_rib1000', f_table = 'f_table_rib1000', source = 's', dest = '1299', output='t2_rib1000'):
    """
    q7 in the paper that reachability between source and dest under 2-link failure, specify one of the failure

    @param t_table: the output table of q6
    @param f_table: the F table 
    @param source: AS node
    @param dest: AS node
    @param output: the table stores the result of q7
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create ans in database
    cur.execute("DROP TABLE IF EXISTS {} CASCADE;".format(output))
    cur.execute("CREATE TABLE {} ( fid text, source TEXT, dest TEXT, condition TEXT);".format(output))

    # get fids where source and dest are specific
    cur.execute("select distinct fid from {} where source = '{}' and dest = '{}'".format(t_table, source, dest ))

    num = cur.rowcount
    for i in tqdm(range(num)):
        row = cur.fetchone()

        # find primary link in order to generate condition
        pry_link_cur = conn.cursor()
        # sql = "select distinct cond from {} where fid = '{}' and cond like '%=1%'".format(f_table, row[0])
        sql = "select distinct condition from {} where fid = '{}' and mark = 1".format(f_table, row[0])
        pry_link_cur.execute(sql)

        tuple = pry_link_cur.fetchone()

        if tuple is None:
            continue

        conds_list = re.findall('\(([^)]+)', tuple[0])[0].split(',')

        # at least have 2 paths 
        if len(conds_list) < 2: 
            continue
        else:
            y = conds_list[2].split('=')[0]

            sel_cur = conn.cursor()
            sel_cur.execute("select fid, source, dest, condition || '({}=0)' from {} where source = '{}' and dest = '{}' and fid = '{}'".format(y, t_table, source, dest, row[0]))
            tuples = sel_cur.fetchall()

            sql = 'insert into {} values %s'.format(output)
            execute_values(conn.cursor(), sql, tuples)


def q8(r_table = 'rib1000_r', f_table = 'f_table_rib1000', source = '4788'):
    """
    q8 in the paper that reachability from source when out of the second two protected links, at least one fails

    @param r_table: the R table
    @param f_table: the F table
    @param source: AS node
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create ans in database
    cur.execute("DROP TABLE IF EXISTS ans CASCADE;")
    cur.execute("CREATE TABLE ans ( fid text, source TEXT, dest TEXT, condition TEXT);")

    # get fids where source is specific
    cur.execute("select distinct fid from {} where source = '{}'".format(r_table, source ))

    num = db._cursor.rowcount
    for i in tqdm(range(num)):
        row = cur.fetchone()

        # find primary link in order to generate condition
        pry_link_cur = conn.cursor()
        # sql = "select distinct cond from {} where fid = '{}' and cond like '%=1%'".format(f_table, row[0])
        sql = "select distinct condition from {} where fid = '{}' and mark = 1".format(f_table, row[0])
        pry_link_cur.execute(sql)

        tuple = pry_link_cur.fetchone()
        if tuple is None:
            continue

        conds_list = re.findall('\(([^)]+)', tuple[0])[0].split(',')

        # at least have three protected links
        if len(conds_list) < 3: # no three protected links
            continue
        else:
            # x = conds_list[0].split('=')[0]
            y = conds_list[1].split('=')[0]
            z = conds_list[2].split('=')[0]

            # y = 1, z = 0. y + z < 2
            cond = '[{}=1,{}=0]'.format(y, z)
            # y = 0, z = 1. y + z < 2
            cond = cond + '|[{}=1,{}=0]'.format(z, y)
            # y = 0, z = 0. y + z < 2
            cond = cond + '|[{}=0,{}=0]'.format(y, z)

            cond = '('+ cond + ')'

            sel_cur = conn.cursor()
            sel_cur.execute("select fid, source, dest, condition || '{}' from {} where source = '{}' and fid = '{}'".format(cond, r_table, source, row[0]))
            
            tuples = sel_cur.fetchall()

            sql = 'insert into ans values %s'
            execute_values(conn.cursor(), sql, tuples)




if __name__ == '__main__':
    #tablenames = ['rib1000', 'rib10000', 'rib100000', 'rib922067']
    #r_tables = ['rib1000_r', 'rib10000_r', 'rib100000_r', 'rib922067_r']
    #ftablenames = ['f_table_rib1000', 'f_table_rib10000', 'f_table_rib100000', 'f_table_rib922067']
    # times = [5, 5, 2, 1]
    #times = [1, 1, 1, 1]
    tablenames = ['rib1000']
    r_tables = ['rib1000_r']#, 'rib10000_r', 'rib100000_r', 'rib922067_r']
    ftablenames = ['f_table_rib1000']#, 'f_table_rib10000', 'f_table_rib100000', 'f_table_rib922067']
    # times = [5, 5, 2, 1]
    times = [1]

    
    total_time_sql = 0
    total_time_z3 = 0

    for count in range(0,1):
        for i in range(times[count]):
            
            start_time_q6 = time.time()
            q6(r_table=r_tables[count], f_table=ftablenames[count], output='t1_'+tablenames[count])
            sql_running_time = time.time()-start_time_q6

            s = time.time()
            # rem_contrad_q7(tablename='t1_rib100000')
            z3_running_time = time.time() - s

            total_time_sql = total_time_sql + sql_running_time
            total_time_z3 = total_time_z3 + z3_running_time

            print('sql running time: ', sql_running_time)
            print('z3 running time: ', z3_running_time)
            print('q6 running time: ', sql_running_time + z3_running_time)
        print('Average sql running time: ', total_time_sql / times[count])
        print('Average z3 running time: ', total_time_z3 / times[count])

        # create_index_source_dest_fid(tablename='t1_'+tablenames[count])

    # for count in range(3,4):
    #     for i in range(times[count]):
    #         start_time_q7 = time.time()
    #         q7(source='11686', dest='9498', t_table = 't1_'+tablenames[count], f_table = ftablenames[count], output='t2_'+tablenames[count])
    #         # q7(source='1403', dest='33576', r_table='rib1000_r', f_table='f_table_rib1000')
    #         sql_running_time = time.time()-start_time_q7
    #         print('sql done')
    #         s = time.time()
    #         rem_contrad_q7(tablename='t2_'+tablenames[count])
    #         z3_running_time = time.time() - s

    #         total_time_sql = total_time_sql + sql_running_time
    #         total_time_z3 = total_time_z3 + z3_running_time

    #         print('sql running time: ', sql_running_time)
    #         print('z3 running time: ', z3_running_time)
    #         print('q7 running time: ', sql_running_time + z3_running_time)
    #     print('Average sql running time: ', total_time_sql / times[count])
    #     print('Average z3 running time: ', total_time_z3 / times[count])
    
    # for i in range(times):
    #     start_time_q8 = time.time()
    #     q8(source='6461', r_table='rib1000_r', f_table='f_table_rib1000')
    #     sql_running_time = time.time()-start_time_q8

    #     s = time.time()
    #     rem_contrad_q7(tablename='ans')
    #     z3_running_time = time.time() - s

    #     total_time_sql = total_time_sql + sql_running_time
    #     total_time_z3 = total_time_z3 + z3_running_time

    #     print('sql running time: ', sql_running_time)
    #     print('z3 running time: ', z3_running_time)
    #     print('q8 running time: ', sql_running_time + z3_running_time)
    # print('Average sql running time: ', total_time_sql / times)
    # print('Average z3 running time: ', total_time_z3 / times)

    

                


    
