import psycopg2
from tqdm import tqdm
import time
import sys


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

def gen_r_table(num = 3, tablename = 'rib1000'):
    """
    Generate R table.
    R(fid, source, dest, cond) = F(fid, nid1, nid2, condition);
    R(fid, source, dest, cond) = R(fid, source, dest, cond), F(fid, nid1, nid2, condition), R.condition&F.condition;

    @param num: the recursive times (Rn)
    @param tablename: The sub RIB table
    """
    f_table = "f_table_" + tablename

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database
    cur.execute("DROP TABLE IF EXISTS {}_R1 CASCADE;".format(tablename))
    cur.execute("CREATE TABLE {}_R1 AS SELECT fid, nid1 as source, nid2 as dest, condition as condition from {};".format(tablename, f_table))

    union_sql = "create table {}_R as select * from {}_R1".format(tablename, tablename)

    for count in tqdm(range(2, num+1)):
        new_r = '{}_R{}'.format(tablename, count )
        old_r = '{}_R{}'.format(tablename, count-1 )

        cur.execute('DROP TABLE IF EXISTS {} CASCADE;'.format(new_r))

        sql = "CREATE TABLE {} AS \
            select \
            {}.fid, {}.source as source, {}.nid2 as dest, array_cat({}.condition, {}.condition)  as condition \
            from \
            {} inner join {}\
            on \
            {}.fid = {}.fid and \
            {}.nid1 = {}.dest and \
            {}.nid2 != {}.source;" \
            . format(
                new_r, 
                f_table, old_r, f_table, old_r, f_table, 
                old_r, f_table,  
                f_table, old_r, 
                f_table, old_r, 
                f_table, old_r
                )
        
        cur.execute(sql)

        union_sql = union_sql + ' union all select * from {}'.format(new_r)
    
    cur.execute("DROP TABLE IF EXISTS {}_R CASCADE;".format(tablename))
    cur.execute(union_sql)

    conn.commit()
    conn.close()

def create_index_source_dest_fid(tablename = 'rib1000_r'):
    """
    create index for source, dest and fid attributes in the R table

    @param tablename: The name of the R table 
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    sql = "CREATE INDEX index_source_dest_fid_{}\
            ON public.{} USING btree\
            (fid varchar_ops ASC NULLS LAST, \
            source varchar_ops ASC NULLS LAST, \
            dest varchar_ops ASC NULLS LAST) \
            TABLESPACE pg_default;".format(tablename, tablename)
    cur.execute(sql)
    conn.commit()
    conn.close()



if __name__ == '__main__':
    tablenames = [] #, 10000, 100000, 922067]
    print(f"Arguments count: {len(sys.argv)}")
    if (len(sys.argv) < 2):
        print("Please enter the table size")
        exit()
    for i, arg in enumerate(sys.argv):
        if (i > 0):
            tablenames.append("rib"+arg)
    print (tablenames)    # times = []
    # tablenames = ['rib100000']
    num = 10 # 

    for table in tablenames:
        print("create r table - ", table)
        start_time = time.time()

        gen_r_table(num=num, tablename=table)

        print('Done! {} running time: {}'.format(table, time.time()-start_time))

        # create_index_source_dest_fid(tablename= table + '_r')




