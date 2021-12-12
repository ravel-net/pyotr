"""
Author: Bin Gui, Fangping
This python script is used to load topo into database.

Realistic topolgy: RouteView RIB file and UPDATE file
Source: route-views2.oregon-ix.net
Date: 2021-06-10 10:00

The format of RIB file:
#0  -> BGP protocol
#1  -> unix time in seconds
#2  -> Withdraw or Announce  (B)
#3  -> PeerIP
#4  -> PeerAS
#5  -> Prefix
#6  -> AS_PATH
#7  -> Origin
#8  -> Next_Hop
#9  -> Local_Pref
#10 -> MED
#11 -> Community
#12 -> AtomicAGG
#13 -> AGGREGATOR

"""
import psycopg2
import time
import sys


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

filename = 'rib0610.txt'

def gen_raw_rib_table(filename='rib0610.txt', table_name='rib0610'):
    """
    Load realistic topology(RIB file) into database
    @param filename: The path of RIB file that has been transfered to txt version
    @param table_name: The table name that the RIB data stored
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    fo = open(filename)
    count = 0

    cur.execute("DROP TABLE IF EXISTS {}".format(table_name))
    cur.execute("CREATE TABLE {}(Prefix inet_faure, AS_PATH TEXT, Next_Hop inet_faure, Local_Pref TEXT, MED TEXT)".format(table_name))

    subset = []
    for line in fo:
        
        record = line.split('|')

        subset.append((record[5],record[6],record[8],record[9],record[10]))

        count += 1

        if len(subset) == 100:
            query = "INSERT INTO {}(Prefix, AS_PATH, Next_Hop, Local_Pref, MED) VALUES (%s, %s, %s, %s, %s)".format(table_name)
            cur.executemany(query, subset)
            del subset[:] 

        if count  % 100000 == 0:
            print(count)

        if (count > 400000):
            break

    if len(subset) != 100 and len(subset) != 0:      
        query = "INSERT INTO {}(Prefix, AS_PATH, Next_Hop, Local_Pref, MED) VALUES (%s, %s, %s, %s, %s)".format(table_name)
        cur.executemany(query, subset)
    fo.close()

    conn.commit()
    conn.close()

# generate subset prefix by sub queries
# input: size (the number of prefix)
def gen_subset_rib(table_name='rib0610', size = 1000):
    """
    generate subset topo with n different prefixes by sub queries
    @param table_name: the table that stores the whole RIB data
    @param size: the number of unique prefixes
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    cur.execute("DROP TABLE IF EXISTS rib{}".format(size))
    cur.execute("CREATE TABLE rib{}(Prefix inet_faure, AS_PATH TEXT, Next_Hop inet_faure, Local_Pref TEXT, MED TEXT)".format(size))

    cur.execute('insert into rib{} select * from {} where prefix in (select distinct prefix from {} limit {})'.format(size, table_name, table_name, size))

    # create index for column prefix
    index_sql = "CREATE INDEX index_prefix_rib{} \
                ON public.rib{} USING btree \
                (prefix varchar_ops ASC NULLS LAST)\
                TABLESPACE pg_default;".format(size, size)

    # cur.execute(index_sql) TODO: Make inet_faure index-ible

    conn.commit()
    conn.close()


if __name__ == '__main__':

    # create table rib0610
    print("create table rib0610 table...")
    gen_raw_rib_table()
    print("Done!")

    #sizes = [1000, 10000, 100000, 922067]
    sizes = [] #, 10000, 100000, 922067]
    print(f"Arguments count: {len(sys.argv)}")
    if (len(sys.argv) < 2):
        print("Please enter the table size")
        exit()
    for i, arg in enumerate(sys.argv):
        if (i > 0):
            sizes.append(int(arg))
    print (sizes)
    for size in sizes:
        print("create subset rib table size ", size)
        begin = time.time()
        gen_subset_rib("rib0610",size)
        print("Done! timing: ", time.time()-begin)


