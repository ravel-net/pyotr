import psycopg2
import databaseconfig as cfg
from tqdm import tqdm

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()


def gen_join_sql(num_joins=2, tablename="f_table_rib3"):
    tables = []
    constraints = []

    cols = ["t0.n1 as n1", "t{}.n2 as n2".format(num_joins - 1)]

    for i in range(num_joins - 1):
        tables.append("{} t{}".format(tablename, i))
        constraints.append("t{}.n2 = t{}.n1".format(i, i+1))
        constraints.append("t{}.n1 != t{}.n2".format(i, i+1))
    # constraints.append("t{}.n2 = '{}'".format(num_joins - 1, dest))
    tables.append("{} t{}".format(tablename, num_joins-1))
    sql = "select " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    print(sql)
    return sql

def gen_int_table(from_tablename='f_7018', to_tablename='f7018_int'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([int(row[0]), int(row[1]), row[2], row[3]])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 integer, n2 integer, s integer[], condition text[])".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s, %s, %s)".format(to_tablename), tuples)
    conn.commit()

def gen_int_table_reg(from_tablename='f_7018', to_tablename='f7018_intreg'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([int(row[0]), int(row[1])])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 integer, n2 integer)".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(to_tablename), tuples)
    conn.commit()

def gen_int4_faure_table(from_tablename='f_7018', to_tablename='f7018_intf'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([str(row[0]), str(row[1]), row[2], row[3]])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, s integer[], condition text[])".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s, %s, %s)".format(to_tablename), tuples)
    conn.commit()

def gen_int4_faure_table_reg(from_tablename='f_7018', to_tablename='f7018_intfreg'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([str(row[0]), str(row[1])])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure)".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(to_tablename), tuples)
    conn.commit()

def gen_text_table(from_tablename='f_7018', to_tablename='f7018_t'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([str(row[0]), str(row[1]), row[2], row[3]])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 text, n2 text, s integer[], condition text[])".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s, %s, %s)".format(to_tablename), tuples)
    conn.commit()

def gen_text_table_reg(from_tablename='f_7018', to_tablename='f7018_treg'):
    cursor.execute("select * from {}".format(from_tablename))
    count = cursor.rowcount
    tuples = []
    for c in tqdm(range(count)):
        row = cursor.fetchone()
        tuples.append([str(row[0]), str(row[1])])
    cursor.execute("drop table if exists {}".format(to_tablename))
    cursor.execute("create table {} (n1 text, n2 text)".format(to_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(to_tablename), tuples)
    conn.commit()

def load_rf_topo(filename, tablename):
    # f = open("Rocketfuel_Topology/{}_edges.txt".format(filename), "r")
    # line = f.readline()
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 text, n2 text)".format(tablename))
    tuples = []
    with open(filename) as f:
        for line in f:
            nodes = line.split(" ")
            tuples.append([nodes[0].strip(), nodes[1].strip()])
    cursor.executemany("insert into {} values(%s, %s)".format(tablename), tuples)
    conn.commit()

if __name__ == '__main__':
    as_nums = [4755, 3356, 2914, 7018]#, 1755, 6461, 3356]
    # gen_join_sql(num_joins=3, tablename="f_table_rib3")
    for num in as_nums:
        # load_rf_topo("sql/f{}.txt".format(num), "f{}".format(num))
        gen_int4_faure_table(from_tablename='fwd_{}'.format(num), to_tablename='fwd{}_intf'.format(num))
        # gen_text_table(from_tablename='fwd_{}'.format(num), to_tablename='fwd{}_text'.format(num))
        # gen_int_table(from_tablename='f{}'.format(num), to_tablename='f{}_int'.format(num))

    