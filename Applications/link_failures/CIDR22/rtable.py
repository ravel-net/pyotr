import psycopg2
import databaseconfig as cfg

CONN = None

"""
class Rtable is used to generate c-table-based r table
"""
class Rtable:
    def __init__(self, dbname, f_table, as_number):
        global CONN
        CONN = psycopg2.connect(host=cfg.postgres["host"], database=dbname, user=cfg.postgres["user"], password=cfg.postgres["password"])
        self.cursor = CONN
        self.F_TABLE = f_table
        self.AS_NUMBER = as_number

    def r1(self):
        r1 = "r1_{}".format(self.AS_NUMBER)
        sql = "DROP TABLE IF EXISTS {} CASCADE;".format(r1)
        self.cursor.execute(sql)

        sql = "CREATE TABLE {} AS SELECT n1, n2, s, ARRAY[n1, n2] as path, condition FROM {};".format(r1, self.F_TABLE)
        self.cursor.execute(sql)
        CONN.commit()

    def rn(self):
        count = 2
        while True:
            r_next = "r{}_{}".format(count, self.AS_NUMBER)
            r_prev = "r{}_{}".format(count - 1, self.AS_NUMBER)

            sql = "drop table if exists {};".format(r_next)
            self.cursor.execute(sql)

            sql = "create table {} as SELECT \
                    {}.n1 as n1, {}.n2 as n2, \
                    array_cat({}.s, {}.s) as s, \
                    array_cat({}.path, ARRAY[{}.n2]) as path, \
                    array_cat({}.condition, {}.condition) as condition \
                    FROM {}, {} \
                    WHERE {}.n2 = {}.n1 and {}.n1 != {}.n2 \
                    and not {}.n2 = ANY({}.path);" \
                    .format(r_next, 
                    r_prev, self.F_TABLE, 
                    self.F_TABLE, r_prev, 
                    r_prev, self.F_TABLE, 
                    r_prev, self.F_TABLE, 
                    r_prev, self.F_TABLE, 
                    r_prev, self.F_TABLE, r_prev, self.F_TABLE, 
                    self.F_TABLE, r_prev)

            self.cursor.execute(sql)
            num = self.cursor.rowcount
            
            CONN.commit()

            if num == 0:
                return count
            
            count = count + 1
            
    def union(self, count):
        sql = "drop table if exists R_{};".format(self.AS_NUMBER)
        self.cursor.execute(sql)

        sql = "create table R_{} as ".format(self.AS_NUMBER)

        for i in range(1, count):
            r_table = "r{}_{}".format(i, self.AS_NUMBER)
            sql = sql + "select n1, n2, s, condition from {} union ".format(r_table)
        
        sql = sql[:-6]

        self.cursor.execute(sql)
        CONN.commit()
    
    def select(self, dest):
        spc_r_name = 'R_{}_s'.format(self.AS_NUMBER)
        sql = "drop table if exists {}".format(spc_r_name);
        self.cursor.execute(sql)

        sql = "create table {} as select * from R_{} where n2 = {}".format(spc_r_name, self.AS_NUMBER, dest)
        self.cursor.execute(sql)
        CONN.commit()

if __name__ == '__main__':
    as_num = 7018
    generator = Rtable(dbname="cidr", f_table='fwd_{}'.format(as_num), as_number=as_num)

    generator.r1()
    count = generator.rn()

    generator.union(count=count)



