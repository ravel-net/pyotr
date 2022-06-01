import psycopg2
import databaseconfig as cfg

CONN = None

"""
class RtableFc is used to generate concrete r table
"""
class RtableFc:
    def __init__(self, dbname, f_table, as_number):
        global CONN
        CONN = psycopg2.connect(host=cfg.postgres["host"], database=dbname, user=cfg.postgres["user"], password=cfg.postgres["password"])
        self.cursor = CONN
        self.F_TABLE = f_table
        self.AS_NUMBER = as_number

    def r1(self):
        r1 = "r1_{}".format(self.F_TABLE)
        sql = "DROP TABLE IF EXISTS {} CASCADE;".format(r1)
        self.cursor.execute(sql)

        sql = "CREATE TABLE {} AS SELECT n1, n2, s, ARRAY[n1, n2] as path FROM {};".format(r1, self.F_TABLE)
        self.cursor.execute(sql)
        CONN.commit()
        

    def rn(self):
        count = 2
        while True:
            r_next = "r{}_{}".format(count, self.F_TABLE)
            r_prev = "r{}_{}".format(count - 1, self.F_TABLE)

            sql = "drop table if exists {};".format(r_next)
            self.cursor.execute(sql)
            CONN.commit()

            sql = "create table {} as select {}.n1 as n1, {}.n2 as n2, \
                array_cat({}.s, {}.s) as s, \
                array_cat({}.path, ARRAY[{}.n2]) as path \
                from {}, {} \
                where {}.n2 = {}.n1 and {}.n1 != {}.n2;".format(r_next, r_prev, self.F_TABLE,
                r_prev, self.F_TABLE,
                r_prev, self.F_TABLE,
                r_prev, self.F_TABLE,
                r_prev, self.F_TABLE, r_prev, self.F_TABLE
                )

            # sql = "create table {} as SELECT \
            #         {}.n1 as n1, {}.n2 as n2, \
            #         array_cat({}.s, {}.s) as s, \
            #         array_cat({}.path, ARRAY[{}.n2]) as path \
            #         FROM {}, {} \
            #         WHERE {}.n2 = {}.n1 and {}.n1 != {}.n2 \
            #         and not {}.s[1] = ANY({}.s) and not {}.n2 = ANY({}.path);" \
            #         .format(r_next, 
            #         r_prev, self.F_TABLE, 
            #         self.F_TABLE, r_prev, 
            #         r_prev, self.F_TABLE, 
            #         r_prev, self.F_TABLE, 
            #         r_prev, self.F_TABLE, 
            #         r_prev, self.F_TABLE, r_prev, self.F_TABLE, 
            #         self.F_TABLE, r_prev, self.F_TABLE, r_prev)

            self.cursor.execute(sql)
            num = self.cursor.rowcount
            CONN.commit()

            if num == 0:
                return count
            
            count = count + 1
       
            
    def union(self, count):
        sql = "drop table if exists R_{};".format(self.F_TABLE)
        self.cursor.execute(sql)

        sql = "create table R_{} as ".format(self.F_TABLE)

        for i in range(1, count + 1):
            r_table = "r{}_{}".format(i, self.F_TABLE)
            sql = sql + "select n1, n2, s, path from {} union ".format(r_table)
        
        sql = sql[:-6]

        self.cursor.execute(sql)
        CONN.commit()

        for i in range(1, count+1):
            sql = "DROP TABLE IF EXISTS r{}_{}".format(i, self.F_TABLE)
            self.cursor.execute(sql)
        CONN.commit()
    
    def select(self, dest):
        spc_r_name = 'R_{}_s'.format(self.F_TABLE)

        sql = "drop table if exists {}".format(spc_r_name);
        self.cursor.execute(sql)

        sql = "create table {} as select * from R_{} where n2 = {}".format(spc_r_name, self.F_TABLE, dest)
        self.cursor.execute(sql)
        CONN.commit()


if __name__ == '__main__':
    generator = RtableFc(dbname='cidr_c', f_table='f_4755', as_number=4755)

    generator.r1()
    count = generator.rn()

    generator.union(count=count)



