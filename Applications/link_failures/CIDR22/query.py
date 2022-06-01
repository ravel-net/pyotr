import time
from tqdm import tqdm
import psycopg2

import databaseconfig as cfg



"""
This is the queries(r3, r4, r5) run on the ctable-based R table
"""

as_numbers = [4755, 3356, 7018, 2914] #, 2914
rootes = [108, 1711, 5675, 7121]

count = 10
# db_name = 'cidr_2'
# db_name = 'cidr_4'
db_name = 'cidr_6'

conn = psycopg2.connect(host=cfg.postgres["host"], database=db_name, user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()
# r3_filters = [60, 40, 70, 426] #0.2
# r3_filters = [113, 259, 12616, 129] #0.4
r3_filters = [462, 1730, 8114, 857] #0.6
for index, number in enumerate(as_numbers):
    sql = " SELECT * FROM R_{} \
            WHERE n2 = {} \
            and not {} = ANY(s);".format(number, rootes[index], r3_filters[index])

    print("\nDoing r3_{}: ".format(number))
    start_time = time.time()
    for i in range(count):
        cursor.execute(sql)
    print("Running Time: ", (time.time() - start_time) / count)
    conn.commit()

# r4_nodes = [[(490, 108), (490, 462)], [(1596, 1711), (1596, 1742)], [(12505, 5675), (12505, 12498)], [(6878, 7121), (6878, 6890)] ]
# r4_nodes = [[(530, 463), (530, 462)], [(140, 1890), (140, 1899)], [(1673, 12800), (1673, 12799)], [(301, 6798), (301, 600)]] #0.4
r4_nodes = [[(493, 108), (493, 463)], [(1733, 1711), (1733, 1730)], [(7323, 5675), (7323, 12566)], [(4364, 7121), (4363, 899)]] #0.6

# r4_filters = [490, 1458, 940, 6888] #0.2
# r4_filters = [530, 140, 1673, 301] #0.4
r4_filters = [530, 1727, 12566, 351] #0.6
for index, number in enumerate(as_numbers):
    output_table = "output_{}".format(number)
    r_table = "r_{}".format(number)

    filters = r4_filters[index]
    nodes = r4_nodes[index]

    print("\nDoing r4_{}: ".format(number))
    start_time = time.time()
    for i in range(count):

        sql = "Drop table if exists {}".format(output_table)
        cursor.execute(sql)

        # Create Data Content
        sql = "create table {} as select \
                a.n1, b.n1 as b_n1, \
                a.n2, b.n2 as b_n2, \
                a.s, b.s as b_s,  \
                array_cat(a.condition, b.condition) as condition \
                from {} as a, {} as b \
                where a.n1 = {} and b.n1 = {} \
                and a.n2 = {} and b.n2 = {} \
                and {} = ANY(a.s) and {} = ANY(b.s);".format(
                    output_table,
                    r_table, r_table,
                    nodes[0][0], nodes[0][0],
                    nodes[0][1], nodes[0][1],
                    filters, filters
                )
        # print(sql)

        cursor.execute(sql)
        
        # update condition
        sql = "update {} set condition = array_append(condition, 'l' || {} || ' == ' || {} )".format(output_table, nodes[0][0], nodes[0][1])
        # print(sql)
        cursor.execute(sql)
        sql = "update {} set condition = array_append(condition, 'l' || {} || ' == ' || {} )".format(output_table, nodes[1][0], nodes[1][1])
        # print(sql)
        cursor.execute(sql)

        # Normalization
        # sql = "DELETE FROM {} WHERE is_contradiction(condition);".format(output_table)
        # db.delete(sql)

        # sql = "UPDATE {} SET condition = '{{}}' WHERE is_tauto(condition);".format(output_table)
        # db.update(sql)

        # sql = "UPDATE {} SET condition = remove_redundant(condition) where has_redundant(condition);".format(output_table)
        # db.update(sql)
        conn.commit()
    print("Running Time: ", (time.time() - start_time) / count)
    

"""
r5 query
"""
r5_links = [(498, 462), (1727, 1711), (12668, 12666), (3982, 7117)] # 14, 10, 14, 12 0.2
# r5_links = [(60, 112), (1803, 40), (12616, 5675), (8, 7064)] # 14, 10, 14, 12 0.4
# for index, number in enumerate(as_numbers):
#     output_name = "output_{}".format(number)

#     print("\nDoing r5_{}: ".format(number))
#     start_time = time.time()
#     sql_total_time = 0
#     z3_total_time = 0
#     for n in tqdm(range(count)):
#         db = DB(db=db_name)

#         sql = "DROP TABLE IF EXISTS {};".format(output_name)
#         db.common(sql)
#         sql_start = time.time()
#         # create data content
#         sql = "CREATE TABLE {} AS SELECT * FROM r_{} WHERE n2 = {};".format(output_name, number, rootes[index])
#         db.common(sql)

#         # update condition
#         sql = "UPDATE {} set condition = array_append(condition, 'l{} != {}')".format(output_name, r5_links[index][0], r5_links[index][1])
#         db.update(sql)

#         sql_total_time = sql_total_time + time.time() - sql_start

#         # Normalization
#         z3_start = time.time()
#         sql = "DELETE FROM {} WHERE is_contradiction(condition);".format(output_name)
#         db.delete(sql)

#         sql = "UPDATE {} SET condition = '{{}}' WHERE is_tauto(condition);".format(output_name)
#         db.update(sql)

#         sql = "UPDATE {} SET condition = remove_redundant(condition) where has_redundant(condition);".format(output_name)
#         db.update(sql)
#         z3_total_time = z3_total_time + time.time() - z3_start


#     print("SQL Running Time: ", sql_total_time / count)
#     print("Z3 Running Time: ", z3_total_time / count)

    
    # # Update Condition
    # for f in filters:
    #     sql = "Update {} set condition = array_append(condition, 'l' || {} || ' == ' || {})"
    
    # sql = "alter table {} drop column b_n1, drop column b_n2;"

    # # Normalization
    # sql = "DELETE FROM R2 WHERE is_contradiction(condition);"
    
    # sql = "UPDATE R2 SET condition = '{}' WHERE is_tauto(condition);"

    # sql = "UPDATE R2 SET condition = remove_redundant(condition) where has_redundant(condition);"
    



