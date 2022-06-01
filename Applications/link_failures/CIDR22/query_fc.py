from db import DB
from tqdm import tqdm
import time
import psycopg2
import databaseconfig as cfg



"""
This is the queiries(r3, r4, r5) run on the regular R table
"""

as_numbers = [4755, 3356, 2914, 7018] 

rootes = [108, 1711, 7121, 5675]

num = [1000, 1000, 50, 50]

r3_filters = [434, 41, 4008, 12616]
# r3_filters = [60, 40, 70, 426] #0.2
for index, number in enumerate(as_numbers):
    db_name = "cidr_fc_{}".format(number)
    conn = psycopg2.connect(host=cfg.postgres["host"], database=db_name, user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()

    print("\nDoing r3_{}: ".format(number))
    start_time = time.time()
    for n in tqdm(range(num[index])):
        sql = " SELECT * FROM R_fc_{} \
                WHERE n2 = {}\
                and not {} = ANY(s);".format(n, rootes[index], r3_filters[index])
    cursor.execute(sql)
    print("Running Time: ", (time.time() - start_time) / num[index])
    conn.commit()
    conn.close()

"""
r4 query
"""
r4_filters = [141, 28, 78, 8]
r4_nodes = [[(141, 60),(141, 472)], [(28, 1729), (28, 228)], [(78, 405),(78, 7544)], [(8, 12644), (8, 7735)]]
for index, number in enumerate(as_numbers):
    db_name = "cidr_fc_{}".format(number)

    conn = psycopg2.connect(host=cfg.postgres["host"], database=db_name, user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()

    sql1_result = False
    sql2_result = False

    print("\nDoing r4_{}: ".format(number))
    start_time = time.time()
    for n in tqdm(range(num[index])):
        nodes = r4_nodes[index]
        sql1 = "select * from r_fc_{} as r, fc_{} as f \
                where r.n1 = {} and r.n2 = {} \
                and f.n1 = {} and f.n2 = {} \
                and {} = ANY(r.s) ".format(n, n, nodes[0][0], nodes[0][1], nodes[0][0], nodes[0][1], r4_filters[index])
        
        cursor.execute(sql1)
        sql1_count = cursor.rowcount

        if sql1_result == False and sql1_count > 0:
            sql1_result = True

    for n in tqdm(range(num[index])):
        sql2 = "select * from r_fc_{} as r, fc_{} as f \
                where r.n1 = {} and r.n2 = {} and f.n1 = {} and f.n2 = {} \
                and {} = ANY(r.s) ".format(n, n, nodes[0][0], nodes[0][1], nodes[0][1], nodes[1][1], r4_filters[index])
        
        cursor.execute(sql2)
        sql2_count = cursor.rowcount

        if sql2_result == False and sql2_count > 0:
            sql2_result = True
    
    print(sql1_result and sql2_result)
    print("Running Time: ", (time.time() - start_time) / num[index])
    conn.commit()
    conn.close()


"""
r5 query
"""
# r5_nodes = [(34, 60), (1911, 259), (7120, 129)]#, (25, 12616)]
# for index, number in enumerate(as_numbers):
#     db_name = "cidr_fc_{}".format(number)

#     db = DB(db=db_name)

#     sql1_result = False
#     sql2_result = False

#     print("\nDoing r5_{}: ".format(number))
#     start_time = time.time()
#     for n in tqdm(range(num[index])):
#         nodes = r5_nodes[index]

#         sql = "select * from r_fc_{} as r, fc_{} as f \
#             where f.n1 != {} and f.n2 != {} \
#             and r.n2 = {}".format(n, n, nodes[0], nodes[1], rootes[index])
        
#         db.select(sql)
    
#     print("Running Time: ", (time.time() - start_time) / num[index])

    


    

    


