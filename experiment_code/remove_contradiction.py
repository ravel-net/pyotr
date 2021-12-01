from unicodedata import name
from z3 import *
from tqdm import tqdm
from db import DB
import re
import time

host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

db = DB(username=user, hostname=host, port=5432, dbname=database, dbtype="postgres", password="mubashir")

#only for q6/q7/q8
def rem_contrad(tablename = 'ans'):
    """
    Detect contradiction in condition column and delete the tuples who contain contradictory condition

    @param tablename: the target table
    """
    db.select('select * from {}'.format(tablename))

    del_db = DB(username=user, hostname=host, port=5432, dbname=database, dbtype="postgres", password="mubashir")
    num = db._cursor.rowcount
    print(num)
    count = 0
    for i in tqdm(range(num)):
        row = db._cursor.fetchone()
        check = process(row[3])
        if check == False:
            sql = "delete from {} where fid = '{}' and source = '{}' and dest = '{}' and cond = '{}'".format(tablename, row[0], row[1], row[2], row[3])
            del_db.delete(sql)
            count = count + del_db._cursor.rowcount

    print('Total number of rows deleted: ', count)


#only for q6/q7/q8
def process(cond):
    """
    The variational process for condition that define z3 variable and value

    @param cond: condition. The format of condition: , means 'and'; [] means 'or' that all conditions in [] are 'or' relation; | means 'or'.,
    @output: Bool
    """
    conds_list = re.findall('\(([^)]+)', cond) # find all conditions in parenthess
    s = Solver()
    for count, c in enumerate(conds_list):

        # [(, ,),(, ,),( , , ,)]
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
    if s.check() == sat:
        # print(s.model())
        return True
    else:
        return False

def process_con_or_disjunction(cond, delimiter):
    """
    Split variable and values by delimiter

    @param delimiter: character, such as , |
    @output: variable list and value list
    """    
    conds = cond.split(delimiter)

    var_list = []
    val_list = []
    for c in conds:
        strs = c.split('=')
        
        var_list.append(strs[0])
        val_list.append(strs[1])
    return var_list, val_list

# remove duplicate conditions in cond column
def rem_redunct(tablename = 'rib1000_r'):
    """
    remove duplicated conditions

    @param tablename: the target table
    """
    db.select('select * from {}'.format(tablename))

    num = db._cursor.rowcount
    upd_db = DB()

    count = 0
    for i in tqdm(range(num)):
        row = db._cursor.fetchone()
        conds_list = re.findall('\(([^)]+)', row[3]) # find all conditions in parenthess
        new_list = list(set(conds_list)) # remove duplicates

        if len(conds_list) != len(new_list):
            new_cond = ''.join('({})'.format(item) for item in new_list)
            sql = "update {} set cond = '{}' where fid = '{}' and source = '{}' and dest = '{}' and cond = '{}'".format(tablename, new_cond, row[0], row[1], row[2], row[3])
            upd_db.update(sql)
            count = count + upd_db._cursor.rowcount
    print('Total number of rows updated: ', count)
            

if __name__ == '__main__':
    start_time = time.time()
    cond = '"(ls-11686=1,l11686-6461=1,l6461-2914=1,l2914-3223=1,l3223-{8262,34224}=1,l{8262,34224}-201200=1)(ls-11686=1,l11686-6461=1,l6461-2914=1,l2914-3223=1,l3223-{8262,34224}=1,l{8262,34224}-201200=1)(l4637-3223=0|l1221-4637=0|ls-1221=0)(l8262-201200=0|l1299-8262=0|ls-1299=0)(l1403-6461=0|ls-1403=0)(ls-11686=0|l11686-6461=0|l6461-2914=0|l2914-3223=0|l3223-{8262,34224}=0|l{8262,34224}-201200=0)(l4637-3223=0|l1221-4637=0|ls-1221=0)(l8262-201200=0|l1299-8262=0|ls-1299=0)(l1403-6461=0|ls-1403=0)(ls-11686=0|l11686-6461=0|l6461-2914=0|l2914-3223=0|l3223-{8262,34224}=0|l{8262,34224}-201200=0)([l11686-6461=1,l6461-2914=0]|[l6461-2914=1,l11686-6461=0]|[l11686-6461=0,l6461-2914=0])"'
    # rem_redunct()
    # rem_contrad()
    
    print(process(cond=cond))
   
    print('running time is ', time.time()- start_time)

 
