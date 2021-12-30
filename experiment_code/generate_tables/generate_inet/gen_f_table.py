import psycopg2
from tqdm import tqdm 
import time
import sys


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

# generate the F table
# input: tablename(subset of raw rib table,such as rib1000)
def gen_f_table(tablename = 'rib1000'):
    """
    Generate the F table
    @param tablename: the name of the F table, default rib1000
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    #create f_table in database
    cur.execute("DROP TABLE IF EXISTS f_table_{}".format(tablename))
    cur.execute("CREATE TABLE f_table_{}(id SERIAL PRIMARY KEY, fid inet, nid1 TEXT, nid2 TEXT, condition TEXT[], mark SMALLINT)".format(tablename))


    # get prefix list
    cur.execute('select distinct prefix from {};'.format(tablename))
    prefix_list = cur.fetchall()

    count = 1
    for p in tqdm(prefix_list): # tqdm is used to show progress bar
        
        # get AS_PATH list
        path_cur = conn.cursor()
        path_cur.execute("select setseed(0.5);") # setting a seed so that the comparison is fair
        path_cur.execute("select as_path from {} where prefix= '{}' order by random() limit 5;".format(tablename, p[0]))
        # print("The number of parts: ", cur.rowcount)

        row = path_cur.fetchone()[0]

        if ',' in row: # for special AS number{n1,n2} to {n1-n2}
            row = row.replace(',', '-')

        # set first row of as path as best path
        best_path = row.split(' ')
        # print('best_path: '+str(best_path))

        row = path_cur.fetchone()
        path_list = []
        while row is not None:
            row = row[0]
            if ',' in row: # for special AS number{n1,n2} to {n1-n2}
                row = row.replace(',', '-')

            path_list.append(row.split(' '))
            row = path_cur.fetchone()
        
        backup_links = find_backup(prefix=p[0], best_path=best_path, path_list=path_list)
        tuples = link_to_f_table(prefix=p[0], best_path=best_path, links_dict=backup_links)
        
        for t in tuples:
            cur.execute('insert into f_table_{} (fid, nid1, nid2, condition, mark) values(%s, %s, %s, %s, %s)'.format(tablename), (t[0], t[1],t[2], t[3], t[4]))
        
        conn.commit()
        count = count + 1
    conn.close()

# input: best_path(array), path_list(list(array))
# return: links(list(array(source, backup_hop, source, best_hop)))
def find_backup(prefix, best_path, path_list):
    """
    Find the backup links among remaining paths.
    @param prefix: the number of prefixes in the rib table
    @param best_path: A list of AS nodes that constitutes a path which is best path
    @param path_list: A list of backup paths

    @output: A dict. checkpoint flag the start point of common part between primary path and each backup path
    """
    # print('Best path: ', best_path)
    links = {}

    # set priority condition for each backup link (high to low according to the order in list)
    priority = [] # first backup link is highest priority, it is chosen only when the primary link fails

    for path in path_list:
        check_point = len(best_path) - 1 # check the point of shortest common path in AS path
        # print('****************')
        # print('path: ', path)

        # find common part
        i, j = len(best_path)-1, len(path)-1
        while i >= 0 and j >= 0:
            if best_path[i] == path[j]:
                i = i - 1
                j = j - 1
            else:
                check_point = i + 1
                break

        blink = []
        '''
        # check_point < len(best_path), it means there is common part
        # check_point >= len(best_path), it means there is no common part
        '''
        if check_point < len(best_path): 
            temp_p = '' # record failure condition for current backup link
            while j >= 0 : 
                if path[j] != path[j+1]: # skip several same AS number (ABBC)
                    blink.append([prefix, path[j], path[j+1], priority.copy()])

                    # update faliure condition when new link was found
                    temp_p = 'l{}-{} == 0'.format(path[j],path[j+1]) if len(temp_p) == 0 else '{}, l{}-{} == 0'.format(temp_p,path[j],path[j+1])
                    # print('temp_p: ',temp_p)

                j = j - 1
            blink.append([prefix, 's', path[j+1], priority.copy()])
            temp_p = 'ls-{} == 0'.format(path[j+1]) if len(temp_p) == 0 else temp_p + ', ls-{} == 0'.format(path[j+1]) # update faliure condition when new link was found
            temp_p = "Or({})".format(temp_p)

            if check_point in links.keys():
                links[check_point] = links[check_point] + blink 
            else:
                links[check_point] = blink

            # update condition for next backup link failure
            priority.append(temp_p) #= priority + '({})'.format(temp_p) #if len(priority) == 0 else '{},({})'.format(priority, temp_p)

    return links  

# input: best_path(array), links_dict(dict(array))
# return tuple-like array list, the format of each tuple is the same as f-table schema
def link_to_f_table(prefix, best_path, links_dict):
    """
    Transform dict generated by find_backup function to list that can directly insert into table;
    Transform best_path(array) so that can directly insert into table.

    @param prefix: the number of prefixes in the rib table
    @param best_path: best path array
    @param links_dict: dict generated by find_backup function

    @output:  tuple-like array list, the format of each tuple is the same as f-table schema
    """
    examples = []
    check = -1

    for key in links_dict.keys():
        if key > check:
            check = key
        link_list = links_dict[key]

        # set backup link condition
        cond = 'ls-{} == 0'.format(best_path[0])
        for i in range(key):
            if best_path[i]!= best_path[i+1]:
                cond = cond+', l{}-{} == 0'.format(best_path[i],best_path[i+1])
        cond = "Or({})".format(cond)

        for link in link_list:
            # add the condition of primary link failure
            link[3].append(cond) # +'({})'.format(cond) #if len(link[3]) == 0 else '{},({})'.format(link[3], cond) 
            link.append(0) # mark backup link as 0
            examples.append(tuple(link))
            # print(link)  

    # set primary link condition
    p_cond = []
    if check != -1:
        p_cond.append('ls-{} == 1'.format(best_path[0]))
        # cond = 'ls-{}=1'.format(best_path[0])
        for i in range(check):
            if best_path[i]!= best_path[i+1]:
                p_cond.append('l{}-{} == 1'.format(best_path[i], best_path[i+1]))
                # cond = cond+',l{}-{}=1'.format(best_path[i], best_path[i+1])
    
        #set primary link
        examples.append((prefix, 's', best_path[0], p_cond, 1 )) #'({})'.format(cond), 1)) # mark primary link as 1
        # print(['s', best_path[0], cond])
        for i in range(check):
            if best_path[i] != best_path[i+1]: # skip the same AS number
                examples.append((prefix, best_path[i], best_path[i+1], p_cond, 1)) #'({})'.format(cond), 1))
                # print([best_path[i], best_path[i+1], cond])
            else: 
                continue

    # set unprotected links
    if check == -1: # if check = -1, it means all links in best path are unprotected link
        check = 0 
        examples.append((prefix, 's',best_path[check],'{}', 2)) # mark unprotected link as 2
        # print(['s',best_path[check],''])
    while check < len(best_path)-1:
        if best_path[check] != best_path[check+1]: # skip the same AS number
            examples.append((prefix, best_path[check], best_path[check+1],'{}', 2))
            # print([best_path[check], best_path[check+1],''])
        check = check + 1
        
    # print('check: ', check) 
    return examples
            
# links = find_backup([1,2,3,4,5], [1,2,3,7,5])
# print(links)

def create_index_fid_mark(tablename = 'f_table_rib1000'):
    """
    create index for fid attribute in the F table

    @param tablename: the target F table that wants to create index for 
    """
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    sql = "CREATE INDEX index_fid_mark{}\
            ON public.{} USING btree\
            (fid varchar_ops ASC NULLS LAST, mark ASC NULLS LAST)\
                TABLESPACE pg_default;".format(tablename,tablename)
    cur.execute(sql)
    conn.commit()
    conn.close()

if __name__ == '__main__':
    sizes = [100, 1000, 10000] #, 10000, 100000, 922067]
    # sizes = [922067]
    # sizes = [500000, 922067]
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
        print("create f table size ", size)
        tablename = 'rib' + str(size)
        start_time = time.time()
        gen_f_table(tablename=tablename)
        print('Done! {} running time: {}'.format(tablename, time.time()-start_time))

        # create_index_fid_mark(tablename='f_table_'+tablename) TODO: Make inet index-ible
        # print('{} running time: {}'.format(tablename, time.time()-start_time))


