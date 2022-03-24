import sys
from os.path import dirname, abspath, join
from xml.etree.ElementTree import tostring

from cv2 import sort

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'support_int')
sys.path.append(filename)

import re
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database="pyotr", user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

import functools

def count_condition(pattern, tablename):
    cursor.execute("select * from {tablename}".format(tablename=tablename))
    cond_idx = -1
    for idx, row in enumerate(cursor.description):
        if row[0] == 'condition':
            cond_idx = idx
            break

    row_count = cursor.rowcount
    total_num = 0
    for i in tqdm(range(row_count)):
        row = cursor.fetchone()
        conditions = row[cond_idx]
        for cond in conditions:
            # print("cond", cond)
            cond = preprocessing(cond)
            res = cond.count(pattern)
            if res != 0:
                print(cond)
                exit()
            total_num += res
        
    return total_num

def preprocessing(tauto_condition):
    parenth_list = find_parenthesis(tauto_condition)
    # print(tauto_condition)
    condition_copy = list(tauto_condition)
    last_pos = 0
    for pair in parenth_list:
        left = pair[0]
        right = pair[1]
        part = "".join(condition_copy[left+1: right])
        sorted_cond = list(sort_conditions(part))
        condition_copy[left+1: right] = sorted_cond
    if len(parenth_list) == 0:
        part = "".join(condition_copy)
        sorted_cond = list(sort_conditions(part))
        condition_copy = sorted_cond
    # print("".join(condition_copy))
    # print(tauto_condition)
    # condition_copy = tauto_condition
    # last_pos = 0
    # for pair in parenth_list:
    #     prcd_condition = ""
    #     left = pair[0]
    #     right = pair[1]

    #     prcd_condition += condition_copy[last_pos:left+1]
    #     sorted_cond = sort_conditions(condition_copy[left+1: right])
    #     prcd_condition += sorted_cond
    #     prcd_condition += condition_copy[right:]

    #     condition_copy = prcd_condition
    # print(condition_copy)
    return "".join(condition_copy)


def find_parenthesis(tauto_condition):
    i = 0
    parenth_list = []
    # parenth_dict = {}
    stack = []
    while i < len(tauto_condition):
        if tauto_condition[i] == '(':
            stack.append(i)
        elif tauto_condition[i] == ')':
            left_parenth = stack.pop()
            temp = (left_parenth, i)
            parenth_list.append(temp)
        i += 1

    return parenth_list

def sort_conditions(conditions):

    '''
    split conditions
    '''
    last_pos = 0
    num_left = 0
    num_right = 0
    cond_list = []
    for i in range(len(conditions)):
        if conditions[i] == '(':
            num_left += 1
        elif conditions[i] == ')':
            num_right += 1
        elif conditions[i] == ',' and num_left == num_right:
            part = conditions[last_pos: i]
            if not ('And' in part or 'Or' in part or ',' in part):
                part = adjust(part)
            cond_list.append(part)
            
            last_pos = i + 1
    if last_pos < len(conditions):
        part = conditions[last_pos:]
        if not ('And' in part or 'Or' in part or ',' in part):
            part = adjust(part)
        cond_list.append(part)
    # print("cond_list",cond_list)
    # cond_list.sort(functools.cmp_to_key(compare))

    '''
    sort conditions
    '''
    new_list = sorted(cond_list, key=functools.cmp_to_key(compare))
    # print(new_list)
    return ",".join(new_list)

def adjust(condition):
    items = condition.split(" ")
    idx = 0
    for i in range(len(items)):
        if items[i] == '==':
            idx = i

    left_opd = items[idx-1]
    right_opd = items[idx+1]

    if left_opd.isdigit() and not right_opd.isdigit():
        items[idx-1] = right_opd
        items[idx+1] = left_opd

    elif (not left_opd.isdigit() and not right_opd.isdigit()) or (left_opd.isdigit() and right_opd.isdigit()):
        if left_opd > right_opd:
            items[idx-1] = right_opd
            items[idx+1] = left_opd
    
    return " ".join(items)
    
def compare(x1, x2):
    """
    keyword And is larger than Or
    If with the same keyword, return the result of string comparison

    with keyword is lager than without keyword

    if both without keywords, return the result of string comparison
    """
    x1 = x1.strip()
    x2 = x2.strip()
    if ("And" in x1 or "Or" in x1) and not ("And" in x2 or "Or" in x2):
        return 1 # True #x1 > x2
    elif not ("And" in x1 or "Or" in x1) and ("And" in x2 or "Or" in x2):
        return -1 # False # x1 < x2
    elif ("And" in x1 or "Or" in x1) and ("And" in x2 or "Or" in x2):
        if "And" in x1 and not "And" in x2:
            return 1 # True # x1 > x2
        elif not "And" in x1 and "And" in x2:
            return -1 # False x1 < x2
        else:
            if x1 < x2:
                return -1
            else:
                return 1
    else:
        if x1 < x2:
            return -1
        else:
            return 1



if __name__ == '__main__':
    # tablename = 'r1_2'
    tau_cond1 = "Or(And(x1 == x2, x2 == x3), And(1 == x2, x2 == x3), x1 == x3, 1 == x3, And(x1 == 1, x2 == x3), And(x1 == 1, x2 == x3), And(x2 == 1, x3 == x2), x2 == 1, And(x2 == 1, x2 == x3), And(x2 == 1, x2 == x3), And(x3 == 1, x3 == x2), x3 == 1)"
    # tau_cond2 = "Or(And(1 == x1, x1 == x2), And(x2 == 1, x3 == x1, x1 == x2), And(x3 == 1, 2 == x1, x1 == x2), And(x3 == 1, x3 == x1, x1 == x2), x1 == x2, x1 == x2, 1 == x2, And(x1 == 1, x2 == x1), x1 == 1, And(x2 == 1, x3 == x2), And(x3 == 1, 2 == x2), And(x2 == 1, x2 == x1), x2 == 1, And(x3 == 1, x3 == x2))"
    # pattern = "Or(And(x1 == 1), And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), And(x2 == 1), And(x3 == 1))"
    # p = "Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1)))"
    # condition = "Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))"
    # sort_conditions(condition)
    # preprocessing(p)
    # find_parenthesis(p)
    # x1 = "x == 1"
    # x2 = "And(x == 1, x == 2)"
    # res = larger(x1, x2)
    # print(res)
    # x1 = [{"x == 1"}, ["x2 == x3", "x1 == x2", {"x == 1"}]]
    # x2 = [{'x == 1'}, ["x2 == x3", "x1 == x2", {"x == 1"}]]
    # print(x1 == x2)

    # pattern = "Or(And(x1 == 1), And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), And(x2 == 1), And(x3 == 1))"
    contrd_condition = "1 == x3, x3 == 2"
    pattern = preprocessing(contrd_condition)
    print(pattern)
    for i in range(2, 8):
        tablename = 'r1_{}'.format(i)
        num = count_condition(pattern, tablename)
        print(num)
    # pattern = "what's the matter"
    
    # res = re.findall(pattern, text)
    # res = text.count(pattern)
    # print(res)
    # print(pattern == text)