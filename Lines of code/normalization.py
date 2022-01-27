def normalization():
    print("\n************************Step 3: Normalization****************************")
    cursor = conn.cursor()
    # print('Step3: Normalization')
    begin = time.time()
    # sql = 'delete from output where is_contradiction(condition);'
    # print(sql)
    # cursor.execute(sql)
    
    # sql = "UPDATE output SET condition = '{}' WHERE is_tauto(condition);"
    # print(sql)
    # cursor.execute(sql)

    # sql = "UPDATE output SET condition = remove_redundant(condition) WHERE has_redundant(condition);"
    # print(sql)
    # cursor.execute(sql)
    # print("\nz3 execution time:", time.time()-begin)
    # print("red, tau", time.time()-begin)
    cursor.execute("select * from output limit 1")
    cols = [row[0] for row in cursor.description]
    if 'id' not in cols:
        cursor.execute("ALTER TABLE output ADD COLUMN id SERIAL PRIMARY KEY;")
    else:
        cols.remove('id')
    '''
    delete duplicate rows
    '''
    delete_duplicate_row_sql = "DELETE FROM output WHERE id IN ( \
                SELECT id FROM ( \
                    SELECT \
                        id, row_number() OVER w as row_num FROM output \
                        WINDOW w AS ( \
                            PARTITION BY {} ORDER BY id \
                        ) \
                    ) t \
                WHERE t.row_num > 1);".format(", ".join(cols))
    cursor.execute(delete_duplicate_row_sql)
    print("Deleted duplicate rows: ", cursor.rowcount)

    '''
    delete contradiction
    '''
    print("delete contradiction")
    contrd_begin = time.time()
    cursor.execute("select id, condition from output")
    contrad_count = cursor.rowcount
    # logging.info("size of input(delete contradiction): %s" % str(count))
    del_tuple = []
    solver = z3.Solver()
    for i in tqdm(range(contrad_count)):
        row = cursor.fetchone()
        is_contrad = iscontradiction(solver, row[1])

        if is_contrad:
            del_tuple.append(row[0])
        
    if len(del_tuple) == 0:
        pass
    elif len(del_tuple) == 1:
        cursor.execute("delete from output where id = {}".format(del_tuple[0]))
    else:
        cursor.execute("delete from output where id in {}".format(tuple(del_tuple)))
    contr_end = time.time()
    # logging.warning("delete contradiction execution time: %s" % str(contr_end-contrd_begin))

    '''
    delete duplicate rows
    '''
    cursor.execute(delete_duplicate_row_sql)
    print("Deleted duplicate rows: ", cursor.rowcount)

    '''
    set tautology and remove redundant
    '''
    print("remove redundant")
    redun_begin = time.time()
    cursor.execute("select id, condition from output")
    redun_count = cursor.rowcount
    # logging.info("size of input(remove redundancy and tautology): %s" % str(count))
    upd_cur = conn.cursor()

    tauto_solver = z3.Solver()
    for i in tqdm(range(redun_count)):
        row = cursor.fetchone()
        has_redun, result = has_redundancy(solver, tauto_solver, row[1])
        if has_redun:
            if result != '{}':
                result = ['"{}"'.format(r) for r in result]
                upd_cur.execute("UPDATE output SET condition = '{}' WHERE id = {}".format("{" + ", ".join(result) + "}", row[0]))
            else:
                upd_cur.execute("UPDATE output SET condition = '{{}}' WHERE id = {}".format(row[0]))
    redun_end = time.time()

    '''
    delete duplicate rows
    '''
    cursor.execute(delete_duplicate_row_sql)
    print("Deleted duplicate rows: ", cursor.rowcount)
    # logging.warning("remove redundancy and tautology execution time: %s" % str(redun_end-redun_begin))
    
    # logging.warning("z3 execution time: %s" % str((contr_end-contrd_begin)+(redun_end-redun_begin)))
    print("Z3 execution time: ", contr_end-contrd_begin + redun_end-redun_begin)
    # print("Z3 execution time: ", contr_end-contrd_begin)
    conn.commit()
    return {"contradiction":[contrad_count, contr_end-contrd_begin], "redundancy":[redun_count, redun_end-redun_begin]}
   

def iscontradiction(solver, conditions):
    solver.push()

    if len(conditions) == 0:
        return 

    vars = set() # save Int compared variables for shortest path policy
    for c in conditions:
        if '<=' in c:
            conds = c.split('<=')  # l(x3) <= x4
            
            var1 = conds[0].strip()
            var2 = conds[1].strip()
            
            if var1[0].isalpha():
                op1 = "z3.Int('{}')".format(var1)
                vars.add(var1)
            else:
                op1 = "z3.IntVal({})".format(int(var1))

            if var2[0].isalpha():
                op2 = "z3.Int('{}')".format(var2)
                vars.add(var2)
            else:
                op2 = "z3.IntVal({})".format(int(var2))

            expr = "{} <= {}".format(op1, op2)
            #print(expr)
            solver.add(eval(expr))
            continue

        # nopath means no path to dest
        if 'nopath' in c:
            solver.pop()
            return True
            
        if 'Or' not in c:
            #c_list = c.strip().split(' ')
            c = c.strip()

            first_space = c.find(' ')
            second_space = c.find(' ', first_space + 1)

            c_list = [c[:first_space].strip(), c[first_space + 1: second_space].strip(), c[second_space + 1:].strip()]

            if c_list[0] in vars: # if variable in vars that means this variable is Int variable and need to further set Int value for it
                solver.add(z3.Int(c_list[0]) == z3.IntVal(int(c_list[2])))
                continue
            elif c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                op1 = f"z3.Int('{c_list[0]}')"
            else: 
                if c_list[0].startswith("i_"):
                    op1 = f"z3.IntVal('{int(c_list[0][2:])}')"
                else:
                    op1 = f"z3.IntVal('{int(c_list[0])}')"

            if c_list[2][0].isalpha() and not c_list[2].startswith("i_"):
                op2 = f"z3.Int('{c_list[2]}')"
            else:
                if c_list[2].startswith("i_"):
                    op2 = f"z3.IntVal('{int(c_list[2][2:])}')"
                else:
                    op2 = f"z3.IntVal('{int(c_list[2])}')"
                
            #expr = f"{c_list[0]} {c_list[1]} z3.StringVal('{c_list[2]}')"
            expr = f"{op1} {c_list[1]} {op2}"
            # print(expr)
            #plpy.info(expr)
            solver.add(eval(expr))
        
        else:  #-- includes Or()
            c = c.strip().replace('Or','').replace('(','').replace(')','').strip()

            or_input = "Or("
            or_list =  c.split(',')
            for single_cond in or_list:
                c_list = single_cond.strip(). split(' ')
            
                if c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                    op1 = f"z3.Int('{c_list[0]}')"
                else: 
                    # op1 = f"z3.StringVal('{c_list[0]}')"
                    if c_list[0].startswith("i_"):
                        op1 = f"z3.IntVal('{int(c_list[0][2:])}')"
                    else:
                        op1 = f"z3.IntVal('{int(c_list[0])}')"

                if c_list[2][0].isalpha() and not c_list[2].startswith("i_"):
                    op2 = f"z3.Int('{c_list[2]}')"
                else:
                    # op2 = f"z3.StringVal('{c_list[2]}')"
                    if c_list[2].startswith("i_"):
                        op2 = f"z3.IntVal('{int(c_list[2][2:])}')"
                    else:
                        op2 = f"z3.IntVal('{int(c_list[2])}')"
                    
                #expr = f"{c_list[0]} {c_list[1]} z3.StringVal('{c_list[2]}')"
                expr = f"{op1} {c_list[1]} {op2}"
                or_input += expr + ','
    
            or_input = or_input[:-1] + ')'
            #plpy.info(or_input)
            solver.add(eval(or_input))

    result = solver.check()

    if result == z3.unsat:
        solver.pop()
        return True
    else:
        solver.pop()
        return False

def istauto(solver, conditions):
    if len(conditions) == 0:
        return True
    for c in conditions:
        condition = initial_z3_variable(c)
        solver.push()
        solver.add(eval(condition))
        re = solver.check()
        solver.pop()

        if str(re) == 'sat':
            pass
        else:
            return False
    return True

def initial_z3_variable(condition):
    expr = ""
    if 'Or' not in condition:

        c1_list = condition.split(' ')
        
        if c1_list[0][0].isalpha() and not c1_list[0].startswith("i_"):
            op11 = f"z3.Int('{c1_list[0]}')"
        else: 
            # op11 = f"z3.StringVal('{c1_list[0]}')"
            if c1_list[0].startswith("i_"):
                op11 = f"z3.IntVal('{int(c1_list[0][2:])}')"
            else:
                op11 = f"z3.IntVal('{int(c1_list[0])}')"
    
        if c1_list[2][0].isalpha() and not c1_list[0].startswith("i_"):
            op12 = f"z3.Int('{c1_list[2]}')"
        else:
            # op12 = f"z3.StringVal('{c1_list[2]}')"
            if c1_list[2].startswith("i_"):
                op12 = f"z3.IntVal('{int(c1_list[2][2:])}')"
            else:
                op12 = f"z3.IntVal('{int(c1_list[2])}')"
        
        operator1 = c1_list[1]

        expr = f"{op11} {operator1} {op12}"
    else: 
        cond_idx1 = condition.strip().replace('Or','')[1:-1]
        or_input = "Or("
        or_list =  cond_idx1.split(',')
        for single_cond in or_list:
            c_list = single_cond.strip(). split(' ')
        
            if c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                op11 = f"z3.Int('{c_list[0]}')"
            else: 
                # op11 = f"z3.StringVal('{c_list[0]}')"
                if c_list[0].startswith("i_"):
                    op11 = f"z3.IntVal('{int(c_list[0][2:])}')"
                else:
                    op11 = f"z3.IntVal('{int(c_list[0])}')"

            if c_list[2][0].isalpha() and not c_list[0].startswith("i_"):
                op12 = f"z3.Int('{c_list[2]}')"
            else:
                # op12 = f"z3.StringVal('{c_list[2]}')"
                if c_list[2].startswith("i_"):
                    op12 = f"z3.IntVal('{int(c_list[2][2:])}')"
                else:
                    op12 = f"z3.IntVal('{int(c_list[2])}')"
                
            operator1 = c_list[1]
            expr = f"{op11} {operator1} {op12}"
            or_input += expr + ','

        expr = or_input[:-1] + ')'
    
    return expr

def has_redundancy(solver, tau_solver, conditions):
    has_redundant = False

    result = conditions[:]
    
    drop_idx = {}
    dp_arr = []
    for i in range(len(conditions)):
        drop_idx[i] = []
    
    if len(conditions) == 0:
        return has_redundant, result
    
    processed_conditions = {}
    for idx1 in range(len(conditions) - 1):
        expr1 = ""
        if idx1 not in processed_conditions.keys():
            expr1 = initial_z3_variable(conditions[idx1])
            processed_conditions[idx1] = expr1
        else:
            expr1 = processed_conditions[idx1]

        for idx2 in range(idx1+1,len(conditions)):
            expr2 = ""
            if idx2 not in processed_conditions.keys():
                expr2 = initial_z3_variable(conditions[idx2])
                processed_conditions[idx2] = expr2  
            else:
                expr2 = processed_conditions[idx2]
            
            G = Implies(eval(expr1), eval(expr2))
            solver.push()
            solver.add(Not(G))
            re = str(solver.check())
            solver.pop()
            if str(re) == 'unsat':
                drop_idx[idx1].append(idx2)
                if not has_redundant:
                    has_redundant = True

            G = Implies(eval(expr2), eval(expr1))
            solver.push()
            solver.add(Not(G))
            re = str(solver.check())
            solver.pop()
            if str(re) == 'unsat':
                drop_idx[idx2].append(idx1)
                if not has_redundant:
                    has_redundant = True

    if has_redundant:
        drop_result = {}
        for i in range(len(conditions)):
            drop_result[i] = []

        for c1 in list(drop_idx):
            for c2 in drop_idx[c1]:
                if c2 == c1:
                    continue
                drop_idx[c1]+=(drop_idx[c2])
                drop_idx[c1] = list(set(drop_idx[c1]))
                drop_idx[c2] = []
                if c1 in drop_idx[c1]:
                    drop_idx[c1].remove(c1)

        for c1 in list(drop_idx):
            for c2 in drop_idx[c1]:        
                dp_arr.append(c2)

        is_tauto = True
        final_result = []
        for i in range(0, len(result), 1):
            if i not in dp_arr:
                final_result.append(result[i])

                c = "Not({})".format(processed_conditions[i])
                tau_solver.push()
                tau_solver.add(eval(c))
                if tau_solver.check() == z3.sat:
                    is_tauto = False
                tau_solver.pop()
        
        # result = [result[i] for i in range(0, len(result), 1) if i not in dp_arr]
        if is_tauto:
            return has_redundant, '{}'
        return has_redundant, final_result
    else:
        return has_redundant, ""