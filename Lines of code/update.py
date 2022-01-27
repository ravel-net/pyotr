def upd_condition(tree):
    count_time = 0
    print("\n************************Step 2: update condition****************************")
    cursor = conn.cursor()

    where_caluse = tree['where']
    keyword = list(where_caluse.keys())[0]
    conditions = copy.deepcopy(where_caluse[keyword])

    sql = ""
    cond_list = []
    where_list = []
    for cond in conditions:
        if cond[0][1] == '.': cond[0][1] = '_'
        if cond[2][1] == '.': cond[2][1] = '_'
        left_opd = "".join(cond[0])
        right_opd = "".join(cond[2])

        if cond[1] == '=':
            cond_list.append("{} || ' {} ' || {}".format(left_opd, '==', right_opd))
        else:
            cond_list.append("{} || ' {} ' || {}".format(left_opd, cond[1], right_opd))
        
        where_list.append([left_opd, right_opd])

    begin = time.time()
    if keyword == '' or keyword == 'and':
        
        # for c in cond_list:
        for idx, c in enumerate(cond_list):
            # sql = "update output set condition = array_append(condition, {})".format(c)
            sql = "update output set condition = array_append(condition, {}) where is_var({}) or is_var({})".format(c, where_list[idx][0], where_list[idx][1])
            print(sql)
            cursor.execute(sql)
    else:
        # keyword == or
        sql = "update output set condition = array_append(condition, {})".format("'Or(' || " + " || ' , ' || ".join(cond_list) + " || ')'")
        print(sql)
        cursor.execute(sql)
    count_time += (time.time() - begin)

    '''
    Check the selected columns
    if select *, drop duplicated columns,
    else only keep selected columns
    '''
    # table_num = len(tree['from'])
    drop_cols = []
    # if table_num > 1:
    if '*' in tree['select']:
        # remove duplicated columns
        # print('remove redundent')
        cursor.execute("select * from output limit 1")
        cols_name = [row[0] for row in cursor.description]
        begin = time.time()
        for cond in conditions:
            if cond[1] == '=':
                left_opd = "".join(cond[0])
                right_opd = "".join(cond[2])
                sql = "update output set {} = {} where not is_var({})".format(left_opd, right_opd, right_opd)
                if right_opd in cols_name:
                    drop_cols.append(right_opd)
                print(sql)
                cursor.execute(sql)
        count_time += time.time() - begin
    else:
        # only keep specified columns
        # print('keep specified columns')
        selected_cols = copy.deepcopy(tree['select'])
        select_col_dict = {}
        for col in selected_cols:
            if col[0][1] == '.': 
                col[0][1] = '_'
            name = "".join(col[0])
            select_col_dict[name] = col[2]

        rename_col = []
        keys = select_col_dict.keys()
        cursor.execute("select * from output limit 1")
        for col in cursor.description:
            col = col[0]
            if col in keys and select_col_dict[col] != '' and col != select_col_dict[col] :
                rename_col.append("{} to {}".format(col, select_col_dict[col]))
                continue
            if col == 'condition':
                continue
            if col not in keys:
                drop_cols.append(col)

        if len(rename_col) > 0: 
            begin = time.time()
            for new_col in rename_col:
                sql = "ALTER TABLE output rename column " + new_col
                print(sql)
                cursor.execute(sql)
            count_time += time.time() - begin

    if len(drop_cols) > 0:
        begin = time.time()
        sql = "ALTER TABLE output drop column " + ", drop column ".join(drop_cols)
        print(sql)
        cursor.execute(sql)
        count_time += time.time() - begin
    conn.commit()
    print("\ncondition execution time:", count_time)
    # logging.warning("condition execution time: %s" % str(count_time))
    return count_time