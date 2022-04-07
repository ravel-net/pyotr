def convert_z3_variable(condition, datatype):
    c_list = condition.split()

    if c_list[0][0].isalpha():
        op1 = f"z3.{datatype}('{c_list[0]}')"
    else: 
        op1 = f"z3.{datatype}Val('{c_list[0]}')"
    
    if c_list[2][0].isalpha():
        op2 = f"z3.{datatype}('{c_list[2]}')"
    else:
        op2 = f"z3.{datatype}Val('{c_list[2]}')"
    
    operator = c_list[1]
    return op1, operator, op2

def analyze(condition):
    cond_str = condition
    prcd_cond = ""
    if 'And' in cond_str or 'Or' in cond_str:
        stack_last_post = []
        i = 0
        stack_last_post.insert(0, i)
        condition_positions = []
        while i < len(cond_str):
            if cond_str[i] == '(':
                if len(stack_last_post) != 0:
                    stack_last_post.pop()
                stack_last_post.insert(0, i+1)
            elif cond_str[i] == ')' or cond_str[i] == ',':
                begin_idx = stack_last_post.pop()
                if i != begin_idx:
                    condition_positions.append((begin_idx, i))
                stack_last_post.insert(0, i+1)      
            i += 1
            
        if len(stack_last_post) != 0:
            begin_idx = stack_last_post.pop()
            if begin_idx !=  len(cond_str):
                condition_positions.append((begin_idx, len(cond_str)))
        # print(cond_str[51:])
        # print(stack_last_post)
        # print("condition_positions",condition_positions)
        for idx, pair in enumerate(condition_positions):
            if idx == 0:
                prcd_cond += cond_str[0:pair[0]]
            else:
                prcd_cond += cond_str[condition_positions[idx-1][1]:pair[0]]
            
            c = cond_str[pair[0]: pair[1]].strip()
            op1, operator, op2 = convert_z3_variable(c, 'Int')
            prcd_cond += "{} {} {}".format(op1, operator, op2)
        if len(condition_positions) != 0:
            prcd_cond += cond_str[condition_positions[-1][1]:]
        else:
            prcd_cond += cond_str
        # print("prcd_cond", prcd_cond)
    else:
        op1, operator, op2 = convert_z3_variable(condition, 'Int')
        prcd_cond += "{} {} {}".format(op1, operator, op2)
        # print(prcd_cond)
    return prcd_cond