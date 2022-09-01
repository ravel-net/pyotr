import sys
import psycopg2 
from psycopg2.extras import execute_values
from os.path import dirname, abspath 
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import databaseconfig as cfg
import Core.Homomorphism.translator_pyotr as translator_z3
import Core.Homomorphism.translator_pyotr_BDD as translator_bdd
import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_tautology as merge_tuples_z3
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_BDD as merge_tuples_bdd
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

DATATYPE = 'inet_faure'
REASONING_TYPE = 'BitVec'

def check_programP_contains_ruleQ(P_programs, Q_data_instance, Q_summary, reasoning_type, datatype, reasoning_engine, simplification='On'):
    """
    Check if program P contains a single rule Q.

    Parameters:
    -----------
    P_programs: list[dict]
        the SQL and the header of P(single rule). tablename is the table of header.  Format: {tablename: str, sql: str, header: list, attributes:list}

    Q_data_instance: dict
        treat program Q (single rule) is ctables. Format: {tablename: {attributes:list, datatype: list, instance: list[tuple], variables: {var: list}}}

    Q_summary: dict
        the header of program Q/ Format: {tablename: str, header: list, datatype: list, attributes:list}

    reasoning_type: string
        the type of reasoning engine

    datatype: string
        the type of data. 'int4_faure', 'inet_faure', ...
    
    reasoning_engine: 'z3' or 'bdd'
        the type of reason engine. There are two types: Z3 or BDD

    simplification: 'on' or 'off'
        only works when reasoning engine set to 'z3'. 'on' sets z3 engine simplifying conditions, 'off' sets z3 engine does not simplify conditions
    
    Returns:
    --------
    Result: Boolean
        True or False. Program P contains Q, return True; otherwise, return False.
    """

    '''
    Store Q data instance into database
    '''
    for tablename in Q_data_instance.keys():
        cursor.execute("Drop table if exists {}".format(tablename))
        datatypes = Q_data_instance[tablename]['datatype']
        attributes = Q_data_instance[tablename]['attributes']
        cursor.execute("create table {} ({})".format(tablename, ", ".join("{} {}".format(attributes[idx], datatypes[idx]) for idx in range(len(datatypes)))))

        insert_sql = "insert into {} values %s".format(tablename)
        execute_values(cursor, insert_sql, Q_data_instance[tablename]['instance'])
        conn.commit()

    '''
    Run P program until no changes happen
    '''
    changes = True
    iteration = 0
    
    while changes or iteration < 10:
        iteration += 1
        for program in P_programs:
            # program = P_programs[iteration]
            program_sql = program['sql']
            program_table = program['tablename']

            '''
            generate new facts
            '''
            if reasoning_engine == 'z3':
                tree = translator_z3.generate_tree(program_sql)
                translator_z3.data(tree)
                translator_z3.upd_condition(tree, datatype)

                if simplification == 'On':
                    translator_z3.normalization(reasoning_type)

                '''
                compare generating IDB and existing DB if there are new IDB generated
                if yes, the DB changes, continue run the program on DB
                if no, the DB does not change, stop running 
                '''
                cursor.execute("select {} from output".format(", ".join(program['attributes'])))
                output_results = cursor.fetchall()

                cursor.execute("select * from {}".format(program_table))
                existing_tuples = cursor.fetchall()

                inserting_tuples = []
                for res_tup in output_results:
                    for existing_tup in existing_tuples:
                        # print("res_tup", res_tup)
                        # print("existing_tup", existing_tup)
                        if str(res_tup) == str(existing_tup):
                            continue 
                        else:
                            inserting_tuples.append(res_tup)
                if len(inserting_tuples) == 0:
                    changes = False
                else:
                    changes = True
                    insert_sql = "insert into {} values %s".format(program_table)
                    execute_values(cursor, insert_sql, inserting_tuples)
                conn.commit()

                '''
                Merge tuples
                '''
                merge_tuples_z3.merge_tuples(Q_summary['tablename'], # tablename of header
                                        "{}_out".format(Q_summary['tablename']), # output tablename
                                        [], # domain
                                        reasoning_type) # reasoning type of engine
                cursor.execute("drop table if exists {}".format(Q_summary['tablename']))
                cursor.execute("alter table {}_out rename to {}".format(Q_summary['tablename'], Q_summary['tablename']))
                conn.commit()
            elif reasoning_engine == 'bdd':
                if reasoning_type == 'BitVec':
                    print("BDD engine does not support BitVec now! ")
                    exit()

                bddmm.initialize(3, 2)
                translator_bdd.set_domain(['1', '2'])
                translator_bdd.set_variables(['u', 'v', 'd'])
                translator_bdd.process_condition_on_ctable('R')
                translator_bdd.process_condition_on_ctable('L')
                
                tree = translator_bdd.generate_tree(program_sql)
                translator_bdd.data(tree)
                translator_bdd.upd_condition(tree, datatype)

                # TODO: How to judge the generating tuple is already in the table
                cursor.execute("insert into {} select {} from output".format(program_table, ", ".join(program['attributes'])))
                conn.commit()

                '''
                Merge tuples
                '''
                merge_tuples_bdd.merge_tuples(Q_summary['tablename'], # tablename of header
                                        "{}_out".format(Q_summary['tablename'])) # output tablename
                                        
                cursor.execute("drop table if exists {}".format(Q_summary['tablename']))
                cursor.execute("alter table {}_out rename to {}".format(Q_summary['tablename'], Q_summary['tablename']))
                conn.commit()
            else:
                print("We do not support {} engine!".format(reasoning_engine))
                exit()

            '''
            check whether Q_summary is in resulting table
            '''
            cursor.execute("select {} from {}".format(", ".join(Q_summary['attributes']), Q_summary['tablename']))
            resulting_tuples = cursor.fetchall()
            conn.commit()

            header = Q_summary['header']
            for tup in resulting_tuples:
                contains = False

                idx = 0
                while idx < len(tup): 
                    if 'condition' in Q_summary['attributes'][idx]: # Assume the condition locates the last attribute
                        condition1 = None
                        condition2 = None
                        if len(tup[idx]) == 0:
                            condition1 = True
                        elif len(tup[idx]) == 1:
                            condition1 = tup[idx][0]
                        else:
                            condition1 = "And({})".format( ", ".join(tup[idx]))
                        
                        if len(header[idx]) == 0:
                            condition2 = True
                        elif len(header[idx]) == 1:
                            condition2 = header[idx][0]
                        else:
                            condition2 = "And({})".format( ", ".join(header[idx]))

                        '''
                        Assume: the condition attribute locates the last attribute
                        if conditions are equavalent, meaning that two tuple are equivalent.
                        '''
                        if reasoning_engine == 'z3':
                            is_equal = check_tautology.check_equivalence_for_two_string_conditions(condition1, condition2, reasoning_type)
                            if is_equal:
                                contains = True
                                break
                        else:
                            print("Only z3 engine supports to check equivalance for two conditions!")
                            exit()

                    if tup[idx] != header[idx]:
                        break

                    idx += 1
                
                if contains:
                    return True
        exit()    
    return False

# def check_equivalence_between_program_PandQ_integer():



if __name__ == '__main__':
    # """
    # Program P

    # p1: R(z, d1)[d1 = 1] :- R(x, d1), R(y, d2), L(z, x), L(z, y), [d1 = 1]
    # p2: R(z, d2)[d2 = 2] :- R(x, d1), R(y, d2), L(z, x), L(z, y), [d2 = 2]

    # Program Q
    # q1: R(v, d)[d = 1 or d = 2] :- R(u, d), L(v, u), [d = 1 or d = 2]
    # """
    
    # # {tablename: str, sql: str, header: list, attributes:list}
    # program_p1 = {
    #     'tablename': 'R',
    #     'sql':"select l1.a1 as a1, r1.a2 as a2 from R r1, R r2, L l1, L l2 where r1.a1 = l1.a2 and r2.a1 = l2.a2 and l1.a1 = l2.a1 and r1.a2 = '1'",
    #     'header': ['z', 'd1', ["d1 == 1"]],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    # # {tablename: {attributes:list, datatype: list, instance: list[tuple]}}
    # instance_p1 = {
    #     'R': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('3', 'd1', '{"d1 == 1"}'),
    #             ('4', 'd2', '{}')
    #         ]
    #     },
    #     'L': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('5', '3', '{}'),
    #             ('5', '4', '{}')
    #         ]
    #     }
    # }

    # # {tablename: str, header: list, datatype: list, attributes:list}
    # summary_p1 = {
    #     'tablename': 'R',
    #     'header': ['5', 'd1', ["d1 == 1"]],
    #     'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    # program_p2 = {
    #     'tablename': 'R',
    #     'sql': "select l1.a1 as a1, r1.a2 as a2 from R r1, R r2, L l1, L l2 where r1.a1 = l1.a2 and r2.a1 = l2.a2 and l1.a1 = l2.a1 and r2.a2 = '2'",
    #     'header': ['z', 'd1', ["d1 == 1"]],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    # instance_p2 = {
    #     'R': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('3', 'd1', '{}'),
    #             ('4', 'd2', '{"d2 == 2"}')
    #         ]
    #     },
    #     'L': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('5', '3', '{}'),
    #             ('5', '4', '{}')
    #         ]
    #     }
    # }

    # summary_p2 = {
    #     'tablename': 'R',
    #     'header': ['5', 'd2', ["d2 == 2"]],
    #     'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    # program_q1 = {
    #     'tablename': 'R',
    #     'sql':"select l1.a1 as a1, r1.a2 as a2 from R r1, L l1 where r1.a1 = l1.a2 and (r1.a2 = '1' or r1.a2 = '2')",
    #     'header': ['v', 'd', ["Or(d == 1, d == 2)"]],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    # instance_q1 = {
    #     'R': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('3', 'd', '{"Or(d == 1, d == 2)"}')
    #         ]
    #     },
    #     'L': {
    #         'attributes': ['a1', 'a2', 'condition'],
    #         'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #         'instance': [
    #             ('4', '3', '{}')
    #         ]
    #     }
    # }

    # summary_q1 = {
    #     'tablename': 'R',
    #     'header': ['4', 'd', ["Or(d == 1, d == 2)"]],
    #     'datatype': [DATATYPE, DATATYPE, 'text[]'],
    #     'attributes': ['a1', 'a2', 'condition']
    # }

    """
    Program P

    p1: R(z, d1)[d1 = 10.0.0.0] :- R(x, d1), R(y, d2), L(z, x), L(z, y), [d1 = 10.0.0.0]
    p2: R(z, d2)[d2 = 10.0.0.1] :- R(x, d1), R(y, d2), L(z, x), L(z, y), [d2 = 10.0.0.1]

    Program Q
    q1: R(v, d)[d = 10.0.0.0/31] :- R(u, d), L(v, u), [d = 10.0.0.0/31]
    """
    
    # {tablename: str, sql: str, header: list, attributes:list}
    program_p1 = {
        'tablename': 'R',
        'sql':"select l1.a1 as a1, r1.a2 as a2 from R r1, R r2, L l1, L l2 where r1.a1 = l1.a2 and r2.a1 = l2.a2 and l1.a1 = l2.a1 and r1.a2 = '10.0.0.0'",
        'header': ['z', 'd1', ["d1 == 10.0.0.0"]],
        'attributes': ['a1', 'a2', 'condition']
    }

    # {tablename: {attributes:list, datatype: list, instance: list[tuple]}}
    instance_p1 = {
        'R': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('11.0.0.3', 'd1', '{"d1 == 10.0.0.0"}'),
                ('11.0.0.4', 'd2', '{}')
            ]
        },
        'L': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('12.0.0.5', '11.0.0.3', '{}'),
                ('12.0.0.5', '11.0.0.4', '{}')
            ]
        }
    }

    # {tablename: str, header: list, datatype: list, attributes:list}
    summary_p1 = {
        'tablename': 'R',
        'header': ['12.0.0.5', 'd1', ["d1 == 10.0.0.0"]],
        'datatype': [DATATYPE, DATATYPE, 'text[]'],
        'attributes': ['a1', 'a2', 'condition']
    }

    program_p2 = {
        'tablename': 'R',
        'sql': "select l1.a1 as a1, r1.a2 as a2 from R r1, R r2, L l1, L l2 where r1.a1 = l1.a2 and r2.a1 = l2.a2 and l1.a1 = l2.a1 and r2.a2 = '10.0.0.1'",
        'header': ['z', 'd2', ["d2 == 10.0.0.1"]],
        'attributes': ['a1', 'a2', 'condition']
    }

    instance_p2 = {
        'R': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('11.0.0.3', 'd1', '{}'),
                ('11.0.0.4', 'd2', '{"d2 == 10.0.0.1"}')
            ]
        },
        'L': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('12.0.0.5', '11.0.0.3', '{}'),
                ('12.0.0.5', '11.0.0.4', '{}')
            ]
        }
    }

    summary_p2 = {
        'tablename': 'R',
        'header': ['12.0.0.5', 'd2', ["d2 == 10.0.0.1"]],
        'datatype': [DATATYPE, DATATYPE, 'text[]'],
        'attributes': ['a1', 'a2', 'condition']
    }

    program_q1 = {
        'tablename': 'R',
        'sql':"select l1.a1 as a1, r1.a2 as a2 from R r1, L l1 where r1.a1 = l1.a2 and r1.a2 = '10.0.0.0/31'",
        'header': ['v', 'd', ["d == 10.0.0.0/31"]],
        'attributes': ['a1', 'a2', 'condition']
    }

    instance_q1 = {
        'R': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('11.0.0.3', 'd', '{"d == 10.0.0.0/31"}')
            ]
        },
        'L': {
            'attributes': ['a1', 'a2', 'condition'],
            'datatype': [DATATYPE, DATATYPE, 'text[]'],
            'instance': [
                ('12.0.0.4', '11.0.0.3', '{}')
            ]
        }
    }

    summary_q1 = {
        'tablename': 'R',
        'header': ['12.0.0.4', 'd', ["d == 10.0.0.0/31"]],
        'datatype': [DATATYPE, DATATYPE, 'text[]'],
        'attributes': ['a1', 'a2', 'condition']
    }

    # check P contains q1
    result1 = check_programP_contains_ruleQ([program_p1, program_p2], instance_q1, summary_q1, REASONING_TYPE, DATATYPE, 'z3', 'on')
    print("P contains q1: ", result1)

    # check q1 contains p1
    result2 = check_programP_contains_ruleQ([program_q1], instance_p1, summary_p1, REASONING_TYPE, DATATYPE, 'z3', 'on')
    print("q1 contains p1: ", result2)

    # check q1 contains p2
    result3 = check_programP_contains_ruleQ([program_q1], instance_p2, summary_p2, REASONING_TYPE, DATATYPE, 'z3', 'on')
    print("q1 contains p2: ", result3)

    print("P equivalents Q: ", result1 and result2 and result3)






    



