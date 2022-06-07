import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.translator_pyotr as translator_pyotr
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology



def load_table(tablename, tableau, columns, datatypes):
    """
    Load data instance into database

    Parameters:
    ------------
    tablename: string, database table which stores tableau

    tableau: list, data instance

    columns: dict, table attributes with corresponding datatype. E.g. {name: text, age: integer}
    """
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()

    cursor.execute("drop table if exists {}".format(tablename))
    attributes = ["{} {}".format(columns[i], datatypes[i]) for i in range(len(columns))]
    cursor.execute("create table {} ({})".format(tablename, ", ".join(attributes)))
    conn.commit()

    execute_values(cursor, "insert into {} values %s".format(tablename), tableau)
    conn.commit()

    conn.close()

def run_homo(query, instance, variables, domains, columns):
    """
    Parameters:
    -----------
    query: string, tablea name which is treated as query

    instance: string, instance name(table name) which is treated as data instance and wil be input in query

    Returns:
    ----------
    ans: Boolean, whether homo is holds or not
    
    counter_models: Z3 model, one counter example
    """
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()

    cursor.execute("select * from {}".format(query))
    query_tableau = cursor.fetchall()
    print(query_tableau)
    conn.commit()
    conn.close()

    sql = tableau.general_convert_tableau_to_sql(query_tableau, instance, columns, ['1', '2'])
    print(sql)
    tree = translator_pyotr.generate_tree(sql)
    translator_pyotr.data(tree)
    translator_pyotr.upd_condition(tree, "int4_faure")
    translator_pyotr.normalization("Int")

    union_conditions, union_time = check_tautology.get_union_conditions(tablename="output", datatype="Int")
    ans = None
    counter_model = None

    if union_conditions != "False": # i.e. Empty table
        domain_conditions, domain_time = check_tautology.get_domain_conditions(domains, variables, "Int")
        ans, runtime, counter_model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
        print(ans)
        print(counter_model)
    else:
        ans = False
    
    return ans, counter_model

if __name__ == "__main__":
    # T_v = [('1', '2', '{}')]
    T_v = [('1', '2', '{}'), ('1', '1', '{}')]
    T_v_attrs = ['n1', 'n2', 'condition']
    T_v_datatypes = ["int4_faure", "int4_faure", "text[]"]

    # T_p = [
    #     ('1', 'u', '{}'),
    #     ('u', 'v', '{}'),
    #     ('v', '2', '{}')
    # ]
    T_p = [
        ('1', 'u', '{}'),
        ('u', 'v', '{}'),
        ('v', '2', '{}'),
        ('1', '1', '{}'),
        ('u', 'u', '{}'),
        ('v', 'v', '{}')
    ]
    T_p_attrs = ['n1', 'n2', 'condition']
    T_p_datatypes = ["int4_faure", "int4_faure", "text[]"]

    load_table("T_v", T_v, T_v_attrs, T_v_datatypes)
    load_table("T_p", T_p, T_p_attrs, T_p_datatypes)

    domain_T_p = [1, 2]
    variables_T_p = ['u', 'v']
    ans1, counter_model1 = run_homo("T_v", "T_p", variables_T_p, domain_T_p, T_v_attrs)

    domain_T_v = []
    variables_T_v = []
    ans2, counter_model2 = run_homo("T_p", "T_v", variables_T_v, domain_T_v, T_p_attrs)
    print("T_v(T_p): ", ans1, counter_model1)
    print("T_p(T_v): ", ans2, counter_model2)


    

