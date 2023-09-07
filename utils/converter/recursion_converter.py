"""
-- 1 -> 2 -> 4 -> 5
-- \        /
--  -> 3 -> 

-- R(x4, x5) :- L(x4, x5)
-- R(x2, x5) :- R(x4, x5), L(x2, x4)
-- R(x3, x5) :- R(x4, x5), L(x3, x4)
-- R(x1, x5) :- R(x2, x5), L(x1, x2)
-- R(x1, x5) :- R(x3, x5), L(x1, x3)

# IDB relations: R
# EDB relations: L


def converter(program):
    define rules being in program

    # identify IDB relations and EDB relations
    IDB_relations, EDB_relations = identify_relations(rules)

    # group rules
    remaining_rules = rules
    ctes = []  # stores ctes

    for each IDB_relation in IDB_relations
        base_rules, recursive_rules, non_recursive_rules, remaining_rules = find_rules_for_IDB(IDB_relation, remaining_rules, IDB_relations, EDB_relations)

        ctes += generate_ctes(base_rules, recursive_rules, non_recursive_rules)
    
    recursive_sql = generate_recursive_sql(ctes)

    return recursive_sql

def find_rules_for_IDB(IDB_relation, rules, IDB_relations, EDB_relations):
    # IDB_relations: R, T; EDB_relations: L
    # R(1, 2) :-          -> base rule
    # R(x, y) :- L(x, y)  -> base_rule
    # T(x, y) :- R(x, z), L(z, y)  -> nonrecursive rule
    # T(x, y) :- T(x, z), R(z, y)  -> recursive rule

    base_rules = []
    recursive_rules = []
    non_recursive_rules = []

    for each rule in rules:
        if IDB_relation is the head of rule:
            define atoms being in the body of rule
            if atoms is empty: # it's a fact rule
                stores rule to base_rules
            elif atoms - EDB_relations is empty: # only contains EDBs
                stores rule to base_rules
            elif atoms contains IDB_relation: # body contains head
                stores rule to recursive_rules
            else:
                stores rule to non_recursive_rules

    return base_rules, recursive_rules, non_recursive_rules


def generate_ctes(base_rules, recursive_rules, non_recursive_rules):

    ctes = []
    if base_rules is empty and non_recursive_rules is empty:
        for each recursive_rule in recursive_rules
            base_rule = add_base_rules(recursive_rule)
            generate cte storing in ctes
    else:
        generate cte storing in ctes

def add_base_rules(recursive_rule):
    # G(x,y,z) :- G(x,w,z), A(w,y), A(w,z), A(z,z), A(z,y)
    # =>
    # G(x,y,z) :- G0(x,y,z)  # -> added base rule
    # G(x,y,z) :- G(x,w,z), A(w,y), A(w,z), A(z,z), A(z,y)

    find IDB relation in body
    create a base rule according IDB relation
"""

from copy import deepcopy
from utils.logging import timeit

class RecursiveConverter:
    """
    Assume all recursive rules are linear recursion
    
    Parameters:
    -----------
    _program: DT_program
        Instance of DT_program

    IDB_relations: list[string]
        IDB relations 

    EDB_relations: list[string]
        EDB relations
    
    """
    ########@timeit
    def __init__(self, program) -> None:
        self._program = program
        
        self._identify_relations()

        # self.program_sqls = self.recursion_converter()

    ########@timeit
    def recursion_converter(self):
        rules = self._program._rules

        # group rules
        remaining_rules = rules
        program_sqls = []  # stores program_sql for each IDB

        for IDB_relation in self.IDB_relations:
            base_rules, recursive_rules, non_recursive_rules, remaining_rules = self._find_rules_for_IDB(IDB_relation, remaining_rules)

            sql = self._generate_sql_for_each_IDB(IDB_relation, base_rules, recursive_rules, non_recursive_rules)
            program_sqls.append(sql)

        # print("program_sqls", program_sqls)
        return program_sqls

    ########@timeit
    def _identify_relations(self):
        self.IDB_relations = []
        self.EDB_relations = []

        body_atoms = []
        for rule in self._program._rules:
            head_relation = rule._head.db['name']
            if head_relation not in self.IDB_relations:
                self.IDB_relations.append(head_relation)

            for atom in rule._body:
                atom_relation = atom.db['name']
                if atom_relation not in body_atoms:
                    body_atoms.append(atom_relation)
        
        for b_atom in body_atoms:
            if b_atom not in self.IDB_relations:
                self.EDB_relations.append(b_atom)

    ########@timeit
    def _find_rules_for_IDB(self, IDB_relation, rules):
        base_rules = []
        recursive_rules = []
        non_recursive_rules = []
        remaining_rules = []

        for rule in rules:
            head_relation = rule._head.db['name']
            
            if IDB_relation == head_relation:
                atoms_relations = set([atom.db['name'] for atom in rule._body])
                if len(atoms_relations) == 0: # it's a fact rule
                    base_rules.append(rule)
                elif len(atoms_relations - set(self.EDB_relations)) == 0: # only contains EDBs
                    base_rules.append(rule)
                elif IDB_relation in atoms_relations: # body contains head
                    recursive_rules.append(rule)
                else:
                    non_recursive_rules.append(rule)
            else:
                remaining_rules.append(rule)
        return base_rules, recursive_rules, non_recursive_rules, remaining_rules

    ########@timeit
    def _generate_sql_for_each_IDB(self, IDB_relation, base_rules, recursive_rules, non_recursive_rules):
        
        # if no base rules, add a new base rule
        # if len(base_rules) == 0 and len(non_recursive_rules) == 0:
        #     base_rule = self._add_base_rules(IDB_relation, recursive_rules[0])
        #     base_rules.append(base_rule)
            # for recursive_rule in recursive_rules:

        # generate cte storing in ctes
        base_sqls = []
        for rule in base_rules:
            sql = rule.convertRuleToSQL()
            base_sqls.append(sql)

        for rule in non_recursive_rules:
            sql = rule.convertRuleToSQL()
            base_sqls.append(sql)
        
        program_sql = ""
        if len(recursive_rules) == 0: # non-recursive program
            union_sqls = []
            cte_sqls = []
            for idx, base_sql in enumerate(base_sqls):
                cte_sql = "temp_{}{} as ({})".format(IDB_relation, idx+1, base_sql)
                cte_sqls.append(cte_sql)

                temp_table = "temp_{}{}".format(IDB_relation, idx+1)
                union_sqls.append("select * from {}".format(temp_table))
            
            program_sql = "WITH {ctes} {main_query}".format(
                ctes=", ".join(cte_sqls),
                main_query="insert into {} ({})".format(IDB_relation, " UNION ".join(union_sqls))
            )

        else: # recursive program
            
            union_sqls = []
            cte_sqls = []
            for idx, rule in enumerate(recursive_rules):
                base_query = "select * from temp_{}{}".format(IDB_relation, idx)
                temp_table = "temp_{}{}".format(IDB_relation, idx+1)
                union_sqls.append("select * from {}".format(temp_table))
 
                rule_copy = deepcopy(rule)
                for atom in rule_copy._body:
                    if atom.db['name'] == IDB_relation:
                        atom.db['name'] = temp_table
                        
                        break
                recursive_sql = rule_copy.convertRuleToSQL()

                if idx == 0:
                    if len(base_sqls) == 0: # no base rule, add a new base rule
                        base_rule = self._add_base_rules(IDB_relation, recursive_rules[0])
                        base_sqls.append(base_rule.convertRuleToSQL())
                    else: # has base rules, add information for IDB
                        base_sqls.append("select * from {}".format(IDB_relation))  # for IDB information
                        # base_query = "select * from ({}) as foo".format(" union ".join(base_sqls))
                    if len(base_sqls) == 1:
                        base_query = base_sqls[0]
                    else:
                        base_query = "select * from ({}) as foo".format(" union ".join(base_sqls))
                
                cte_sql = "{cte_table} AS ({base_query} UNION {recursive_query})".format(
                    cte_table=temp_table,
                    base_query=base_query,
                    recursive_query=recursive_sql
                )

                cte_sqls.append(cte_sql)
            
            program_sql = "WITH RECURSIVE {ctes} {main_query}".format(
                ctes=", ".join(cte_sqls),
                main_query="insert into {} ({})".format(IDB_relation, " UNION ".join(union_sqls))
            )

        # print("program_sql", program_sql)
        return program_sql

    ########@timeit
    def _add_base_rules(self, IDB_relation, recursive_rule):
        new_body = []
        head_atom = None
        for atom in recursive_rule._body:
            if atom.db['name'] == IDB_relation:
                new_body.append(atom)
                head_atom = atom
                break
        
        new_rule = deepcopy(recursive_rule)
        new_rule._body = new_body
        new_rule._head = head_atom
        # print("new_rule", str(new_rule))
        return new_rule
        

