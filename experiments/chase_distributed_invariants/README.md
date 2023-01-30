# Scripts for running the chase experiments

## code for test idea 

`script_chase_distributed_invariants.py`

- the_chase(conn, initial_T_tablename, initial_T_tuples, initial_T_attributes, initial_datatypes, policies)
  - conn: a instance of Postgres connection
  - initial_T: A python dictionary. Including `tablename`, `tuples`, `attributes`, `datatypes`.
    - `tablename`:  tablename of input table T
    - `tuples`: the tuples of input table T
    - `attributes`: a list of attributes for initial T table
    - `datatypes`: a list of datatypes for each attributes in initial T table
    - format:`{'tablename': xxx, 'tuples':[(...), (...),...], 'attributes': [...], 'datatypes':[...]}`
  - policies: a list of policies. A policy contains multiple dependencies. The format of a policy see below.

- database configuration, modify [`databaseconfig.py`](../../databaseconfig.py)
  ```python
    # modify config in databaseconfig.py under pyotr folder
    postgres = {
        "host": "127.0.0.1",
        "user": "postgres",
        "password": "postgres",
        "db": "db"  #working database
    }

    # connect to Postgres, `conn` is a instance of Postgres connection
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
  ```

- Policy format

  ```python
  # rewrite (src:B, dst:C) to (src:A, dst:C) at first node
  policy_p1 = [ 
        { # rewriting policy at first node
            'dependency_tuples': [
                ('f', '10', '11', '10', '2'), # the body of dependency
                ('f', 's', 'd', '2', '3')
            ], 
            'dependency_summary': ["s = 9", "d = 11"],  # the summary of dependency
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  # the schema of dependency
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'  # the type of dependency, tgd or egd
        }, # This is a dependency
        { 
            'dependency_tuples': [
                ('f', '9', '11', '9', '1'),
                ('f', 's', 'd', '1', '3')
            ], 
            'dependency_summary': ["s = 9", "d = 11"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '9', '12', '9', '1'),
                ('f', 's', 'd', '1', '3')
            ], 
            'dependency_summary': ["s = 9", "d = 12"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]  # This is a policy containing three dependencies
  ```
**Note1: we use etheir integer or IP prefix for nodes and hosts. '10.2' is invalid encoding**

**Note2: we call `the_chase()` to completely run the chase. For the complete example, see `__main__` in [`script_chase_distributed_invariants.py`](script_chase_distributed_invariants.py). The ordering strategy is random permutation.**

****
## experiment code

- [`run_scrip.py`](run_script.py):
  - `run_ordering_strategies_new()`: run experiments with a specific configuration

- [`script_chase_distributed_invariants.py`](script_chase_distributed_invariants.py):
  - `run_chase_distributed_invariants()`: script for chasing for a specific configuration.
    - `gen_gamma_table()`: generate gamma table
    - `gen_E_for_chase_distributed_invariants()`: generate tableau query E of the topology
    - `gen_Z_for_chase_distributed_invariants()`: generate inverse image
    - `gen_dependencies_for_chase_distributed_invariants()`: generate deoendencies
      - `gen_rewrite_dependencies()`: generate rewrite dependencies
      - `gen_forwarding_dependency()`: generate forwarding dependency
      - `gen_firewall_dependency()`: generate firewall dependency
      - `gen_new_dependency()`: generate new additional dependency
