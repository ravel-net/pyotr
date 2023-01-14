# Scripts for running the chase experiments

## code for test idea 

`run_toy.py`

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

- rewriting policy format

  ```python
  # rewrite src from 10.0.0.2 to 10.0.0.1 at node 1
  rewrite_policy1 = [
      {  # \sigma_1: inserting entry
          'dependency_tuples': [
              ('f', '10.0.0.2', '10.0.0.3', '1', '2')   # the body of dependency
          ], 
          'dependency_summary': ['f', '10.0.0.1', '10.0.0.3', '1', '2'],  # the summary of dependency
          'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],   # the schema of dependency
          'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
          'dependency_summary_condition': None, 
          'dependency_type': 'tgd'  # tgd for inserting tuple in rewriting policy
      },  # This is a dependency
      {   # \sigma_1': the flow id should be the same before and after rewriting 
          'dependency_tuples': [
              ('f1', '10.0.0.2', '10.0.0.3', '1', '2'),  # the body of dependency
              ('f2', '10.0.0.1', '10.0.0.3', '1', '2')
          ], 
          'dependency_summary': ['f1 = f2'],  # the summary of dependency
          'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],   # the schema of dependency
          'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
          'dependency_summary_condition': None, 
          'dependency_type': 'egd'  
      } # This is a dependency
  ] # This is a policy containing two dependencies
  ```

- firewall policy format
  ```python
  # block flow with source=10.0.0.2 and dest=10.0.0.4
  firewall_policy1 = [
      {
          'dependency_tuples': [
              ('f', 's', 'd', '1', 'x_x') # the body of dependency
          ], 
          'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
          'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
          'dependency_summary': [],  # summary is empty for firewall dependency, means it's a deletion
          'dependency_summary_condition': ["s = 10.0.0.2", "d = 10.0.0.4"], # using '=' is easy for query encoding 
          'dependency_type': 'egd'
      } # this dependency means deleting the entry with source = 10.0.0.2 and dest=10.0.0.4 at node 1
  ] # This is a policy containing one dependency
  ```

- \sigma_new 
  - We haven't decided the final version of the \sigma_new, so we use SQLs corresponding to the datalog rules to encode \sigma_new.

- initial_table_T
  ```python
  initial_T_tablename = "T"  # assgin a namt for input table T
  initial_T_tuples = [  # the tuples in input table T
          ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '1')
      ]
  ```

- Mapping E
  - The mapping E is not decided yet, so we should input the tuples of mapping E.
  ```python 
  E_tupls = [
          ('f', 's', 'd0', 's', '1'), 
          ('f', 's1', 'd1', '1', '2'), 
          ('f', 's2', 'd2', '2', '3'),
          ('f', 's3', 'd', '3', 'd')
      ]
  ```
- security_hole
  - we should detemine the checking security hole
  ```python
  security_hole = ['10.0.0.2', '10.0.0.4'] # block [source, dest]
  ```

- run_the_chase(conn, initial_T_tablename, initial_T_tuples, policies, sigma_new_sqls, E_tuples, security_hole)
  - conn: a instance of Postgres connection
  - initial_T_tablename: tablename of input table T
  - initial_T_tuples: the tuples of input table T
  - policies: a list of policies. A policy contains multiple dependencies.
  - sigma_new_sqls: a list of SQLs corresponding to the datalog rules of \sigma_new
  - security_hole: the checking security hole

**Note1: we use etheir integer or IP prefix for nodes and hosts. '10.2' is invalid encoding**

**Note2: we call `run_the_chase()` to completely run the chase. For the complete example, see `__main__` in [`run_toy.py`](run_toy.py). The ordering strategy is that chasing policies by given a certain ordering then checking security hole until run to converge**

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
