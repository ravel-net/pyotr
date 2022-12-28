# Scripts for running the chase experiments

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
