# Homomorphism Erroneous Examples

## Problem description

This problem happened on the overlay toy examples. Let's denote a physical forwarding chain which has two constant nodes as a one-hop forwarding chain(1->u1->u2->2), a physical forwarding chain which has three constant nodes as a two-hop forwarding chain(1->u1->u2->2->v1->v2->3). The homomorphsim works on the one-hop toy example when removing `('u1', 'u1', '{}')` but does not work on the two-hop toy example that means the logical-disjuncted conditions of the final result is a tautology on the one-hop toy example but is not a tautology on the two-hop toy example.


The encoding of the one-hop forwarding chain is 

```python
[
    ('1', 'u1', '{}'), 
    ('u1', 'u2', '{}'), 
    ('u2', '2', '{}'), 
    ('1', '1', '{}'), 
    ('u1', 'u1', '{}'), 
    ('u2', 'u2', '{}')
]
```


The encoding of the two-hop forwarding chain is 

```python
[
    ('1', 'u1', '{}'), 
    ('u1', 'u2', '{}'), 
    ('u2', '5', '{}'), 
    ('5', '2', '{}'), 
    ('2', 'v1', '{}'), 
    ('v1', 'v2', '{}'), 
    ('v2', '3', '{}'), 
    ('1', '1', '{}'), 
    ('u1', 'u1', '{}'), 
    ('u2', 'u2', '{}'), 
    ('2', '2', '{}'), 
    ('v1', 'v1', '{}'), 
    ('v2', 'v2', '{}')
]
```

## Codes

`multijoin_toy_one_hop.py` is the code I used to test homomorphism on the on-hop toy example when removing `('u1', 'u1', '{}')`. It directly used multiple-join query instead of split-joins method.

`multijoin_toy_twohop.py` is the code I used to test homomorphism on the two-hop toy example when removing `('u1', 'u1', '{}')`. It directly used multiple-join query instead of split-joins method.