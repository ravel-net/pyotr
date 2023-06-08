# Datalog Program
This folder provides a representation of a datalog program. The datalog program is made up of a list of rules, which in turn is made up of a list of atoms. The main function supported by the datalog program are `contains` and `minimize`. Contains checks for uniform containment between two programs and minimize removes redundant atoms and rules from a program. Postgresql is used as the reasoning engine and datalog programs are converted to sql, which is iteratively run until a fixed point is reached (or maximum number of iterations, defined by user, is reached)

All other details are given as docstrings in the code
## Usage examples:
````
  # Example 6 - Containment
  p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
  p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
  program1 = DT_Program(p1)
  program2 = DT_Program(p2)
  print(program1.contains(program2))
  print(program2.contains(program1))    

  # # Example 7 - Minimization
  p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
  p2 = "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"
  program1 = DT_Program(p1)
  program2 = DT_Program(p2)
  print(program1.contains(program2))
  print(program2.contains(program1))    
  program1.minimize()
  print(program1)

  # # Control Plane Toy Example
  p1 = "R(x2,xd,x2 || xp) :- link(x2,x3), link(x2,x4), R(x3,xd,xp)\nR(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), link(x2,x4), R(x2,xd,xp)"
  p2 = "R(x2,xd,x2 || xp) :- link(x2,x3), R(x3,xd,xp)\nR(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), R(x2,xd,xp)"
  program1 = DT_Program(p1, {"R":["integer", "integer","integer[]"]}) # We need to provide the second argument, the list of column types for a database only when the default column type is not integer
  program2 = DT_Program(p2, {"R":["integer", "integer","integer[]"]})
  print(program2.contains(program1))
  print(program1.contains(program2))
````
 
## Datalog with incomplete information:
 
### Terminology
A datalog rule with c-variables consists of a head, body, (optionally) a pattern matching condition, and (optionally) an additional condition. The head and the body can have constants, c-variables, and variables. Consider the query: `T(f,1,n)[ϕ ∧ ȳ + z̄<2] :- R(f,1,n)[ϕ], ȳ + z̄ < 2`. Here `T(f,1,n)` is the head atom, `R(f,1,n)` is the body atom, `ϕ` is a pattern matching condition and `ȳ + z̄ < 2` is an additional condition. 

### Rule as a program:
When a datalog rule is treated as a program, c-variables are treated as normal variables. The generated database is also a c-table with a condition column. The pattern matching conditions associated with the c-variables are converted into WHERE clauses. The additional conditions, which are not part of pattern matching, are just appended in the condition column of the generated database (not shown in the examples below). Consider the examples: 

#### Examples 1:
(x and y are c-variables)  
**Rule:** `R(1,x)[x == 30] :- l(1,2),l(1,3),l(1,4),R(4,x)[x == 30]`  
**SQL:** `select 1 as c0, t3.c1 as c1 from l t0, l t1, l t2, R t3 where t0.c0 = 1 and t0.c1 = 2 and t1.c0 = 1 and t1.c1 = 3 and t2.c0 = 1 and t2.c1 = 4 and t3.c0 = 4 and t3.c1 = 30`

#### Example 2:
(x and y are c-variables)  
**Rule:** `R(1,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))] :- l(1,2),l(1,3),l(1,4),R(y,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))]`  
**SQL:** `select 1 as c0, t3.c1 as c1 from l t0, l t1, l t2, R t3 where t0.c0 = 1 and t0.c1 = 2 and t1.c0 = 1 and t1.c1 = 3 and t2.c0 = 1 and t2.c1 = 4 and ((t3.c0 = 2 And t3.c1 = 10) Or ((t3.c0 = 3 And t3.c1 = 20) Or (t3.c0 = 4 And t3.c1 = 30)))`

#### Example 3:
(h3 is a c-variable)  
**Rule:** `R(a1,h3,[e1, x, y],3)[h3 == 10] :- R(e1,h3,[x, y],2)[h3 == 10],l(a1,h1),l(a1,e1),l(a1,h2)`  
**SQL:** `select t1.c0 as c0, t0.c1 as c1, ARRAY[t0.c0, t0.c2[1], t0.c2[2]] as c2, 3 as c3 from R t0, l t1, l t2, l t3 where t0.c3 = 2 and t0.c0 = t2.c1 and t1.c0 = t2.c0 and t2.c0 = t3.c0 and t0.c1 = 10`

For a discussion on the changes in the fixed point computation, see issue [2](https://github.com/ravel-net/pyotr/issues/2)

### Rule as a data instance:
When a rule that has c-variables is treated as a data instance, the constants are treated as constants, the c-variables are treated as c-variables, and the variables are treated as distinct constants. The pattern matching conditions are added to the condition column of the instantiated database. (It’s unclear how to handle additional conditions that are not part of pattern matching. Currently we ignore them when treating a rule as a data instance, but we might want to append such conditions to all generated tuples i.e. treat such conditions as global conditions). 

#### Example 1:
(h3 is a c-variable, while a3 is a variable instantiated to a distinct constant 0)  
**Atom:** l(a3,h3)[h3 == 10]  
**Database:** l  
 c0 | c1 |  condition   
----+----+--------------  
 0  | h3 | {"h3 == 10"}  
 
#### Example 2:
(y and z are c-variables, x is a variable instantiated to a distinct constant 0)  
**Atom:** L(x,y,z)[And(y == 10, y < 20)]  
**Database:** L  
 c0 | c1 | c2 |        condition           
----+----+----+--------------------------  
  0 | y  | z  | {"And(y == 10, y < 20)"}

#### Example 3:
(x is a c-variable)  
**Atom:** R(4,x)[x == 30]  
**Database:** R  
c0 | c1 |  condition    
----+----+-------------  
 4  | x  | {"x == 30"}  

When checking if the instantiated head is in the generated database, there is some more nuance involved when dealing with c-variables. We need a proper way to handle the conditions and the mapping of c-variables to constants and other c-variables. When checking if the data portion of a tuple is equal to the data portion of the instantiated head, we need to generate additional conditions for mapping of c-variables. For example, if c-variable x maps to constant 1, we need to add x=1 condition in the tuple condition. This will become clear in the example below. Note that the instantiated head and the tuples in the generated database will only have constants and c-variables (since variables are converted to distinct constants). 


### Comprehensive Example
Consider program P and Q, where x and y are c-variables. The domain of y is {2,3,4} and the domain of x is {10,20,30}:  
**P:** `R(1,x)[x == 30] :- l(1,2), l(1,3), l(1,4), R(4,x)[x == 30]`  
**Q:** `R(1,x)[Or(x == 10, x == 20, x == 30)]  :- l(1,2), l(1,3), l(1,4), R(y,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))] `	

We want to check if program P contains program Q. 

#### Step 1:
Instantiate the body of program Q  
**l:**  
 c0 | c1 | condition   
----+----+-----------  
  1 |  2 | {}  
  1 |  3 | {}  
  1 |  4 | {}  

**R:**  
 c0 | c1 |                                 condition                                   
----+----+---------------------------------------------------------------------------  
 y  | x  | {"Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))"}  

#### Step 2:
Execute program P  
**SQL:** `select 1 as c0, t3.c1 as c1 from l t0, l t1, l t2, R t3 where t0.c0 = 1 and t0.c1 = 2 and t1.c0 = 1 and t1.c1 = 3 and t2.c0 = 1 and t2.c1 = 4 and t3.c0 = 4 and t3.c1 = 30`    
**New R:**  
 c0 | c1 |                                 condition                                   
----+----+---------------------------------------------------------------------------  
 y  | x  | {"Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))"}  
 1  | x  | {"And(1 == 1, 2 == 2, 1 == 1, 3 == 3, 1 == 1, 4 == 4, y == 4, x == 30)"}  

Note that y maps to 4 since the body of program P contains the rule R(4,x). Also, the domain of y adds trivial constraints (e.g 1 == 1, 2 == 2, 1 == 1, 3 == 3, 1 == 1, 4 == 4)

#### Step 4: 
Check if data portion of generated head is contained within the result  
**Instantiated Head:** ['1', 'x']  
**Tuple 1:** ['y', 'x']

Since y is a c-variable, the data portion of tuple 1 matches the instantiated head. However, an additional condition is imposed on the tuple, namely y = 1

#### Step 5: 
Check if condition of generated head is contained within the matched tuple from step 4  
**(i) Condition of instantiated head:** `Or(x == 10, x == 20, x == 30)`  
**(ii) Condition of tuple 1:** `Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))`  
**(iii) Condition of tuple 1 with data portion mapping condition:** `And(Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30)), 1 == y, x == x)`

Since conditions (i) and (iii) are not equivalent, we move on to the next tuple.

#### Step 6:
Repeat step 4 and 5 until all tuples are considered or we find that the instantiated head is in the result. Then, repeat step 1-5 until a fixed point is reached or we find that the instantiated head is in the result.

## Miscellaneous
### Variables as distinct constants:
When a rule is treated as a data instance, variables are replaced with distinct constants. Ideally, this requires making sure that the constants are different from any other constant in the rule and any other constant in the program that is applied to it. One way to do this would be to treat variables as c-variables without conditions. However, this might be slow. In our current implementation, we treat variables as constants that are unlikely to appear elsewhere. For integer datatype, we replace variables as constant above 10000. For IP Addresses, the IP for variables starts with 0.0.0.*.  