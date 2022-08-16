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
 ```
