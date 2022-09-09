from z3 import *

I = IntSort() # the datatype in Set
s = Solver()

# declare an empty set for IntSort
Nodes = EmptySet(I)

# add values 1 and 2 into set
# it's equal to below two: Nodes = SetAdd(SetAdd(Nodes, 1), 2)
Nodes = SetAdd(Nodes, 1) 
Nodes = SetAdd(Nodes, 2)
print(Nodes)

s.push()
s.add(IsMember(3,Nodes)) # check is 3 is a memeber of set Nodes
print(s.check())
s.pop()

s.push()

# Check 2 in set(1, 2, 3)
expr_str1 = "IsMember(2, SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), 3))"

# add a Int variable a3 into set, 
# if we do not specify domain of a3, then other values except for 1 and 2 that are not sure a member of this set
expr_str1_1 = "Not(IsMember(3, SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), Int('a3'))))"
s.add(eval("Int('a3') == IntVal(3)")) # add domain for a3 for expr_str1_1
s.add(eval(expr_str1_1))
print(s.check())
s.pop()

s.push()
# check if set(1, 2) is a subset of set(1, 2, 3)
expr_str2 = "IsSubset( \
        SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), \
        SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), 3)\
        )"

s.add(eval(expr_str2))
print(s.check())
s.pop()

s.push()
# check if set(1, 2, 3) is a subset of set(1, 2)
expr_str3 = "IsSubset( \
        SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), 3), \
        SetAdd(SetAdd(EmptySet(IntSort()), 1), 2) \
        )"

s.add(eval(expr_str3))
print(s.check())
s.pop()


