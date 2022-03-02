#And(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))), 1 == x3, x3 == 2)
from collections import deque


def popUntilLogicalOP(stack):
	elem = stack.pop()
	listItems = []
	while elem != "Or" and elem != "And":
		listItems.append(elem)
		elem = stack.pop()
	return listItems[::-1], elem #Todo: Should work even without reversing array using ::-1

def combineItems(listItems, logicalOP):
	if len(listItems) == 1:
		return listItems[0]+")"
	elif len(listItems) == 2:
		return logicalOP+"("+listItems[0]+","+listItems[1]+")"
	currString = logicalOP+"("+listItems[0]+","+combineItems(listItems[1:], logicalOP)+")"
	return currString


def convertToCUDD(conditions):
	stack = deque()
	for i in range(len(conditions)):
		if conditions[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.
			stack.append(combineItems(listItems, logicalOP))

		elif conditions[i:i+4] == "And(":
			stack.append("And")
			i+=4
		elif conditions[i:i+3] == "Or(":
			stack.append("Or")
			i+=3
		elif conditions[i] == 'x': #Todo: Make general
			stack.append(conditions[i:i+7])
			i += 6
	final = stack.pop()
	print(final)

# print(combineItems(["x1","x2", "x3", "x4"],"Or"))
convertToCUDD("And(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))), 1 == x3, x3 == 2)")
# convertToCUDD("And(Or(x1 == 1,x2 == 2),x3 == 3,x4 == 5)")

# 8K hours
# Ask for feedback from Anduo

