CFLAGS = -I ~/cudd/cudd -I ~/cudd/util -I ~/cudd/
LFLAGS = -static -L ~/cudd/cudd/.libs/ -lcudd -lm

default: testprogram

testprogram: exampleManipulation.o
	$(CC) exampleManipulation.o -o exampleManipulation $(LFLAGS)

test.o: exampleManipulation.c
	$(CC) exampleManipulation.c -c -o exampleManipulation.o $(CFLAGS)