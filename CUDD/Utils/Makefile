CFLAGS = -I ~/cudd/cudd -I ~/cudd/util -I ~/cudd/
LFLAGS = -static -L ~/cudd/cudd/.libs/ -lcudd -lm

default: testprogram

testprogram: convertToBDD.o
	$(CC) convertToBDD.o -o convertToBDD $(LFLAGS)

test.o: convertToBDD.c
	$(CC) convertToBDD.c -c -o convertToBDD.o $(CFLAGS)