CFLAGS = -I ~/cudd/cudd -I ~/cudd/util -I ~/cudd/
LFLAGS = -static -L ~/cudd/cudd/.libs/ -lcudd -lm

default: testprogram

testprogram: output.o
	$(CC) output.o -o output $(LFLAGS)

test.o: output.c
	$(CC) output.c -c -o output.o $(CFLAGS)