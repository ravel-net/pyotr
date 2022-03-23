CFLAGS = -I ~/cudd/cudd -I ~/cudd/util -I ~/cudd/
LFLAGS = -static -L ~/cudd/cudd/.libs/ -lcudd -lm

default: testprogram

testprogram: BDD_manager.o
	$(CC) BDD_manager.o -o BDD_manager $(LFLAGS)

test.o: BDD_manager.c
	$(CC) BDD_manager.c -c -o BDD_manager.o $(CFLAGS)