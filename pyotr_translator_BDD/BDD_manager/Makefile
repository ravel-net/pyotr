CUDD_PATH = cudd
CFLAGS = -I ~/$(CUDD_PATH)/cudd -I ~/$(CUDD_PATH)/util/util -I ~/$(CUDD_PATH)/
LFLAGS = -L ~/$(CUDD_PATH)/cudd/.libs/ -lcudd -lm

default: libBDD_manager

# testprogram: BDD_manager.o
# 	$(CC) BDD_manager.o -o BDD_manager $(LFLAGS)

libBDD_manager: BDD_manager.o
	$(CC) BDD_manager.o -shared -o libBDD_manager.so $(LFLAGS)

test.o: BDD_manager.c
	$(CC) -c -fPIC BDD_manager.c -o BDD_manager.o $(CFLAGS) 
