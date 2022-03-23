#include "BDD_utils.c"
#include "BDD_array.c"

#define INITIALSIZE 16 // Initial Size of the array

// Global variables for state management
BDD_array BDDs; // Data structure to store BDDs
DdManager* gbm; // 
int numVars; // Number of variables in program


void initialize(int n) {
  initializeBDD(&BDDs, INITIALSIZE);
  gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
  numVars = n;
}

// Evaluate a BDD at a given index. Returns 0 for satisfiable, 1 for tautology, and 2 for contradiction
int evaluate(int bdd_index) {
    DdNode* bdd = getBDD(&BDDs, bdd_index);
    return evaluateBDD(bdd);
}

// Input: Encoded string condition
// Output: Index of the constructed BDD
int str_to_BDD(char* C) {
    DdNode* bdd = convertToBDD(gbm, C, numVars);
    return insertBDD(&BDDs, bdd);
}

// Input: Encoded string condition
// Output: Index of the constructed BDD
int operate_BDDs(int bdd_index1, int bdd_index2, char operation) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_index1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_index2);
    DdNode* bdd = logicalOpBDD(operation, gbm, bdd_1, bdd_2);
    return insertBDD(&BDDs, bdd);
}

int main (int argc, char *argv[])
{
    // evaluateFromFile(argc, argv);
    initialize(3);
    int taut = str_to_BDD("^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))");
    int contr = str_to_BDD("&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))");
    int sat = str_to_BDD("^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))");
    int OR = operate_BDDs(contr, sat, '^');
    int AND = operate_BDDs(contr, sat, '&');
    // printf("%d\n", taut);
    // printf("%d\n", contr);
    // printf("%d\n", OR);
    // printf("%d\n", AND);
    // printf("%d\n", evaluate(taut));
    // printf("%d\n", evaluate(contr));
    printf("%d\n", evaluate(AND));
    freeBDD(&BDDs);
}