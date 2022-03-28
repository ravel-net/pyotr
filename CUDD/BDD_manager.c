#include "BDD_utils.c"
#include "BDD_array.c"

#define INITIALSIZE 16 // Initial Size of the array

// Global variables for state management
BDD_array BDDs; // Data structure to store BDDs
DdManager* gbm; // 
int numVars; // Number of variables in program

 
void initialize(int numberOfVariables, int domainCardinality) { 
  initializeBDD(&BDDs, INITIALSIZE);
  gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
  numVars = numBinaryVars(numberOfVariables, domainCardinality);
}

// Evaluate a BDD given by a reference. Returns 2 for satisfiable, 1 for tautology, and 0 for contradiction
int evaluate(int bdd_reference) {
    DdNode* bdd = getBDD(&BDDs, bdd_reference);
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
int operate_BDDs(int bdd_reference1, int bdd_reference2, char operation) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_reference1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_reference2);
    DdNode* bdd = logicalOpBDD(operation, gbm, bdd_1, bdd_2);
    return insertBDD(&BDDs, bdd);
}

/*Returns the memory in use by the manager measured in bytes*/
long readMemoryInUse() {
    return Cudd_ReadMemoryInUse(gbm);  
}

int main (int argc, char *argv[]) 
{
    // evaluateFromFile(argc, argv);
    initialize(4, 4);
    int fangpingCondition = str_to_BDD("&((1),&(&(~(2),3),&(~(6),7)))"); 
    int taut = str_to_BDD("^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))");
    int contr = str_to_BDD("&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))");
    int sat = str_to_BDD("^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))");
    int OR = operate_BDDs(taut, sat, '^');
    int AND = operate_BDDs(contr, sat, '&');
    // printf("%d\n", taut);
    // printf("%d\n", contr);
    // printf("%d\n", OR);
    // printf("%d\n", AND);
    // printf("%d\n", evaluate(taut));
    // printf("%d\n", evaluate(contr));

    printf("%d\n", evaluate(fangpingCondition));
    printf("DdManager memory: %ld bytes \n", readMemoryInUse() );
    freeBDD(&BDDs);
}