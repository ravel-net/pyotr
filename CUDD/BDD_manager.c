#include "BDD_utils.c"
#include "BDD_array.c"

#define INITIALSIZE 16 // Initial Size of the array

// Global variables for state management
BDD_array BDDs; // Data structure to store BDDs
DdManager* gbm; // 
DdNode** variableNodes; // stores variables
int numVars; // Number of variables in program


void write_dd (DdManager *gbm, DdNode *dd, char* filename)
{
    FILE *outfile; // output file pointer for .dot file
    outfile = fopen(filename,"w");
    DdNode **ddnodearray = (DdNode**)malloc(sizeof(DdNode*)); // initialize the function array
    ddnodearray[0] = dd;
    Cudd_DumpDot(gbm, 1, ddnodearray, NULL, NULL, outfile); // dump the function to .dot file
    free(ddnodearray);
    fclose (outfile); // close the file */
}

void initialize(int numberOfVariables, int domainCardinality) { 
  initializeBDD(&BDDs, INITIALSIZE);
  numVars = numBinaryVars(numberOfVariables, domainCardinality);
  gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
  variableNodes = initVars(numVars, gbm);
  // gbm = Cudd_Init(numVars,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
  // Cudd_AutodynEnable(gbm, CUDD_REORDER_SYMM_SIFT);
  // Cudd_ReduceHeap(gbm, CUDD_REORDER_SYMM_SIFT, 3000);
}

// Evaluate a BDD given by a reference. Returns 2 for satisfiable, 1 for tautology, and 0 for contradiction
int evaluate(int bdd_reference) {
    DdNode* bdd = getBDD(&BDDs, bdd_reference);
    return evaluateBDD(bdd);
}
 
// Input: Encoded string condition
// Output: Index of the constructed BDD
int str_to_BDD(char* C) {
    DdNode* bdd = convertToBDD(gbm, C, numVars, variableNodes);
    return insertBDD(&BDDs, bdd);
}

int operate_BDDs(int bdd_reference1, int bdd_reference2, char operation) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_reference1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_reference2);
    DdNode* bdd = logicalOpBDD(operation, gbm, bdd_1, bdd_2);
    return insertBDD(&BDDs, bdd);
}   

bool is_implcation(int bdd_reference1, int bdd_reference2) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_reference1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_reference2);
    DdNode* bdd_1_not = logicalNotBDD(bdd_1);
    DdNode* bdd_ans = logicalOpBDD('^', gbm, bdd_1_not, bdd_2);
    // TODO: Might be a good idea to see if bdd_ans and bdd_1_not can be derefrenced
    int answer = evaluateBDD(bdd_ans);
    return (answer == 1); // If answer is 1, that means it's a tautology
}    

/*Returns the memory in use by the manager measured in bytes*/
long readMemoryInUse() {
    return Cudd_ReadMemoryInUse(gbm);   
}

/*Frees the memory of a given BDD*/
void freeBDD(int bdd_reference) {
    DdNode* bdd = getBDD(&BDDs, bdd_reference);
    Cudd_RecursiveDeref(gbm,bdd);
    // free(bdd);
}    
 
int main (int argc, char *argv[])  
{
    // evaluateFromFile(argc, argv);  
    initialize(2,2);
    // int OR = str_to_BDD("^(~(^(&(~(3),~(2)),&(~(3),2))),&(~(3),~(3)))");
    int p = str_to_BDD("^(&(~(3),~(2)),&(~(3),2))");
    int q = str_to_BDD("&(~(3),~(3))");
    bool OR = is_implcation(p, q);
    printf("%d\n", OR);

    // int q = str_to_BDD("&(~(2),~(2))");
    // bool imp = is_implcation(p,q);
    // printf("%d\n", imp);
    
    // initialize(4, 4);
    // int fangpingCondition = str_to_BDD("&((1),&(&(~(2),3),&(~(6),7)))"); 
    // int taut = str_to_BDD("^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))");
    // int contr = str_to_BDD("&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))");
    // int sat = str_to_BDD("^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))");
    // int OR = operate_BDDs(taut, sat, '^');
    // int AND = operate_BDDs(contr, sat, '&');
    // // printf("%d\n", taut);
    // // printf("%d\n", contr);
    // // printf("%d\n", OR);
    // // printf("%d\n", AND);
    // // printf("%d\n", evaluate(taut));
    // // printf("%d\n", evaluate(contr));
    // freeBDD(taut);
    // printf("%d\n", evaluate(fangpingCondition));
    // printf("DdManager memory: %ld bytes \n", readMemoryInUse() );
    // freeBDDArray(&BDDs);
} 
