#include "util.h"
#include "cudd.h"

// DdManager *manager;
// DdNode *f, *var, *tmp;
// int i;

// f = Cudd_ReadOne(manager);
// Cudd_Ref(f);
// for (i = 3; i >= 0; i--) {
//     var = Cudd_bddIthVar(manager,i);
//     tmp = Cudd_bddAnd(manager,Cudd_Cudd_Not(var),f);
//     Cudd_Ref(tmp);
//     Cudd_RecursiveDeref(manager,f);
//     f = tmp;
// }

void print_dd (DdManager *gbm, DdNode *dd, int n, int pr )
{
    printf("DdManager nodes: %ld | ", Cudd_ReadNodeCount(gbm)); /*Reports the number of live nodes in BDDs and ADDs*/
    printf("DdManager vars: %d | ", Cudd_ReadSize(gbm) ); /*Returns the number of BDD variables in existence*/
    printf("DdManager reorderings: %d | ", Cudd_ReadReorderings(gbm) ); /*Returns the number of times reordering has occurred*/
    printf("DdManager memory: %ld \n", Cudd_ReadMemoryInUse(gbm) ); /*Returns the memory in use by the manager measured in bytes*/
    Cudd_PrintDebug(gbm, dd, n, pr);  // Prints to the standard output a DD and its statistics: number of nodes, number of leaves, number of minterms.
}

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

int main (int argc, char *argv[])
{
    char filename[30] = "graph2.dot";
    DdManager *gbm; /* Global BDD manager. */
    gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    DdNode *bdd;
    DdNode *x1_1, *x2_1, *x3_0, *x3_1;
    x1_1 = Cudd_bddNewVar(gbm);
    x2_1 = Cudd_bddNewVar(gbm);
    x3_0 = Cudd_bddNewVar(gbm);
    x3_1 = Cudd_bddNewVar(gbm);
    // bdd = Cudd_bddAnd(gbm, x1, x2); /*Perform AND Boolean operation*/
    // bdd = Cudd_bddAnd(gbm, x1, Cudd_Cudd_Not(x1)); /*Perform AND Boolean operation*/
    bdd = Cudd_bddAnd(gbm,Cudd_bddOr(gbm,Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x1_1,x2_1),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1))),Cudd_bddOr(gbm,x2_1,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1)))))),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1)),Cudd_bddOr(gbm,x2_1,Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1)),x1_1)),Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x1_1,x2_1),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,x1_1),Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1)),x1_1))))))))),Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Cudd_Not(x3_1)),Cudd_bddAnd(gbm,Cudd_Not(x3_0),x3_1)));
    Cudd_Ref(bdd);          /*Update the reference count for the node just created.*/
    bdd = Cudd_BddToAdd(gbm, bdd); /*Convert BDD to ADD for display purpose*/
    // print_dd (gbm, bdd, 2,4);   /*Print the dd to standard output*/
    // sprintf(filename, "./bdd/graph.dot"); /*Write .dot filename to a string*/
    write_dd(gbm, bdd, filename);  /*Write the resulting cascade dd to a file*/
    Cudd_Quit(gbm);
    return 0; 
}

// FILE *fptr = fopen("dumpfile.dot");
// Cudd_DumpDot(manager, 4, f, fptr);


// preProcess(string)->string
// pruneVariables(string)->string Take pass to look for any variable to variable assignment. If any encountered, then replace all instances of LHS variable with the RHS variable
// findDomain(string)->dictionary(variable->variables(values))Take pass to get distint variables and their domains
// replaceDomains(string, dictionary)->string Create a mapping from value to domain for each variable

// constructBdd(string)->DDNode*
// Then take aCudd_Nother recusrive pass to evaluate conditions from left to right. Whenever a logical operator is found, check for right and left hand sides and then call the recursive function
    // The base case is when there are either no left and right hand sides (e.g. And(x==1)) or it is an atomic constraint (e.g. x==1)
        // For either case, return te appropriate boolean variable

//And(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))), 1 == x3, x3 == 2)
