#include "util.h"
#include "cudd.h"
// #include "cuddInt.h"
#include <time.h>
#include <stdbool.h>


int varNameLength = 5;

void print_dd (DdManager *gbm, DdNode *dd, int n, int pr )
{
    printf("DdManager nodes: %ld | ", Cudd_ReadNodeCount(gbm)); /*Reports the number of live nodes in BDDs and ADDs*/
    printf("DdManager vars: %d | ", Cudd_ReadSize(gbm) ); /*Returns the number of BDD variables in existence*/
    printf("DdManager reorderings: %d | ", Cudd_ReadReorderings(gbm) ); /*Returns the number of times reordering has occurred*/
    printf("DdManager memory: %ld \n", Cudd_ReadMemoryInUse(gbm)); /*Returns the memory in use by the manager measured in bytes*/
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

// Gets the current variable referenced in the condition
char* getVar(char* condition, int* i) {
    char* var = malloc(sizeof(char)*varNameLength); // TODO: make it dynanmic. We are restricting work to be of 3 letters
    int j = 0;
    while (condition[*i] != '(' && condition[*i] != ',' && condition[*i] != ')'){
        assert(j < varNameLength);
        var[j] = condition[*i];
        j++;
        *i = *i +1;
    }
    var[j] = '\0';
    *i = *i+1; // skipping bracket/comma
    return var;

}

// Returns the bdd node corresponding to a given variable
int stringToBDDIndex(char** variables, char* var, int numVars) {
    for (int i = 0; i<numVars; i++) {
        if (strcmp(variables[i], var) == 0)
            return i;
    }
    assert(false); // should never reach this point since the variable encountered should be in the list of variables
}

bool isLogicalOp(char letter){
    return letter == '&' || letter == '^' || letter == '$';
}

DdNode* logicalOpBDD(char curr_char, DdManager* gbm, DdNode* bdd_left, DdNode* bdd_right) {
    if (curr_char == '&')
        return Cudd_bddAnd(gbm, bdd_left, bdd_right);
    else if (curr_char == '^')
        return Cudd_bddOr(gbm, bdd_left, bdd_right);    
    else if (curr_char == '$')
        return Cudd_bddXnor(gbm, bdd_left, bdd_right);
}

bool isLogicalNot(char curr_char) {
    return (curr_char == '~');
}

// Returns a BDD that is referencec
DdNode* convertToBDDRecursive(char* condition, int* i, DdManager* gbm, DdNode** variableNodes, char** variables, int numVars) {
    DdNode *bdd;
    char curr_char = condition[*i];
    int k = 0;
    if (isLogicalOp(curr_char)) {
        *i = *i + 2; // Skipping bracket
        DdNode* bdd_left = convertToBDDRecursive(condition, i, gbm, variableNodes, variables, numVars); // i passed as reference to remember where we are in encoding
        DdNode* bdd_right = convertToBDDRecursive(condition, i, gbm, variableNodes, variables, numVars); // i passed as reference to remember where we are in encoding
        bdd = logicalOpBDD(curr_char, gbm, bdd_left, bdd_right);
        Cudd_Ref(bdd);
        // Cudd_RecursiveDeref(gbm, bdd_left);
        // Cudd_RecursiveDeref(gbm, bdd_right);
    }
    else if (isLogicalNot(curr_char)) {
        *i = *i + 2; // Skipping bracket
        DdNode * tmp = convertToBDDRecursive(condition, i, gbm, variableNodes, variables, numVars);
        bdd = Cudd_Not(tmp);
        // Cudd_Ref(bdd);
        // Cudd_RecursiveDeref(gbm, tmp);

    }
    else if (curr_char == ',' || curr_char == '(' || curr_char == ')') {
        *i = *i + 1;
        bdd = convertToBDDRecursive(condition, i, gbm, variableNodes, variables, numVars); 
    }

    // must be a variables at this point
    else if (isalpha(curr_char)) {
        char* var = getVar(condition, i); // get variable name and adds to i
        int index = stringToBDDIndex(variables, var, numVars); // get index of variable in global copy of var to index mapping
        bdd = variableNodes[index];
        free(var);
    }
    return bdd;
}

DdNode** initVars(int numVars, char** variables, DdManager* gbm) {
    DdNode** variableNodes = malloc(sizeof(DdNode*)*numVars);
    for (int i = 0; i < numVars; i++) {
        variableNodes[i] = Cudd_bddNewVar(gbm);
        Cudd_Ref(variableNodes[i]);
    }
    return variableNodes;

}

// Variables given as space separated command line inputs
DdNode* convertToBDD(DdManager* gbm, char* condition, int numVars, char** variables) {
    DdNode** variableNodes = initVars(numVars, variables, gbm);
    int* i = malloc(sizeof(int));
    *i = 0;
    DdNode* bdd = convertToBDDRecursive(condition, i, gbm, variableNodes, variables, numVars);
    free(i); 
    return bdd;
} 

void evaluate(char** variables, char* condition, int numVars){
    clock_t start, end;
    double total_time;
    DdManager* gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    start = clock();
    DdNode* bdd = convertToBDD(gbm, condition, numVars, variables);
    // bdd = Cudd_BddToAdd(gbm, bdd); /*Convert BDD to ADD for display purpose*/
    // Cudd_DebugCheck(gbm);
    // cuddHeapProfile(gbm);
    // Cudd_CheckKeys(gbm);
    if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 1) {
        end = clock();
        total_time = ((double) (end - start)) / CLOCKS_PER_SEC;
        printf("Tautology\t%f\n", total_time);
    }
    else if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 0) {
        end = clock();
        total_time = ((double) (end - start)) / CLOCKS_PER_SEC;
        printf("Contradiction\t%f\n", total_time);
    }
    else {
        end = clock();
        total_time = ((double) (end - start)) / CLOCKS_PER_SEC;
        printf("Satisfiable\t%f\n", total_time);
    }
    Cudd_Quit(gbm);
    return;
}

int main (int argc, char *argv[])
{
    assert(argc == 2);

    int numVars, maxVarNameLength, conditionSize;
    int r;
    char* condition;
    char** variables;

    FILE *fp;
    fp = fopen(argv[1], "rt");
    if (fp == NULL) 
    { 
        printf("File does not exist"); 
        exit(1); 
    }
    printf("Case\t\tTotal Time\n");
    while ((r = fscanf(fp, "%d %d %d", &numVars, &maxVarNameLength, &conditionSize)) != EOF) {
        // printf("numVars: \t\t%d\n", numVars);
        // printf("maxVarNameLength: \t\t%d\n", maxVarNameLength);
        // printf("conditionSize: \t\t%d\n", conditionSize);
        varNameLength = maxVarNameLength+1;
        variables = malloc(sizeof(char*)*numVars);
        for (int i = 0; i < numVars; i++) {
            variables[i] = malloc(sizeof(char)*varNameLength);
            r = fscanf(fp, "%s", variables[i]);
            // printf("variable: \t\t%s\n", variables[i]);

        }
        condition = malloc(sizeof(char)*conditionSize+1);
        r = fscanf(fp, "%s", condition);
        // printf("condition: \t\t%s\n\n", condition);
        evaluate(variables, condition, numVars);
    }

    fclose(fp);
    free(condition);
    for (int i = 0; i < numVars; i++) {
        // printf("var %d: \t\t%s\n\n", i, condition);
        free(variables[i]);
    }
    free(variables);
    return 0;
}