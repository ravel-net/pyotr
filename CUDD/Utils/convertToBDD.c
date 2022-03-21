#include "util.h"
#include "cudd.h"
// #include "cuddInt.h"
#include <time.h>
#include <stdbool.h>

int numDigits = 3;

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
int getVar(char* condition, int* i) {
    char* var = malloc(sizeof(char)*numDigits); // TODO: make it dynanmic. We are restricting work to be of 3 letters
    int j = 0;
    while (condition[*i] != '(' && condition[*i] != ',' && condition[*i] != ')'){
        assert(j < numDigits);
        var[j] = condition[*i];
        j++;
        *i = *i +1;
    }
    var[j] = '\0';
    *i = *i+1; // skipping bracket/comma
    return atoi(var);

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
DdNode* convertToBDDRecursive(char* condition, int* i, DdManager* gbm, DdNode** variableNodes, int numVars) {
    DdNode *bdd;
    char curr_char = condition[*i];
    int k = 0;
    if (isLogicalOp(curr_char)) {
        *i = *i + 2; // Skipping bracket
        DdNode* bdd_left = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars); // i passed as reference to remember where we are in encoding
        DdNode* bdd_right = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars); // i passed as reference to remember where we are in encoding
        bdd = logicalOpBDD(curr_char, gbm, bdd_left, bdd_right);
        Cudd_Ref(bdd);
        // Cudd_RecursiveDeref(gbm, bdd_left);
        // Cudd_RecursiveDeref(gbm, bdd_right);
    }
    else if (isLogicalNot(curr_char)) {
        *i = *i + 2; // Skipping bracket
        DdNode * tmp = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars);
        bdd = Cudd_Not(tmp);
        // Cudd_Ref(bdd);
        // Cudd_RecursiveDeref(gbm, tmp);

    }
    else if (curr_char == ',' || curr_char == '(' || curr_char == ')') {
        *i = *i + 1;
        bdd = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars); 
    }

    // must be a variables at this point
    else if (isdigit(curr_char)) {
        int index = getVar(condition,i);
        if (index == 1) {
            bdd = Cudd_ReadOne(gbm);
            Cudd_Ref(bdd);
        }
        else if (index == 0) {
            bdd = Cudd_Not(Cudd_ReadOne(gbm));
            Cudd_Ref(bdd);
        }
        else
            bdd = variableNodes[index-2];
    }
    return bdd;
}

DdNode** initVars(int numVars, DdManager* gbm) {
    DdNode** variableNodes = malloc(sizeof(DdNode*)*numVars);
    for (int i = 0; i < numVars; i++) {
        variableNodes[i] = Cudd_bddNewVar(gbm);
        Cudd_Ref(variableNodes[i]);
    }
    return variableNodes;

}

DdNode* convertToBDD(DdManager* gbm, char* condition, int numVars) {
    DdNode** variableNodes = initVars(numVars, gbm);
    int* i = malloc(sizeof(int));
    *i = 0;
    DdNode* bdd = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars);
    free(i); 
    return bdd;
} 

void evaluate(char* condition, int numVars){
    clock_t start, end;
    double total_time;
    DdManager* gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    start = clock();
    DdNode* bdd = convertToBDD(gbm, condition, numVars);

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

    int numVars, conditionSize;
    int r;
    char* condition;

    FILE *fp;
    fp = fopen(argv[1], "rt");
    if (fp == NULL) 
    { 
        printf("File does not exist"); 
        exit(1); 
    }
    printf("Case\t\tTotal Time\n");
    while ((r = fscanf(fp, "%d %d", &numVars, &conditionSize)) != EOF) {
        condition = malloc(sizeof(char)*conditionSize+1);
        r = fscanf(fp, "%s", condition);
        // printf("condition: \t\t%s\n\n", condition);
        evaluate(condition, numVars);
    }

    fclose(fp);
    free(condition);
    return 0;
}