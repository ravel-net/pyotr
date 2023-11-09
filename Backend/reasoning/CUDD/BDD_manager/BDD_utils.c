
#include "util.h"
#include "cudd.h"

// #include "cuddInt.h"
#include <time.h>
#include <stdbool.h>
#include <math.h>
#include <unistd.h>
#include <sys/time.h>
#define MAX_DIGITS_FOR_VARS 5 // The number of digits required to store the variable indexes. This should be one more than the log base 10 of the number of variables

// Gets the current variable index referenced in the condition
int getVar(char* condition, int* i) {
    char* var = malloc(sizeof(char)*MAX_DIGITS_FOR_VARS); 
    int j = 0;
    while (condition[*i] != '(' && condition[*i] != ',' && condition[*i] != ')'){
        assert(j < MAX_DIGITS_FOR_VARS);
        var[j] = condition[*i];
        j++;
        *i = *i +1;
    }
    var[j] = '\0';
    *i = *i+1; // skipping bracket/comma
    int varIndex = atoi(var);
    free(var);
    return varIndex;
}

bool isLogicalOp(char letter){
    return letter == '&' || letter == '^' || letter == '$';
}

DdNode* logicalOpBDD(char curr_char, DdManager* gbm, DdNode* bdd_left, DdNode* bdd_right) {
    DdNode* tmp = NULL;
    if (curr_char == '&')
        tmp = Cudd_bddAnd(gbm, bdd_left, bdd_right);
    else if (curr_char == '^')
        tmp = Cudd_bddOr(gbm, bdd_left, bdd_right);    
    else if (curr_char == '$')
        tmp = Cudd_bddXnor(gbm, bdd_left, bdd_right);
    else
        assert(false);
    Cudd_Ref(tmp);
    return tmp;
}

DdNode* logicalNotBDD(DdNode* bdd) {
    DdNode* bdd_not = Cudd_Not(bdd);
    Cudd_Ref(bdd_not);
    return bdd_not;
}

bool isLogicalNot(char curr_char) {
    return (curr_char == '~');
}

// Returns a BDD from a string condition
DdNode* convertToBDDRecursive(char* condition, int* i, DdManager* gbm, DdNode** variableNodes, int numVars) {
    DdNode *bdd;
    char curr_char = condition[*i];

    if (isLogicalOp(curr_char)) {
        int j = *i;
        *i = *i + 2; // Skipping bracket
        DdNode* bdd_left = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars); // i passed as reference to remember where we are in encoding
        DdNode* bdd_right = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars); // i passed as reference to remember where we are in encoding

        // clock_t t;
        // t = clock();
        bdd = logicalOpBDD(curr_char, gbm, bdd_left, bdd_right);
        Cudd_RecursiveDeref(gbm,bdd_right);
        Cudd_RecursiveDeref(gbm,bdd_left);
        // t = clock() - t;
        // double time_taken = ((double)t)/CLOCKS_PER_SEC; // in seconds
    }
    else if (isLogicalNot(curr_char)) {
        *i = *i + 2; // Skipping bracket
        DdNode * tmp = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars);
        bdd = Cudd_Not(tmp);
        Cudd_Ref(bdd);
        Cudd_RecursiveDeref(gbm,tmp);
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
        else {
            bdd = variableNodes[index-2];
            if (bdd == NULL) {
                bdd = Cudd_bddNewVar(gbm);
                variableNodes[index-2] = bdd;
            }
            Cudd_Ref(bdd);
        }
    }
    else {
        assert(false);
        bdd = NULL;
    }
    return bdd;
}

DdNode** initVars(unsigned int numVars, DdManager* gbm) {
    DdNode** variableNodes = malloc(sizeof(DdNode*)*numVars);
    for (unsigned int i = 0; i < numVars; i++) {
        variableNodes[i] = NULL; // we initialize variables as we encounter them
        // variableNodes[i] = Cudd_bddNewVar(gbm);
        // Cudd_Ref(variableNodes[i]);
    }
    return variableNodes;
}

DdNode* convertToBDD(DdManager* gbm, char* condition, unsigned int numVars, DdNode** variableNodes) {
    int* i = malloc(sizeof(int));
    *i = 0;
    DdNode* bdd = convertToBDDRecursive(condition, i, gbm, variableNodes, numVars);
    free(i); 
    return bdd;
} 

int evaluateBDD(DdNode* bdd) {
    if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 1) {
        return 1; // tautology
    }
    else if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 0) {
        return 0; // contradiction
    }
    else {
        return 2; // satisfiable
    }
}

// d is the same as c but all ones
// TODO: Have more descriptive names
DdNode* transform_to_BDD(DdManager* gbm, DdNode* f, DdNode* c, DdNode* d) {
    DdNode* tmp = Cudd_bddExistAbstract(gbm, f, d);
    DdNode* transformed = Cudd_bddAnd(gbm, tmp, c);
    Cudd_Ref(transformed);
    Cudd_RecursiveDeref(gbm, tmp);
    return transformed;
}
 
int evaluateString(char* condition, unsigned int numVars, long* mem){
    // clock_t start, end;
    // double total_time;
    DdManager* gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    DdNode** variableNodes = initVars(numVars, gbm);
    // start = clock();
    DdNode* bdd = convertToBDD(gbm, condition, numVars, variableNodes);
    int result = evaluateBDD(bdd);
    // end = clock();
    // total_time = ((double) (end - start)) / CLOCKS_PER_SEC;
    // printf("Total Time: %f\n", total_time);
    // printf("Result: %d %ld", result);
    *mem = Cudd_ReadMemoryInUse(gbm);
    Cudd_Quit(gbm);
    return result;
}

int numBinaryVars(unsigned int numberOfVariables, unsigned int domainCardinality) {
    double log_base_2_domain = log(domainCardinality)/log(2); // log base 2 of the number of elements in the domain
    int binaryVarPerVar = (int) ceil(log_base_2_domain); // number of binary variables per a single variable in decimal. TODO: Need to have separate domain for every variable
    return binaryVarPerVar*numberOfVariables;
}

int evaluateFromFile (int argc, char *argv[])
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
    printf("Case\t\tTotal Time (ms)\tMemory (mb)\n");
    while ((r = fscanf(fp, "%d %d", &numVars, &conditionSize)) != EOF) {
        condition = malloc(sizeof(char)*conditionSize+1);
        r = fscanf(fp, "%s", condition);
        long* mem = malloc(sizeof(long));
        
        // measuring time
        long start, end;
        struct timeval timecheck;
        gettimeofday(&timecheck, NULL);
        start = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

        int result = evaluateString(condition, numVars, mem);

        gettimeofday(&timecheck, NULL);
        end = (long)timecheck.tv_sec * 1000 + (long)timecheck.tv_usec / 1000;

        printf("%d\t\t%ld\t\t%ld\n", result, (end - start), (*mem)/1048576);
        free(mem);
    }

    fclose(fp);
    free(condition);
    return 0;
}