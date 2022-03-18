#include "util.h"
#include "cudd.h"
// #include "cuddInt.h"
#include <time.h>
#include <stdbool.h>


#define VAR_NAME_LENGTH 5

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

// DdManager *manager;
// DdNode *f, *var, *tmp;
// int i;

// f = Cudd_ReadOne(manager);
// Cudd_Ref(f);
// for (i = 3; i >= 0; i--) {
//     var = Cudd_bddIthVar(manager,i);
//     tmp = Cudd_bddAnd(manager,Cudd_Cudd_Not(var),f);
//     Cudd_Ref(tmp);
//     Cudd_RecursiveDeref(gbm, manager,f);
//     f = tmp;
// }

// struct node { 
//     char* logicalOp; // The logical operator represented by the node. NULL if it a variable node
//     char* var; // The variable represented by the node. Must be a leaf
//     bool isNot; // is the node a not? 
//     struct node* left;
//     struct node* right;
// };
 
// // Create a new node in a linked list
// struct node* newNode(char* logicalOp, char* var, bool isNot)
// {
//     struct node* curr_node = (struct node*) malloc(sizeof(struct node));
//     curr_node->var = var;
//     curr_node->logicalOp = logicalOp;
//     curr_node->isNot = isNot;
//     curr_node->left = NULL;
//     curr_node->right = NULL;
//     return (curr_node);
// }

// struct node* convertToBinaryTree(char* condition, int length) {
//     for (int i = 0; i < length; i++) {
//         if 
//     }
// }

// // Is the current character a logical operator?
// bool isCharALogicalOp(struct node* curr_node) {
    
// }

// // Is the current node a logical operator?
// bool isNodeALogicalOp(struct node* curr_node) {
//     if (logicalOp == NULL){
//         assert(var != NULL); // assertion so that both var and logicalOp are not null at the same time
//         return false;
//     }
//     else {
//         assert(var == NULL); // assertion so that var is NULL when logicalOp is not
//         return true;
//     }
// }

// Gets the current variable referenced in the condition
char* getVar(char* condition, int* i) {
    char* var = malloc(sizeof(char)*VAR_NAME_LENGTH); // TODO: make it dynanmic. We are restricting work to be of 3 letters
    int j = 0;
    while (condition[*i] != '(' && condition[*i] != ',' && condition[*i] != ')'){
        assert(j < VAR_NAME_LENGTH);
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


int main (int argc, char *argv[])
{
    // char** strings = malloc(sizeof(char*)*4);
    // DdManager* gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);
    // strings[0] = "Hello";
    // strings[1] = "It's";
    // strings[2] = "Me";
    // strings[3] = "I was wondering";
    // initVars(4, strings, gbm);
    // printf("%d\n",stringToBDDIndex(strings, "Me", 4));

    clock_t start, end;
    double total_time;
    DdManager* gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    start = clock();
    char** variables = malloc(sizeof(char*)*30);
    variables[0] = "y1_0";
    variables[1] = "y2_0";
    variables[2] = "y3_0";
    variables[3] = "y4_0";
    variables[4] = "y5_0";
    variables[5] = "y6_0";
    variables[6] = "y7_0";
    variables[7] = "y8_0";
    variables[8] = "y9_0";
    variables[9] = "y10_0";

    variables[10] = "y1_1";
    variables[11] = "y2_1";
    variables[12] = "y3_1";
    variables[13] = "y4_1";
    variables[14] = "y5_1";
    variables[15] = "y6_1";
    variables[16] = "y7_1";
    variables[17] = "y8_1";
    variables[18] = "y9_1";
    variables[19] = "y10_1";

    variables[20] = "y1_2";
    variables[21] = "y2_2";
    variables[22] = "y3_2";
    variables[23] = "y4_2";
    variables[24] = "y5_2";
    variables[25] = "y6_2";
    variables[26] = "y7_2";
    variables[27] = "y8_2";
    variables[28] = "y9_2";
    variables[29] = "y10_2";
    // DdNode* bdd = convertToBDD(gbm, "^(x1_0,&(x2_0,x3_0))", 3, variables);
    // DdNode* bdd = convertToBDD(gbm,"^(^(^(~(x1_0),^(&(~(x1_0),~(x2_0)),^(&(~(x2_0),~(x3_0)),^(~(x2_0),~(x3_0))))),^(~(x3_0),^(~(x2_0),^(~(x1_0),^(&(~(x2_0),&(~(x3_0),~(x1_0))),^(~(x1_0),^(&(~(x1_0),~(x2_0)),^(&(~(x2_0),~(x1_0)),&(~(x3_0),~(x1_0)))))))))),^(~(x3_0),^(~(x2_0),~(x1_0))))", 3, variables);
    // free(variables);
    DdNode* bdd = MODIFY
    bdd = Cudd_BddToAdd(gbm, bdd); /*Convert BDD to ADD for display purpose*/
// Cudd_DebugCheck(gbm);
// cuddHeapProfile(gbm);
// Cudd_CheckKeys(gbm);
    int i;
        // i = 0;
    if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 1) {
        i = 0;
        printf("Tautology\n");
    }
    else if (Cudd_DagSize(bdd) == 1 && Cudd_CountLeaves(bdd) == 1 && Cudd_CountPathsToNonZero(bdd) == 0) {
        i = 1;
        printf("Contradiction\n");
    }
    else {
        i = 2;
        printf("Satisfiable\n");
    }
     end = clock();
     total_time = ((double) (end - start)) / CLOCKS_PER_SEC;
     printf("Total Time %f\n", total_time);
     if (i == 4)
         printf("CPU Time Used %f\n", total_time);
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
