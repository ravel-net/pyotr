#define PY_SSIZE_T_CLEAN
#include <Python.h>
   
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

void Cinitialize(int numberOfVariables, int domainCardinality) { 
    initializeBDD(&BDDs, INITIALSIZE);
    numVars = numBinaryVars(numberOfVariables, domainCardinality);
    gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    variableNodes = initVars(numVars, gbm);
    // gbm = Cudd_Init(numVars,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0); /* Initialize a new BDD manager. */
    // Cudd_AutodynEnable(gbm, CUDD_REORDER_SYMM_SIFT);
    // Cudd_ReduceHeap(gbm, CUDD_REORDER_SYMM_SIFT, 3000);
}
  
static PyObject* initialize(PyObject* self, PyObject* args)
{
    // instantiate our `n` value
    int numberOfVariables;
    int domainCardinality;
    // if our `n` value
    if(!PyArg_ParseTuple(args, "ii", &numberOfVariables, &domainCardinality))
        return NULL;

    Cinitialize(numberOfVariables, domainCardinality);
    return Py_None;
}
         
// Evaluate a BDD given by a reference. Returns 2 for satisfiable, 1 for tautology, and 0 for contradiction
int Cevaluate(int bdd_reference) {
    DdNode* bdd = getBDD(&BDDs, bdd_reference);
    return evaluateBDD(bdd);
}

/*Returns the memory in use by the manager measured in bytes*/
long CreadMemoryInUse() {
    long mem = Cudd_ReadMemoryInUse(gbm);
//printf("\n\n\n=====\n%ld\n=======\n\n", mem);
    return mem;   
}

static PyObject* readMemoryInUse(PyObject* self, PyObject* args){
    long mem = CreadMemoryInUse();
    return Py_BuildValue("l", mem);
}

static PyObject* evaluate(PyObject* self, PyObject* args)
{
    // instantiate our `n` value
    int bdd_reference;
    // if our `n` value
    if(!PyArg_ParseTuple(args, "i", &bdd_reference))
        return NULL;
    int result = Cevaluate(bdd_reference);
    return Py_BuildValue("i", result);
}

// Input: Encoded string condition
// Output: Index of the constructed BDD
int Cstr_to_BDD(char* C) {
    DdNode* bdd = convertToBDD(gbm, C, numVars, variableNodes);
    return insertBDD(&BDDs, bdd);
}

static PyObject* str_to_BDD(PyObject* self, PyObject* args)
{
    // instantiate our `n` value
    char* C;
    // if our `n` value
    if(!PyArg_ParseTuple(args, "s", &C))
        return NULL;
    
    return Py_BuildValue("i", Cstr_to_BDD(C));
}

bool Cis_implication(int bdd_reference1, int bdd_reference2) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_reference1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_reference2);
    DdNode* bdd_1_not = logicalNotBDD(bdd_1);
    DdNode* bdd_ans = logicalOpBDD('^', gbm, bdd_1_not, bdd_2);
    // TODO: Might be a good idea to see if bdd_ans and bdd_1_not can be derefrenced
    int answer = evaluateBDD(bdd_ans);
    return (answer == 1); // If answer is 1, that means it's a tautology
}    

static PyObject* is_implication(PyObject* self, PyObject* args)
{
    // instantiate our `n` value
    int bdd_reference1; 
    int bdd_reference2;
    
    // if our `n` value
    if(!PyArg_ParseTuple(args, "ii", &bdd_reference1, &bdd_reference2))
        return NULL;
    bool result = Cis_implication(bdd_reference1, bdd_reference2);
    if(result)
        return Py_BuildValue("i", 1);
    else
        return Py_BuildValue("i", 0);
}

// Input: Encoded string condition
// Output: Index of the constructed BDD
int Coperate_BDDs(int bdd_reference1, int bdd_reference2, char operation) {
    DdNode* bdd_1 = getBDD(&BDDs, bdd_reference1);
    DdNode* bdd_2 = getBDD(&BDDs, bdd_reference2);
    DdNode* bdd = logicalOpBDD(operation, gbm, bdd_1, bdd_2);
    return insertBDD(&BDDs, bdd);
}

static PyObject* operate_BDDs(PyObject* self, PyObject* args)
{
    // instantiate our `n` value
    int bdd_reference1; 
    int bdd_reference2;
    char *operation;
    
    // if our `n` value
    if(!PyArg_ParseTuple(args, "iis", &bdd_reference1, &bdd_reference2, &operation))
        return NULL;
    int result = Coperate_BDDs(bdd_reference1, bdd_reference2, *operation);
    return Py_BuildValue("i", result);
}

// Our Module's function Definition struct
static PyMethodDef BDD_Methods[] = {
    {"initialize", initialize, METH_VARARGS, "Initialize BDD array with the number of variables."},
    {"evaluate", evaluate, METH_VARARGS, "Evaluate a BDD given by a reference. Returns 2 for satisfiable, 1 for tautology, and 0 for contradiction"},
    {"str_to_BDD", str_to_BDD, METH_VARARGS, "Constrcut BDD for string condition."},
    {"operate_BDDs", operate_BDDs, METH_VARARGS, "Do logical operation between two BDDs."},
    {"readMemoryInUse", readMemoryInUse, METH_VARARGS, "Get memory of gbm"},
    {"is_implication", is_implication, METH_VARARGS, "Check if BDD1 implies BDD2."},
    {NULL, NULL, 0, NULL}
};

static struct PyModuleDef BDD_managerModule = {
    PyModuleDef_HEAD_INIT,
    "BDD_managerModule",
    "The Module for constructing BDDs.",
    -1,
    BDD_Methods
}; 

PyMODINIT_FUNC PyInit_BDD_managerModule(void){
    return PyModule_Create(&BDD_managerModule);
}

// int main (int argc, char *argv[])
// {
//     // evaluateFromFile(argc, argv);
//     initialize(3);
//     int taut = str_to_BDD("^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))");
//     int contr = str_to_BDD("&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))");
//     int sat = str_to_BDD("^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))");
//     int OR = operate_BDDs(taut, sat, '^');
//     int AND = operate_BDDs(contr, sat, '&');
//     // printf("%d\n", taut);
//     // printf("%d\n", contr);
//     // printf("%d\n", OR);
//     // printf("%d\n", AND);
//     // printf("%d\n", evaluate(taut));
//     // printf("%d\n", evaluate(contr));
//     printf("%d\n", evaluate(OR));
//     freeBDD(&BDDs);
// }
