# Instruction 

## Compilation and linkage

- Compile and install CUDD (https://github.com/ivmai/cudd) with option `./configure --enable-shared`
    ```bash
    ./configure --enable-shared
    make
    make check
    ```
    Note: If CUDD gives  `'aclocal-1.14' is missing on your system` error when running `make`, then run `autoreconf` and again `./configure`.



- run following commands to compile and link it with Python system. 
    ```bash
    python setup.py build
    python setup.py install
    ```

    Notes: 
    1. Installation of library might require sudo privileges (e.g. sudo python setup.py install)
    2. if system cannot find 'Python.h', install python-dev which includes header `"Python.h"`
        ```bash
        sudo apt-get install python-dev
        ```
    3. If system cannot find related CUDD headers, export path of CUDD headers to `CPATH`.
        ```bash
        export CPATH=/path/to/cudd/:/path/to/cudd/cudd/:/path/to/cudd/util
        ```
    4.  If system cannot find cudd library, copy `libcudd.so`, `libcudd-3.0.0.so.0` and `libcudd-3.0.0.so.0.0.0` to `/usr/lib/x86_64-linux-gnu/`. In some processors, you might need to copy to `/usr/local/lib` instead. In addition, add `extra_link_args=['-L/usr/lib/x86_64-linux-gnu/']` to `setup.py`.

        ```bash
        cp path/to/cudd/cudd/.libs/libcudd.so /usr/lib/x86_64-linux-gnu/
        cp path/to/cudd/cudd/.libs/libcudd-3.0.0.so.0 /usr/lib/x86_64-linux-gnu/
        cp path/to/cudd/cudd/.libs/libcudd-3.0.0.so.0.0.0 /usr/lib/x86_64-linux-gnu/
        ```
        **setup.py**
        ```python
        from distutils.core import setup, Extension

        PATH = 'path/to/cudd'

        MODULE = Extension(
            'BDD_managerModule', 
            include_dirs = [PATH+'/cudd', PATH+'/util', PATH+'/'],
            libraries = ['cudd', 'm'],
            library_dirs = [PATH+'/cudd/.libs/'],
            extra_link_args=['-L/usr/lib/x86_64-linux-gnu/'], # add this line
            sources = ['BDD_manager.c']
        )

        setup(
            name = 'BDD_managerModule',
            version='1.0',
            ext_modules=[MODULE]
        )
        ```

# CUDD

The files in this folder implement BDDs for use in the Pyotr system. The main file that implements API calls for BDDs in Pyotr is ***BDD_manager***, which depends on *BDD_util* and *BDD_array*. *encodeCUDD.py* converts conditions from Z3 format (as encoded in earlier Pyotr versions) to a format that CUDD understands. 

## Compilation
1. **Install CUDD**. CUDD needs to be installed in order to use this code. Instructions to install CUDD can be found [here](https://github.com/ivmai/cudd). The simplest installation should be enough to use *BDD_manager*.

2. **Run *make***. This compiles *BDD_manager*, which in turn uses *BDD_util *and *BDD_array*. The executable is called *BDD_manager*.


## Code Description

### BDD_manager.c:
---
The *BDD_manager* stores BDDs in a data structure and provides API calls to add and evaluate BDDs in that structure. *BDD_manager* currently uses the dynamic array structure defined in *BDD_array* as the data structure to store BDD state but it can use any data structure as long as the data structure provides a few function calls (described in BDD_array description). *BDD_manager* provides the following API calls for use in Pyotr:

1. **void initialize(int numberOfBDDVariables):** This initializes a data structure that stores the BDDs. Calling this function is necessary before using any other functions. The parameter numberOfBDDVariables is the number of variables in the BDD program. This is the length of the second return value of the *convertToCUDD* functions (see below in *encodeCUDD.py*) For IP addresses, the number of BDD variables is numOfActualVariables\*32
2. **int str_to_BDD(char\* C):** This function takes an encoded condition, converts it to a BDD, stores the BDD in an internal data structure, and returns a reference number (an integer) for that BDD. The reference number can then be used to access the corresponding BDD. The input string *C* must be encoded by calling function *convertToCUDD* defined in *encodeCUDD.py*. *str_to_BDD* uses the function *convertToBDD* defined in *BDD_utils* to convert the encoded string to a BDD. 
3. **int operate_BDDs(int bdd_reference1, int bdd_reference2, char operation)**: Performs a logical operation between a BDD referenced by *bdd_reference1* and a BDD referenced by *bdd_reference2*. Note that the operation could be either ***'&'*** (logical AND) or ***'^'*** (logical OR). 
4. **int evaluate(int bdd_reference)**: Evaluates the BDD referenced by bdd_reference. Returns either 0 (denotes Contradiction), 1 (denotes Tautology), or 2 (denotes Satisfiable).
5. **bool is_implcation(int bdd_reference1, int bdd_reference2)**: Checks if the condition associated with bdd_reference1 implies the condition associated with bdd_reference2. Returns true if an implication exists

### BDD_array.c:
---
This provides the data structure to store BDDs and return BDDs by reference numbers. *initializeBDD* initializes the BDD data structure (dynamic array in this case), *insertBDD* adds a new BDD to the array and returns a reference number (i.e. index in dynamic array) for the added BDD, *getBDD* returns a BDD referenced by a given reference number. A new data structure can be added instead of an array by providing the aforementioned functions.

### BDD_utils.c:
---
Provides code to construct a BDD given by an encoded string (*convertToBDD*), evaluate a BDD (*evaluateBDD*), and evaluate and time a list of encoded conditions from a file (*evaluateFromFile*).

### encodeCUDD.py:
---
Provides function ***convertToCUDD(condition, domain, variables, is_ip)*** which takes a *condition* (in Z3 string format), the *domain* of variables in that condition, the variables (as a list of strings), and whether or not the domain is an ip address as input and returns an encoded condition that can be understood by the function *convertToBDD* defined in *BDD_utils*. The *domain* is a dictionary keyed by a variable, and the value is the corresponding domain of the variable. If the domain for a particular variable is the entire integer set, do not include the entry for the variable in the dictionary *domain* (e.g. *domain* should not have the key for that variable). This conversion is important to encode conditions into binary variables. We use binary encoding here. Only IPv4 addresses are currently supported, so the domain argument is not needed when *is_ip* is *True*

#### Binary Encoding
If the domain of a variable *x* is [20,40,50,60,70] then *x = 50* can be encoded as the binary representation of two (since 50 is the second element in the domain). Thus, *x* can be encoded as 010 in binary, or more specifically, using three separate variables, *And(not(x_1), x_2, not(x_3))*. 
For IP Address, the binary representation of the IP is stored. For example, y = 3.0.0.0/8 is stored as the binary '00000011 xxxxxxxx xxxxxxxx xxxxxxxx', where x is a ternary bit. This translates to condition -> And(not(x_1),not(x_2),not(x_3),not(x_4),not(x_5), not(x_6), x_7, x_8).

#### Domain Size Issue
Note that this encoding only works if the cardinality of the domain is a power of two. If that is not the case for a domain, we extend the domain by defining multiple assignments to a particular element in the domain. Not doing so is incorrect and results in errors that are often hard to detect. For example, we convert the domain [20,40,50,60,70] into [20,40,50,60,70,20,20,20] to increase the length of the domain from 5 to 8 (a power of 2). In this example, a constraint like *x = 20* is represented by a logical OR of the binary representation of 0, 5, 6, and 7 (which are the indexes of the element 20 in the domain) i.e. (*x = 20* -> *Or(000, 101, 110, 111)* -> *Or(And(not(x_1), not(x_2), not(x_3)), And(x_1, not(x_2), x_3), And(x_1, x_2, not(x_3)), And(x_1, x_2, x_3))*

#### Z3 to Encoded String Map
We use single characters to denote logical operations in the encoded string. This is done to make parsing in CUDD simpler. The mapping is given below, where the operation in Z3 condition is on the left and the corresponding char in the encoded string is on the right:

1. And: & 
2. Or: ^
3. Not: ~
4. Xnor: %

Similarly, variables are encoded using numbers instead of strings to make parsing faster. If there are *n* number of variables then the variables are encoded using digits 2 to (n+1). For example, if a condition has four variables *[x1, x2, x3, x4]* then they will be encoded as *[2,3,4,5]*. Note that number 0 is reserved for constant value of False and 1 is reserved for the constant value of True. For example, a condition like *2 == 2* will be encoded as *1* (always true) and a condition like *2 == 1* will be encoded as *0* (always false). 

## Testing BDD Implementation
_runExperiment.sh_ can be used to test and time the implementation of BDDs. Before running _runExperiment.sh_, make sure to call evaluateFromFile(argc, argv) at the start of main in BDD_manager. _runExperiment.sh_ takes one argument, a path to a file containing a list of conditions (in z3 string format), as input and then encodes the conditions, constructs BDDs, and returns the result of evaluating the conditions along with the time taken. This script can be useful to debug the CUDD implementation







