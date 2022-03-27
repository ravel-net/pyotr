// Dynamic array management
typedef struct {
  DdNode** array;
  int used; // number of used entries
  int size; // current size of dynamic array
} BDD_array;

 
// Inserts a BDD in the dynamic array and returns the reference
int insertBDD(BDD_array* BDDs, DdNode* element) {
  if (BDDs->used == BDDs->size) {
    BDDs->size *= 2;
    BDDs->array = realloc(BDDs->array, BDDs->size * sizeof(DdNode*));
  }
  BDDs->array[BDDs->used++] = element;
  return BDDs->used-1; 
}

void freeBDD(BDD_array* BDDs) {
  free(BDDs->array);
  BDDs->array = NULL;
  BDDs->used = BDDs->size = 0;
}
//

void initializeBDD(BDD_array* BDDs, int initialSize) {
  BDDs->array = malloc(initialSize * sizeof(int));
  BDDs->used = 0;
  BDDs->size = initialSize;
}

// For reference to BDD mapping. Returns the BDD stored at the given reference
DdNode* getBDD(BDD_array* BDDs, int reference) {
    if (reference > BDDs->used) {
        printf("Error: Could not find a BDD with index %d\n", reference);
        return NULL;
    }
    return BDDs->array[reference];
}