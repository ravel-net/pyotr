#include <stdbool.h>

typedef enum {
    BIT_z = 0x0,
    BIT_0 = 0x1,
    BIT_1 = 0x2,
    BIT_x = 0x3
} tbit;

// This will represent a single header in binary i.e. 1x1z0, 1xxx01 etc)
typedef struct TVector {
  long byte_array;
  int len; // Current allocated size
} tvector;

tvector emptyTVector() {
  tvector empty;
  empty.byte_array = 0;
  empty.len = 0;
  return (empty);
}

typedef struct TVector_Array {
  tvector* tvectors;
  int max_elems; // Current allocated size
  int num_elems;
} tvector_array;

tvector_array emptyTVectorArray() {
  tvector_array empty;
  empty.tvectors = NULL;
  empty.max_elems = 0;
  empty.num_elems = 0;
  return (empty);
}

bool full(tvector_array array) {
  return (array.max_elems == array.num_elems);
}

// Copy max_elems number of elements from tvectors_old to tvectors_new
void copy(tvector* tvectors_new, tvector* tvectors_old, int max_elems) {
  for (int i = 0; i < max_elems; i++)
    tvectors_new[i] = tvectors_old[i];
}


// FIXME: Resize is not working correctly
void resize(tvector_array array) {
  tvector* tvectors_new = malloc(sizeof(tvector)*array.max_elems*2); // double the size
  copy(tvectors_new, array.tvectors, array.max_elems);
  free(array.tvectors);
  array.max_elems *= 2;
  array.tvectors = tvectors_new;
}

void add_to_vector(tvector_array* array, tvector value) {
  if (full(*array))
    resize(*array);
  array->tvectors[array->num_elems] = value;
  array->num_elems++;
}

tvector_array initialize_tvector_array(tvector new_tvec) {
  tvector_array tmp;
  tmp.tvectors = malloc(sizeof(tvector)*2);
  tmp.max_elems = 2;
  tmp.tvectors[0] = new_tvec;
  tmp.num_elems = 1;
  return tmp;
}

// Assumes that the caller has assigned in its stack a char[] of size tvec.len
void byte_array_to_hs_string(tvector tvec, char* string) {
    int len = tvec.len;
    string[0] = '\0'; // TODO: Treating this as error state
    if (len <= 0)
      return; // TODO: Add excetion
    for (int i = 0; i < len; i++) {
      short byte = tvec.byte_array >> (2*i) & 0x03; // get the last two bytes
        if (byte == BIT_x)
            string[len-i-1] = 'x';
        else if (byte == BIT_1)
          string[len-i-1] = '1';
        else if (byte == BIT_0)
          string[len-i-1] = '0';
        else if (byte == BIT_z)
          string[len-i-1] = 'z';
        else {
        printf("ERROR: Unrecognized string given\n");
          return; // TODO: Add exception
        }
    }
    string[len] = '\0';
    return;
}

int size_tvector_arr_string(tvector_array tvector_arr_to_print) {
    int size = 0;
    for (int i = 0; i < tvector_arr_to_print.num_elems; i++) { // for each tvector in tvector array
      size += tvector_arr_to_print.tvectors[i].len;
    }
    size += 1; // 1 for null
    size += tvector_arr_to_print.num_elems - 1; // for union sign
    return size;
}

tvector hs_string_to_byte_array(char* hs_string) {
  int len = strlen(hs_string);
    if (!hs_string || len == 0) {
      printf("ERROR: Empty or null string given\n");
        return (emptyTVector()); // TODO: Add exception
    }

    int elems = 0;
    long br = 0;
    for (int i = 0; i < len; i++) {
      br = br << 2;
      elems++;
        if (hs_string[i] == 'X' || hs_string[i] == 'x')
            br += BIT_x;
        else if (hs_string[i] == '1')
            br += BIT_1;
        else if (hs_string[i] == '0')
            br += BIT_0;
        else if (hs_string[i] == 'Z' || hs_string[i] == 'z')
            br += BIT_z;
        else {
        printf("ERROR: Unrecognized string given\n");
          return (emptyTVector()); // TODO: Add exception
        }
    }
    tvector tvec_new;
    tvec_new.byte_array = br;
    tvec_new.len = elems;
    return tvec_new;
}


void tvector_array_to_string(tvector_array tvector_arr_to_print, char* string) {
  for (int i = 0; i < tvector_arr_to_print.num_elems; i++) { // for each tvector in tvector array
    tvector curr = tvector_arr_to_print.tvectors[i];
    int len = curr.len;
    char tvec_string[len + 1];
    byte_array_to_hs_string(curr, tvec_string);
    if (i != 0)
      strcat(string,"U");
    strcat(string,tvec_string);
  }
}
