#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tvector.c"

typedef struct HS {
   tvector_array hs_list;
   tvector_array hs_diff;
} hs;

int size_hs_string(hs hs_vector) {
    int size = 0;
    size += size_tvector_arr_string(hs_vector.hs_list);
    if (hs_vector.hs_diff.num_elems > 0)
	    size += size_tvector_arr_string(hs_vector.hs_diff) + 1;
	return size;
}

void to_string(hs hs_to_print, char* string) {
   int size = size_hs_string(hs_to_print);
   // FIX: This is ignoring hs_diff
   tvector_array_to_string(hs_to_print.hs_list, string);
   printf("%s\n", string);
}



void add_hs_to_hs (hs *self, hs *value);
void add_tvector_to_hs (hs *self, tvector value);
