#include "hs.h"

// Add a tvector to hs_list. Not doing header length checking for now
void add_tvector_to_hs (hs *self, tvector value) {
  add_to_vector(&self->hs_list, value);
}

// Add a headerspace to another headerspace. Not doing header length checking for now
void add_hs_to_hs (hs *self, hs *value) {
  // add to hs_list
  for (int i = 0; i < value->hs_list.num_elems; i++) 
    add_to_vector(&self->hs_list, value->hs_list.tvectors[i]);


  // add to hs_diff
  for (int i = 0; i < value->hs_diff.num_elems; i++)
    add_to_vector(&self->hs_diff, value->hs_diff.tvectors[i]);
}

// hs initialize_empty_hs() {
//   hs new_hs;
//   new_hs.hs_list = emptyTVectorArray();
//   new_hs.hs_diff = emptyTVectorArray();
// }

hs initialize_hs(char* hs_string) {
  hs new_hs;
  tvector tmp = hs_string_to_byte_array(hs_string);
  new_hs.hs_list = initialize_tvector_array(tmp);
  new_hs.hs_diff = emptyTVectorArray();
  return new_hs;
}

void test_hs_string_converstions() {
   tvector tmp = hs_string_to_byte_array("1xx01");
   printf("%ld\n", tmp.byte_array);
   char string[tmp.len+1];
   printf("%d\n", tmp.len);
   byte_array_to_hs_string(tmp,string);
   printf("%s\n", string);
}

void test_hs_size() {
   hs hs1 = initialize_hs("1xx01");
   hs hs2 = initialize_hs("1x01xx");
   add_hs_to_hs(&hs1, &hs2);
   int size = size_hs_string(hs1);
   printf("%d\n", size);
}

void test_hs_print() {
   hs hs1 = initialize_hs("1xx01");
   hs hs2 = initialize_hs("1x01xx");
   add_hs_to_hs(&hs1, &hs2);
   int size = size_hs_string(hs1);
   char string[size];

   to_string(hs1, string);
}

int main() {
   // test_hs_string_converstions();
   // test_hs_size();
   test_hs_print();
   return 0;
}