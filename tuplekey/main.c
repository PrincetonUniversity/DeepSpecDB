#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"
#include "index.h"

int main(void) {
  /* Index i_str = index_new(&stringlist_schema); */
  /* Index i_int = index_new(&inthash_schema); */
  Schema intstr_schema = tuple_schema(&inthash_schema, &stringlist_schema);
  Index i_intstr = index_new(intstr_schema);

  Key k1 = (Key) 50;
  Key k2 = strdup("Hello");
  Key k12 = build_keypair(k1, k2);
  index_insert(intstr_schema, i_intstr, k12, (void*) 123);
  size_t v = (size_t) index_lookup(intstr_schema, i_intstr, k12);

  printf("Result: %zu\n", v);
  
  return 0;
}
