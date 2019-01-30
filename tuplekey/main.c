#include <stddef.h>
#include "stdlib.h"
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"
#include "index.h"

int main(void) {
  Index i_str = index_new(&stringlist_schema);
  Index i_int = index_new(&inthash_schema);
  Schema intstr_schema = tuple_schema(&inthash_schema, &stringlist_schema);
  Index i_intstr = index_new(intstr_schema);

  return 0;
}
