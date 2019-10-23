#include <stddef.h>
#include <stdlib.h>
#include "index.h"

Index index_new(Schema sch) {
  return sch->mtable->schema_new (sch->schema_private);
}

Value index_insert (Schema sch, Index ind, Key key, Value val) {
  return sch->mtable->schema_insert(sch->schema_private, ind, key, val);
}

Value index_lookup (Schema sch, Index ind, Key key) {
  return sch->mtable->schema_lookup(sch->schema_private, ind, key);
}

  

