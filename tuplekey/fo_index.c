#include <stddef.h>
#include "stdlib.h"
#include "fo_index.h"
#include "inthash.h"
#include "stringlist.h"

Index index_new(Schema sch) {
  switch (sch[0]) {
  case desc_Int: return inthash_new();
  case desc_Str: return stringlist_new();
  }
  assert(0);
  return NULL;
}
  
Value index_insert (Schema sch, Index ind, Key key, Value val) {
  Index bindex;
  VectorKey vk = (VectorKey)key;
  switch (sch[0]) {
  case desc_End: return ind;

  case desc_Int:
    bindex = inthash_lookup(ind, (size_t)(vk[0]));
    if (!bindex) {
      bindex = index_new(sch+1);
      inthash_insert(ind, (size_t)(vk[0]), bindex);
    }
    return index_insert(sch+1, bindex, vk+1, val);

  case desc_Str:
    bindex = stringlist_lookup(ind, vk[0]);
    if (!bindex) {
      bindex = index_new(sch+1);
      stringlist_insert(ind, vk[0], bindex);
    }
    return index_insert(sch+1, bindex, vk+1, val);
    }
  return NULL; /* unreachable */
}

Value index_lookup (Schema sch, Index ind, Key key) {
  Index bindex;
  VectorKey vk = (VectorKey)key;
  switch (sch[0]) {
  case desc_End: return ind;

  case desc_Int:
    bindex = inthash_lookup(ind, (size_t)(vk[0]));
    if (!bindex) return NULL;
    return index_lookup(sch+1, bindex, vk+1);

  case desc_Str:
    bindex = stringlist_lookup(ind, vk[0]);
    if (!bindex) return NULL;
    return index_lookup(sch+1, bindex, vk+1);
  }
  return NULL; /* unreachable */
}



