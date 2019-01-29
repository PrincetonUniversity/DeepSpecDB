#include "stdlib.h"
#include "inthash.h"
#include "index.h"

Index inthash_new_method(SchemaPrivate priv) {
  return inthash_new();
}

Index inthash_insert_method(SchemaPrivate priv,
			       Index ind, Key key, Value val) {
  return (Index)inthash_insert(ind, (size_t)key, val);
}

Index inthash_lookup_method(SchemaPrivate priv,
			       Index ind, Key key) {
  return (Index)inthash_lookup(ind, (size_t)key);
}

struct schema_methods inthash_mtable =
  { &inthash_new_method,
    &inthash_insert_method,
    &inthash_lookup_method};

struct schema_t inthash_schema = { &inthash_mtable, NULL };
