#include "stdlib.h"
#include "stringlist.h"
#include "index.h"

Index stringlist_new_method(SchemaPrivate priv) {
  return stringlist_new();
}

Index stringlist_insert_method(SchemaPrivate priv,
			       Index ind, Key key, Value val) {
  return stringlist_insert(ind, key, val);
}

Index stringlist_lookup_method(SchemaPrivate priv,
			       Index ind, Key key) {
  return stringlist_lookup(ind, key);
}

struct schema_methods stringlist_mtable =
  { &stringlist_new_method,
    &stringlist_insert_method,
    &stringlist_lookup_method};

struct schema_t stringlist_schema = { &stringlist_mtable, NULL };

				     
