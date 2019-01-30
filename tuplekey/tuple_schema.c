#include <stddef.h>
#include "stdlib.h"
#include "index.h"
#include "tuple_schema.h"

struct keypair {
  Key a, b;
};

struct schemapair {
  Schema a,b;
};

Index tuple_new_method(SchemaPrivate priv) {
  struct schemapair *p = (struct schemapair *) priv;  
  return index_new(p->a);
}

Value tuple_insert_method(SchemaPrivate priv, Index ind, Key key, Value val) {
  struct schemapair *p = (struct schemapair *) priv;
  struct keypair *k = (struct keypair *)key;
  Index bindex = index_lookup(p->a, ind, k->a);
  if (!bindex) {
    bindex = index_new(p->b);
    index_insert(p->a, ind, k->a, bindex);
  }
  return index_insert(p->b, bindex, k->b, val);
}

Value tuple_lookup_method(SchemaPrivate priv, Index ind, Key key) {
  struct schemapair *p = (struct schemapair *) priv;  
  struct keypair *k = (struct keypair *)key;
  Index bindex = index_lookup(p->a, ind, k->a);
  if (!bindex) return NULL;
  return index_lookup(p->b, bindex, k->b);
}

struct schema_methods tuple_mtable =
  { &tuple_new_method,
    &tuple_insert_method,
    &tuple_lookup_method};

Schema tuple_schema(Schema a, Schema b) {
  struct schemapair *p;
  struct schema_t *sch;
  p = (struct schemapair *) malloc (sizeof (struct schemapair));
  p->a=a; p->b=b;

  sch = (struct schema_t *) malloc (sizeof (struct schema_t));
  sch->mtable= &tuple_mtable;
  sch->schema_private = p;
  return sch;
}
