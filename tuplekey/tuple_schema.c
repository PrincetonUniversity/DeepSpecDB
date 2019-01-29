#include "stdlib.h"
#include "index.h"
#include "tuple_schema.h"

struct keypair {
  Key a, b;
};

struct schemapair {
  Schema a,b;
};

Index tuple_new_method(struct schemapair *priv) {
  return index_new(priv->a);
}

Index tuple_insert_method(struct schemapair *priv,
			  Index ind, struct keypair *key, Value val) {
  Index bindex = index_lookup(priv->a, ind, key->a);
  if (!bindex) {
    bindex = index_new(priv->b);
    index_insert(priv->a, ind, key->a, bindex);
  }
  return index_insert(priv->b, bindex, key->b, val);
}

Index tuple_lookup_method(struct schemapair *priv, 
			       Index ind, struct keypair *key) {
  Index bindex = index_lookup(priv->a, ind, key->a);
  if (!bindex) return NULL;
  return index_lookup(priv->b, bindex, key->b);
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
