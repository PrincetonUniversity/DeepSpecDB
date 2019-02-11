#ifndef INDEX_INCLUDED
#define INDEX_INCLUDED

typedef struct schema_t *Schema;
typedef void *SchemaPrivate;
typedef void *Index;
typedef void *Value;
typedef void *Key;

struct schema_methods {
  Index (*schema_new)(SchemaPrivate priv);
  Value (*schema_insert)(SchemaPrivate priv, Index ind, Key key, Value val);
  Value (*schema_lookup)(SchemaPrivate priv, Index ind, Key key);
};

struct schema_t {
  struct schema_methods *mtable;
  SchemaPrivate schema_private;
};

Index index_new(Schema sch);
Value index_insert (Schema sch, Index ind, Key key, Value val);
Value index_lookup (Schema sch, Index ind, Key key);
#endif
