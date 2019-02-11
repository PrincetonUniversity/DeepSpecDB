#ifndef FO_INDEX_INCLUDED
#define FO_INDEX_INCLUDED

enum descriptor {desc_End=0, desc_Int, desc_Str};

typedef enum descriptor *Schema;

typedef void *Index;
typedef void *Value;
typedef void *Key;

typedef Key *VectorKey;

Index index_new(Schema sch);
Value index_insert (Schema sch, Index ind, Key key, Value val);
Value index_lookup (Schema sch, Index ind, Key key);
#endif
