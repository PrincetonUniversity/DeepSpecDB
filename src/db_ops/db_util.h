#ifndef _DBUTILH_
#define _DBUTILH_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "queue2.h"

#include "index.h" // in ../tuplekey/
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"

#include "inthash.h"
#include "stringlist.h"

// types of entries that can appear in the table
typedef enum domain { Int, Str } domain;

// list of "columns" in the table
typedef struct attribute_list_t {
  char* id;
  domain domain;
  struct attribute_list_t* next;
} *attribute_list;


//NEW - separated from the definition of "relation"
typedef struct index_attributes_t {
    attribute_list attrs;
    attribute_list pk_attrs; // has to be unique for now
} *index_attributes;

/*================ INDEX DEF ================ */

/* does not support efficient lookup */
struct UnordSetMtable {
  void* (*create) (void* env);
  void* (*insert) (void* env);
  size_t (*cardinality) (void* env);
  void* (*move_to_next) (void* env);
  void* (*move_to_first) (void* env);
  void* (*get_cursor) (void* index);
  const void* (*get_pair) (void* env);
  void (*free_cursor) (void* env);
};

/* supports efficient lookup */
struct UnordIndexMtable {
  void* (*create) (void* env);
  void* (*insert) (void* env);
  void* (*lookup) (void* env);
  size_t (*cardinality) (void* env);
  void* (*move_to_next) (void* env);
  void* (*move_to_first) (void* env);
  void* (*get_cursor) (void* index);
  const void* (*get_pair) (void* env);
  void (*free_cursor) (void* env);
};

/* supports movement of cursor in either direction */
struct OrdIndexMtable {
  void* (*create) (void* env);
  void* (*insert) (void* env);
  void* (*lookup) (void* env);
  size_t (*cardinality) (void* env);
  void* (*move_to_next) (void* env);
  void* (*move_to_previous) (void* env);
  void* (*move_to_first) (void* env);
  void* (*move_to_last) (void* env);
  void* (*get_cursor) (void* index);
  const void* (*get_pair) (void* env);
  void (*free_cursor) (void* env);
};

/* not using this yet
struct BtreeIndexObj {
  struct OrdIndexMtable* mtable; 
  btree index_data;
  index_attributes attr;
}; */

struct HashtableIndexObj {
  struct UnordIndexMtable* mtable;
  inthash_t index_data;
  /* column information, schema */
  index_attributes attr;
};

struct StringlistIndexObj {
  struct UnordSetMtable* mtable;
  stringlist_t index_data;
  /* column information, schema */
  index_attributes attr;
};

struct IndexObj {
  void* obj;
};


/* what should this mtable be?
struct TupleIndexObj {
  struct IndexMtable *mt;
  struct IndexObj* a;
  struct IndexObj* b;
};

*/


/*================ ENTRY  DEF ================ */

// a single value in the table
// does this need to have size_t?
union value {
  unsigned long int_value;
  char* str_value;
};

// an entry is an int val/string val + domain specifying which one it is
struct entry {
  domain domain;
  union value value;
};

/*================ ITERATOR DEF ================ */

struct iterator_methods {
  void (*init) (void* env);
  const void* (*next) (void* env);
  void (*close) (void* env);
};

// Keeping the idea of an iterator as return type of all db ops
typedef struct iterator_t {
  struct iterator_methods *mtable;
  // each operator requires their own env
  void* env;
} *iterator;


/*================ HELPERS ================ */

// how many columns in the list
size_t attribute_list_length(attribute_list l);

// builds schema object from a list of columns
Schema get_schema(attribute_list attrs);

// finds the offset of a column in the list
int get_offset(attribute_list attrs_all, char* id, domain dom);

// gets physical address of a column in the list
const void* get_field_address(attribute_list attrs_all, char* id, domain dom, const void* t);

// multi-level key built from the entries in the columns we want to project
Key get_projection(attribute_list attrs_all, const void* t, attribute_list attrs_proj);

// builds a btree index from data
//btree index_data(void*** data, int tuple_count, attribute_list attrs, attribute_list primary_key);

/*================ ITERATOR METHODS ================ */

void init_iterator(iterator it);
const void* get_next(iterator it);
void close_iterator(iterator it);

fifo* materialize(iterator it);

#endif