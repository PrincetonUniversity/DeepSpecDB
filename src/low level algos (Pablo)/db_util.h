#ifndef _DBUTILH_
#define _DBUTILH_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// resolve conflicting Key typedef
// I know, this is ugly and needs to be fixed
#define Key btree_Key
#include "relation.h"
#undef Key

#include "queue2.h"

#include "index.h" // in ../tuplekey/
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"

// types of entries that can appear in the table
typedef enum domain { Int, Str } domain;

// list of "columns" in the table
typedef struct attribute_list_t {
  char* id;
  domain domain;
  struct attribute_list_t* next;
} *attribute_list;

typedef Relation_T btree;
typedef Cursor_T btree_cursor;

typedef struct relation_t {
  attribute_list attrs;
  attribute_list pk_attrs; // has to be unique for now
  btree pk_index;
} *relation;

// a single value in the table
union value {
  unsigned long int_value;
  char* str_value;
};

// an entry is an int val/string val + domain specifying which one it is
struct entry {
  domain domain;
  union value value;
};

struct methods {
  void (*init) (void* env);
  const void* (*next) (void* env);
  void (*close) (void* env);
};

typedef struct iterator_t {
  struct methods *mtable;
  void* env;
} *iterator;

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
btree index_data(void*** data, int tuple_count, attribute_list attrs, attribute_list primary_key);


void init_iterator(iterator it);
const void* get_next(iterator it);
void close_iterator(iterator it);

fifo* materialize(iterator it);

#endif