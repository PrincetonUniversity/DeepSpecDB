#include <stdio.h>
#include "util.h"

// resolve conflicting Key typedef
// I know, this is ugly and needs to be fixed
#define Key btree_Key
#include "relation.h"
#undef Key

#include "queue2.c"

#include "index.h" // in ../tuplekey/
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"
#include "tuple_schema.c"

typedef enum domain { Int, Str } domain;

typedef struct attribute_list_t {
  char* id;
  domain domain;
  struct attribute_list_t* next;
} *attribute_list;

typedef Relation_T btree;
typedef Cursor_T btree_cursor;

typedef struct relation {
  attribute_list attributes;
  char* pk_attribute; // the UNIQUE primary key attribute name
  btree pk_index;
} relation;

union value {
  unsigned long int_value;
  char* str_value;
};

struct entry {
  domain domain;
  union value value;
};

/* The iterator class */

struct methods {
  void (*init) (void* env);
  const void* (*next) (void* env);
  void (*close) (void* env);
};

typedef struct iterator_t {
  struct methods *mtable;
  void* env;
} *iterator;

void init_iterator(iterator it) { it->mtable->init(it->env); };
const void* get_next(iterator it) { return it->mtable->next(it->env); };
void close_iterator(iterator it) { it->mtable->close(it->env); };

/* Materialize produces a fifo list out of an iterator. */

fifo* materialize(iterator it) {
  fifo* res = fifo_new();
  init_iterator(it);
  const void* a;
  while(a = get_next(it)) {
    fifo_put(res, make_elem(a));
  };
  return res;
};

/* The sequential scan creates an iterator on the tuples
   pointed to by the primary key index of the relation.
   To learn more about PostgreSQL's physical plans, visit
   https://www.postgresql.org/docs/9.2/using-explain.html */

struct seq_scan_env {
  btree bt;
  btree_cursor c; // this includes the btree too, but is uninitialized before a call to init(). We need the btree to be able to create the new cursor.
};

void seq_scan_iterator_init(void* env) {
  struct seq_scan_env *e = (struct seq_scan_env*) env;
  if(!(e->c = RL_NewCursor(e->bt))) exit(1);
  RL_MoveToFirst(e->c);
};

const void* seq_scan_iterator_next(void* env) {
  btree_cursor c = ((struct seq_scan_env*) env)->c;
  if (RL_IsEmpty(c)) return NULL;
  const void* res = RL_GetRecord(c);
  // then, move the btree cursor to the next valid position
  while(RL_MoveToNextValid(c)); // could loop forever? TODO: check that
  return res;
};

void seq_scan_iterator_close(void* env) {
  btree_cursor c = ((struct seq_scan_env*) env)->c;
  RL_FreeCursor(c);
}

struct methods seq_scan_iterator_mtable = {&seq_scan_iterator_init, &seq_scan_iterator_next, &seq_scan_iterator_close};
					   
iterator seq_scan(btree t) {
  iterator it = malloc(sizeof(struct iterator_t));
  if(!it) exit(1);
  it->mtable = &seq_scan_iterator_mtable;
  struct seq_scan_env *env = malloc(sizeof(struct seq_scan_env));
  if(!env) exit(1);
  env->bt = t;
  env->c = NULL;
  it->env = (void*) env;
  return (iterator) it;
}

/* The index scan produces an index given a list of attributes and a pk index (btree) */

// Generate a Schema out of an attribute list
Schema get_schema_aux(domain d) {
  switch (d) {
  case Int:
    return &inthash_schema;
  case Str:
    return &stringlist_schema;
  default:
    exit(1);
  };
};

Schema get_schema(attribute_list attrs) {
  if(!attrs) return NULL;
  Schema s = get_schema_aux(attrs->domain);
  if(!attrs->next) return s;
  return tuple_schema(s, get_schema(attrs->next));
};

unsigned int get_offset(attribute_list attrs_all, char* id, domain dom) {
  if (!attrs_all) exit(1);
  attribute_list x = attrs_all;
  unsigned int res = 0;
  do {
    if(strcmp(id, x->id) == 0) return res;
    res++;
  }  while(!(x = x->next));
  exit(1); // attribute not found
};

Key get_projection(attribute_list attrs_all, const void* t, attribute_list attrs_proj) {
  if(!attrs_proj) exit(1);
  unsigned int ofs = get_offset(attrs_all, attrs_proj->id, attrs_proj->domain);
  Key current = (void*) *((size_t*) t + ofs);
  if(!attrs_proj->next) return current;
  struct keypair *kp = (struct keypair*) malloc(sizeof(struct keypair));
  kp->a = current;
  kp->b = get_projection(attrs_all, t, attrs_proj->next); // TODO: optimize this
  return (Key) kp;
}

Index index_scan(relation *rel, attribute_list attrs) {
  Schema sch = get_schema(attrs);
  Index ind = index_new(sch);
  iterator it = seq_scan(rel->pk_index);
  const void* t; Key proj;
  while(t = get_next(it)) {
    proj = get_projection(rel->attributes, t, attrs);
    // TODO: lookup, then insert in the lookuped list, then insert back into the index
    // xxxx = (fifo*) index_lookup(sch, ind, proj);
  };
  return ind;
}


/* The rest of the code is great, but I didn't take the time to update it with the new datatypes */
// Note that, according to what I read (and tried to understand), there is no such thing as a "filter" physical operator.
// Filtering is done at the leaves of the plan (eg at the scan) or after a join.
// That is, many physical operators accept a predicate to filter out results.


/*  CREATE function
    inputs: array of data, length of array, schema
    output: pointer to an index on the data */

/* array of void*
size_t and void * are of the same size */

/*

DBIndex create(Entry* arr, int arrLen, Schema* schema) {
	DBIndex index;

	// length of each row
	int rowLen = schema->size;

	// figure out index (offset) of the PK Column and the type of data
	Column* col = schema->col;
	int offset = 0;
	char valType = 'u';
	while (col != NULL) {
		if (col->pkFlag == 1) {
			valType = col->valType;
			break;
		}
		col = col->nextCol;
		offset++;
	}

	// if pk is int, make btree index. if it's string, make trie index.
	if (valType == 'i') {
		index.tree = Iempty();
		if (index.tree == NULL) exit(1);
		index.cursor = RL_NewCursor(index.tree);
		if (index.cursor == NULL) exit(1);
		index.keyType = 'i';

		for (int i = 0; i < arrLen; i = i + rowLen) {
			Entry* values = &arr[i];
			Entry item = arr[i + offset];
			Key key = item.intEntry;

			Iput(key, values, index.cursor);
		}
	} else {
		index.trie = KV_NewKVStore();
		if (index.trie == NULL) exit(1);
		index.keyType = 's';

		for (int i = 0; i < arrLen; i = i + rowLen) {
			Entry* values = &arr[i];
			Entry item = arr[i + offset];
			char* str = item.stringEntry;
			KVKey_T key = KV_NewKey(str, strlen(str));

			Bool b = KV_Put(index.trie, key, values);
			if (b == False) exit(1);
		}
	}

	return index;
}

*/

//
//
//
//
//
// DBIndex filter(Bool (*f)(Entry), DBIndex i) {
// 	DBIndex filtered;
//
// 	if (i.keyType == 'i') {
// 		/* to be adjusted using functions from index_int.c */
// 		filtered.tree = Iempty();
// 		if (filtered.tree == NULL) exit(1);
// 		filtered.cursor = RL_NewCursor(filtered.tree);
// 		if (filtered.cursor == NULL) exit(1);
// 		filtered.keyType = 'i';
//
// 		Bool b = RL_MoveToFirst(i.cursor);
// 		if (!b) exit(1);
// 		while (b) {
// 			Key key = RL_GetKey(i.cursor);
// 			Entry* num = malloc(sizeof(Entry));
// 			num->intEntry = key;
// 			num->valType = 'i';
//
// 			if (f(*num) == True) {
// 				RL_PutRecord(filtered.cursor, key, RL_GetRecord(i.cursor));
// 			}
//
// 			b = RL_MoveToNextValid(i.cursor);
// 		}
// 	} else if (i.keyType == 's'){
// 		filtered.trie = KV_NewKVStore();
// 		if (filtered.trie == NULL) exit(1);
// 		filtered.keyType = 's';
//
// 		/* to be completed using index_string.c */
//
// 	} else {
// 		// no other key types supported yet
// 		exit(1);
// 	}
//
// 	return filtered;
//
// }
//
//
// int main() {
// 	Schema* schema = NULL;
// 	schema = malloc(sizeof(Schema));
// 	if (schema == NULL) {
// 		return -1;
// 	}
// 	schema->size = 3;
// 	Column* col3 = malloc(sizeof(Column));
// 	Column* col2 = malloc(sizeof(Column));
// 	Column* col1 = malloc(sizeof(Column));
//
// 	col3->valType = 'i';
// 	col2->valType = 'i';
// 	col1->valType = 'i';
//
// 	col3->pkFlag = 1;
// 	col2->pkFlag = 0;
// 	col1->pkFlag = 0;
//
// 	col1->nextCol = col2;
// 	col2->nextCol = col3;
//
// 	schema->col = col1;
//
// 	Entry arr[9];
// 	for (int i = 0; i < 9; i++) {
// 		Entry* e = malloc(sizeof(Entry));
// 		e->intEntry = i;
// 		arr[i] = *e;
// 	}
//
// 	DBIndex ind = create(arr, 9, schema);
//
// 	RL_MoveToKey(ind.cursor, 3);
// 	Entry* values = (Entry*) RL_GetRecord(ind.cursor);
//
// 	for (int i = 0; i < schema->size; i++) {
// 		printf("%lu\n", values[i].intEntry);
// 	}
//
// }
 
