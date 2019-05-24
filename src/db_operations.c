#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "util.h"
#include "relation.h"
#include "queue2.c"
// #include "index.h" // in ../tuplekey/


typedef enum domain { Int, Str } domain;

typedef struct attribute {
  char* name;
  domain domain;
  struct attribute* next;
} attribute;

typedef Relation_T btree;
typedef Cursor_T btree_cursor;

typedef struct relation {
  attribute* attributes;
  unsigned char pk_attribute; // the UNIQUE primary key field number
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

struct iterator_t;

struct methods {
  void (*init) (struct iterator_t *self);
  const void* (*next) (struct iterator_t *self);
  void (*close) (struct iterator_t *self);
};

typedef struct iterator_t {
  struct methods *mtable;
} *iterator;

/* Materialize produces a fifo list out of an iterator. */

fifo* materialize(iterator it) {
  fifo* res = fifo_new();
  it->mtable->init(it);
  const void* a;
  while(a = it->mtable->next(it)) {
    fifo_put(res, make_elem(a));
  };
  return res;
};

/* The sequential scan creates an iterator on the tuples
   pointed to by the primary key index of the relation.
   To learn more about PostgreSQL's physical plans, visit
   https://www.postgresql.org/docs/9.2/using-explain.html */

struct seq_scan_iterator_t {
  struct methods *mtable;
  btree bt;
  btree_cursor c; // this includes the btree too, but is uninitialized before a call to init(). We need the btree to be able to create the new cursor.
};

typedef struct seq_scan_iterator_t * seq_scan_iterator; 

void seq_scan_iterator_init(seq_scan_iterator self) {
  self->c = RL_NewCursor(self->bt);
  if(!self->c) exit(1);
  RL_MoveToFirst(self->c);
};

const void* seq_scan_iterator_next(seq_scan_iterator self) {
  if (RL_IsEmpty(self->c)) return NULL;
  const void* res = RL_GetRecord(self->c);
  // then, move the btree cursor to the next valid position
  while(RL_MoveToNextValid(self->c));
  return res;
};

void seq_scan_iterator_close(seq_scan_iterator self) {
  RL_FreeCursor(self->c);
  self->c = NULL;
}

struct methods seq_scan_iterator_mtable = {&seq_scan_iterator_init, &seq_scan_iterator_next, &seq_scan_iterator_close};
					   
iterator seq_scan(btree t) {
  seq_scan_iterator it = malloc(sizeof(struct seq_scan_iterator_t));
  if(!it) exit(1);
  it->mtable = &seq_scan_iterator_mtable;
  it->bt = t;
  it->c = NULL;
  return (iterator) it;
}

/* The index scan produces an index given a list of attributes and a pk index (btree)

// TODO



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
 
