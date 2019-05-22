#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "kvstore.h"
#include "util.h"
#include "relation.h"
#include "index_string.h"
#include "queue2.c"

// maximum number of fields the primary key of a table can span
// For now, we allow a unique compulsory pk field (which defaults to the Oth attribute)
#define MAX_PK_ATTRIBUTES 1

typedef enum domain { Int, Str } domain;

typedef struct attribute {
  char* name;
  domain domain;
  struct attribute* next;
} attribute;

typedef struct schema {
  unsigned char size;
  attribute* attributes;
  unsigned char pk_attributes[MAX_PK_ATTRIBUTES];
} schema;

typedef Relation_T btree;
typedef Cursor_T btree_cursor;

typedef SIndex trie;
typedef SCursor trie_cursor;

union index_container {
  btree btree;
  trie trie;
};  

enum which_index_container { is_btree, is_trie };

typedef struct index {
  enum which_index_container which;
  union index_container container;
} index;

union value {
  unsigned long int_value;
  char* str_value;
};

struct entry {
  domain domain;
  union value value;
};

typedef struct cursor {
  void* env;
  const void* (*next)(void*);
  // void (*reset)(void*); // I see no use for reset for now
} cursor;

// clightgen doesn't allow struct parameters by default, so had to use pointer
fifo* materialize(cursor* c) {
  fifo* res = fifo_new();
  // c->reset();
  const void* a;
  while(a = c->next(c->env)) {
    fifo_put(res, make_elem(a));
  };
  return res;
};

const void* null_next(void* env) { return NULL; };
// void null_reset(void* env) { return; };

cursor empty_cursor = { .env = NULL, .next = null_next };

const void* btree_cursor_next(void* env) {
  btree_cursor c = (btree_cursor) env;
  if (RL_IsEmpty(c)) return NULL;
  const void* res = RL_GetRecord(c);
  // then, move the btree cursor to the next valid position
  while(RL_MoveToNextValid(c));
  return res;
};

const void* trie_cursor_next(void* env) {

  /*
  trie_cursor c = (trie_cursor) env;
  trie t = // retrieve from env? use struct?
  const void* res = Sget_value(c, t); // GRRR the get_value function needs the trie
  // and GESS WHAT it's not even implemented
  // the "next cursor" function isn't implement either
  Snext_cursor(trie_cursor, t);
  return res;
  */

  return NULL;
};



/* The sequential scan: creates an iterator on the tuples
pointed to by the primary key index of the relation
To learn more about PostgreSQL's physical plans, visit
https://www.postgresql.org/docs/9.2/using-explain.html
*/

cursor seq_scan(index* i) {
  cursor res;
  switch (i->which) {
  case is_btree:
    {
      btree_cursor c = RL_NewCursor(i->container.btree);
      if (!c) exit(1);
      if (!RL_MoveToFirst(c)) /* relation is empty */ return empty_cursor;
      // equivalently:
      // if (RL_IsEmpty(c)) return empty_cursor;
      
      // after that, the cursor is necessarily valid and the relation non-empty
      res.env = (void*) c;
      res.next = btree_cursor_next;
      return res;
    }
  case is_trie:
    {
      trie_cursor c = Sfirst_cursor(i->container.trie); // this function isn't even implemented in C, there is just the signature [LOL] let's pretend it does what it's supposed to do
      if (!c) exit(1);
      res.env = (void*) c;
      res.next = trie_cursor_next;
      return res;
    }
  default:
    exit(1);
  };
};


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
 
