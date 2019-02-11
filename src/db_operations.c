#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "kvstore.h"
#include "util.h"
#include "relation.h"
#include "index_string.h"
#include "index_int.h"

typedef struct Column Column;
typedef struct Schema Schema;
typedef struct DBIndex DBIndex;
typedef struct Entry Entry;

//each column in the table has these attributes
struct Column {
	char* name;
	char valType; /* possible value types: i = int, s = string  */
	int pkFlag; /* possible pkflag types: 0 = not pk, 1 = pk */
	Column* nextCol;
};

// a schema is a linked list of columns
struct Schema {
	Column* col;
	int size;
};

//provides two different options for pointers, a tree or a trie
struct DBIndex {
	//if index is btree
	Relation_T tree;
	Cursor_T cursor;

	//if index is trie
	KVStore_T trie;

	char keyType; /* possible value types: i = int, s = string  */
};

// an entry in the array of data
struct Entry {
	char valType; /* possible value types: i = int, s = string */
	unsigned long intEntry;
	char* stringEntry;
};


/*  CREATE function
    inputs: array of data, length of array, schema
    output: pointer to an index on the data */
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


DBIndex filter(Bool (*f)(Entry), DBIndex i) {
	DBIndex filtered;

	if (i.keyType == 'i') {
		/* to be adjusted using functions from index_int.c */ 
		filtered.tree = Iempty();
		if (filtered.tree == NULL) exit(1);
		filtered.cursor = RL_NewCursor(filtered.tree);
		if (filtered.cursor == NULL) exit(1);
		filtered.keyType = 'i';

		Bool b = RL_MoveToFirst(i.cursor);
		if (!b) exit(1);
		while (b) {
			Key key = RL_GetKey(i.cursor);
			Entry* num = malloc(sizeof(Entry));
			num->intEntry = key;
			num->valType = 'i';

			if (f(*num) == True) {
				RL_PutRecord(filtered.cursor, key, RL_GetRecord(i.cursor));
			}

			b = RL_MoveToNextValid(i.cursor);
		}
	} else if (i.keyType == 's'){
		filtered.trie = KV_NewKVStore();
		if (filtered.trie == NULL) exit(1);
		filtered.keyType = 's';
		
		/* to be completed using index_string.c */

	} else {
		// no other key types supported yet
		exit(1);
	}

	return filtered;

}


int main() {
	Schema* schema = NULL;
	schema = malloc(sizeof(Schema));
	if (schema == NULL) {
		return -1;
	}
	schema->size = 3;
	Column* col3 = malloc(sizeof(Column));
	Column* col2 = malloc(sizeof(Column));
	Column* col1 = malloc(sizeof(Column));

	col3->valType = 'i';
	col2->valType = 'i';
	col1->valType = 'i';

	col3->pkFlag = 1;
	col2->pkFlag = 0;
	col1->pkFlag = 0;

	col1->nextCol = col2;
	col2->nextCol = col3;

	schema->col = col1;

	Entry arr[9];
	for (int i = 0; i < 9; i++) {
		Entry* e = malloc(sizeof(Entry));
		e->intEntry = i;
		arr[i] = *e;
	}

	DBIndex ind = create(arr, 9, schema);

	RL_MoveToKey(ind.cursor, 3);
	Entry* values = (Entry*) RL_GetRecord(ind.cursor);

	for (i = 0; i < schema->size; i++) {
		printf("%lu\n", values[i].intEntry);
	}

}
