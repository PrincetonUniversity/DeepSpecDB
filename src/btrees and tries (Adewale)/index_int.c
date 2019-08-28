#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "inttypes.h"
#include "index_int.h"
#include "relation.h"
#include "util.h"

void *surely_malloc(unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

IIndex Iempty(void) {
    return RL_NewRelation();
}

ICursor Imake_cursor(IKey key, IIndex index) {
	if (index == NULL) return NULL;
	
	ICursor cursor = RL_NewCursor(index);
	
	/* error creating the cursor */
	if (cursor == NULL) return NULL;
	
	return Imove_cursor(key, cursor);
}

ICursor Imove_cursor(IKey key, ICursor cursor) {
	if (cursor == NULL) return NULL;
	
	if (RL_MoveToKey(cursor, key) == False) {
		return NULL;
	} else {
		return cursor;
	}
}

ICursor Ifirst_cursor(ICursor cursor) {
	if (cursor == NULL) return NULL;
	
	if (RL_MoveToFirst(cursor) == False) {
		return NULL;
	} else {
		return cursor;
	}
}


ICursor Ilast_cursor(ICursor cursor) {
	if (cursor == NULL) return NULL;
	
	while(RL_MoveToNextValid(cursor) == True) {
		/* keep looping till the end */
	}
	RL_MoveToPrevious(cursor);
	return cursor;
}

ICursor Inext_cursor(ICursor cursor) {
	if (cursor == NULL) return NULL;
	
	RL_MoveToNext(cursor);
	return cursor;
}

void Ifree_cursor(ICursor cursor) {
	RL_FreeCursor(cursor);
}

ICursor Iprev_cursor(ICursor cursor) {
	if (cursor == NULL) return NULL;
	
	RL_MoveToPrevious(cursor);
	return cursor;
}

Bool Iget_key(ICursor cursor, IKey *key) {
	if (cursor == NULL) return False;
	
	*key = RL_GetKey(cursor);
	if (*key) return True;
	return False;
}

Bool Iget_value(ICursor cursor, IValue *value) {
	if (cursor == NULL) return False;
	
	*value = RL_GetRecord(cursor);
	if (*value) return True;
	return False;
}

void Iput(IKey key, IValue value, ICursor cursor) {
	RL_PutRecord(cursor, key, value);
}

int main(){
	IIndex i = Iempty();
	ICursor cursor = RL_NewCursor(i);
	IKey k1 = 5;
	char str1[] = "twenty";
	IValue v1 = &str1;
	IKey k2 = 6;
	char str2[] = "twenty four";
	IValue v2 = &str2;
	IKey k3 = 7;
	char str3[] = "twenty eight";
	IValue v3 = &str3;
	
	Iput(k1, v1, cursor);
	Iput(k2, v2, cursor);
	Iput(k3, v3, cursor);
	
	IValue val = surely_malloc(sizeof(IValue));
	
	cursor = Ilast_cursor(cursor);
	Bool b = Iget_value(cursor, &val);
	if (b == True) {
		printf("%s \n", val);
	}
	
	IKey key = surely_malloc(sizeof(IKey));
	b = Iget_key(cursor, &key);
	if (b == True) {
		printf("%lu \n", key);
	}
	
	/*
	cursor = Ilast_cursor(cursor);
	IValue val = RL_GetRecord(cursor);
	printf("%s \n", val);
	
	cursor = Ifirst_cursor(cursor);
	val = RL_GetRecord(cursor);
	printf("%s \n", val);
	
	cursor = Ilast_cursor(cursor);
	val = RL_GetRecord(cursor);
	printf("%s \n", val);
	*/
	
	
	return 0;
}
