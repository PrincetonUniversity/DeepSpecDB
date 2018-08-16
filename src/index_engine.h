/** This file should serves as an example of what interface an
 *  index object(trie, b+-tree, pair operator) should provide

 *  This file follows closely the [ABSTRACT_TABLE] in file
 *  [cursored_kv.v]

 *  This file shows only what ineterface would look like, but
 *  makes no attempt to be formal
 */

/** Type Definitions */

#include "util.h"

typedef void *Key;
typedef void *Value;
typedef void *Cursor;
typedef void *Index;

/** Functions
 * for all functions that takes a cursor and returns a cursor,
 *  it should make an in place update and return exactly the same cursor
 */

Index empty();

Cursor make_cursor(Key key, Index index);

/** This function has exactly the same semantic as [make_cursor] */
Cursor move_cursor(Key key, Cursor cursor, Index index);

Cursor first_cursor(Index index);

Cursor last_cursor(Index index);

Cursor next_cursor(Cursor cursor, Index index);

Cursor prev_cursor(Cursor cursor, Index index);

void free_cursor(Cursor cursor);

Bool get_key(Cursor cursor, Index index, Key *key);

Bool get_value(Cursor cursor, Index index, Value *value);

void put(Key key, Value value, Cursor cursor, Index index);

