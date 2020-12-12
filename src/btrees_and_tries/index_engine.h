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

Index empty();

Cursor allocate_cursor(Index index);

/** duplicate the cursor */
Cursor copy_cursor(Cursor cursor);

/** these functions will perform in-place updates to the cursor */
void move_cursor(Key key, Cursor cursor, Index index);

void first_cursor(Cursor cursor, Index index);

void last_cursor(Cursor cursor, Index index);

void next_cursor(Cursor cursor, Index index);

void prev_cursor(Cursor cursor, Index index);

void free_cursor(Cursor cursor);

/** key/value are returned through arguments, the return value indicates success or not */
Bool get_key(Cursor cursor, Index index, Key *key);

Bool get_value(Cursor cursor, Index index, Value *value);

/** in-place update to both index and (might be different in concurrent implementations) cursor */
void put(Key key, Value value, Cursor cursor, Index index);
