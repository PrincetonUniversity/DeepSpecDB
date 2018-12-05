/** This file contains the ideal interface of index for stirng.

 *  This should be implemented by tries in [index_string.c]
 */

#ifndef _INDEX_STRING_H
#define _INDEX_STRING_H

#include "inttypes.h"
#include "util.h"

typedef struct Key_T *SKey;
typedef void *SValue;
typedef struct Cursor_T *SCursor;
typedef struct Trie_T *SIndex;

SIndex Sempty(void);

SCursor Smake_cursor(SKey key, SIndex index);

SCursor Smove_cursor(SKey key, SCursor cursor, SIndex index);

SCursor Sfirst_cursor(SIndex index);

SCursor Slast_cursor(SIndex index);

SCursor Snext_cursor(SCursor cursor, SIndex index);

void Sfree_cursor(SCursor cursor);

SCursor Sprev_cursor(SCursor cursor, SIndex index);

Bool Sget_key(SCursor cursor, SIndex index, SKey *key);

Bool Sget_value(SCursor cursor, SIndex index, SValue *value);

void Sput(SKey key, SValue value, SCursor cursor, SIndex index);

#endif
