/** This file contains the ideal interface of index for int.

 *  This should be implemented by b+-trees, as the original
 *  [relation_mem.c]
 */

#ifndef _INDEX_INT_H
#define _INDEX_INT_H

#include "inttypes.h"
#include "util.h"

typedef keyslice_t IKey;
typedef void *IValue;
typedef void *ICursor;
typedef void *IIndex;

IIndex Iempty(void);

ICursor Imake_cursor(IKey key, IIndex index);

ICursor Imove_cursor(IKey key, ICursor cursor);

ICursor Ifirst_cursor(ICursor cursor);

ICursor Ilast_cursor(ICursor cursor);

ICursor Inext_cursor(ICursor cursor);

void Ifree_cursor(ICursor cursor);

ICursor Iprev_cursor(ICursor cursor);

Bool Iget_key(ICursor cursor, IKey *key);

Bool Iget_value(ICursor cursor, IValue *value);

void Iput(IKey key, IValue value, ICursor cursor);

#endif
