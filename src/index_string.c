/** This file contains the implementation of index for
    strings (sequence of bytes with given length).

 *  The code is adapted from original [kvstore.c], but due to
 *  naming and interface issues the code is ported here instead
 */

#include <stdint.h>
#include <stdlib.h>
#include "inttypes.h"
#include "index_int.h"
#include "util.h"
#define mask 255

struct Key_T {
  const char *content;
  size_t len;
};

struct CursorSlice_T {
  ICursor node_cursor;
  uint32_t bnode_cursor;
};

struct Cursor_T {
  size_t capacity;
  size_t size;
  struct CursorSlice_T *content;
};

typedef struct Key_T *SKey;
typedef void *SValue;
typedef struct Cursor_T *SCursor;
typedef IIndex SIndex;

/** auxilary function begin */

void *surely_malloc(unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

void push_cursor(ICursor node_cursor, size_t bnode_cursor, SCursor cursor) {
  /* allocate space for one slice at first, for simplicity */
  if (cursor->capacity == 0) {
    cursor->content = surely_malloc(sizeof(struct CursorSlice_T));
  }
  else if (cursor->capacity <= cursor->size) {
    cursor->capacity *= 2;
    struct CursorSlice_T *new_addr = surely_malloc(sizeof(struct CursorSlice_T) * cursor->capacity);
    for (size_t i = 0; i < cursor->size; ++ i) {
      new_addr[i].node_cursor = cursor->content[i].node_cursor;
      new_addr[i].bnode_cursor = cursor->content[i].bnode_cursor;
    }
    free(cursor->content);
    cursor->content = new_addr;
  }
  cursor->content[cursor->size].node_cursor = node_cursor;
  cursor->content[cursor->size].bnode_cursor = bnode_cursor;
  ++ cursor->size;
}

void pop_cursor(SCursor cursor) {
  if (cursor->size != 0) {
    -- cursor->size;
  }
}

SCursor new_cursor() {
  SCursor cursor = surely_malloc(sizeof(SCursor));

  cursor->capacity = cursor->size = 0;
  cursor->content = NULL;

  return cursor;
}

keyslice_t UTIL_GetNextKeySlice(const char* str, size_t len) {
  keyslice_t res = 0;
  size_t i = 0;

  while(i < keyslice_length) {
    /* Shift res left by keyslice_length *bits* padding with zeroes. */
    res <<= 8;
    if (i < len) {
      res |= (((keyslice_t) *str) & mask);
      str ++;
    }
    i ++;
  }
  return res;
}

Bool UTIL_StrEqual(const char* a, size_t lenA, const char* b, size_t lenB) {
  if(lenA != lenB) {
    return False;
  }

  for (size_t i = 0; i < lenA; ++ i) {
    if (a[i] != b[i]) {
      return False;
    }
  }

  return True;
}

SKey new_key(const char *str, size_t len) {
  SKey newKey = (SKey) NULL;

  char *newStr = (char *)surely_malloc(sizeof(char) * len);
  for(size_t i = 0; i < len; ++ i) {
    newStr[i] = str[i];
  }

  newKey = (SKey) surely_malloc(sizeof(struct Key_T));
  newKey->content = newStr;
  newKey->len = len;

  return newKey;
}

SKey move_key(const char *str, size_t len) {
  SKey newKey = (SKey) NULL;

  newKey = (SKey) surely_malloc(sizeof(struct Key_T));
  newKey->content = str;
  newKey->len = len;

  return newKey;
}

enum {MAX_BN_SIZE = keyslice_length};

struct BorderNode {
  void *prefixLinks[MAX_BN_SIZE];
  void *suffixLink;
  char *keySuffix;
  size_t keySuffixLength;
};

typedef struct BorderNode *BorderNode_T;

BorderNode_T BN_NewBorderNode() {
  BorderNode_T bordernode =
      (struct BorderNode*) surely_malloc(sizeof(struct BorderNode));

  for (int i = 0; i < MAX_BN_SIZE; ++ i) {
    bordernode->prefixLinks[i] = NULL;
  }
  bordernode->suffixLink = NULL;
  bordernode->keySuffix = NULL;
  bordernode->keySuffixLength = 0;

  return bordernode;
}

void BN_FreeBorderNode(BorderNode_T bordernode) {
  if (bordernode == NULL)
    return;

  if (bordernode->keySuffix != NULL) {
    free(bordernode->keySuffix);
  }

  free(bordernode);

  return;
}

void BN_SetPrefixValue(BorderNode_T bn, int i, void* val) {
  bn->prefixLinks[i - 1] = val;
}

const void* BN_GetPrefixValue(BorderNode_T bn, int i) {
  return bn->prefixLinks[i - 1];
}

void BN_SetSuffixValue(BorderNode_T bn, const char *suffix, const size_t len, void *val) {
  if (bn->keySuffix != NULL) {
    free(bn->keySuffix);
  }

  bn->keySuffix = (char *) surely_malloc(sizeof(char) * len);
  for (size_t i = 0; i < len; ++ i) {
    bn->keySuffix[i] = suffix[i];
  }
  bn->keySuffixLength = len;
  bn->suffixLink = val;
}

Bool BN_TestSuffix(BorderNode_T bn, SKey key) {
  if (bn->keySuffix != NULL) {
    return UTIL_StrEqual(key->content + keyslice_length,
                         key->len - keyslice_length,
                         bn->keySuffix, bn->keySuffixLength);
  }
  else {
    return False;
  }
}

const void *BN_GetSuffixValue(BorderNode_T bn, const char *suf, const size_t len) {
  if (bn->keySuffix == NULL) {
    return NULL;
  }

  if (UTIL_StrEqual(suf, len, bn->keySuffix, bn->keySuffixLength)) {
    return bn->suffixLink;
  }
  else {
    return NULL;
  }
}

const void *BN_ExportSuffixValue(BorderNode_T bn, SKey *key) {
  if (bn->keySuffix != NULL) {
    *key = move_key(bn->keySuffix, bn->keySuffixLength);
    bn->keySuffix = NULL;
    bn->keySuffixLength = 0;
  }
  else {
    *key = NULL;
  }

  const void *ret_temp = bn->suffixLink;
  bn->suffixLink = NULL;
  return ret_temp;
}

void BN_SetLink(BorderNode_T bn, void *val) {
  if (bn->keySuffix != NULL) {
    free(bn->keySuffix);
  }

  bn->keySuffix = NULL;
  bn->keySuffixLength = 0;
  bn->suffixLink = val;
}

void *BN_GetLink(BorderNode_T bn) {
  if (bn->keySuffix != NULL) {
    return NULL;
  }

  return bn->suffixLink;
}

Bool BN_HasSuffix(BorderNode_T bn) {
  return bn->keySuffix != NULL;
}

void BN_SetValue(BorderNode_T bn, SKey key, void *val) {
  if (key->len > keyslice_length) {
    BN_SetSuffixValue(bn,
                      key->content + keyslice_length,
                      key->len - keyslice_length,
                      val);
  }
  else {
    BN_SetPrefixValue(bn, key->len, val);
  }
}

int BN_CompareSuffix(BorderNode_T bn, SKey key);

/** auxilary function end */

SIndex Sempty() {
  SIndex new_index = surely_malloc(sizeof(SIndex));
  return new_index;
}

void _make_cursor(SKey key, SIndex index, SCursor cursor) {
  keyslice_t keyslice = UTIL_GetNextKeySlice(key->content, key->len);
  ICursor node_cursor = Imake_cursor(keyslice, index);
  keyslice_t obtained_keyslice;
  Bool success = Iget_key(node_cursor, index, &obtained_keyslice);
  if (success && keyslice == obtained_keyslice) {
    if (key->len <= keyslice_length) {
      push_cursor(node_cursor, key->len, cursor);
      /* end 1 */
    }
    else {
      void * ret_value;
      BorderNode_T bnode;

      Iget_value(node_cursor, index, &ret_value);
      bnode = (BorderNode_T) ret_value;
      if (BN_HasSuffix(bnode)) {
        SKey subkey = new_key(key->content + keyslice_length, key->len - keyslice_length);
        if (BN_CompareSuffix(bnode, subkey)) {
          push_cursor(node_cursor, keyslice_length + 1, cursor);
          /* end 2 */
        }
        else {
          push_cursor(node_cursor, keyslice_length + 2, cursor);
          /* end 3 */
        }
      }
      else {
        SIndex subindex = BN_GetLink(bnode);

        if (subindex != NULL) {
          push_cursor(node_cursor, keyslice_length + 1, cursor);
          /* move_key is sufficient here */
          SKey subkey = new_key(key->content + keyslice_length, key->len - keyslice_length);
          _make_cursor(subkey, subindex, cursor);
          /* end 4 */
        }
        else {
          push_cursor(node_cursor, keyslice_length + 2, cursor);
          /* end 5 */
        }
      }
    }
  }
  else {
    Ifree_cursor(node_cursor);
    /* end 6 */
  }
};

SCursor Smake_cursor(SKey key, SIndex index) {
  SCursor cursor = new_cursor();
  _make_cursor(key, index, new_cursor());

  return cursor;
}

SCursor Sfirst_cursor(SIndex index);

SCursor Slast_cursor(SIndex index);

SCursor Snext_cursor(SCursor cursor, SIndex index);

SCursor Sprev_cursor(SCursor cursor, SIndex index);

Bool Sget_key(SCursor cursor, SIndex index, SKey *key);

Bool Sget_value(SCursor cursor, SIndex index, SValue *value) {
  return True;
}

SCursor Sput(SKey key, SValue value, SCursor cursor, SIndex index);
