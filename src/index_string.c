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
  char *content;
  size_t len;
};

struct CursorSlice_T {
  IIndex node;
  ICursor node_cursor;
  uint32_t bnode_cursor;
};

struct Cursor_T {
  size_t capacity;
  size_t size;
  struct CursorSlice_T *content;
};

struct Trie_T {
  IIndex root;
  size_t size;
};

typedef struct Key_T *SKey;
typedef void *SValue;
typedef struct Cursor_T *SCursor;
typedef struct Trie_T *SIndex;

/** auxilary function begin */

void *surely_malloc(unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

void push_cursor(IIndex node, ICursor node_cursor, size_t bnode_cursor, SCursor cursor) {
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
  cursor->content[cursor->size].node = node;
  cursor->content[cursor->size].node_cursor = node_cursor;
  cursor->content[cursor->size].bnode_cursor = bnode_cursor;
  ++ cursor->size;
}

void pop_cursor(SCursor cursor) {
  if (cursor->size != 0) {
    -- cursor->size;
    Ifree_cursor(cursor->content[cursor->size].node_cursor);
  }
}

struct CursorSlice_T *top_cursor(SCursor cursor) {
  if (cursor->size != 0) {
    return cursor->content + (cursor->size - 1);
  }
  else {
    return NULL;
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

SKey move_key(char *str, size_t len) {
  SKey newKey = (SKey) NULL;

  newKey = (SKey) surely_malloc(sizeof(struct Key_T));
  newKey->content = str;
  newKey->len = len;

  return newKey;
}

void free_key(SKey key) {
  free(key->content);
  free(key);
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

void *BN_ExportSuffixValue(BorderNode_T bn, SKey *key) {
  if (bn->keySuffix != NULL) {
    *key = move_key(bn->keySuffix, bn->keySuffixLength);
    bn->keySuffix = NULL;
    bn->keySuffixLength = 0;
  }
  else {
    *key = NULL;
  }

  void *ret_temp = bn->suffixLink;
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

static size_t bordernode_next_cursor(size_t bnode_cursor, BorderNode_T bn) {
  for (size_t i = bnode_cursor; i <= keyslice_length; ++ i) {
    if (bn->prefixLinks[i]) {
      return i;
    }
  }

  if (bnode_cursor <= keyslice_length + 1 && bn->suffixLink) {
    return keyslice_length + 1;
  }
  else {
    return keyslice_length + 2;
  }
}

static size_t bordernode_length_to_cursor(size_t len) {
  if (len <= keyslice_length) {
    return len;
  }
  else {
    return keyslice_length + 1;
  }
}

/** auxilary function end */

SIndex Sempty() {
  SIndex new_index = surely_malloc(sizeof(SIndex));
  return new_index;
}

static void make_cursor(SKey key, IIndex index, SCursor cursor) {
  keyslice_t keyslice = UTIL_GetNextKeySlice(key->content, key->len);
  ICursor node_cursor = Imake_cursor(keyslice, index);
  keyslice_t obtained_keyslice;
  Bool success = Iget_key(node_cursor, index, &obtained_keyslice);
  if (success && keyslice == obtained_keyslice) {
    if (key->len <= keyslice_length) {
      push_cursor(index, node_cursor, key->len, cursor);
      /* end 1 */
    }
    else {
      void * ret_value;
      BorderNode_T bnode;

      Iget_value(node_cursor, index, &ret_value);
      bnode = (BorderNode_T) ret_value;
      if (BN_HasSuffix(bnode)) {
        if (BN_CompareSuffix(bnode, key)) {
          push_cursor(index, node_cursor, keyslice_length + 1, cursor);
          /* end 2 */
        }
        else {
          push_cursor(index, node_cursor, keyslice_length + 2, cursor);
          /* end 3 */
        }
      }
      else {
        IIndex subindex = BN_GetLink(bnode);

        if (subindex != NULL) {
          push_cursor(index, node_cursor, keyslice_length + 1, cursor);
          SKey subkey = new_key(key->content + keyslice_length, key->len - keyslice_length);
          make_cursor(subkey, subindex, cursor);
          free_key(subkey);
          /* end 4 */
        }
        else {
          push_cursor(index, node_cursor, keyslice_length + 2, cursor);
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
  make_cursor(key, index->root, new_cursor());

  return cursor;
}

Bool strict_first_cursor(IIndex index, SCursor cursor) {
  ICursor node_cursor = Ifirst_cursor(index);
  void *ret_value;
  Bool success = Iget_value(node_cursor, index, &ret_value);

  if (success) {
    BorderNode_T bnode = (BorderNode_T) ret_value;
    size_t bnode_cursor = bordernode_next_cursor(1, bnode);

    if (bnode_cursor <= keyslice_length) {
      push_cursor(index, node_cursor, bnode_cursor, cursor);
      return True;
    }
    else if (bnode_cursor == keyslice_length + 1) {
      push_cursor(index, node_cursor, bnode_cursor, cursor);

      if (BN_HasSuffix(bnode)) {
        return True;
      }
      else {
        IIndex subindex = BN_GetLink(bnode);

        /* subindex must not be null */
        if (strict_first_cursor(subindex, cursor)) {
          return True;
        }
        else {
          pop_cursor(cursor);
          return False;
        }
      }
    }
    else {
      Ifree_cursor(node_cursor);
      return False;
    }
  }
  else {
    Ifree_cursor(node_cursor);
    return False;
  }
}

Bool normalize_cursor(SCursor cursor) {
  struct CursorSlice_T *cs = top_cursor(cursor);

  if (cs) {
    void *ret_value;

    Iget_value(cs->node, cs->node_cursor, &ret_value);
    BorderNode_T bnode = ret_value;
    size_t next_bnode_cursor = bordernode_next_cursor(cs->bnode_cursor, bnode);
    if (next_bnode_cursor <= keyslice_length) {
      cs->bnode_cursor = next_bnode_cursor;
      return True;
    }
    else if (next_bnode_cursor == keyslice_length + 1) {
      cs->bnode_cursor = keyslice_length + 1;
      if (! BN_HasSuffix(bnode)) {
        IIndex subindex = BN_GetLink(bnode);
        /* if the table is correct, then it won't fail for this part */
        strict_first_cursor(subindex, cursor);
      }
      return True;
    }
    else {
      ICursor next_cursor = Inext_cursor(cs->node_cursor, cs->node);
      Bool success = Iget_value(cs->node_cursor, next_cursor, &ret_value);
      if (success) {
        free(cs->node_cursor);
        cs->node_cursor = next_cursor;
        BorderNode_T next_bnode = ret_value;

        size_t bnode_cursor = bordernode_next_cursor(1, next_bnode);
        cs->bnode_cursor = bnode_cursor;
        if (next_bnode_cursor == keyslice_length + 1 && ! BN_HasSuffix(next_bnode)) {
          IIndex subindex = BN_GetLink(bnode);
          /* if the table is correct, then it won't fail for this part */
          strict_first_cursor(subindex, cursor);
        }
        return True;
      }
      else {
        Ifree_cursor(next_cursor);
        return False;
      }
    }
  }
  else {
    pop_cursor(cursor);
    return False;
  }
}

SCursor Sfirst_cursor(SIndex index);

SCursor Slast_cursor(SIndex index);

SCursor Snext_cursor(SCursor cursor, SIndex index);

SCursor Sprev_cursor(SCursor cursor, SIndex index);

Bool Sget_key(SCursor cursor, SIndex index, SKey *key);

Bool Sget_value(SCursor cursor, SIndex index, SValue *value) {
  return True;
}

IIndex create_pair(char *key1, size_t len1, char *key2, size_t len2, void *v1, void *v2) {
  keyslice_t keyslice1 = UTIL_GetNextKeySlice(key1, len1);
  keyslice_t keyslice2 = UTIL_GetNextKeySlice(key2, len2);
  if (keyslice1 == keyslice2) {
    if (len1 <= keyslice_length || len2 <= keyslice_length) {
      BorderNode_T bnode = BN_NewBorderNode();
      SKey k1 = new_key(key1, len1);
      BN_SetValue(bnode, k1, v1);
      SKey k2 = new_key(key2, len2);
      BN_SetValue(bnode, k2, v2);
      free_key(k1);
      free_key(k2);
      IIndex index = Iempty();
      ICursor temp_cursor = Ifirst_cursor(index);
      Iput(keyslice1, bnode, temp_cursor, index);
      Ifree_cursor(temp_cursor);
      return index;
    }
    else {
      BorderNode_T bnode = BN_NewBorderNode();
      BN_SetLink(bnode, create_pair(key1 + keyslice_length, len1 - keyslice_length,
                                    key2 + keyslice_length, len2 - keyslice_length,
                                    v1, v2));
      IIndex index = Iempty();
      ICursor temp_cursor = Ifirst_cursor(index);
      Iput(keyslice1, bnode, temp_cursor, index);
      Ifree_cursor(temp_cursor);
      return index;
    }
  }
  else {
    BorderNode_T bnode1 = BN_NewBorderNode();
    SKey k1 = new_key(key1, len1);
    BN_SetValue(bnode1, k1, v1);
    BorderNode_T bnode2 = BN_NewBorderNode();
    SKey k2 = new_key(key2, len2);
    BN_SetValue(bnode2, k2, v2);
    free_key(k1);
    free_key(k2);
    IIndex index = Iempty();
    ICursor temp_cursor = Ifirst_cursor(index);
    Iput(keyslice2, bnode2, temp_cursor, index);
    Ifree_cursor(temp_cursor);
    temp_cursor = Ifirst_cursor(index);
    Iput(keyslice1, bnode1, temp_cursor, index);
    Ifree_cursor(temp_cursor);
    return index;
  }
}

void put(char *key, size_t len, void *v, IIndex index) {
  keyslice_t keyslice = UTIL_GetNextKeySlice(key, len);
  ICursor node_cursor = Imake_cursor(keyslice, index);

  keyslice_t obtained_keyslice;
  Bool success = Iget_key(node_cursor, index, &obtained_keyslice);
  if (success && obtained_keyslice == keyslice) {
    void *ret_value;
    Iget_value(node_cursor, index, &ret_value);
    BorderNode_T bnode = ret_value;
    if (len <= keyslice_length) {
      BN_SetPrefixValue(bnode, len, v);
      return;
    }
    else {
      if (BN_HasSuffix(bnode)) {
        SKey k = new_key(key, len);
        if (BN_TestSuffix(bnode, k)) {
          BN_SetSuffixValue(bnode, key + keyslice_length, len - keyslice_length, v);
          return;
        }
        else {
          SKey k2;
          void *v2 = BN_ExportSuffixValue(bnode, &k2);
          IIndex subindex = create_pair(key + keyslice_length, len - keyslice_length,
                                        k2->content, k2->len, v, v2);
          BN_SetLink(bnode, subindex);
          return;
        }
      }
      else {
        IIndex subindex = BN_GetLink(bnode);

        if (subindex) {
          put(key + keyslice_length, len - keyslice_length, v, index);
          return;
        }
        else {
          BN_SetSuffixValue(bnode, key + keyslice_length, len - keyslice_length, v);
          return;
        }
      }
    }
  }
  else {
    BorderNode_T bnode = BN_NewBorderNode();
    SKey k = new_key(key, len);
    BN_SetValue(bnode, k, v);
    free_key(k);
    Iput(keyslice, bnode, node_cursor, index);
    Ifree_cursor(node_cursor);
    return;
  }
}

SCursor Sput(SKey key, SValue value, SCursor cursor, SIndex index);
