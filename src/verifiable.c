#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdlib.h>

#include "util.h"
#include "bordernode.h"
#include "inttypes.h"
#include "kvstore_int.h"
#define mask 255

void *surely_malloc(unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
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

keyslice_t UTIL_GetNextKeySlice(const char* str, long len) {
  keyslice_t res = 0;
  int i = 0;

  assert(len >= 0);
  assert(len <= keyslice_length);


  while(i < len) {
    /* Shift res left by keyslice_length *bits* padding with zeroes. */
    res <<= 8;
    res |= (((keyslice_t) *str) & mask);
    str++, i++;
  }
  while(i < keyslice_length) {
    /* Shift res left until most significant bits are not 0. */
    res <<= 8;
    i++;
  }
  return res;
}

enum {MAX_BN_SIZE = keyslice_length};

struct BorderNode {
  const void *prefixLinks[MAX_BN_SIZE];
  const void *suffixLink;
  char *keySuffix;
  size_t keySuffixLength;
};

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

void BN_SetPrefixValue(BorderNode_T bn, int i, const void* val) {
  assert(i >= 0);
  assert(i < MAX_BN_SIZE);
  bn->prefixLinks[i] = val;
}

const void* BN_GetPrefixValue(BorderNode_T bn, int i) {
  assert(i >= 0);
  assert(i < MAX_BN_SIZE);
  return bn->prefixLinks[i];
}

void BN_SetSuffixValue(BorderNode_T bn, const char *suffix, const size_t len, const void *val) {
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

Bool BN_TestSuffix(BorderNode_T bn, KVKey_T key) {
  if (bn->keySuffix != NULL) {
    return UTIL_StrEqual(KV_GetCharArray(key) + keyslice_length,
                         KV_GetCharArraySize(key) - keyslice_length,
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

const void *BN_ExportSuffixValue(BorderNode_T bn, KVKey_T key) {
  if (bn->keySuffix != NULL) {
    key = KV_MoveKey(bn->keySuffix, bn->keySuffixLength);
    bn->keySuffix = NULL;
    bn->keySuffixLength = 0;
  }

  return bn->suffixLink;
}

void BN_SetLink(BorderNode_T bn, void *val) {
  if (bn->keySuffix != NULL) {
    free(bn->keySuffix);
  }

  bn->keySuffix = NULL;
  bn->keySuffixLength = 0;
  bn->suffixLink = val;
}

const void *BN_GetLink(BorderNode_T bn) {
  if (bn->keySuffix != NULL) {
    return NULL;
  }

  return bn->suffixLink;
}

Bool BN_HasLink(BorderNode_T bn) {
  return bn->keySuffix == NULL && bn->suffixLink != NULL;
}

Bool BN_HasSuffix(BorderNode_T bn) {
  return bn->keySuffix != NULL;
}

void BN_SetValue(BorderNode_T bn, KVKey_T key, const void *val) {
  if (KV_GetCharArraySize(key) >= keyslice_length) {
    BN_SetSuffixValue(bn,
                      KV_GetCharArray(key) + keyslice_length,
                      KV_GetCharArraySize(key) - keyslice_length,
                      val);
  }
  else {
    BN_SetPrefixValue(bn, KV_GetCharArraySize(key), val);
  }
}

const void* getValueOfPartialKey(const KVNode* node, const char* partialKey, size_t len);

KVKey_T KV_NewKey(const char* str, size_t len) {
  char* newStr = NULL;
  KVKey_T newKey = NULL;
  size_t i = 0;

  if (len > 0) {
    assert (str != NULL);

    newStr = (char*) surely_malloc (sizeof(char) * len);
    if (newStr == NULL) {
      return NULL;
    }

    for(i = 0; i < len; ++ i) {
      newStr[i] = str[i];
    }
  }

  newKey = (KVKey_T) surely_malloc (sizeof(KVKey));
  if (newKey == NULL) {
    free(newStr);
    return NULL;
  }

  newKey->str = newStr;
  newKey->len = len;

  return newKey;
}

KVKey_T KV_MoveKey(const char *str, size_t len) {
  KVKey_T newKey = NULL;

  if (len > 0) {
    assert (str != NULL);
  }

  newKey = (KVKey_T) surely_malloc(sizeof(KVKey));
  newKey->str = str;
  newKey->len = len;

  return newKey;
}

const char* KV_GetCharArray(KVKey_T key) {
  assert(key != NULL);
  return key->str;
}

size_t KV_GetCharArraySize(KVKey_T key) {
  assert(key != NULL);
  return key->len;
}

Bool KV_KeyEqual(KVKey_T key1, KVKey_T key2) {
  return UTIL_StrEqual(key1->str, key1->len, key2->str, key2->len);
}

void KV_FreeKey(KVKey_T key) {
  assert(key != NULL);
  free((void*) key->str);
  free(key);
}

/* Creates a new KVStore
 * Returns the KVStore on success. Returns NULL on failure. */
KVStore_T KV_NewKVStore(void) {
  KVStore_T store;
  KVNode* root;

  store = (KVStore_T) malloc(sizeof(KVStore));
  if(store == NULL) {
    return NULL;
  }

  root = newKVNode();
  if(root == NULL){
    free(store);
    return NULL;
  }

  store->rootNode = root;
  store->numKeys = 0;

  return store;
}

/* Return a new KVNode. Returns NULL on failure. */
KVNode* newKVNode() {
  KVNode* root;
  Relation_T tree;
  Cursor_T cursor;

  root = (KVNode *) malloc(sizeof(KVNode));
  if(root == NULL) {
    return NULL;
  }

  tree = RL_NewRelation();
  if(tree == NULL) {
    free(root);
    return NULL;
  }

  cursor = RL_NewCursor(tree);
  if(cursor == NULL) {
    free(root);
    RL_DeleteRelation(tree, NULL);
    return NULL;
  }

  root->cursor = cursor;
  root->tree = tree;

  return root;
}

/* Get the node's B+-tree's cursor. */
Cursor_T getNodeCursor(const KVNode* node) {
  return node->cursor;
}

/* Deletes the store. Frees values with a pointer to a call back function.
 * freeStore can be NULL. */
void KV_DeleteKVStore(KVStore_T store, void (* freeStore)(void *));

Bool KV_Put(KVStore_T kvStore, KVKey_T key, const void* value) {
  /* General insertion variables. */
  Bool putCompleted = False;
  const KVNode* currNode;
  Bool btreeStatus = False;
  Cursor_T btreeCursor;
  Relation_T btree;
  BorderNode_T borderNode;
  unsigned long nextKeySlice;
  KVNode* link;

  /* Variable to track suffix of key that shares prefix with this key.
   * to be reinserted. */
  KVKey_T sndKey = NULL;
  const void* sndValue = NULL;
  unsigned long sndKeySlice = 0;

  assert(kvStore != NULL);
  assert(key != NULL);
  /* str can be null only if len is 0. */
  assert(key->str != NULL || key->len == 0);

  assert(value != NULL);

  currNode = kvStore->rootNode;

  /* While we haven't inserted the current key*/
  while(putCompleted == False) {
    /* Get the current btree from the trie node and a cursor onto it. */
    btreeCursor = getNodeCursor(currNode);
    btree = currNode->tree;

    nextKeySlice = UTIL_GetNextKeySlice(key->str,
                                        UTIL_Min(KEY_SLICE_LENGTH, key->len));

    if (sndKey != NULL) {
      /* case 0: we have a second key, it means we even don't need to traverse the btree */
      /* as second key are only introduced by suffix conflict */
      sndKeySlice = UTIL_GetNextKeySlice(sndKey->str,
                                         UTIL_Min(KEY_SLICE_LENGTH, sndKey->len));

      if (nextKeySlice == sndKeySlice) {
        /* case 0.0: keyslices are the same */
        if(key->len <= KEY_SLICE_LENGTH || sndKey->len <= KEY_SLICE_LENGTH) {
          /* case 0.0.0: at least one key is not complete, no need for further pushing */
          borderNode = BN_NewBorderNode();
          BN_SetValue(borderNode, key, value);
          BN_SetValue(borderNode, key, sndValue);
          RL_PutRecord(btreeCursor, nextKeySlice, borderNode);
          /* In this branch of first if value put here then this was an insertion. */
          kvStore->numKeys++;

          putCompleted = True;
        }
        else {
          /* case 0.0.1: both are complete and the same, one more layer required */
          link  = newKVNode();
          assert(link != NULL);

          borderNode = BN_NewBorderNode();
          BN_SetLink(borderNode, link);
          /* insert the new bordernode. */
          RL_PutRecord(btreeCursor, nextKeySlice, borderNode);

          /* Update partial keys and lengths */
          key->str += KEY_SLICE_LENGTH;
          key->len -= KEY_SLICE_LENGTH;

          sndKey->len -= KEY_SLICE_LENGTH;
          sndKey->str += KEY_SLICE_LENGTH;

          /* point to the next layer. */
          currNode = link;
        }
      }
      else {
        /* case 0.1: keyslices are different */

        /* Put first partial key in its borderNode */
        borderNode = BN_NewBorderNode();
        BN_SetValue(borderNode, key, value);
        RL_PutRecord(btreeCursor, nextKeySlice, borderNode);

        /* Put second partial key in its borderNode */
        borderNode = BN_NewBorderNode();
        BN_SetValue(borderNode, sndKey, sndValue);
        RL_PutRecord(btreeCursor, sndKeySlice, borderNode);

        /* In this branch of first if value put here then this was an insertion. */
        kvStore->numKeys++;

        putCompleted = True;
      }
    }
    else {
      /* case 1: there isn't a second key, we need to check the btree */
      btreeStatus = RL_MoveToKey(btreeCursor, nextKeySlice);

      if(btreeStatus == False) {
        /* case 1.0: the keyslice is not in the btree, therefore we directly insert it */
        borderNode = BN_NewBorderNode();
        BN_SetValue(borderNode, key, value);
        RL_PutRecord(btreeCursor, nextKeySlice, borderNode);
        /* In this branch of first if value put here then this was an insertion. */
        kvStore->numKeys++;
      }
      else {
        /* case 1.1: the keyslice is in the btree */
        /* Get the bordernode. */
        borderNode = (BorderNode_T) RL_GetRecord(btreeCursor);

        if(key->len <= KEY_SLICE_LENGTH) {
          /* case 1.1.0: we are at the tail of the key */
          /* whatever it was, this means a overwrite action */
          /* FIXME: this could be a memory leak for client if not handled well */

          /* If the bordernode exists this may be an insert or an update. */
          if(BN_GetPrefixValue(borderNode, key->len) == NULL) {
            kvStore->numKeys++;
          }
          BN_SetPrefixValue(borderNode, key->len, value);

          putCompleted = True;
        }
        else {
          /* case 1.1.1: we still have more slices */

          /* now we need to know if there is a link or suffix/value at the bordernode */
          if (BN_HasLink(borderNode)) {
            /* case 1.1.0: there is a link to the next layer */
            /* suffix == NULL /\ value != NULL */
            key->str += KEY_SLICE_LENGTH;
            key->len -= KEY_SLICE_LENGTH;
            currNode = BN_GetLink(borderNode);
          }
          else if (BN_HasSuffix(borderNode)) {
            /* case 1.1.1: there is a suffix/value pair */
            /* suffix != NULL */

            if (BN_TestSuffix(borderNode, key)) {
              /* case 1.1.1.0: the two suffixs are the same */
              /* FIXME: overwrite */
              BN_SetSuffixValue(borderNode,
                                key->str + KEY_SLICE_LENGTH,
                                key->len - KEY_SLICE_LENGTH,
                                value);
              putCompleted = True;
            }
            else {
              /* case 1.1.1.1: two suffixs differ */
              sndValue = BN_ExportSuffixValue(borderNode, sndKey);

              /* Create new node for next layer */
              link = newKVNode();

              /* Set link BEWARE, this clears the suffix. */
              BN_SetLink(borderNode, link);

              /* update appropriate values and pointers. */
              key->str += KEY_SLICE_LENGTH;
              key->len -= KEY_SLICE_LENGTH;

              /* Move current node to lower layer. */
              currNode = link;
            }
          }
          else {
            /* case 1.1.2: there is nothing */
            /* suffix == NULL /\ value == NULL */
            BN_SetSuffixValue(borderNode,
                              key->str+ KEY_SLICE_LENGTH,
                              key->len - KEY_SLICE_LENGTH,
                              value);

            /* If no suffix, then this is an insert. */
            kvStore->numKeys++;

            putCompleted = True;
          }
          /* note that, it's impossible suffix != NULL and value == NULL,
           * but it's just user behavior */
        }
      }
    }
  }

  return True;
}

/* Returns the value of the key, if the key is in the kvStore. If the key is
 * not return NULL. */
const void* KV_Get(KVStore_T kvStore, KVKey_T key) {
  const char* totalKey;
  size_t totalKeyLength;

  assert(kvStore != NULL);
  assert(key != NULL);

  totalKey = key->str;
  totalKeyLength = key->len;

  return getValueOfPartialKey(kvStore->rootNode, totalKey, totalKeyLength);

}

/* Delete key from the kvStore. Return the key's value.*/
const void* KV_Delete(KVStore_T kvStore, KVKey_T key);

/* Get's at most num key-value pairs starting with the next key at or after key.
 * Returns an array of KVPair objects.
 * Stores the length of the array in resSize. */
struct KVPair* KV_GetRange(KVStore_T kvStore, KVKey_T key, size_t num, size_t* resSize);

/* Return the Number of Key in the kvStore */
size_t KV_NumKeys(KVStore_T kvStore) {
  assert(kvStore != NULL);
  return kvStore->numKeys;
}

/* Returns the value of the key, if the key is in the kvStore. If the key is
 * not return NULL. */
const void* getValueOfPartialKey(const KVNode* node, const char* partialKey, size_t len) {
  Cursor_T cursor;
  Relation_T btree;
  BorderNode_T borderNode;

  unsigned long keySlice;
  Bool btreeStatus;

  cursor = getNodeCursor(node);
  btree = node->tree;

  keySlice = UTIL_GetNextKeySlice(partialKey, (long) UTIL_Min(KEY_SLICE_LENGTH, len));
  btreeStatus = RL_MoveToKey(cursor, keySlice);

  /* If there is no bordernode responsible for this keyslice. Return NULL. */
  if(btreeStatus == False) {
    return NULL;
  }

  /* Get the bordernode. */
  borderNode = (BorderNode_T) RL_GetRecord(cursor);

  /* If partialkey is less than 8 bytes. return the associated value if there is one. */
  if(len <= KEY_SLICE_LENGTH) {
    return BN_GetPrefixValue(borderNode, len);
  }
  /* Else if there is a matching suffix return the value. If suffix does not
   * match or no suffix / link return NULL. If there is a link go to the next layer. */
  else {
    if (BN_HasLink(borderNode)) {
      return getValueOfPartialKey(BN_GetLink(borderNode),
                                  partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH);
    }
    else if (BN_HasSuffix(borderNode)) {
      return BN_GetSuffixValue(borderNode, partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH);
    }
    else {
      return NULL;
    }
  }
}

/* static void printKey(KVKey_T key) { */
/*   size_t i; */
/*   assert(key != NULL); */

/*   for(i = 0; i < key->len; i++) { */
/*     fprintf(stderr, "%lu: %d ", (unsigned long)i, (int)(key->str)[i]); */
/*   } */
/*   if(key->str == NULL) { */
/*     fprintf(stderr, "NULL KEY "); */
/*   } */
/*   fprintf(stderr, "len: %lu \n", (unsigned long) key->len); */

/* } */

/* void printKVStoreTreee (KVStore_T store) { */

/*   BorderNode_T** borderNodesByLayer; */

/*   borderNodesByLayer = (BorderNode_T**) calloc(10, sizeof(BorderNode_T*)); */

/* } */

/* void buildBorderNodes (KVNode* node, size_t layer, BorderNode_T** borderNodesByLayer) { */

/* } */
