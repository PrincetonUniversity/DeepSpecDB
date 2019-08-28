/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/*
 * File:   kvstore_int.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on March 10, 2018, 4:18 PM
 */

#ifndef KVSTORE_INT_H
#define KVSTORE_INT_H
#include "kvstore.h"
#include "relation.h"
#include "inttypes.h"

enum {KEY_SLICE_LENGTH = keyslice_length};

/* Type declarations */
typedef struct KVStore KVStore;
typedef struct KVNode KVNode;
typedef union LinkOrValue LinkOrValue;

/* The KV Store's key type. This is necessary because the store's keys are not
 * necessarily terminated with a null character, in fact some key's could have
 * multiple nul characters within the string.  */
typedef struct KVKey {
  /* Array of characters */
  const char* str;
  /* length of key*/
  size_t len;
} KVKey;

/* A KVStore is a collection of key-value pairs. It is implemented as a trie
 * of Nodes. Each node is a b+-tree that indexes an 8-byte portion of a search
 * key. */
struct KVStore {
  KVNode* rootNode;
  size_t numKeys;
};

/* A node consists of a B+-tree and a cursor that operates on that B+-tree.
 * Could modify implementation to have multiple cursors to support concurrency.
 * newKVNode() returns a new KVNode. getNodeCursor() returns the node's cursor.
 */
struct KVNode {
  Relation_T tree;
  Cursor_T cursor;
};

/* Some KVNode helper functions. */
Cursor_T getNodeCursor(const KVNode* node);
KVNode* newKVNode();

/* A link or value is a link to a node in the next layer or a value associated
 * with the current key. */
union LinkOrValue {
  const KVNode* link;
  const void* value;
};

#endif /* KVSTORE_INT_H */
