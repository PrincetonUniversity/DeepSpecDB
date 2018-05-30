/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/*
 * File:   bordernode.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on December 3, 2017, 7:37 PM
 */

#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "bordernode.h"
#include "inttypes.h"
#include "surely_malloc.h"

/* Maximum number of keys in a BorderNode */
enum {MAX_BN_SIZE = keyslice_length};
/* /\* Key length to denote that a key has a suffix *\/ */
/* enum {KEYSUFFIX_KEYLENGTH = 64}; */
/* /\* Key length to denote that a key is just an intermediary layer and points */
/*  * to a next layer. *\/ */
/* enum {LAYER_KEYLENGTH = 128}; */

/* BorderNodes can hold different keys belonging to a key slice. For each key,
 * there is a value. At most one key has a suffix or a link to the next layer.*/
/* struct BorderNode { */
/*   /\* The keySlice all the keys in this node are composed from *\/ */
/*   unsigned long keySlice; */
/*   /\* Link to next layer or value of key. 10th key(idx 9) has suffix and value */
/*    * or link to next layer.*\/ */
/*   void* val[MAX_BN_SIZE]; */
/*   /\* Length of the key suffix. *\/ */
/*   size_t keySuffixLength; */
/*   /\* keySuffix string, if last key has suffix. Else, keySuffix is NULL, */
/*    * if key points to next layer.*\/ */
/*   char* keySuffix; */
/* }; */

/* modeified version of [BorderNode], the differences and reason are:
 * 1. remove the keyslice field, as it's used in nowhere
 * 2. split the [val] array, and rename into [prefixLinks] and [suffixLink]
 */
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
  return UTIL_StrEqual(KV_GetCharArray(key) + keyslice_length,
                       KV_GetCharArraySize(key) - keyslice_length,
                       bn->keySuffix, bn->keySuffixLength);
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
  key = KV_NewKey(bn->keySuffix, bn->keySuffixLength);
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
