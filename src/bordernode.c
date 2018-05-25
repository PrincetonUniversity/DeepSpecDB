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
  void *prefixLinks[MAX_BN_SIZE];
  void *suffixLink;
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

void BN_SetPrefixValue(BorderNode_T bn, int i, void* val) {
  assert(i >= 0);
  assert(i < MAX_BN_SIZE);
  bn->prefixLinks[i] = val;
}

void* BN_GetPrefixValue(BorderNode_T bn, int i) {
  assert(i >= 0);
  assert(i < MAX_BN_SIZE);
  return bn->prefixLinks[i];
}

void BN_SetSuffixValue(BorderNode_T bn, char* suf, size_t len, void *val) {
  if (bn->keySuffix != NULL) {
    free(bn->keySuffix);
  }

  bn->keySuffix = (char *) surely_malloc(sizeof(char) * len);
  for (size_t i = 0; i < len; ++ i) {
    bn->keySuffix[i] = suf[i];
  }
  bn->keySuffixLength = len;
  bn->suffixLink = val;
}

Bool BN_HasSuffix(BorderNode_T bn) {
  return bn->keySuffix != NULL;
}

void *BN_GetSuffixValue(BorderNode_T bn, char* suf, size_t len) {
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
