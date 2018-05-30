/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/*
 * File:   bordernode.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on December 3, 2017, 7:37 PM
 */

#ifndef BORDERNODE_H
#define BORDERNODE_H

#include <stddef.h>
#include "util.h"
#include "kvstore.h"

/* A BorderNode hold keys and their values and/or points to a Relation
 * indexing the next slice of keys with similar prefixes. */
typedef struct BorderNode* BorderNode_T;

/* Create a new BorderNode.
 * TODO: This function invokes [surely_malloc], which will exit when malloc fail */
BorderNode_T BN_NewBorderNode();

/* Free a BorderNode.*/
void BN_FreeBorderNode(BorderNode_T bordernode);

/* Set the value of the key at idx i, where i \in [0, keyslice_length). */
void BN_SetPrefixValue(BorderNode_T bn, int i, const void* val);

/* Get the value of the key. */
const void *BN_GetPrefixValue(BorderNode_T bn, int i);

/* Set the suffix key, length and value.*/
void BN_SetSuffixValue(BorderNode_T bn, const char *suffix, const size_t len, const void *val);

/* note this function ignore the first keyslice_length characters */
Bool BN_TestSuffix(BorderNode_T bn, KVKey_T key);

/* Test whether the suffix is the same as the given one,
 * return value if successful, NULL otherwise */
const void *BN_GetSuffixValue(BorderNode_T bn, const char *suf, const size_t len);

const void *BN_ExportSuffixValue(BorderNode_T bn, KVKey_T key);

void BN_SetLink(BorderNode_T bn, void *val);

const void *BN_GetLink(BorderNode_T bn);

Bool BN_HasLink(BorderNode_T bn);

Bool BN_HasSuffix(BorderNode_T bn);

/* proposal: combine prefix and suffix set into one function */
void BN_SetValue(BorderNode_T bn, KVKey_T key, const void *val);


#endif /* BORDERNODE_H */
