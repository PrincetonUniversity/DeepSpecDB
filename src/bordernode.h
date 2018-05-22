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

/* A BorderNode hold keys and their values and/or points to a Relation
 * indexing the next slice of keys with similar prefixes. */
typedef struct BorderNode* BorderNode_T;

/* Create a new BorderNode.
 * TODO: This function invokes [surely_malloc], which will exit when malloc fail */
BorderNode_T BN_NewBorderNode();

/* Free a BorderNode.*/
void BN_FreeBorderNode(BorderNode_T bordernode);

/* Set the value of the key at idx i, where i \in [0, keyslice_length). */
void BN_SetPrefixValue(BorderNode_T bn, int i, void* val);

/* Get the value of the key. */
void* BN_GetPrefixValue(BorderNode_T bn, int i);

/* Set the suffix key, length and value.*/
void BN_SetSuffixValue(BorderNode_T bn, char* suf, size_t len, void *val);

/* Test whether the bordernode has a value corresponding to a suffix. */
Bool BN_HasSuffix(BorderNode_T bn);

/* Test whether the suffix is the same as the given one,
 * return value if successful, NULL otherwise */
void *BN_GetSuffixValue(BorderNode_T bn, char *suf, size_t len);

#endif /* BORDERNODE_H */
