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

/* A BorderNode hold keys and their values and/or points to a Relation 
 * indexing the next slice of keys with similar prefixes. */
typedef struct BorderNode* BorderNode_T;

/* Create a new BorderNode. Returns the new BorderNode if successful, otherwise
 * returns NULL. All values and the suffix are set to NULL. */
BorderNode_T BN_NewBorderNode(unsigned long keyslice);

/* Free a BorderNode.*/
void BN_FreeBorderNode(BorderNode_T bordernode);

/* Get the keySlice associated with this bordernode. */
unsigned long BN_GetKeySlice(BorderNode_T bn);

/* Set the value of the key at idx i. i must be between 0 and 9. */
void BN_SetValue(BorderNode_T bn, int i, void* val);

/* Get the value of the key. */
void* BN_GetValue(BorderNode_T bn, int i);

/* Set the suffix for key at idx 9 and its length.*/
void BN_SetSuffix(BorderNode_T bn, char* suf, size_t len);

/* Get the suffix of the key at idx 9. */
char* BN_GetSuffix(BorderNode_T bn);

/* Get the length of the suffix of the key at idx 9. */
size_t BN_GetSuffixLength(BorderNode_T bn);


#endif /* BORDERNODE_H */
