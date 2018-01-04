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

/* Maximum number of keys in a BorderNode */
enum {MAX_BN_SIZE = 10};
/* Key length to denote that a key has a suffix */
enum {KEYSUFFIX_KEYLENGTH = 64};
/* Key length to denote that a key is just an intermediary layer and points
 * to a next layer. */
enum {LAYER_KEYLENGTH = 128};


/* BorderNodes can hold different keys belonging to a key slice. For each key, 
 * there is a value. At most one key has a suffix or a link to the next layer.*/
struct BorderNode {
    /* The keySlice all the keys in this node are composed from */
    unsigned long keySlice;
    /* Link to next layer or value of key. 10th key(idx 9) has suffix and value 
     * or link to next layer.*/
    void* val[MAX_BN_SIZE];
    /* keySuffix string, if last key has suffix. Else, keySuffix is NULL, 
     * if key points to next layer.*/
    char* keySuffix;
};


BorderNode_T BN_NewBorderNode(unsigned long keyslice) {

    BorderNode_T bordernode = 
            (struct BorderNode*) malloc(sizeof(struct BorderNode));

    if (bordernode == NULL)
        return bordernode;
    
    memset(bordernode->val, 0, MAX_BN_SIZE * sizeof(void*));
    bordernode->keySlice = keyslice;    
    
    return bordernode;
}

void BN_FreeBorderNode(BorderNode_T bordernode) {
    if (bordernode == NULL)
        return;
    
    if (bordernode->keySuffix)
        free(bordernode->keySuffix);
    
    free(bordernode);
    
    return;
}


char* BN_GetKeySlice(BorderNode_T bn) {
    return bn->keySlice;
}

void BN_SetValue(BorderNode_T bn, int i, void* val) {
    assert(i >= 0);
    assert(i < 10);
    bn->val[i] = val;
}

void* BN_GetValue(BorderNode_T bn, int i) {
    assert(i >= 0);
    assert(i < 10);
    return bn->val[i];
}

void BN_SetSuffix(BorderNode_T bn, char* suf) {
    bn->keySuffix = suf;
}

char* BN_GetSuffix(BorderNode_T bn) {
    return bn->keySuffix;
}

