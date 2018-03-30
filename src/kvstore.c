/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   kvstore.c
 * Author: Oluwatosin V. Adewale
 * 
 * Created on February 20, 2018, 11:45 PM
 */

#include "kvstore.h"
#include "relation.h"
#include "util.h"
#include "bordernode.h"
#include "kvstore_int.h"

#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>


/* Function declarations. */
static BorderNode_T putPartialKeyInBorderNode(BorderNode_T borderNode, 
        const char* partialKey, size_t len, const void* linkOrValue, 
        Bool isLink, Bool* newEntryCreated);
static const void* getValueOfPartialKey(const KVNode* node, const char* partialKey, 
        size_t len); 

static void printKey(KVKey_T key);


/* Type Definitions. */


KVKey_T KV_NewKey(const char* str, size_t len) {
    char* newStr = NULL;
    KVKey_T newKey = NULL;

    if (len > 0) {
        assert (str != NULL);
        
        newStr = (char*) malloc (sizeof(char) * len);
        if (newStr == NULL) {
            return NULL;
        }
        
        strncpy(newStr, str, len);

    }
    
    newKey = (KVKey_T) malloc (sizeof(KVKey));
    if (newKey == NULL) {
        free(newStr);
        return NULL;
    }
    
    newKey->str = newStr;
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
    size_t layerNum;
    Bool putCompleted = False;
    const KVNode* currNode;
    Bool btreeStatus = False;
    Cursor_T btreeCursor;
    Relation_T btree;
    BorderNode_T borderNode;
    unsigned long nextKeySlice;
    KVNode* link;
    
    /* Variables to track key we are currently inserting. */
    size_t partialKeyLength;
    const char* keyPtr = NULL;
    const char*  partialKeyPtr = NULL;
    
    /* Variable to track suffix of key that shares prefix with this key.
     * to be reinserted. */
    size_t sndPartialKeyLength = 0;
    const char* sndPartialKeyPtr = NULL; const char* sndTotalKeyPtr = NULL;
    const void* sndValue = NULL;
    unsigned long sndKeySlice = 0;
    
    assert(kvStore != NULL);
    assert(key != NULL); 
    /* str can be null only if len is 0. */
    assert(key->str != NULL || key->len == 0);
    
    assert(value != NULL);

    
    currNode = kvStore->rootNode;
    layerNum = 0;

    partialKeyLength = key->len;
    keyPtr = key->str;
    partialKeyPtr = key->str;
      
    /* While we haven't inserted the current key*/
    while(putCompleted == False) {
        
        const char* tempSuffix = NULL;
        size_t tempSuffixLength = 0;
        const char* partialKeySuffix = NULL;
        size_t partialKeySuffixLength = 0;
        BorderNodeEntry* tempBNEntry = NULL;
        Bool newEntryCreated = False;
        Bool test;
        
        /* Get the current btree from the trie node and a cursor onto it. */
        btreeCursor = getNodeCursor(currNode);
        btree = currNode->tree;
        
        nextKeySlice = UTIL_GetNextKeySlice(partialKeyPtr, 
                UTIL_Min(KEY_SLICE_LENGTH, partialKeyLength));
                
        btreeStatus = RL_MoveToKey(btreeCursor, nextKeySlice);
        
        if(btreeStatus == False) {
            borderNode = NULL;
            /* If only one key to insert then insert it. */
            if(sndPartialKeyPtr == NULL) {
                borderNode = putPartialKeyInBorderNode(NULL, partialKeyPtr, 
                        partialKeyLength, value, False, &newEntryCreated);
		RL_PutRecord(btreeCursor, nextKeySlice, 
                        borderNode);
                assert(btreeStatus == True);
                putCompleted = True;
                
                /* In this branch of first if value put here then this was an insertion. */
                kvStore->numKeys++;
            } 
            /* If two keys to insert...*/
            else {
                sndKeySlice = UTIL_GetNextKeySlice(sndPartialKeyPtr, 
                        UTIL_Min(KEY_SLICE_LENGTH, sndPartialKeyLength));
                
                /* if keyslices are same */ 
                if (nextKeySlice == sndKeySlice) {
                    /* If at least one of the key lengths are 8 bytes or less, then
                     * we can insert both of them into the borderNode. */
                    if(partialKeyLength <= 8 || sndPartialKeyLength <= 8) {
                        borderNode = putPartialKeyInBorderNode(NULL, partialKeyPtr,
                                partialKeyLength, value, False, &newEntryCreated);
                        borderNode = putPartialKeyInBorderNode(borderNode, 
                                sndPartialKeyPtr, sndPartialKeyLength,
                                sndValue, False, &newEntryCreated);

			RL_PutRecord(btreeCursor, nextKeySlice, 
                            borderNode);
                        assert(btreeStatus == True);

                        putCompleted = True;

                        /* In this branch of first if value put here then this was an insertion. */
                        kvStore->numKeys++;
                    }
                    else {
                        /* Create a new node for the next layer  and insert a link to
                         * that layer in the borderNode */
                        link  = newKVNode();
                        assert(link != NULL);

                        borderNode = putPartialKeyInBorderNode(NULL, partialKeyPtr,
                            KEY_SLICE_LENGTH, link, True, &newEntryCreated);

                        /* insert the new bordernode. */
			RL_PutRecord(btreeCursor, nextKeySlice, borderNode);
                        assert(btreeStatus == True);
                        
                        /* Update partial keys and lengths */
                        partialKeyPtr += KEY_SLICE_LENGTH;
                        sndPartialKeyPtr += KEY_SLICE_LENGTH;

                        partialKeyLength -= KEY_SLICE_LENGTH;
                        sndPartialKeyLength -= KEY_SLICE_LENGTH;
                        
                        /* point to the next layer. */
                        currNode = link;
                    }
                } 
                /* Else keyslices are different. Can insert partialkeys in separate bordernodes. */
                else {
                
                    /* Put first partial key in its borderNode */
                    borderNode = putPartialKeyInBorderNode(NULL, partialKeyPtr, 
                            partialKeyLength, value, False, &newEntryCreated);
		    RL_PutRecord(btreeCursor, nextKeySlice, 
                            borderNode);
                    assert(btreeStatus == True);

                    /* Put second partial key in its borderNode */
                    borderNode = putPartialKeyInBorderNode(NULL, sndPartialKeyPtr, 
                            sndPartialKeyLength, sndValue, False, &newEntryCreated);
		    RL_PutRecord(btreeCursor, sndKeySlice, 
                            borderNode);
                    assert(btreeStatus == True);

                    putCompleted = True;

                    /* In this branch of first if value put here then this was an insertion. */
                    kvStore->numKeys++;
                
                }
                
               
            }
        
        }
        /* Else this slice is in the B+-tree and has a bordernode. */
        else {
            /* Should not have a second key to insert if the key is in layer. */
            assert(sndPartialKeyPtr == NULL);
            /* Get the bordernode. */
            borderNode = (BorderNode_T) RL_GetRecord(btreeCursor);
            
            /* If the key we want to insert is 8 bytes or less. */
            if(partialKeyLength <= 8) {
               
                putPartialKeyInBorderNode(borderNode, partialKeyPtr,
                       partialKeyLength, value, False, &newEntryCreated); 
                
                putCompleted = True;
                
                /* If the bordernode exists this may be an insert or an update. */
                if(newEntryCreated == True) {
                    kvStore->numKeys++;
                }
            } 
            /* Else this key should be a link or suffix */
            else {
                tempBNEntry = BN_GetValue(borderNode, 9);
                tempSuffix = BN_GetSuffix(borderNode);
                tempSuffixLength = BN_GetSuffixLength(borderNode);

                /* If is link, continue to next layer */
                if(tempBNEntry != NULL && tempBNEntry->isLink == True) {
                    partialKeyPtr += KEY_SLICE_LENGTH;
                    partialKeyLength -= KEY_SLICE_LENGTH;
                    
                    currNode = tempBNEntry->linkOrValue.link;
                }                 
                /* If no suffix for this keyslice / borderNode. */
                else if (tempSuffix == NULL) {
                    putPartialKeyInBorderNode(borderNode, partialKeyPtr, 
                            partialKeyLength, value, False, &newEntryCreated);
                    putCompleted = True;
                    
                    /* If no suffix, then this is an insert. */
                    kvStore->numKeys++;
                } 
                /* If there is a suffix, compare it to the partialKey's suffix. */
                else {
                    
                    /* Should have a bn entry if there is a suffix. */
                    assert(tempBNEntry != NULL);
                    
                    partialKeySuffix = partialKeyPtr + KEY_SLICE_LENGTH;
                    partialKeySuffixLength = partialKeyLength - KEY_SLICE_LENGTH;
                    
                    test = UTIL_StrEqual(tempSuffix, BN_GetSuffixLength(borderNode),
                            partialKeySuffix, partialKeySuffixLength);
                    
                    /* if suffixes are the same. */
                    if (test == True) {
                        putPartialKeyInBorderNode(borderNode, partialKeyPtr,
                                partialKeyLength, value, False, &newEntryCreated);
                        putCompleted = True;
                    }
                    /* Else suffixes are different, */
                    else {
                        
                        /* Store the old value of the new snd partial key. */
                        tempBNEntry = BN_GetValue(borderNode, 9);
                        sndValue = tempBNEntry->linkOrValue.value;
                        
                        /* Create new node for next layer*/
                        link = newKVNode();
                        
                        /* Set link BEWARE, this clears the suffix. */
                        putPartialKeyInBorderNode(borderNode, partialKeyPtr, 
                                partialKeyLength, link, True, &newEntryCreated);
                        
                        
                        /* update appropriate values and pointers. */
                        partialKeyPtr += KEY_SLICE_LENGTH;
                        partialKeyLength -= KEY_SLICE_LENGTH;
                        
                        sndTotalKeyPtr = tempSuffix;
                        sndPartialKeyPtr = tempSuffix;
                        sndPartialKeyLength = tempSuffixLength;
   
                        
                        /* Move current node to lower layer. */
                        currNode = link;

                    }
                }
            }
        }
    }
    
    free((void*)sndTotalKeyPtr);

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





/* If borderNode is NULL, return a new BorderNode using the keyslice from the 
 * partialKey and len of the key.. 
 * 
 * The key's linkOrValue is either value for the total key or a link 
 * to the next layer.
 * 
 * If isLink is false, put this partial key's value in the borderNode. If the
 * partialkey is too long insert a copy of its suffix.  
 *
 * If isLink is true, the the link is added to the bordernode and the previous
 * key suffix is NOT freed. the partialKey and length of key are not used. 
 * 
 * If a new entry inserted, set newEntryCreated to true.
 */
static BorderNode_T putPartialKeyInBorderNode(BorderNode_T borderNode, const char* partialKey, 
        size_t len, const void* linkOrValue, Bool isLink, Bool* newEntryCreated) {
    
    unsigned long nextKeySlice;
    BorderNodeEntry* bnEntry = NULL;
    char* suffix = NULL;

    
    assert(partialKey != NULL || len == 0);
    assert(linkOrValue != NULL);
    
    /* Get the current btree from the trie node and a cursor onto it. */
    nextKeySlice = UTIL_GetNextKeySlice(partialKey, (long) UTIL_Min(KEY_SLICE_LENGTH, len));
    if(partialKey == NULL) {
        assert(nextKeySlice == 0);
    }
    
    /* We only create a new entry if we have to. */
    *newEntryCreated = False;
    
    /* If the there is no BorderNode create one for the key slice, then create 
     * one */
    if (borderNode == NULL) {
        borderNode = BN_NewBorderNode(nextKeySlice);
        assert(borderNode != NULL); 
    } 
    
    /* assert that this key belongs in the supplied border node */
    assert(BN_GetKeySlice(borderNode) == nextKeySlice);
    
    /* If inserting new link. */
    if (isLink == True) {
        bnEntry = BN_GetValue(borderNode, 9);
        
        /* If this bordernode entry is empty, create one. */
        if(bnEntry == NULL) {
            bnEntry = (BorderNodeEntry*) malloc(sizeof(BorderNodeEntry));
            assert(bnEntry != NULL);
            *newEntryCreated = True;
        }
        
        suffix = BN_GetSuffix(borderNode);
        BN_SetSuffix(borderNode, NULL, 0);
        
        /* Finally set the value. */
        bnEntry->isLink = isLink;
        bnEntry->linkOrValue.link = (KVNode*) linkOrValue;
        BN_SetValue(borderNode, 9, bnEntry);  
        
    }
    /* If current key 8 bytes or less. */
    else if (len  <= KEY_SLICE_LENGTH) {

        bnEntry = BN_GetValue(borderNode, len);

        /* If this bordernode entry is empty, create one. */
        if(bnEntry == NULL) {
            bnEntry = (BorderNodeEntry*) malloc(sizeof(BorderNodeEntry));
            assert(bnEntry != NULL);
            *newEntryCreated = True;
        }

        bnEntry->isLink = isLink;
        bnEntry->linkOrValue.value = (void*) linkOrValue;
        /* Update bordernode entry. */        
        BN_SetValue(borderNode, len, bnEntry);
    } 
    /* Else if greater than 8 bytes */
    else {
        bnEntry = BN_GetValue(borderNode, 9);

        /* If this bordernode entry is empty, create one. */
        if(bnEntry == NULL) {
            bnEntry = (BorderNodeEntry*) malloc(sizeof(BorderNodeEntry));
            assert(bnEntry != NULL);
            *newEntryCreated = True;
        }
           
        /* Else either insert new suffix and value or update old value. Assert 
         * that the older or updated suffix is the same as the new suffix.*/
        suffix = BN_GetSuffix(borderNode);
        
        /* If no suffix already, create one and insert it.*/
        if(suffix == NULL) {
            /* Create a new string to hold the suffix of the key. */
            suffix = (char *) malloc (sizeof(char) * len - KEY_SLICE_LENGTH);
            assert(suffix != NULL);
            memcpy(suffix, partialKey + KEY_SLICE_LENGTH, 
                    len - KEY_SLICE_LENGTH);
            /* Set the suffix. */
            BN_SetSuffix(borderNode, suffix, sizeof(char) * len - KEY_SLICE_LENGTH); 
        } 
        /* else If existing suffix, assert that the suffix is the same. */
        assert(UTIL_StrEqual(suffix, BN_GetSuffixLength(borderNode),
                partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH) == True);
        
        /*{
            printKey(KV_NewKey(suffix, BN_GetSuffixLength(borderNode)));
            printKey(KV_NewKey(partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH));
            if(suffix == NULL) {
                fprintf(stderr, "suffix is NULL.\n");
            }
            fprintf(stderr,"suffix length: %lu\n",(unsigned long) BN_GetSuffixLength(borderNode));
            fprintf(stderr,"keyslice: %lu\n",BN_GetKeySlice(borderNode));

            assert(0);
        }*/
        
        /* Finally set the value. */
        bnEntry->isLink = isLink;
        bnEntry->linkOrValue.value = linkOrValue;
        BN_SetValue(borderNode, 9, bnEntry);        
    }   
    
    /* Return the BorderNode */
    return borderNode;
}

/* Returns the value of the key, if the key is in the kvStore. If the key is 
 * not return NULL. */
static const void* getValueOfPartialKey(const KVNode* node, const char* partialKey, size_t len) {
    Cursor_T cursor;
    Relation_T btree;
    BorderNode_T borderNode;
    char * suffix;
    size_t suffixLength;
    BorderNodeEntry* bnEntry;
    Bool status;
    
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
        bnEntry = BN_GetValue(borderNode, len);
        if (bnEntry == NULL) {
            return NULL;
        } else {
            assert(bnEntry->isLink == False);
            return bnEntry->linkOrValue.value;
        }
    } 
    
    /* Else if there is a matching suffix return the value. If suffix does not
     * match or no suffix / link return NULL. If there is a link go to the next layer. */
    else {
        bnEntry = (BorderNodeEntry*) BN_GetValue(borderNode, 9);
        if(bnEntry == NULL) {
            return NULL;
        } else {            
            if(bnEntry->isLink == True) {
                return getValueOfPartialKey(bnEntry->linkOrValue.link, 
                        partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH);
            } else {
                suffix = BN_GetSuffix(borderNode);
                suffixLength = BN_GetSuffixLength(borderNode);
                
                status = UTIL_StrEqual(suffix, suffixLength, 
                        partialKey + KEY_SLICE_LENGTH, len - KEY_SLICE_LENGTH);
                if(status == True) {
                    return bnEntry->linkOrValue.value;
                } else {
                    return NULL;
                }
            }
        }
    }
        
}

static void printKey(KVKey_T key) {
    size_t i;
    assert(key != NULL);
        
    for(i = 0; i < key->len; i++) {
        fprintf(stderr, "%lu: %d ", (unsigned long)i, (int)(key->str)[i]);
    }
    if(key->str == NULL) {
        fprintf(stderr, "NULL KEY ");
    }
    fprintf(stderr, "len: %lu \n", (unsigned long) key->len);

}

void printKVStoreTreee (KVStore_T store) {
    
    BorderNode_T** borderNodesByLayer;
    
    borderNodesByLayer = (BorderNode_T**) calloc(10, sizeof(BorderNode_T*));
    
    
    
    

}

void buildBorderNodes (KVNode* node, size_t layer, BorderNode_T** borderNodesByLayer) {
    
}
