/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   kvstore.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on February 20, 2018, 11:45 PM
 */

#ifndef KVSTORE_H
#define KVSTORE_H

#include "util.h"
#include <stddef.h>


/* The KV Store's key type. */
typedef struct KVKey* KVKey_T;

/* A KVStore is a collection of key-value pairs. */
typedef struct KVStore* KVStore_T;

/* A KVPair is used when returning getRange results, which returns an array of
 * KVPairs. */
struct KVPair {
    /* copy of the key */
    KVKey_T key;
    /* value */
    const void* value;
};


/* Create an immutable KVKey from an array of characters str with length len 
 * and return it. On failure, return NULL. 
 * If len == 0 then an empty key is created. In this case str can be NULL. */
KVKey_T KV_NewKey(const char* str, size_t len);

/* same as KV_NewKey, but the string is not copied but rather moved
 */
KVKey_T KV_MoveKey(const char *str, size_t len);

/* Get the character array of the kvKey. If this is the empty string, return 
 * NULL;
 */
const char* KV_GetCharArray(KVKey_T key);

/* Get the size of the character array. If this is the empty string, return 0.*/
size_t KV_GetCharArraySize(KVKey_T key);

/* Compare both keys and return -1, 0 or 1 if key1 is less than, equal to or 
 * greater than key2. */
Bool KV_KeyEqual(KVKey_T key1, KVKey_T key2);

/* Free the key. */
void KV_FreeKey(KVKey_T key);


/* Creates a new KVStore
 * Returns the KVStore on success. Returns NULL on failure. */
KVStore_T KV_NewKVStore(void);

/* Deletes the store. Frees values with a pointer to a call back function.
 * freeStore can be NULL. */
void KV_DeleteKVStore(KVStore_T store, void (* freeStore)(void *));


/* Puts a copy of the key and its value into the relation. 
 * If the key already exists, update value. Values cannot be NULL.
 * Return True on success, False on failure. 
 * 
 * TODO: (handling failures here and elsewhere because of mem alloc issues.) */
Bool KV_Put(KVStore_T kvStore, KVKey_T key, const void* value);

/* Returns the value of the key, if the key is in the kvStore. If the key is 
 * not return NULL. */
const void* KV_Get(KVStore_T kvStore, KVKey_T key);

/* Delete key from the kvStore. Return the key's value.*/
const void* KV_Delete(KVStore_T kvStore, KVKey_T key);

/* Get's at most num key-value pairs starting with the next key at or after key.
 * Returns an array of KVPair objects. 
 * Stores the length of the array in resSize. */
struct KVPair* KV_GetRange(KVStore_T kvStore, KVKey_T key, size_t num, size_t* resSize);

/* Return the Number of Key in the kvStore */
size_t KV_NumKeys(KVStore_T kvStore);

#endif /* KVSTORE_H */
