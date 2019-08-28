/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   btreecomplexity.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on April 17, 2018, 7:34 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>
#include <string.h>

#include "relation.h"
#include "kvstore.h"

/*
 * Simple C Test Suite
 */

static int compareInt(const void* first, const void* second){
    int iFirst = *((int*)first);
    int iSecond = *((int*)second);
    
    if (iFirst < iSecond) {
        return -1;
    } else if (iFirst > iSecond) {
        return +1;
    } else {
        return 0;
    }
}

/* Return the time it takes to traverse a relation of numKeys keys in order. */
static double timeSequentialGets(int numKeys) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;

    
    bTree= RL_NewRelation();
    cursor = RL_NewCursor(bTree);
    
    for(i = 0; i < numKeys; i++) {
        RL_PutRecord(cursor, i, NULL);
    }
    
    begin = clock();
    
    RL_MoveToFirst(cursor);
    for(i = 0; i < numKeys - 1; i++) {
        RL_MoveToNext(cursor);
    }
    end = clock();
    
    RL_DeleteRelation(bTree, NULL);
    RL_FreeCursor(cursor);
    
    return (double) (end - begin) / CLOCKS_PER_SEC;  
}

/* Return the time it visit the first and last key numkeys number of times. 
 * The relation is of size numkeys. Alternates between first and last key based
 * on parity of current iteration. */
static double timeAlternateGets(int numKeys) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;

    int* testKeys;
    
    testKeys = (int*) calloc(numKeys, sizeof(int));
    assert(testKeys != NULL);
    
    bTree= RL_NewRelation();
    cursor = RL_NewCursor(bTree);
    
    
    for(i = 0; i < numKeys; i++) {
        RL_PutRecord(cursor, i, NULL);
        testKeys[i] = i;
    }
        
    begin = clock();
    for(i = 0; i < numKeys; i++) {
        if(i%2 == 0) {
            RL_MoveToKey(cursor, testKeys[0]);
        } else {
            RL_MoveToKey(cursor, testKeys[numKeys - 1]);
        }
    }
    end = clock();
    
    RL_DeleteRelation(bTree, NULL);
    RL_FreeCursor(cursor);
    
    free(testKeys);
    
    return (double) (end - begin) / CLOCKS_PER_SEC;  
}


/* Return the time it takes to traverse a relation of size numkeys in a 
 * partially random order. A random sequence of the keys are generated. This sequence
 * is partially sorted in batches of size interval.  */
static double timePartiallySortedGets(int numKeys, int interval) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;
    int* testKeys;

    
    assert(numKeys > 0);
    assert(interval >= 0);

    
    testKeys = (int*) calloc(numKeys, sizeof(int));
    assert(testKeys != NULL);
    
    bTree= RL_NewRelation();
    cursor = RL_NewCursor(bTree);
    
    for(i = 0; i < numKeys; i++) {
        testKeys[i] = i;
        RL_PutRecord(cursor, testKeys[i], NULL);
    }
         
    UTIL_Shuffle(testKeys, numKeys);

    i = 0;
    while(interval != 0 && i < numKeys) {
        int numElem = UTIL_Min(interval, numKeys - i); 
        qsort(testKeys+i, numElem, sizeof(int), compareInt);
        i += numElem;
    }
         
    begin = clock();
    for(i = 0; i < numKeys; i++) {
        RL_MoveToKey(cursor, testKeys[i]);
    }
    end = clock();
    
    RL_DeleteRelation(bTree, NULL);
    RL_FreeCursor(cursor);
    
    free(testKeys);
    
    return (double) (end - begin) / CLOCKS_PER_SEC;  
}

/* Return the time it takes to sequentially insert the numKeys keys from 0 to 
 * numKeys - 1. */
static double timeSequentialInsertions(int numKeys) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;

    
    bTree= RL_NewRelation();
    cursor = RL_NewCursor(bTree);
    
    begin = clock();
    for(i = 0; i < numKeys; i++) {
        RL_PutRecord(cursor, i, NULL);
    }
    end = clock();
    
    RL_DeleteRelation(bTree, NULL);
    RL_FreeCursor(cursor);
    
    return (double) (end - begin) / CLOCKS_PER_SEC;  
}

/* Return the time it takes to insert the keys between 0 and numKeys - 1
 * partially random order. A random sequence of the keys are generated. 
 * This sequence is partially sorted in batches of size interval.  */
static double timePartiallySortedInsertions(int numKeys, int interval) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;
    int* testKeys;

    
    assert(numKeys > 0);
    assert(interval >= 0);

    
    testKeys = (int*) calloc(numKeys, sizeof(int));
    assert(testKeys != NULL);
    
    bTree= RL_NewRelation();
    cursor = RL_NewCursor(bTree);
    
    for(i = 0; i < numKeys; i++) {
        testKeys[i] = i;
    }
         
    UTIL_Shuffle(testKeys, numKeys);

    i = 0;
    while(interval != 0 && i < numKeys) {
        int numElem = UTIL_Min(interval, numKeys - i);  
        qsort(testKeys+i, numElem, sizeof(int), compareInt);
        i += numElem;
    }
         
    begin = clock();
    for(i = 0; i < numKeys; i++) {
        RL_PutRecord(cursor, testKeys[i], NULL);
    }
    end = clock();
    
    RL_DeleteRelation(bTree, NULL);
    RL_FreeCursor(cursor);
    
    free(testKeys);
    
    return (double) (end - begin) / CLOCKS_PER_SEC;  
}

static char* generateRandomKey (int keyLength, int prefixLength) {
    
    int i;
    char* key;
    assert(prefixLength <= keyLength);
    
    key = (char *) calloc(keyLength, sizeof(char));
    assert(key != NULL);
    
    for(i = prefixLength; i < keyLength; i++) {
        key[i] = rand() % sizeof(char);
    }
    
    return key;
}

/* Create a kvstore with numKeys number of keys each of length keyLength, sharing
 * a common prefix of prefix length prefixLength. return the time it takes to
 * get all keys in a partially sorted order. Random sequence of gets generated
 * and sorted in batches of interval.
*/
static double timeKVStoreGets(int numKeys, int keyLength, int prefixLength, int interval) {
    KVStore_T store;
    int i;
    int * testKeyIndices;
    KVKey_T *  testKeys;
    char** testStr;
    
    clock_t begin, end;

    assert(numKeys > 0); assert(keyLength >= 1); 
    assert(prefixLength <= keyLength); assert(interval >= 0);
    
    store= KV_NewKVStore();
    assert(store != NULL);
    
    testKeyIndices = (int*) calloc(numKeys, sizeof(int));
    assert(testKeyIndices != NULL);
    
    testStr = (char**) calloc(numKeys, sizeof(char*));
    assert(testStr != NULL);
    
    testKeys = (KVKey_T*) calloc(numKeys, sizeof(KVKey_T));
    assert(testKeys != NULL);
    
    /*initialize testkeyindices*/
    
    for(i = 0; i < numKeys; i++) {
        testKeyIndices[i] = i;
    }
    
    /* Generate random keys*/
    for(i = 0; i < numKeys; i++) {
        testStr[i] = generateRandomKey(keyLength, prefixLength);
        testKeys[i] = KV_NewKey(testStr[i], keyLength);
        KV_Put(store, testKeys[i], testKeys[i]);
    }
    
    UTIL_Shuffle(testKeyIndices, numKeys);

    i = 0;
    while(interval != 0 && i < numKeys) {
        int numElem = UTIL_Min(interval, numKeys - i); 
        qsort(testKeyIndices+i, numElem, sizeof(int), compareInt);
        i += numElem;
    }
    
    begin = clock();
    for(i = 0; i < numKeys; i++) {
        /*iterate through all test keys using order of */
        KV_Get(store, testKeys[testKeyIndices[i]]);
    }
    end = clock();
    
    for(i = 0; i < numKeys; i++){
        free(testStr[i]);
        KV_FreeKey(testKeys[i]);
    }
    
    free(testKeys);
    free(testKeyIndices);
    free(testStr);
    
    /* Would have freed kvstore but KV_DeleteKVStore not implemented yet.*/

    return (double) (end - begin) / CLOCKS_PER_SEC;  
}


static void runBtreeExperiments(){
    
    double secondsTaken;
    int startNumKeys = 500000;
    int step = 500000;
    int numKeys = startNumKeys;
    int i,j, iterations = 10;
    
    
    fprintf(stderr, "\n\nBtree Time Complexity Experiments. %d iterations per experiment", iterations);

    
    fprintf(stderr, "\nTiming btree traversals for different number of keys\n");

    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeSequentialGets(numKeys);
        }
        fprintf(stderr, "Traversal %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
        
    fprintf(stderr, "\nTiming btree partially sorted gets for different number of keys\n");
    fprintf(stderr, "Sorted intervals of FANOUT: %d gets for different number of keys\n", FANOUT);
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedGets(numKeys, FANOUT);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted gets for different number of keys\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 100. Gets for different number of keys\n");
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedGets(numKeys, numKeys / 100 );
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted gets for different number of keys\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 1000. Gets for different number of keys\n");
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedGets(numKeys, numKeys / 1000 );
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree random gets for different number of keys\n");
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedGets(numKeys, 0);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree Alternate (first/last) gets for different number of keys\n");
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeAlternateGets(numKeys);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    

    fprintf(stderr, "\nTiming sequential btree Insertions for different number of keys\n");

    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeSequentialInsertions(numKeys);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted Insertions for different number of keys\n");
    fprintf(stderr, "Sorted intervals of FANOUT: %d Insertions for different number of keys\n", FANOUT);
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedInsertions(numKeys, FANOUT);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted Insertions for different number of keys\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 100. Insertions for different number of keys\n");
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedInsertions(numKeys, numKeys / 100 );
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted Insertions for different number of keys\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 1000. Insertions for different number of keys\n");
    
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedInsertions(numKeys, numKeys / 1000 );
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming btree random Insertions for different number of keys\n");
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timePartiallySortedInsertions(numKeys, 0);
        }
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
}


static void runKVStoreExperiments(){
    
    double secondsTaken;
    int startNumKeys = 500000;
    int step = 250000;
    int numKeys, prefixLength, keyLength;
    int i,j, iterations = 11;
    
    
    fprintf(stderr, "\n\n KVStore Time Complexity Experiments. %d iterations per experiment", iterations);
    
    
    numKeys = 100;
    keyLength = 100;
    prefixLength = 0;
    fprintf(stderr, "\nTiming KVStore random gets for keys of length %d and common prefix length of size %d\n", keyLength, prefixLength);
    
    while(numKeys < 1000000){
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeKVStoreGets(numKeys, keyLength, prefixLength, 0);
        }
        fprintf(stderr, "%d Keys took %0.2f milliseconds\n", numKeys, (secondsTaken/10) * 1000);
        numKeys *= 10;
    }
    
    numKeys = 100;
    keyLength = 100;
    prefixLength = 80;
    fprintf(stderr, "\nTiming KVStore random gets for keys of length %d and common prefix length of size %d\n", keyLength, prefixLength);
    
    while(numKeys < 1000000){
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeKVStoreGets(numKeys, keyLength, prefixLength, 0);
        }
        fprintf(stderr, "%d Keys took %0.2f milliseconds\n", numKeys, (secondsTaken/10) * 1000);
        numKeys *= 10;
    }
    
    numKeys = 100;
    keyLength = 30;
    prefixLength = 0;
    
    fprintf(stderr, "\nThe following tests have keys of length %d and prefixLength %d\n", 
            keyLength, prefixLength);
    
    fprintf(stderr, "\nTiming KVStore random gets for different number of keys\n");
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeKVStoreGets(numKeys, keyLength, prefixLength, 0);
        }
        fprintf(stderr, "Traversal %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    fprintf(stderr, "\nTiming KVStore sequential gets for different number of keys\n");
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeKVStoreGets(numKeys, keyLength, prefixLength, numKeys);
        }
        fprintf(stderr, "Traversal %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
    
    
    fprintf(stderr, "\nTiming KVStore partially sorted gets for different number of keys\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 100. Gets for different number of keys\n");
    numKeys = startNumKeys;
    for(i = 0; i < iterations; i++) {
        secondsTaken = 0;
        for(j = 0; j < 10; j++){
            secondsTaken+=timeKVStoreGets(numKeys, keyLength, prefixLength, numKeys / 100);
        }
        fprintf(stderr, "Traversal %d %d Keys took %0.2f milliseconds\n", i, numKeys, (secondsTaken/10) * 1000);
        numKeys += step;
    }
}




int main(int argc, char** argv) {
       
    if (argc >= 2) {
        if(strcmp(argv[1], "btree") == 0) {
            runBtreeExperiments();
        }
        else if(strcmp(argv[1], "kvstore") == 0) {
            runKVStoreExperiments();
        } else {
            fprintf(stderr, "Usage: ./btreecomplexity [btree | kvstore]\n");
            return EXIT_FAILURE;
        }
    } else {    
        runBtreeExperiments();
        runKVStoreExperiments();
    }
  
    return 0;
}
