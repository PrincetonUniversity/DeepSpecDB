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
#include "relation.h"
#include <assert.h>

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

/* Return the time it takes to traverse a relation of numKeys keys*/
static double timeNext(int numKeys) {
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

/* Return the time it takes to traverse a relation of numKeys keys*/
static double timeRandomGets(int numKeys) {
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
    
    
    UTIL_Shuffle(testKeys, numKeys);
    
    
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


/* Return the time it takes to traverse a relation of p keys*/
static double timePartiallySortedGets(int numKeys, int interval) {
    Relation_T bTree;
    Cursor_T cursor;
    int i;
    clock_t begin, end;
    
    assert(numKeys > 0);
    assert(interval > 0);

    int* testKeys;
    
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
    while(i < numKeys) {
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
static double timePut(int numKeys) {
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




int main(int argc, char** argv) {
    
    double secondsTaken;
    int numKeys = 1000;
    int i, iterations = 13;
    
    fprintf(stderr, "\nTiming btree traversals for different key sizes\n");

    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timeNext(numKeys);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
        
    fprintf(stderr, "\nTiming btree partially sorted gets for different key sizes\n");
    fprintf(stderr, "Sorted intervals of FANOUT: %d gets for different key sizes\n", FANOUT);
    
    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timePartiallySortedGets(numKeys, FANOUT);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted gets for different key sizes\n");
    fprintf(stderr, "Sorted intervals of 2 * FANOUT: %d gets for different key sizes\n", 2*FANOUT);
    
    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timePartiallySortedGets(numKeys, 2*FANOUT);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted gets for different key sizes\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 100. Gets for different key sizes\n");
    
    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timePartiallySortedGets(numKeys, numKeys / 100);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    fprintf(stderr, "\nTiming btree partially sorted gets for different key sizes\n");
    fprintf(stderr, "Sorted intervals of Numkeys / 1000. Gets for different key sizes\n");
    
    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timePartiallySortedGets(numKeys, numKeys / 1000);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    fprintf(stderr, "\nTiming btree random gets for different key sizes\n");

    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timeRandomGets(numKeys);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    fprintf(stderr, "\nTiming sequential btree insertions for different key sizes\n");

    numKeys = 1000;
    for(i = 0; i < iterations; i++) {
        secondsTaken = timePut(numKeys);
        fprintf(stderr, "Iteration %d %d Keys took %0.2f milliseconds\n", i, numKeys, secondsTaken*1000);
        numKeys = numKeys * 2;
    }
    
    return 0;
    
    
   
    /*
    printf("%%SUITE_STARTING%% btreecomplexity\n");
    printf("%%SUITE_STARTED%%\n");

    printf("%%TEST_STARTED%% test1 (btreecomplexity)\n");
    test1();
    printf("%%TEST_FINISHED%% time=0 test1 (btreecomplexity) \n");

    printf("%%TEST_STARTED%% test2 (btreecomplexity)\n");
    test2();
    printf("%%TEST_FINISHED%% time=0 test2 (btreecomplexity) \n");

    printf("%%SUITE_FINISHED%% time=0\n");
    */

    return (EXIT_SUCCESS);
}
