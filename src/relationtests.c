/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relationtests.c
 * Author: Oluwatosin V. Adewale
 *
 * 
 *  Rough Behavioral Tests.
 * 
 * Created on November 7, 2017, 7:57 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "relation.h"
#include "relapps.h"
#include "bordernode.h"

static void testGetAndGetNext(unsigned long* testArr, Bool* isInserted,
        int arrSize, Cursor_T testCursor, Relation_T relation);
static int findIdx(unsigned long key, unsigned long* arr, int arrSize);

static void printRelationKeys(Cursor_T cursor){
    Bool status = True;
    unsigned long key;
    
    if(RL_MoveToFirst(cursor)) {
        printf("Printing Keys: ");
        while(status) {
            key = RL_GetKey(cursor);
            printf("%lu ", key);
            status = RL_MoveToNextValid(cursor);
        }
        printf("\n");
    }
} 

static void tests(void) {
    enum {TEST_SIZE = 2800};
    enum {NUM_VALUES = 5000};
    
    Relation_T testRelation = RL_NewRelation();
    Cursor_T testCursor = RL_NewCursor(testRelation);
    /*Cursor_T printCursor = RL_NewCursor(testRelation);*/
    
    unsigned long i;
    unsigned long *test_values;
    unsigned long *testIdx;
    Bool *isInserted;
    int count = 0, numRecords = 0;
    Bool status;
    int res = 0;
    void** freeArr;
    /* move and put should behave diff on empty and non empty record, take you 
     close to the desired key assert check here and change code in move and put*/
    assert(RL_MoveToKey(testCursor, (unsigned long) 0) == False);
    assert(RL_CursorIsValid(testCursor) == False);
    
    test_values = (unsigned long *) malloc (NUM_VALUES * sizeof(unsigned long));
    testIdx = (unsigned long *) malloc (NUM_VALUES * sizeof(unsigned long));
    isInserted = (Bool*) calloc(TEST_SIZE, sizeof(Bool));
    freeArr = malloc(NUM_VALUES * sizeof(void*));
    
    for (i = 0; i < NUM_VALUES; i++) {
        test_values[i] = (unsigned long) i;
    }
    
    /* Try putting duplicate keys. 
       NUM_VALUES should be greater than Test_SIZE. */
    while(count <  NUM_VALUES) {
        unsigned long temp;
        i = rand() % TEST_SIZE;
        
        
        /* printf("%d: Putting key <%lu> with value %lu\n", count, i, test_values[i]); */

        RL_PutRecord(testCursor, i, &test_values[i]);

	/* RL_PrintTree(testRelation); */
	/* RL_PrintCursor(testCursor); */
	/* printf("\n\n"); */
	
        if(isInserted[i] == False) {
            numRecords++;
            isInserted[i] = True;
        }
	/* printf("%d / %d keys\n\n\n",(int) (RL_NumRecords(testCursor)),numRecords); */
        /* temp = *(unsigned long *)RL_GetRecord(testCursor); */
        /* assert(temp == test_values[i]); */
	/* this does not work anymore because RL_PutRecord moves the cursor to the next position */

        testIdx[count] = i;
        count++;
	
    }

    /* I have a bug here. At count=5088, i=9. But 9 is already in the tree 
     * relation->numRecords does not change (good). But numRecords change, as if isInserted[9] was false
     * but it should be True. This also happens later 
     * This probably means that an array is out of bound somewhere, or that a null pointer has been dereferenced */

    RL_PrintTree(testRelation);
    RL_PrintCursor(testCursor);

    printf("%d / %d keys\n",(int) (RL_NumRecords(testCursor)),numRecords);

    
    assert (True == False);
    assert(numRecords == (int) (RL_NumRecords(testCursor)));
    
    for (i = 0; i < TEST_SIZE; i++) {
        RL_MoveToKey(testCursor, testIdx[i]);
        /* printf("Key: %lu Record: %lu\n", testIdx[i], *((unsigned long *) RL_GetRecord(testCursor)));*/
    }
    printf("RL_MoveToKey successful\n");
    
    status = RL_MoveToFirst(testCursor);
    assert(status);

    printf("RL_MoveToFirst successful\n");
    assert (False == True); 	/* stopping here for now */
    
    /* printf("\nPrinting In order.\n"); */
    while(status){
        /* printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor)));*/
        status = RL_MoveToNextValid(testCursor);
    }
    /* printf("\nFinished In order.\n"); */
    
    
    printf("\nPut and get from 0 to %d\n", TEST_SIZE -1);
    for (i = 0; i < TEST_SIZE; i++) {
        RL_PutRecord(testCursor, i, &test_values[i]);
    }
    
    for (i = 0; i < TEST_SIZE; i++) {
        RL_MoveToKey(testCursor, i);
        /* printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor))); */
    }
    
    /* printf("\nPrint in order %d\n", TEST_SIZE -1); */
    status = RL_MoveToFirst(testCursor);
    assert(status);
    
    while(status){
        /* printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor)));*/
        status = RL_MoveToNextValid(testCursor);
    }

    fprintf(stderr, "\nTesting That RL_MoveToKey properly tracks ancestors\n");
    
    for(i = TEST_SIZE; i == 0; i--) {
        unsigned long prev, curr;
        RL_MoveToKey(testCursor, test_values[i-1]);
        prev = *(unsigned long *)RL_GetRecord(testCursor);
        assert(prev == test_values[i-1]);
         
        status = RL_MoveToNextValid(testCursor);
        while(status) {
            curr = *(unsigned long *)RL_GetRecord(testCursor);
            assert(prev < curr);
            prev = curr;
            status = RL_MoveToNextValid(testCursor);
        }   
    }
    

    fprintf(stderr, "\nTesting That RL_PutRecord properly tracks ancestors\n");
    count = 0;
    for(i = TEST_SIZE; i > 0; i--) {   
        unsigned long prev, curr;
        unsigned long *pRandNum;
        
        pRandNum = (unsigned long *) malloc(sizeof(unsigned long));
        freeArr[i] = (void*) pRandNum;
        count++;
        *pRandNum = rand() % (TEST_SIZE * 3);
                     
        RL_PutRecord(testCursor, *pRandNum, pRandNum);
        prev = *(unsigned long *)RL_GetRecord(testCursor);
        
        if(prev != *pRandNum)
            printf("%lu %lu", prev, *pRandNum);
        assert(prev == *pRandNum);    
        
        status = RL_MoveToNextValid(testCursor);
        while(status) {
            curr = *(unsigned long *)RL_GetRecord(testCursor);
            assert(prev < curr);
            prev = curr;
            status = RL_MoveToNextValid(testCursor);
        }     
    }
    
    fprintf(stderr, "\nDone with Basic RL Tests\n\n");

    RL_FreeCursor(testCursor);
    RL_DeleteRelation(testRelation, NULL);
    
    free(test_values);
    free(testIdx);
    free(isInserted);
    
    for(i = 0; i < (unsigned long) count; i++) {
        free(freeArr[i]);
    }
    free(freeArr);          
}

/* In order traversal test */
void in_order_test(char* infilename, char* outfilename) {
    char temp[100];
    int count;
    Bool status; 
    FILE* outfile = fopen(outfilename, "w");
    FILE* infile = fopen(infilename, "r");
    Relation_T testRelation = RL_NewRelation();
    Cursor_T testCursor = RL_NewCursor(testRelation);
    
    while (fgets(temp,100, infile) != NULL) {
        char* word = malloc(sizeof(char) * (strlen(temp) + 1));
        int scanfReturn;
        scanfReturn = sscanf(temp,"%s %d",word, &count);
        if (scanfReturn == 2) {
            RL_PutRecord(testCursor, count, (void *)word);
        } else {
            printf("Failed to read word and count from %s\n", temp); 
        }
    }
    
    printf("\nPrinting words and word count to file %s\n", outfilename);
    status = RL_MoveToFirst(testCursor);
    assert(status);
    
    while(status){
        fprintf(outfile, "%lu %s\n", RL_GetKey(testCursor), (char *) RL_GetRecord(testCursor));
        status = RL_MoveToNextValid(testCursor);
    } 
}

static void testDelete(int testSize) {
    
    int i, counter, total;
    /* Array of keys / values to be inserted*/
    unsigned long* testArr;
    /* Array indicating whether key at each index should be in the array*/
    Bool* isInserted;
    Cursor_T testCursor;
    Relation_T testRelation;
    Bool status;
    
    
    assert(FANOUT < testSize / 2);
    
    testArr = (unsigned long*) malloc(sizeof(unsigned long) * testSize);
    isInserted = (Bool*) malloc(sizeof(Bool) * testSize);
    
    /* initialize test numbers, nothing has been inserted*/
    for (i = 0; i < testSize; i++) {
        testArr[i] = (unsigned long)i;
        isInserted[i] = False;
    }
    
    /* Create new cursor and new relation. */
    testRelation = RL_NewRelation();
    assert(testRelation != False);
    
    testCursor = RL_NewCursor(testRelation);
    
    
    /* First test corner case of filling relation to  2* max capacity, 
     * deleting all entries and reinserting*/
    
    for (counter = 0; counter < 2 * FANOUT; counter++) {
        /* Get a suitable random location*/
        i = rand() % testSize;
        while (isInserted[i] == True) {
           i = rand() % testSize;
        }
        
        RL_PutRecord(testCursor, testArr[i], (void *)&(testArr[i]));
        isInserted[i] = True;
        assert(status == True);
    }  
    
    testGetAndGetNext(testArr, isInserted, testSize, testCursor, testRelation);
    
    /* Delete all Inserted Records. */
    for(i = 0; i < testSize; i++) {
        if(isInserted[i] == True) {
            status = RL_DeleteRecord(testCursor, testArr[i]);
            /* printf("Deleting: %lu\n", testArr[i]); */
            assert(status == True);
            isInserted[i] = False;
            
            /* Test Move and Get operations. */
            testGetAndGetNext(testArr, isInserted, testSize, testCursor, testRelation);
        }

    }
    
    fprintf(stderr, "\n\n***Delete Tests: insertion of 2 * FANOUT(%d) records "
            "then deletion of records, successful.\n", FANOUT);
    
    /* Now insert all the test values. */
    
    
    /* Now Stress test. */
    /* Insert all testValues  */
    for (i = 0; i < testSize; i++) {
        RL_PutRecord(testCursor, testArr[i], &(testArr[i]));
        isInserted[i] = True;
        assert(status == True);
    }
    
    /* Now randomly delete all test values */
    for(counter = 0; counter < testSize; counter++) {
        /* Get a suitable random location for deletion.*/
        i = rand() % testSize;
        while (isInserted[i] == False) {
           i = rand() % testSize;
        }        
        
       /* printRelationKeys(testCursor);
        printf("Deleting: %lu\n", testArr[i]); */
        
        status = RL_DeleteRecord(testCursor, testArr[i]);
        isInserted[i] = False;
        assert(status == True);
        
        /* Test that we can carry out move and get operations on relation
         * successfully. */
        testGetAndGetNext(testArr, isInserted, testSize, testCursor, testRelation);
    }
    
    fprintf(stderr, "\n\n***Delete Stress Test: insertion and then deletion of all test values successful.\n");
    
    /* Final Test interleaving calls of put and delete */
    
    /* Insert half test size. */
    for (counter = 0; counter < testSize / 4; counter++) {
        /* Get a suitable random location*/
        i = rand() % testSize;
        while (isInserted[i] == True) {
           i = rand() % testSize;
        }
        
        RL_PutRecord(testCursor, testArr[i], (void *)&(testArr[i]));
        isInserted[i] = True;
        assert(status == True);
    }
    
    /* Insert and delete*/
    for (counter = 0; counter < testSize * 2; counter++) {
        i = rand() % testSize;
        
        /* printRelationKeys(testCursor); */
        
        /*fprintf(stderr, "\n\nBefore insertion or deletion.\n\n");
        RL_PrintTree(testRelation);*/

        /* if not inserted, insert. */
        if(isInserted[i] == False) {
            RL_PutRecord(testCursor, testArr[i], (void *)&(testArr[i]));
            isInserted[i] = True;
            /*fprintf(stderr,"Stress Test: Inserted %lu\n", testArr[i]);*/
        }
        /* If inserted,  delete. */
        else {
            status = RL_DeleteRecord(testCursor, testArr[i]);
            isInserted[i] = False;
           /* fprintf(stderr,"Stress Test: Deleted %lu\n", testArr[i]);*/

        }
        
        /* RL_PrintTree(testRelation); */

        assert(status == True); 
        
        /* Test that we can carry out move and get operations on relation
         * successfully. */
        testGetAndGetNext(testArr, isInserted, testSize, testCursor, testRelation);
    }
    
    /* Count how many records have been inserted. */
    total = 0;
    for(i = 0; i < testSize; i++) {
        if (isInserted[i] == True)
            total++;
    }
    
    /* Now randomly delete all test values */
    for(counter= 0; counter < total; counter++) {
        /* Get a suitable random location for deletion.*/
        i = rand() % testSize;
        while (isInserted[i] == False) {
           i = rand() % testSize;
        }        
        
        /*
        fprintf(stderr, "\n\nBefore insertion or deletion.\n\n");
        RL_PrintTree(testRelation);
        */
        
        status = RL_DeleteRecord(testCursor, testArr[i]);
        isInserted[i] = False;
        
        /*
        fprintf(stderr,"Stress Test: Deleted %lu\n", testArr[i]);
        RL_PrintTree(testRelation);
        */
        
        assert(status == True);
        
        /* Test that we can carry out move and get operations on relation
         * successfully. */
        testGetAndGetNext(testArr, isInserted, testSize, testCursor, testRelation);
    }
    
    RL_DeleteRelation(testRelation, NULL);
    RL_FreeCursor(testCursor);
}

/* Find's the location of key in arr of arrSize. Returns -1 if not found.*/
static int findIdx(unsigned long key, unsigned long* arr, int arrSize) {
    int i;
    
    for(i = 0; i < arrSize; i++) {
        if (arr[i] == key) return i;
    }
    
    return -1;
}

/* Test that GetRecord, MoveToRecord, MoveToFirst and MoveToNext are working
 * TODO: move to previous. */
static void testGetAndGetNext(unsigned long* testArr, Bool* isInserted,
        int arrSize, Cursor_T testCursor, Relation_T relation) {
    int i, pRes, isInsertedCount = 0, forwardCount = 0, backwardCount = 0;
    Bool status;
    unsigned long result, prev, next;
    
    assert(testArr != NULL);
    assert(isInserted != NULL);
    assert(arrSize > 0);
    
    /* First test that every isInserted element in testArr is 
     * actually inserted. */
    
    for(i = 0; i < arrSize; i++) {
        if(isInserted[i] == True){
           /* RL_PrintTree(relation); */
            status = RL_MoveToKey(testCursor, testArr[i]);
            /* printf("Attempt to move to %lu\n", testArr[i]); */
            assert(status == True);
            result = *((unsigned long *)RL_GetRecord(testCursor));
            assert(result == testArr[i]);
            isInsertedCount++;
        }
    }
    
    /* If not records have been inserted, assert that the relation is indeed
     * empty. */
    if(isInsertedCount == 0) {
        assert(RL_IsEmpty(testCursor) == True);
        return;
    }
    
    /* Next test that GetNext is working  */
    status = RL_MoveToFirst(testCursor);
    assert(status == True);  
    
    /* Get a record and test that it is valid. */
    result = *((unsigned long *)RL_GetRecord(testCursor));
    i = findIdx(result, testArr, arrSize);
    assert(isInserted[i] == True);
    forwardCount++;

    /* Move to the next record */
    status = RL_MoveToNextValid(testCursor);
    prev = result;
      
    /* While there is a next record. Do the following. */
    while (status == True) {
        /* Get a record and test that it is valid. */
        result = *((unsigned long *)RL_GetRecord(testCursor));
        i = findIdx(result, testArr, arrSize);
        assert(isInserted[i] == True);
        assert(result > prev);
        forwardCount++;
        
        /* Move to the next record */
        status = RL_MoveToNextValid(testCursor);
        prev = result;
    }
    
    /* Move to the next record */
    status = RL_MoveToPreviousNotFirst(testCursor);
    next = result;
    backwardCount++;
    
    /* While there is a previous record. Do the following. */
    while (status == True) {
        /* Get a record and test that it is valid. */
        result = *((unsigned long *)RL_GetRecord(testCursor));
        i = findIdx(result, testArr, arrSize);
        assert(isInserted[i] == True);
        assert(result < next);
        backwardCount++;
        
        /* Move to the previous record */
        status = RL_MoveToPreviousNotFirst(testCursor);
        next = result;
    }
    
    assert(isInsertedCount == forwardCount);
    assert(isInsertedCount == backwardCount);
    assert(isInsertedCount == (int) RL_NumRecords(testCursor));
 
}


void borderNodeUnitTests(void){
    char* testStr = "testnode";
    char* testSuf = "verylongsuffix";
    unsigned long testLong = UTIL_StrToUl(testStr);
    int testVals[10], i;
    BorderNode_T bn = BN_NewBorderNode(testLong);
    
    testLong = UTIL_StrToUl(testStr);
    
    for (i = 0; i < 10; i++) {
        testVals[i] = i;
    }
    
    for (i = 0; i < 10; i++) { 
        assert(BN_GetValue(bn, i) == NULL);
    }
        
    for (i = 0; i < 10; i++) {
        BN_SetValue(bn, i, &testVals[i]);
    }
    
    BN_SetSuffix(bn, testSuf, strlen(testSuf));
    
    for (i = 0; i < 10; i++) {
        int value;
        value = *((int*)BN_GetValue(bn, i));
        assert(value == testVals[i]);
    }
    assert(strcmp(testSuf, BN_GetSuffix(bn)) == 0);
    assert(BN_GetSuffixLength(bn) == strlen(testSuf));
    
    assert(testLong == BN_GetKeySlice(bn));
    
    BN_FreeBorderNode(bn);    
}

static void utilStringULongConversionTests(void){
    char test1[]= "foo";
    char test2[]= "sherlock";
    char test3[]= "sherloc";
    
    unsigned long ul_test1 = UTIL_StrToUl(test1);
    unsigned long ul_test2 = UTIL_StrToUl(test2);
    unsigned long ul_test3 = UTIL_StrToUl(test3);

    
    printf("%s\n", UTIL_UlToStr(ul_test1));
    printf("%s\n", UTIL_UlToStr(ul_test2));
    printf("%s\n", UTIL_UlToStr(ul_test3));
    printf("\n");
}


int main(int argc, char** argv) {
    utilStringULongConversionTests();
    fprintf(stderr, "***Util string / unsigned long conversion tests successful.***\n\n");
    tests(); 
    fprintf(stderr, "***Move and Put Tests successful.***\n\n");
    borderNodeUnitTests();
    fprintf(stderr, "***Border Node Tests Successful.***\n\n");
    testDelete(1000);
    fprintf(stderr, "***Delete Tests Successful.***\n\n");
    fprintf(stderr, "***All Tests Successful***.");
    
    if (argc == 3){
        printf("Argc is 3\n");
        printf("First Arg:%s\n", argv[1]);
        printf("Second Arg:%s\n", argv[2]);
        in_order_test(argv[1], argv[2]);
    }
    
    return 0;
}


/* TODO TEST MOVE TO PREVIOUS. */

