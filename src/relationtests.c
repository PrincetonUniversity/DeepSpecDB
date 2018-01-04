/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relationtests.c
 * Author: Oluwatosin V. Adewale
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


static void printRelationKeys(Cursor_T cursor){
    Bool status = True;
    unsigned long key;
    
    if(RL_MoveToFirstRecord(cursor)) {
        printf("Printing Keys: ");
        while(status) {
            key = RL_GetKey(cursor);
            printf("%lu ", key);
            status = RL_MoveToNext(cursor);
        }
        printf("\n");
    }
}

static void tests(void) {
    enum {TEST_SIZE = 25};
    enum {NUM_VALUES = 5000};
    
    Relation_T testRelation = RL_NewRelation();
    Cursor_T testCursor = RL_NewCursor(testRelation);
    Cursor_T printCursor = RL_NewCursor(testRelation);
    
    unsigned long i;
    unsigned long *test_values;
    unsigned long testIdx[TEST_SIZE];
    int count = 0;
    Bool status;
    int res = 0;
   
    /* move and put should behave diff on empty and non empty record, take you 
     close to the desired key assert check here and change code in move and put*/
    assert(RL_MoveToRecord(testCursor, (unsigned long) 0, &res) == False);
    assert(RL_CursorIsValid(testCursor) == False);
    
    test_values = (unsigned long *) malloc (NUM_VALUES * sizeof(unsigned long));
    
    for (i = 0; i < NUM_VALUES; i++) {
        test_values[i] = (unsigned long) i;
    }
    
    while(count < TEST_SIZE) {
        unsigned long temp;
        i = rand() % TEST_SIZE;
        
        printf("%d: Putting key %lu with value %lu\n", count, i, test_values[i]);
        assert(RL_PutRecord(testCursor, i, &test_values[i]));
        temp = *(unsigned long *)RL_GetRecord(testCursor);
        assert(temp == test_values[i]);

        testIdx[count] = i;
        count++;
    }
    
    for (i = 0; i < TEST_SIZE; i++) {
        RL_MoveToRecord(testCursor, testIdx[i], &res);
        printf("Key: %lu Record: %lu\n", testIdx[i], *((unsigned long *) RL_GetRecord(testCursor)));
    }
    
    status = RL_MoveToFirstRecord(testCursor);
    assert(status);
    
    printf("\nPrinting In order.\n");
    while(status){
        printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor)));
        status = RL_MoveToNext(testCursor);
    }
    printf("\nFinished In order.\n");
    
    
    printf("\nPut and get from 0 to %d\n", TEST_SIZE -1);
    for (i = 0; i < TEST_SIZE; i++) {
        RL_PutRecord(testCursor, i, &test_values[i]);
    }
    
    for (i = 0; i < TEST_SIZE; i++) {
        RL_MoveToRecord(testCursor, i, &res);
        printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor)));
    }
    
    printf("\nPrint in order %d\n", TEST_SIZE -1);
    status = RL_MoveToFirstRecord(testCursor);
    assert(status);
    
    while(status){
        printf("%lu\n", *((unsigned long *) RL_GetRecord(testCursor)));
        status = RL_MoveToNext(testCursor);
    }

    fprintf(stderr, "\nTesting That RL_MoveToRecord properly tracks ancestors\n");
    
    for(i = TEST_SIZE; i == 0; i--) {
        unsigned long prev, curr;
        RL_MoveToRecord(testCursor, test_values[i-1], &res);
        prev = *(unsigned long *)RL_GetRecord(testCursor);
        assert(prev == test_values[i-1]);
         
        status = RL_MoveToNext(testCursor);
        while(status) {
            curr = *(unsigned long *)RL_GetRecord(testCursor);
            assert(prev < curr);
            prev = curr;
            status = RL_MoveToNext(testCursor);
        }   
    }
    

    fprintf(stderr, "\nTesting That RL_PutRecord properly tracks ancestors\n");

    for(i = TEST_SIZE; i > 0; i--) {   
        unsigned long prev, curr;
        unsigned long *pRandNum;
        
        pRandNum = (unsigned long *) malloc(sizeof(unsigned long));
        *pRandNum = rand() % (TEST_SIZE * 3);
                     
        assert(RL_PutRecord(testCursor, *pRandNum, pRandNum));
        prev = *(unsigned long *)RL_GetRecord(testCursor);
        
        if(prev != *pRandNum)
            printf("%lu %lu", prev, *pRandNum);
        assert(prev == *pRandNum);    
        
        status = RL_MoveToNext(testCursor);
        while(status) {
            curr = *(unsigned long *)RL_GetRecord(testCursor);
            assert(prev < curr);
            prev = curr;
            status = RL_MoveToNext(testCursor);
        }     
    }
    
    fprintf(stderr, "\nDone with Tests\n");

   
    RL_FreeCursor(testCursor);
    /*RL_DeleteRelation(testRelation); unimplemented*/
          
  
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
            assert(RL_PutRecord(testCursor, count, (void *)word));
        } else {
            printf("Failed to read word and count from %s\n", temp); 
        }
    }
    
    printf("\nPrinting words and word count to file %s\n", outfilename);
    status = RL_MoveToFirstRecord(testCursor);
    assert(status);
    
    while(status){
        fprintf(outfile, "%lu %s\n", RL_GetKey(testCursor), (char *) RL_GetRecord(testCursor));
        status = RL_MoveToNext(testCursor);
    } 
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
        BN_SetValue(bn, i, &testVals[i]);
    }
    BN_SetSuffix(bn, testSuf);
    
    for (i = 0; i < 10; i++) {
        int value;
        value = *((int*)BN_GetValue(bn, i));
        assert(value == testVals[i]);
    }
    assert(strcmp(testSuf, BN_GetSuffix(bn)) == 0);
    
    assert(strcmp(testStr, BN_GetKeySlice(bn)) == 0);
    
    BN_FreeBorderNode(bn);
}


int main(int argc, char** argv) {
        
    tests();
    borderNodeUnitTests();
    
    if (argc == 3){
        printf("Argc is 3\n");
        printf("%s\n", argv[1]);
        printf("%s\n", argv[2]);
        in_order_test(argv[1], argv[2]);
    }
    
    return 0;
}


