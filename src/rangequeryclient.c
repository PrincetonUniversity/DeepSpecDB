/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   rangequeryclient.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on November 6, 2017, 5:28 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "relation.h"
#include "relapps.h"


static void range_query_client_test(int argc, char **argv){
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
    char *lower, *upper, *temp, *word;
    Relation_T testRelation;
    Cursor_T testCursor;
    void** records; 
    size_t numRecords;
    size_t i;
        
    if (argc != 3) {
        fprintf(stderr, "Usage ./command lower upper < file\n");
        return EXIT_FAILURE;
    }
    
    lower = argv[1], upper = argv[2];
    
    testRelation = RL_NewRelation();
    testCursor = RL_NewCursor(testRelation);
    
    temp = (char*)malloc(sizeof(char)* 100);
    while (fgets(temp,100, stdin) != NULL) {
        if (temp[strlen(temp)-1] == '\n') {
            temp[strlen(temp)-1] = '\0'; 
        }
        word = malloc(sizeof(char) * (strlen(temp) + 1));
        strcpy(word, temp);
        RL_PutRecord(testCursor, UTIL_StrToUl(word), word);
    }
    
    
    records = RLAPP_RangeQuery(testCursor, testRelation, UTIL_StrToUl(lower), 
            UTIL_StrToUl(upper), &numRecords);
    
    if(records == NULL) {
        RL_FreeCursor(testCursor);
        return 0;
    }
    
    for(i = 0; i < numRecords; i++){
        printf("%s\n", (char*)records[i]);
    }
    
    free(records);       
    return 0;
}

