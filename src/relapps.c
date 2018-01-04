/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relapps.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on October 24, 2017, 10:03 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "relapps.h"


void** RLAPP_RangeQuery(Cursor_T cursor, Relation_T relation, 
        unsigned long lower, unsigned long upper, size_t* numRecords) {
    
    void** records;
    unsigned long arrLength;
    int moveCursorRes;
    Bool notAtLast = True;
    void* currRecord;
    
    assert(RL_CursorIsValid(cursor));
    assert(relation != NULL);
    
    *numRecords = 0;
    
    records = (void **) malloc(2* sizeof(void *));
    if (records == NULL) {
        return NULL;
    }
    arrLength = 2;
    
    
    RL_MoveToRecord(cursor, lower, &moveCursorRes);
    if(moveCursorRes < 0) {
        /* if the last record is less than lower, return 0 */
        if (!RL_MoveToNext(cursor)) {
            free(records);
            return NULL;
        }
    }
    
    /* TODO: what if moveCursorRes > 0, then key behind cursor? movetoprevious?*/
  
    /* While there is a next record, continue */
    while(notAtLast) {
        unsigned long currKey = RL_GetKey(cursor);
        
        /* break if we've seen all keys in desired range*/
        if(currKey > upper)
            break;
           
        if(arrLength == *numRecords){
            records = UTIL_ResizeArray(records, arrLength, arrLength*2);
            /* if growArray fails, free records and return*/
            if(arrLength == 0) {
                *numRecords = 0;
                free(records);
                return NULL;
            }
        }
              
        currRecord = (void*)RL_GetRecord(cursor);
        records[*numRecords] = currRecord;
        (*numRecords)++;
        notAtLast = RL_MoveToNext(cursor); 
    }
    
    if(*numRecords == 0) {
        free(records);
        return NULL;
    }
    
    return records;  
}
