/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   utilities.c
 * Author: Oluwatosin V. Adewale
 * 
 * Created on September 29, 2017, 4:43 PM
 */


#include "util.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

int UTIL_BinarySearch(int a[], int tgt, int lo, int hi){
  int mid, val;
  while(lo < hi){
    mid = (lo + hi) >> 1; /* (hi - lo) >> 1 + lo ? */
    val = a[mid];
    if (val == tgt) return mid;
    else if (val < tgt) lo = mid + 1;
    else hi = mid;
  }
  return -1;
}


/* Grows the array*/
void* UTIL_ResizeArray(void* array, unsigned long currLength, 
        unsigned long desiredLength) { 
    void* oldArray = array;
    assert(array != NULL);
    assert(currLength != 0);
        
    array = (void**) realloc(array, desiredLength*sizeof(void*));
    if(array == NULL) {
        return 0;
    }
            
    return array;
}


unsigned long UTIL_StrToUl(const char* str){
    int i = 0;
    unsigned long res = 0;
    char mask = 255;
    
    while((*str) != '\0' && i < 8) {
        res <<= 8;
        res |= (unsigned long)((*str) & mask);
        str++, i++;
    }
    while (i < 8) {
        res <<= 8;
        i++;
    }
    
    return res;
}

char* UTIL_UlToStr(unsigned long ul) {
    char* res = (char*) calloc(9, sizeof(char));
    int i;
    unsigned long mask = 255;
    for(i = 7; i >= 0; i--) {
        res[i] = (char)(ul & mask);
        ul >>= 8;      
    }   
    return res;
}

size_t UTIL_Min(size_t a, size_t b) {
    if (a <= b) {
        return a;
    } else {
        return b;
    }
}

Bool UTIL_StrEqual(const char* a, size_t lenA, const char* b, size_t lenB) {
    if(lenA != lenB) {
        return False;
    }
    
    if(memcmp(a, b, lenA) != 0) {
        return False;
    }
    
    return True;
}


unsigned long UTIL_GetNextKeySlice(const char* str, long len) {
    unsigned long res = 0;
    int i = 0;
    char mask = 255;
    
    assert(len >= 0);
    assert(len <= 8);
    
    
    while(i < len) {
        /* Shift res left by 8 *bits* padding with zeroes. */
        res <<= 8;
        res |= (unsigned long)((*str) & mask);
        str++, i++;
    }
    while(i < 8) {
        /* Shift res left until most significant bits are not 0. */
        res <<= 8;
        i++;
    }   
    return res;
}

char* UTIL_KeySliceToStr(unsigned long keySlice, long len) {
    char* res = (char*) calloc(len, sizeof(char));
    int i;
    unsigned long mask = 255;
    
    assert(len >= 0);
    assert(len <= 8);

    for(i = 7; i >= 0; i--) {
        if (i < len) {
            res[i] = (char)(keySlice & mask);
        }
        keySlice >>= 8;   
    }   
    return res;
}
