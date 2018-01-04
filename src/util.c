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
void** UTIL_ResizeArray(void** array, unsigned long currLength, 
        unsigned long desiredLength) {    
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
