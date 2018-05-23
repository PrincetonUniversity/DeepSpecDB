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
#include <time.h>
#include <stdio.h>

#define mask 255

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
    assert(array != NULL);
    assert(currLength != 0);

    array = (void**) realloc(array, desiredLength*sizeof(void*));
    if(array == NULL) {
        return NULL;
    }

    return array;
}


unsigned long UTIL_StrToUl(const char* str){
    int i = 0;
    unsigned long res = 0;

    while((*str) != '\0' && i < keyslice_length) {
        res <<= 8;
        res |= (unsigned long)((*str) & mask);
        str++, i++;
    }
    while (i < keyslice_length) {
        res <<= 8;
        i++;
    }

    return res;
}

char* UTIL_UlToStr(unsigned long ul) {
    char* res = (char*) calloc(9, sizeof(char));
    int i;
    for(i = 7; i >= 0; i--) {
        res[i] = ul;
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

    for (size_t i = 0; i < lenA; ++ i) {
      if (a[i] != b[i]) {
        return False;
      }
    }

    return True;
}

keyslice_t UTIL_GetNextKeySlice(const char* str, long len) {
    keyslice_t res = 0;
    int i = 0;

    assert(len >= 0);
    assert(len <= keyslice_length);


    while(i < len) {
        /* Shift res left by keyslice_length *bits* padding with zeroes. */
        res <<= 8;
        res |= (((keyslice_t) *str) & mask);
        str++, i++;
    }
    while(i < keyslice_length) {
        /* Shift res left until most significant bits are not 0. */
        res <<= 8;
        i++;
    }
    return res;
}

char* UTIL_KeySliceToStr(unsigned long keySlice, long len) {
    char* res = (char*) calloc(len, sizeof(char));
    int i;

    assert(len >= 0);
    assert(len <= keyslice_length);

    for(i = 7; i >= 0; i--) {
        if (i < len) {
            res[i] = keySlice;
        }
        keySlice >>= 8;
    }
    return res;
}

void UTIL_Shuffle(int* arr, int len) {
    int i, r, temp;

    for(i = 0; i < len; i++) {
        r = random();

        if (r < 0) {
            r = r * -1;
        }

        r = r % (i + 1);

        temp = arr[i];
        arr[i] = arr[r];
        arr[r] = temp;
    }

}
