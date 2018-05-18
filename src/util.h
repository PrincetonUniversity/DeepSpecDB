/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/*
 * File:   utilities.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on September 29, 2017, 4:43 PM
 */

#ifndef UTIL_H
#define UTIL_H

#include <stddef.h>
#include "inttypes.h"

/* Boolean enum type*/
typedef enum { False = 0 , True = 1} Bool;

/* Order of Btree nodes */
/* enum {ORDER = 2}; */

/* Fanout of Btree nodes */
enum {FANOUT = 15};

/* Max Tree depth: maximum number of levels.
 * Levels go from 0 to MAX_TREE_DEPTH - 1. Program will crash if client tries
 * to increase the Btree past MAX_TREE_DEPTH levels. */
enum {MAX_TREE_DEPTH = 20};

/* Binary search on array a to find tgt between lo (inclusive) & hi (exclusive).
 * Code from:
 * https://github.com/PrincetonUniversity/VST/blob/master/progs/bin_search.c */
int UTIL_BinarySearch(int a[], int tgt, int lo, int hi);


/* Grows the array of length currLength to desiredLength.
 * currLength must be greater than 0. If successful, returns the new array.
 * Else, returns NULL and the old array is intact. */
void* UTIL_ResizeArray(void* array, unsigned long currLength,
        unsigned long desiredLength);



/* Conversion functions assume that longs are 8 bytes, write each byte of string
 * into the unsigned long. Significant byte of ul corresponds to significant
 * bytes in string with least significant bytes 0 if string consists of
 * less than 8 chars. */


/* Convert an string str of at most 8 characters to an 8 byte unsigned long.
 * The string does not need to include the NUL byte is it is 8 characters long.
 * Pads the unsigned long with zeros if necessary. The first character of the
 * string is at the most significant position of the ul.
 */
unsigned long UTIL_StrToUl(const char* str);

/* Convert an unsigned long to a string of 9 characters. The resulting string
 * is always terminated by a NUL byte. */
char* UTIL_UlToStr(unsigned long ul);

/* Return the minimum of the two unsigned numbers.*/
size_t UTIL_Min(size_t a, size_t b);

/* */
Bool UTIL_StrEqual(const char* a, size_t lenA, const char* b, size_t lenB);


/* Return num bytes / char of the key as an unsigned long (KeySlice). len must
 * be >= 0 and <= 8.  */
keyslice_t UTIL_GetNextKeySlice(const char* str, long len);

/* Return the keyslice as a string of size len. len must
 * be >= 0 and <= 8.  */
char* UTIL_KeySliceToStr(unsigned long keySlice, long len);

/* Shuffles the input array creating a random permutation.
 * Implemented using the Fisher-Yates / Knuth shuffle. */
void UTIL_Shuffle(int* arr, int len);

#endif /* UTIL_H */
