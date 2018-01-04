/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   stringbag.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on November 19, 2017, 4:13 PM
 */

#ifndef STRINGBAG_H
#define STRINGBAG_H

#include "util.h"
#include <stdio.h>

/* This StringBag implementation is based on Masstree's string bag 
 * implementation and comments. 
 * Please see: https://github.com/kohler/masstree-beta*/


/* A stringBag is a compact collection of W (width) strings with a max capacity.
 * The client should keep store and keep track of W. */
typedef struct StringBag* StringBag_T;

/* Maximum allowable capacity of a StringBag (-1)*/
size_t SB_MaxSize(void);

/* Number of bytes allocated for overhead. */
size_t SB_Overhead(int width);

/* Return a capacity that can definitely contain a stringBag of W strings 
 * and length bytes of strings.*/
size_t SB_SafeSize(int width, size_t length);

/* Construct a string bag in mem of capacity bytes and W strings. The area of 
 * memory pointed to by mem should not be in the stack. */
StringBag_T SB_NewStringBag(void* mem, int width, size_t capacity);

/* Return the capacity (number of bytes) used to construct the bag. */
size_t SB_Capacity(StringBag_T strBag);

/* Return the number of bytes used so far (including overheard).*/
size_t SB_UsedCapacity(StringBag_T strBag);

/* Return the string at position p. (p ranges from 0 to W-1 strings). Store the
 * length of the string in pLen */
const char* SB_Get(StringBag_T strBag, int p, int* pLen);

/* Assign (copy) the string at position p to s with length len characters. 
 * Return True if the assignment successful and False if it failed 
 * (StringBag out of capacity). */
Bool SB_Assign(StringBag_T strBag, int p, char* s, int len);

/* Print a representation of the StringBag of width strings to the stream f. 
 * Print each line with prefix and indent. */
void SB_Print(StringBag_T strBag, int width, FILE* f, char* prefix, int indent);


#endif /* STRINGBAG_H */
