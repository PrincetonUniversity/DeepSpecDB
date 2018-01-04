/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   stringbag.c
 * Author: Oluwatosin V. Adewale
 * 
 * Created on November 19, 2017, 4:13 PM
 */

#include <string.h>
#include <assert.h>
#include "stringbag.h"

/* An InfoType stores the position and length of a string. */
struct InfoType {
    size_t pos;
    size_t len;
};

/* A header stores information about it's string bag. It stores the current 
 * size and capacity of the string bag in bytes, and a variable length array of
 * string info. */
struct Header {
    size_t size;
    size_t capacity;
    struct InfoType info[1];
};



/* A StringBag is a collection of width strings. It has a header storing the 
 * capacity of the StringBag in bytes. Size tracks how much of that capacity has
 * been used. There is a buffer, strBuf, storing the bag's strings immediately 
 * after the header. The header contains the info of each string in strBuf. */
struct StringBag {
    union {
        struct Header header;
        char strBuf[1];
    } bag;
};

size_t SB_MaxSize(void) {
    return (size_t) (- 1);
}

size_t SB_Overhead(int width) {
    assert(width > 0);
    return sizeof(struct StringBag) + (width-1) * sizeof(struct InfoType);
}

size_t SB_SafeSize(int width, size_t length) {
    assert(width > 0);
    assert(length >= 0); 
    return SB_Overhead(width) + length;  
}

StringBag_T SB_NewStringBag(void* mem, int width, size_t capacity) {

    StringBag_T stringbag = (StringBag_T) mem;
    size_t firstPos = SB_Overhead(width);
    
    assert(mem != NULL);
    assert(width > 0);
    assert(capacity >= firstPos && capacity <= SB_MaxSize());
    
    stringbag->bag.header.size = firstPos;
    stringbag->bag.header.capacity = capacity;
    
    memset(stringbag->bag.header.info, 0, sizeof(struct InfoType) * width);
    
    return stringbag;
}

size_t SB_Capacity(StringBag_T strBag) {
    assert(strBag != NULL);
    return strBag->bag.header.capacity;
}

size_t SB_UsedCapacity(StringBag_T strBag) {
    assert(strBag != NULL);
    return strBag->bag.header.size;
}

const char* SB_Get(StringBag_T strBag, int p, int* pLen) {
    size_t pos;
    assert(strBag != NULL);
    assert(pLen != NULL);
    pos = strBag->bag.header.info[p].pos;
    *pLen = (int)(strBag->bag.header.info[p].len);
    return strBag->bag.strBuf + pos;  
}

Bool SB_Assign(StringBag_T strBag, int p, char* s, int len) {
    size_t pos, oldLen;
    assert(strBag != NULL);
    assert(s != NULL);
    
    oldLen = strBag->bag.header.info[p].len;
    if (oldLen >= (size_t)len) {
        pos = strBag->bag.header.info[p].pos;   
    }
    else if (strBag->bag.header.size + len <= strBag->bag.header.capacity) {
        pos = strBag->bag.header.size;
        strBag->bag.header.size += len;
    }
    else {
        return False;
    }
    
    memcpy(strBag->bag.strBuf + pos, s, len);
    
    strBag->bag.header.info[p].pos = pos;
    strBag->bag.header.info[p].len = len;
    
    return True;
}

void SB_Print(StringBag_T strBag, int width, FILE* f, char* prefix, int indent) {
    int i, strLen;
    
    fprintf(f, "%s%*s%p (%d:)%d:%d...\n", prefix, indent, "", (void *)strBag, 
            (int) SB_Overhead(width), (int)(strBag->bag.header.size), 
            (int)(strBag->bag.header.capacity));
    
    for (i = 0; i < width; i++) {
        strLen = (int) strBag->bag.header.info[i].len;
        
        if (strLen > 30)
            strLen = 30;
        
        if (strBag->bag.header.info[i].len) {
            fprintf(f, "%s%*s  #%x %d:%d %.*s\n", prefix, indent, "", i, 
               (int)(strBag->bag.header.info[i].pos), (int)strBag->bag.header.info[i].len, 
                strLen, strBag->bag.strBuf + strBag->bag.header.info[i].pos);
        }  
    }
}
