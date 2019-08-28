/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   stringbagclient.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on November 19, 2017, 11:20 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "stringbag.h"

/*
 * Client to test stringbag.
 */
int main(int argc, char** argv) {

    size_t temp;
    int len;
    StringBag_T bag;
    void* mem;
    char testStr[100] = {0};
    
    /* Testing MaxSize */
    printf("Maximum StringBag Size is %lu bytes.\n", (unsigned long)SB_MaxSize());
    
    /* Testing Overhead */
    printf("Overhead of StringBag for 1 string is %lu bytes.\n", (unsigned long) SB_Overhead(1));
    
    printf("Overhead of StringBag for 5 strings is %lu bytes.\n", (unsigned long) SB_Overhead(5));
    
    /* Testing SafeSize */
    temp = (unsigned long) SB_SafeSize(5, 50);
    
    printf("Safe size for 5 strings using 50 bytes for these is %lu bytes.\n", 
            (unsigned long) temp);
    
    /* Testing new string bag */
    mem = malloc(temp);
    bag = SB_NewStringBag(mem, 5, temp);
    
    /* Test capacity and used capacity */
    assert(SB_Capacity(bag) == temp);
    assert(SB_UsedCapacity(bag) == SB_Overhead(5));
    
    assert(SB_Assign(bag, 0, "Apple", 5));
    assert(SB_Assign(bag, 1, "Ball", 4));
    assert(SB_Assign(bag, 2, "Cat", 3));
    assert(SB_Assign(bag, 3, "Dog", 3));
    assert(SB_Assign(bag, 4, "Egg", 3));
    
    assert(SB_Assign(bag, 3, "Daniel", 6));
    
    /* Should fail*/
    assert(SB_Assign(bag, 4, "pneumonoultramicroscopicsilicovolcanoconiosis", 45) == False);

    /* Print a representation of the string bag */
    SB_Print(bag, 5, stdout, "Test StringBag ", 0);

    
    /* Make sure you can get strings and they are the same. */
    strncpy(testStr, SB_Get(bag, 0, &len), len);
    testStr[len] = '\0';
    assert(strcmp(testStr, "Apple") == 0);
            
    strncpy(testStr, SB_Get(bag, 1, &len), len);
    testStr[len] = '\0';
    assert(strcmp(testStr, "Ball") == 0);
            
    strncpy(testStr, SB_Get(bag, 2, &len), len);
    testStr[len] = '\0';
    assert(strcmp(testStr, "Cat") == 0);
            
    strncpy(testStr, SB_Get(bag, 3, &len), len);
    testStr[len] = '\0';
    assert(strcmp(testStr, "Daniel") == 0);
    
    strncpy(testStr, SB_Get(bag, 4, &len), len);
    testStr[len] = '\0';
    assert(strcmp(testStr, "Egg") == 0);   
    
    return 0;
}

