/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   permuter.c
 * Author: Oluwatosin V. Adewale
 * 
 * Created on December 8, 2017, 8:09 PM
 */

#include "permuter.h"

int Permuter_size(long permutation) {
    return permutation & 15;
}

long Permuter_setSize(long permutation, int size) {
    return (permutation & (~15)) | (size & 15);
}

int Permuter_get(long permutation, int i) {
    return (permutation >> (i * 4 + 4)) & 15;
}

long Permuter_set(long permutation, int i, int val){
    permutation &= (~(15 << (i * 4 + 4)));
    return permutation |= ((val & 15) << (i * 4 + 4));
}


