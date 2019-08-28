/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   permuter.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on December 8, 2017, 8:09 PM
 */

#ifndef PERMUTER_H
#define PERMUTER_H

/* Permuter is a library for working with permutations. It can be thought of as 
 * a compact array of at most 15 elements, each 4 bits wide. The number of
 * elements is also stored in 4 bits. Permutations are stored as longs.
 * See Masstree Paper: https://pdos.csail.mit.edu/papers/masstree:eurosys12.pdf
 * and Implementation: https://github.com/kohler/masstree-beta
 *  */

/* Return the size / number of elements in the permutation. The Permuter 
 * can have at most 15 elements. */
int Permuter_size(long permutation);

/* Set the size / number of elements in the permutation. Size must be between 0 
 * and 15*/
long Permuter_setSize(long permutation, int size);

/* Return the value at position i.*/
int Permuter_get(long permutation, int i);

/* Set element i of permuation to the lower 4 bits of val.*/
void Permuter_set(long permutation, int i, int val);





#endif /* PERMUTER_H */
