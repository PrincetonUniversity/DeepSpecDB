/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relapps.h
 * Author: Oluwatosin V. Adewale
 *
 * Created on November 6, 2017, 11:44 AM
 */

#ifndef RELAPPS_H
#define RELAPPS_H

#include "relation.h" 
#include "util.h"
#include <stddef.h>
#include <stdio.h>

/* Carries out a range query on relation using cursor. Returns records of keys 
 * between lower and upper (inlusive) as a newly allocated array of void 
 * pointers. Sets the number of records / length of the array in numRes. 
 * If there are no keys in the given range or there is insufficient memory, 
 * returns NULL and *numRes is set to zero.  
 * TODO: Client would have to free memory? */
void** RLAPP_RangeQuery(Cursor_T cursor, Relation_T relation, 
        unsigned long lower, unsigned long upper, size_t* numRecords);



#endif /* RELAPPS_H */

