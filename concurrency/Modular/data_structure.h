//
//  data_structure.h
//  BST
//
//  Created by Duc Than Nguyen on 6/15/23.
//

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "threads.h"

lock_t thread_lock;

typedef struct node node;

typedef enum {
    FOUND,
    NOTFOUND,
    NULLNEXT
} Status;

void *surely_malloc (size_t n);
Status findNext(void* p_ds, void** n_ds, int x);
void insertOp(void* p_ds, int x, void* value, Status status);
void changeValue(void* p_ds, void* value);
void *getValue(void* p_ds);
void printDS (void **tgt);
void freeDS(void *p_ds);
