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

void *surely_malloc (size_t n);
int findnext(void* p_tree, void** n_tree, int x);
void insertOp(void* p_tree, int x, void* value);
void changeValue(void* p_tree, void* value);
void *getValue(void* p_tree);
void traverseInorder (void **tgt);
void tree_free(void *p_tree);
