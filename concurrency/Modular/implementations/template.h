//
//  template.h
//  BST
//
//  Created by Duc Than Nguyen on 6/22/23.
//

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "threads.h"
#include "common.h"

typedef struct node_t node_t;
typedef struct node_t **treebox;
treebox tb;

//Template style
typedef struct pn {
    struct node_t *p;
    struct node_t *n;
} pn;

Status traverse(pn *pn, int x);
void insertOp_helper(node_t* p, int x, void* value, Status status);
lock_t * getLock(node_t *p);
node_t * treebox_helper(node_t *newt);
void changeValue(void* p_ds, void* value);
void *getValue_helper(node_t* p_ds);
void changeValue_helper(node_t * p, void * value);
//void freeDS(void *p_ds);

void insert (treebox t, int x, void *value);
void *lookup (treebox t, int x);
treebox treebox_new(void);
void treebox_free(treebox b);
void printDS_helper (void **tgt);
void printDS_1 (node_t *tgt);

