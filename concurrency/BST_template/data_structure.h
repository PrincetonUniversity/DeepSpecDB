//
//  data_structure.h
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//


#include <stddef.h>
#include <stdio.h>
#include <limits.h>
#include "threads.h"

lock_t thread_lock;

//Template style
typedef struct pn {
    struct tree_t *p;
    struct tree_t *n;
} pn;

typedef struct tree {int key; void *value; struct tree_t *left, *right;} tree;
typedef struct tree_t {tree *t; lock_t *lock; int min; int max; } tree_t;
extern void *malloc (size_t n);
extern void free(void *p);
extern void exit(int code);
typedef struct tree_t **treebox;
treebox tb;

void *surely_malloc (size_t n);
int findnext (pn *pn, int x, void *value);
void insertOp(pn *pn, int x, void *value);
treebox treebox_new(void);
void tree_free(struct tree_t *tgp);
void treebox_free(treebox b);

