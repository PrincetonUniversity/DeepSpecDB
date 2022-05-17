#include "./threads.h"
#include <stddef.h>
#include <stdio.h>

typedef struct tree {int key; void *value; struct tree_t *left, *right;} tree;
typedef struct tree_t {tree *t; lock_t *lock;} tree_t;

typedef struct tree_t **treebox;
lock_t thread_lock;
treebox tb;

void *surely_malloc (size_t n);

treebox treebox_new(void);

void tree_free(struct tree_t *tgp);

void treebox_free(treebox b);

void insert (treebox t, int x, void *value);

void *lookup (treebox t, int x);

void turn_left(struct tree_t * tgl, struct tree_t * tgr);

void pushdown_left (struct tree_t *tgp);

void delete(treebox t, int x);

void *thread_func(void *args);