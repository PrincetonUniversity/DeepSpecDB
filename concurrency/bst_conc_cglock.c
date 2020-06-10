#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

extern void *malloc (size_t n);
extern void free(void *p);

typedef struct tree {int key; void *value; struct tree *left, *right;} tree;
typedef struct tree_t {tree *t; lock_t *lock;} tree_t;

typedef struct tree_t **treebox;
lock_t thread_lock;
treebox tb;


void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

treebox treebox_new(void) {
  treebox p = (treebox) surely_malloc(sizeof (*p));
  tree_t *newt = (tree_t *) surely_malloc(sizeof(tree_t));
  *p = newt;
  lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
  makelock(l);
  newt->lock = l;
  newt->t = NULL;
  release2(l);
  return p;
}


void tree_free(struct tree *p) {
  struct tree *pa, *pb;
  if (p!=NULL) {
    pa=p->left;
    pb=p->right;
    free(p);
    tree_free(pa);
    tree_free(pb);
  }
}

void treebox_free(treebox b) {
  struct tree_t *tgp = *b;
  tree* p;
  void *l = tgp -> lock;
  acquire(l);
  p = tgp -> t;
  tree_free(p);
  freelock2(l);
  free(l);
  free(b);
}

void insert (treebox t, int x, void *value) {
  struct tree_t *tgt = *t;
  struct tree *p;
  void *l = tgt -> lock;
  acquire(l);
  struct tree **tr = &tgt -> t;
  for(;;) {
    p = *tr;
    if (p==NULL) {
      p = (struct tree *) surely_malloc (sizeof *p);
      *tr = p;
      p->key=x; p->value=value; p->left=NULL; p->right=NULL;
      release2(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
          tr = &p->left;
      } else if (y<x){
          tr = &p->right;
      } else {
      	p->value=value;
        release2(l);
      	return;
      }
    }
  }
}


void *lookup (treebox t, int x) {
  struct tree *p; void *v;
  struct tree_t *tgt;
  tgt = *t;
  void *l = tgt->lock;
  acquire(l);
  p = tgt->t;
  while (p!=NULL) {
    int y = p->key;
    if (x<y){
      p=p->left;
    }else if (y<x){
      p=p->right;
    }else {
      v = p->value;
      release2(l);
      return v;
    }
  }
  release2(l);
  return NULL;
}

void turn_left(struct tree** _l, struct tree * l, struct tree * r) {
  struct tree * mid;
  mid = r->left;
  l->right = mid;
  r->left = l;
  *_l = r;
}

void pushdown_left (struct tree** t) {
  struct tree *p, *q;
  for(;;) {
    p = *t;
    q = p->right;
    if (q==NULL) {
      q = p->left;
      *t = q;
      free(p);
      return;
    } else {
      turn_left(t, p, q);
      t = &q->left;
    }
  }
}

void delete (treebox t, int x) {
  struct tree *p;
  struct tree_t *tgt;
  tgt = *t;
  void *l = tgt->lock;
  acquire(l);
  struct tree ** tr = &tgt->t;
  for(;;) {
    p = *tr;
    if (p==NULL) {
      release2(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
         tr = &p->left;
      }else if (y<x){
	 tr = &p->right;
      }else {
      	pushdown_left(tr);
        release2(l);
      	return;
      }
    }
  }
}

void *thread_func(void *args) {
  lock_t *l = &thread_lock;

  // insert at key 1
  insert(tb,1,"ONE_FROM_THREAD");

  release2((void*)l);
  return (void *)NULL;
}


int main (void) {
  tb = treebox_new();
  lock_t *t_lock = &thread_lock;
  insert(tb,3,"three");
  insert(tb,1,"one");
  insert(tb,4,"four");

  makelock((void*)t_lock);
  /* Spawn */
  spawn((void *)&thread_func, (void *)NULL);

  //insert at key 1
  insert(tb,1,"ONE");

  /*JOIN */
  acquire((void*)t_lock);
  freelock2((void*)t_lock);

  /* printf("%s\n", lookup(tb, 1)); */
  treebox_free(tb);
  return 0;
}
