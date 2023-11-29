#include <stddef.h>
#include <stdio.h>
/* #include <stdlib.h> */
#include "threads.h"

extern void *malloc (size_t n);
extern void free(void *p);
extern void exit(int code);

typedef struct tree {int key; void *value; struct tree_t *left, *right;} tree;
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


void tree_free(struct tree_t *tgp) {
  struct tree_t *pa, *pb;
  tree* p;
  void *l = tgp->lock;
  acquire(l);
  p = tgp->t;
  if (p!=NULL) {
    pa=p->left;
    pb=p->right;
    free(p);
    tree_free(pa);
    tree_free(pb);
  }
  freelock2(l);
  free(l);
  free(tgp);
}

void treebox_free(treebox b) {
  struct tree_t *t = *b;
  tree_free(t);
  free(b);
}

void insert (treebox t, int x, void *value) {
  struct tree_t *tgt = *t;
  struct tree *p;
  void *l = tgt->lock;
  acquire(l);
  for(;;) {
    p = tgt->t;
    if (p==NULL) {
      tree_t *p1 = (struct tree_t *) surely_malloc (sizeof *tgt);
      tree_t *p2 = (struct tree_t *) surely_malloc (sizeof *tgt);
      p1 ->t = NULL;
      p2 ->t = NULL;
      lock_t *l1 = (lock_t *) surely_malloc(sizeof(lock_t));
      makelock(l1);
      p1->lock = l1;
      release2(l1);
      lock_t *l2 = (lock_t *) surely_malloc(sizeof(lock_t));
      makelock(l2);
      p2->lock = l2;
      release2(l2);
      p = (struct tree *) surely_malloc (sizeof *p);
      tgt->t = p;
      p->key=x; p->value=value; p->left=p1; p->right=p2;
      release2(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
      	tgt = p->left;
        void *l_old = l;
        l = tgt->lock;
        acquire(l);
        release2(l_old);
      } else if (y<x){
        tgt = p->right;
        void *l_old = l;
        l = tgt->lock;
        acquire(l);
        release2(l_old);
      }else {
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
      tgt=p->left;
      void *l_old = l;
      l = tgt->lock;
      acquire(l);
      p=tgt->t;
      release2(l_old);
    }else if (y<x){
      tgt=p->right;
      void *l_old = l;
      l = tgt->lock;
      acquire(l);
      p=tgt->t;
      release2(l_old);
    }else {
      v = p->value;
      release2(l);
      return v;
    }
  }
  release2(l);
  return NULL;
}

void turn_left(struct tree_t * tgl, struct tree_t * tgr) {
  struct tree_t * mid;
  struct tree * r, *l;
  r = tgr->t;
  mid = r->left;
  l = tgl->t;
  l->right = mid;
  r->left = tgr; 
  tgl->t = r;
  tgr->t = l;
}

void pushdown_left (struct tree_t *tgp) {
  struct tree *p, *q;
  struct tree_t *tgq;
  for(;;) {
    void *lp = tgp->lock; // initial lp acquired in delete
    p = tgp->t;
    tgq = p->right;
    void *lq = tgq->lock;
    acquire(lq);
    q = tgq->t;
    if (q==NULL) {
      struct tree_t *tgl = p->left;
      acquire(tgl->lock);
      tgp->t = tgl->t;
      free(p);
      freelock2(lq);
      free(lq);
      free(tgq);
      freelock2(tgl->lock);
      free(tgl->lock);
      free(tgl);
      release2(lp);
      return;
    } else {
      turn_left(tgp, tgq);
      tgp = q->left;
      release2(lp);
    }
  }
}

void delete (treebox t, int x) {
  struct tree *p;
  struct tree_t *tgt;
  tgt = *t;
  void *l = tgt->lock;
  acquire(l);
  for(;;) {
    p = tgt->t;
    if (p==NULL) {
      release2(l);
      return;
    } else {
      int y = p->key;
      if (x<y){
	tgt = p->left;
	void *l_old = l;
	l = tgt->lock;
	acquire(l);
        release2(l_old);
      }else if (y<x){
	tgt = p->right;
	void *l_old = l;
	l = tgt->lock;
	acquire(l);
        release2(l_old);
      }else {
      	pushdown_left(tgt);	
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
