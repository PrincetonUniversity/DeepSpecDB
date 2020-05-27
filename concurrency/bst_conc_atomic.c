#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"
#include <stdatomic.h>


extern void *malloc (size_t n);
extern void free(void *p);

typedef struct tree {int key; void *value; _Atomic struct tree *left, *right;} tree;
typedef _Atomic struct tree **treebox;
treebox tb ;

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

treebox treebox_new(void) {
  treebox p = (treebox) surely_malloc(sizeof (*p));
  *p = NULL;
  return p;
}


// void tree_free(struct tree *tp) {
//   struct tree *tpa, *tpb;
//   tpa=tp->left;
//   tpb=tp->right;
//   free(tp);
//   if (tpa!=NULL) {
//     tree_free(tpa);
//   }
//  if (tpb!=NULL) {
//     tree_free(tpb);
//   }
// }

// void treebox_free(treebox b) {
//   struct tree *t = *b;
//   if(t != NULL){  
//    tree_free(t);
//   }
//   free(b);
// }

void insert (treebox tb, int x, void *value) {
  for(;;) {
       _Atomic struct tree *t = atomic_load(tb);
      if (t==NULL) {         
      struct tree *p  = (struct tree *) surely_malloc (sizeof *p);
      p->key=x;
      p->value=value;
      p->left= NULL;
      p->right=NULL;
      int result = atomic_compare_exchange_strong(tb, &t, p);
      if(result){
        return;
      }
      else{
        free(p);        
        continue;
      }
    } else {
      struct tree p = atomic_load(t);
      int y = p.key;
      if (x<y){
       tb = &p.left;
      } else if (y<x){
       tb = &p.right;       
      }else {
      	p.value=value;
        atomic_store(t,p);
      	return;
      }
    }
  }
}


void *lookup (treebox tb, int x) {
  _Atomic struct tree *t = atomic_load(tb);
   void *v;
  while (t!=NULL) {
     struct tree p = atomic_load(t);
    int y = p.key;
    if (x<y){
      t= p.left;
    }else if (y<x){
      t=p.right;
    }else {
      v = p.value;
      return v;
    }
  }
  return NULL;
}

// void turn_left(struct tree_t * tgl, struct tree_t * tgr) {
//   struct tree_t * mid;
//   struct tree * r, *l;
//   r = tgr->t;
//   mid = r->left;
//   l = tgl->t;
//   l->right = mid;
//   r->left = tgr; 
//   tgl->t = r;
//   tgr->t = l;
// }

// void pushdown_left (struct tree_t *tgp) {
//   struct tree *p, *q;
//   struct tree_t *tgq;
//   for(;;) {
//     void *lp = tgp->lock; // initial lp acquired in delete
//     p = tgp->t;
//     tgq = p->right;
//     void *lq = tgq->lock;
//     acquire(lq);
//     q = tgq->t;
//     if (q==NULL) {
//       struct tree_t *tgl = p->left;
//       acquire(tgl->lock);
//       tgp->t = tgl->t;
//       free(p);
//       freelock2(lq);
//       free(lq);
//       free(tgq);
//       freelock2(tgl->lock);
//       free(tgl->lock);
//       free(tgl);
//       release2(lp);
//       return;
//     } else {
//       turn_left(tgp, tgq);
//       tgp = q->left;
//       release2(lp);
//     }
//   }
// }

// void delete (treebox t, int x) {
//   struct tree *p;
//   struct tree_t *tgt;
//   tgt = *t;
//   void *l = tgt->lock;
//   acquire(l);
//   for(;;) {
//     p = tgt->t;
//     if (p==NULL) {
//       release2(l);
//       return;
//     } else {
//       int y = p->key;
//       if (x<y){
// 	tgt = p->left;
// 	void *l_old = l;
// 	l = tgt->lock;
// 	acquire(l);
//         release2(l_old);
//       }else if (y<x){
// 	tgt = p->right;
// 	void *l_old = l;
// 	l = tgt->lock;
// 	acquire(l);
//         release2(l_old);
//       }else {
//       	pushdown_left(tgt);	
//       	return;
//       }
//     }
//   }
// }

void *thread_func(void *args) {
  //lock_t *l = &thread_lock;
  
  // insert at key 1
  insert(tb,1,"ONE_FROM_THREAD");
  
  //release2((void*)l);
  return (void *)NULL;
}


int main (void) {
  tb = treebox_new();  
 // lock_t *t_lock = &thread_lock;
  insert(tb,3,"three");
  insert(tb,1,"one");
  insert(tb,4,"four");
  
  //makelock((void*)t_lock);
  /* Spawn */
  spawn((void *)&thread_func, (void *)NULL);
  
  //insert at key 1
  insert(tb,1,"ONE");
  
  /*JOIN */
 // acquire((void*)t_lock);  
 // freelock2((void*)t_lock);
  
  /* printf("%s\n", lookup(tb, 1)); */
 // treebox_free(tb);
  return 0;
}
