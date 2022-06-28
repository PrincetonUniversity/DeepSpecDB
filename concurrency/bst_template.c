//
//  main.c
//  BST
//
//  Created by Duc Than Nguyen on 1/2/22.
//


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

//Orginal Code
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
            
            //  printf ("%d %s\n", p->key, p->value);
            release2(l);
            return;
        } else {
            int y = p->key;
            if (x<y){
                tgt = p->left;
                printf("Left - x = %d, y = %d\n", x, p->key);
                void *l_old = l;
                l = tgt->lock;
                acquire(l);
                release2(l_old);
            } else if (y<x){
                tgt = p->right;
                printf("Right - x = %d, y = %d\n", x, p->key);
                void *l_old = l;
                l = tgt->lock;
                acquire(l);
                release2(l_old);
            }else {
                p->value=value;
                printf ("Exclude %d %s\n", p->key, p->value);
                release2(l);
                return;
            }
        }
    }
}


//Template style

typedef struct pn {
    struct tree_t *p;
    struct tree_t *n;
} pn;

int findnext (pn *pn, int x, void *value){
    int y = pn->p->t->key;
    
    if (x < y){
        pn->n = pn->p->t->left;
        //printf("Left - x = %d, y = %d\n", x, pn->p->t->key);
        return 1;
    }
    else if (x > y){
        pn->n = pn->p->t->right;
        //printf("Right - x = %d, y = %d\n", x, pn->p->t->key);
        return 1;
    }
    else{
        return 0;
    }
}

int traverse(pn *pn, int x, void *value) {
    int flag = 1;
    for( ; ; ){
        pn->p = pn->n;
        if (pn->p->t == NULL){
            break;
        }else {
            int b = findnext(pn, x, value);
            if (b == 0){
                flag = 0;
                break;
            }
            else{
                acquire(pn->n->lock);
                release2(pn->p->lock);
            }
        }
    }
    return flag;
}

void insertOp(pn *pn, int x, void *value){
    tree_t *p1 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    tree_t *p2 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    p1->t = NULL;
    p2->t = NULL;
    lock_t *l1 = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l1);
    p1->lock = l1;
    release2(l1);
    lock_t *l2 = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l2);
    p2->lock = l2;
    release2(l2);
    pn->p->t = (struct tree *) surely_malloc (sizeof *(pn->p->t));
    pn->p->t->key = x;
    pn->p->t->value = value;
    pn->p->t->left = p1;
    pn->p->t->right = p2;
}

void insert2 (treebox t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;
    //pn->n->lock = (lock_t *) surely_malloc(sizeof(lock_t));
    
    acquire(pn->n->lock);
    if (traverse(pn, x, value) == 0){
        pn->p->t->value = value;
    }
    else
    {
        insertOp(pn, x, value);
    }
    //release2(pn->p->lock);
    release2(pn->n->lock);
    free(pn);
}

//Traverse
void Inorder(struct tree_t *p){
    if (p->t != NULL){
        Inorder(p->t->left);
        printf ("node->data %d %s \n", p->t->key, p->t->value);
        Inorder(p->t->right);
    }
}

void traverseInorder (treebox t){
    struct tree *p;
    struct tree_t *tgt;
    tgt = *t;
    Inorder(tgt);
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



void *thread_func(void *args) {
    lock_t *l = &thread_lock;
    
    // insert at key 1
    //insert2(tb,6,"ONE_FROM_THREAD");
    //insert2(tb,4,"FOUR");
    //   insert(tb,5,"FIVE");
    
    release2((void*)l);
    return (void *)NULL;
}


int main (void) {
    tb = treebox_new();
    lock_t *t_lock = &thread_lock;
    insert2(tb,3,"three");
    insert2(tb,1,"One");
    insert2(tb,4,"four");
    
    //insert2(tb, 4, "four");
    //insert2(tb, 7, "seven");
    //insert2(tb, 3, "three");
    
    //insert2(tb, 1, "one");
    //insert2(tb, 1, "four");
    //insert2(tb, 1, "three");
    //insert2(tb, 2, "two");
    //insert2(tb, 1, "two");
    
    //insert(tb, 4, "four");
    
    //insert(tb, 6, "six");
    //insert(tb, 5, "five");
    
    makelock((void*)t_lock);
    /* Spawn */
    spawn((void *)&thread_func, (void *)NULL);
    
    //insert at key 1
    //insert2(tb,1,"ONE");
    
    /*JOIN */
    acquire((void*)t_lock);
    freelock2((void*)t_lock);
    
    // printf ("%d", sizeof (pthread_mutex_t));
    
    printf("%s\n", lookup(tb, 4));
    
    printf ("Traverse\n");
    traverseInorder(tb);
    
    treebox_free(tb);
    
    return 0;
}

