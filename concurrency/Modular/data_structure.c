//
//  data_structure.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

int findnext (pn *pn, int x, void *value){
    int y = pn->p->t->key;
    
    if (x < y){
        pn->n = pn->p->t->left;
        return 1;
    }
    else if (x > y){
        pn->n = pn->p->t->right;
        return 1;
    }
    else{
        return 0;
    }
}

void insertOp(pn *pn, int x, void *value){
    tree_t *p1 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    tree_t *p2 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    p1->t = NULL; p2->t = NULL;
    //lock_t *l1;
    //l1 = makelock();
    lock_t *l1 = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l1);
    p1->lock = l1;
    release(l1);
    //lock_t *l2;
    //l2 = makelock();
    lock_t *l2 = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l2);
    p2->lock = l2;
    release(l2);
    pn->p->t = (struct tree *) surely_malloc (sizeof *(pn->p->t));
    pn->p->t->key = x;
    pn->p->t->value = value;
    pn->p->t->left = p1;
    pn->p->t->right = p2;
    //Range
    p1->min = pn->p->min;
    p1->max = x;
    p2->min = x;
    p2->max = pn->p->max;
}

treebox treebox_new(void) {
    treebox p = (treebox) surely_malloc(sizeof (*p));
    tree_t *newt = (tree_t *) surely_malloc(sizeof(tree_t));
    *p = newt;
    //lock_t *l;
    //l = makelock();
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    newt->lock = l;
    newt->t = NULL;
    newt->min = INT_MIN;
    newt->max = INT_MAX;
    release(l);
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
    freelock(l);
    free(tgp);
}

void treebox_free(treebox b) {
    struct tree_t *t = *b;
    tree_free(t);
    free(b);
}

