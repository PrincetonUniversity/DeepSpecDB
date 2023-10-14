//
//  template.c
//  BST
//
//  Created by Duc Than Nguyen on 6/22/23.
//

#include "template.h"
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "threads.h"

void insert (treebox t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;
    Status status = traverse(pn, x);
    if (status == FOUND){
        changeValue(pn->p, value);
    }
    else
    {
        insertOp(pn->p, x, value, status);
    }
    release(pn->n->lock);
    free(pn);
}

void *lookup (treebox t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = *t;
    Status status = traverse(pn, x);
    if (status == FOUND){
        v = getValue(pn->p);
    }
    else
    {
        v = NULL;
    }
    release(pn->n->lock);
    free(pn);
    return v;
}

treebox treebox_new(void) {
    treebox p = (treebox) surely_malloc(sizeof (*p));
    node_t *newt = (node_t *) surely_malloc(sizeof(node_t));
    *p = newt;
    //lock_t *l;
    //l = makelock();
    lock_t l = makelock();
    //makelock(l);
    newt->lock = l;
    newt->t = NULL;
    newt->min = INT_MIN;
    newt->max = INT_MAX;
    release(l);
    return p;
}

void treebox_free(treebox b) {
    struct node_t *t = *b;
    freeDS(t);
    free(b);
}
