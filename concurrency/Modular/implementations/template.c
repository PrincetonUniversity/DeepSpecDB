//
//  template.c
//  BST
//
//  Created by Duc Than Nguyen on 6/22/23.
//

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "threads.h"
#include "template.h"

void insert (treebox t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;
    Status status = traverse(pn, x);
    if (status == 0){
        changeValue_helper(pn->p, value);
    }
    else
    {
        insertOp_helper(pn->p, x, value, status);
    }
    release(getLock(pn->n));
    free(pn);
}


void *lookup (treebox t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = *t;
    Status status = traverse(pn, x);
    if (status == FOUND){
        v = getValue_helper(pn->p);
    }
    else
    {
        v = NULL;
    }
    release(getLock(pn->n));
    free(pn);
    return v;
}


treebox treebox_new(void) {
    treebox p = (treebox) surely_malloc(sizeof (*p));
    node_t *newt;
    //*p = newt;
    *p = treebox_helper(newt);
    return p;
}

/*
void treebox_free(treebox b) {
    struct node_t *t = *b;
    freeDS(t);
    free(b);
}
*/
