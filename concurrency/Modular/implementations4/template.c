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

void insert (css* t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = get_root(t);
    Status status = traverse(t, pn, x);
    insertOp_helper(t, pn->p, x, value, status);
    if (pn->p){
        release(get_lock(t, pn->p));
    }
    free(pn);
}

void *lookup (css* t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = get_root(t);
    Status status = traverse(t, pn, x);
    if (status == FOUND){
        v = get_value(pn->p);
    }
    else{
        v = NULL;
    }
    if (pn->n){
        release(get_lock(t, pn->n));
    }
    free(pn);
    return v;
}