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
    Status status = traverse(pn, x);
    if (status == 0){
        changeValue_helper(pn->p, value);
    }
    else
    {
        insertOp_helper(pn->p, x, value, status);
    }
    release(get_lock(pn->n));
    free(pn);
}


void *lookup (css* t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = get_root(t);
    Status status = traverse(pn, x);
    if (status == FOUND){
        v = getValue(pn->p);
    }
    else
    {
        v = NULL;
    }
    release(get_lock(pn->n));
    free(pn);
    return v;
}
