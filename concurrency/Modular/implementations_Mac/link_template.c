//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "link_template.h"


Status traverse(pn *pn, int x) {
    Status status;
    void *p = (pn->n);
    for( ; ; ){
        acquire(pn->n->lock);
        pn->p = pn->n;
        if (pn->p->t == NULL){
            return NULLNEXT;
        }
        else{
            status = findNext(pn->p, (void**)&pn->n, x);
            if (status == FOUND){
                return FOUND;
            }
            else if (status == NOTFOUND){
                return NOTFOUND;
            }
            else{
                release(pn->p->lock);
            }
        }        
    }
}

void insertOp_helper(void *p, int x, void* value, Status status){
    DList dlist;
    printf("Link\n");
    insertOp(p, x, value, status, &dlist);
    if(dlist.size == 2){
        node_t *p1 = dlist.list[0];
        node_t *p2 = dlist.list[1];
    }
    else if (dlist.size == 1){
        node_t *pl = dlist.list[0];
    }
    else
        return;
}

node_t * treebox_helper(node_t *newt){
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    newt->lock = l;
    newt->t = NULL;
    release(l);
    return newt;
}
