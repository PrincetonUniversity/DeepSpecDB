//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "lock_template.h"

//FOUND == 0, NOTFOUND = 1, NULLNEXT = 2
Status traverse(pn *pn, int x) {
    Status status = 2; //NULLNEXT
    void *p = (pn->n);
    for( ; ; ){
        pn->p = pn->n;
        if (pn->p->t == NULL){
            status = NULLNEXT;
            break;
        }
        else{
            status = findNext(pn->p->t, (void**)&pn->n, x);
            if (status == FOUND){
                status = FOUND;
                break;
            }
            else if (status == NOTFOUND){
                status = NOTFOUND;
                break;
            }
            else{
                acquire(pn->n->lock);
                release(pn->p->lock);
            }
        }
    }
    return status;
}

void insertOp_helper(node_t *p, int x, void* value, Status status){
    insertOp_lock(p, x, value, status);
    //insertOp_list(p, x, value, status);
}
/*
void insertOp_helper(void *p, int x, void* value, Status status){
    DList dlist;
    printf("lock\n");
    //dlist.list = NULL; // Initialize the list to NULL
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
*/


node_t * treebox_helper(node_t *newt){
    newt = (node_t *) surely_malloc(sizeof(node_t));
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    newt->lock = l;
    newt->t = NULL;
    release(l);
    return newt;
}

lock_t* getLock(node_t *p){
    return p->lock;
}

void changeValue_helper(node_t *p, void * value){
    changeValue(p->t, value);
}

void *getValue_helper(node_t* p){
    return getValue(p->t);
}

//for BST

void printDS_helper (void **t){
    printDS_lock(t);
}