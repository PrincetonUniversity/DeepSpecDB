//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "giveup_template.h"

int inRange(node_t *p, int x){
    if (x > p->min && x < p->max)
        return 1;
    else
        return 0;
}
//FOUND == 0, NOTFOUND = 1, NULLNEXT = 2
Status traverse(pn *pn, int x) {
    Status status = 2; //NULLNEXT
    void *p = (pn->n);
    for( ; ; ){
        acquire(pn->n->lock);
        pn->p = pn->n;
        if (inRange (pn->p, x) == 1){
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
                    release(pn->p->lock);
                }
            }
        }
        else{
            release(pn->p->lock);
            pn->n = p;
        }
            
    }
    return status;
}

/*
void insertOp_list(node_t* p, int x, void* value, Status status){
    struct node_t* pl; 
    pl = (struct node_t*)surely_malloc(sizeof (node_t));
    if (status == NULLNEXT) {
        pl->t = NULL;
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        pl->lock = l;
        release(l); 

        insertOp_llist(&p->t, x, value, status, pl);
        pl->max = INT_MAX;
        pl->min = x;
    }
    else{
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        pl->lock = l;
        release(l);
        pl->t = p->t;
        pl->max = p->max; 
        pl->min = x; 
        insertOp_llist(&(p->t), x, value, status, pl);
    }
} 
*/
/*
void insertOp_list(node_t* p, int x, void* value, Status status){
    DList dlist; 
    dlist.size = 1; // For Linked-list 
    dlist.list = (void**)surely_malloc(dlist.size * sizeof(node_t));
    dlist.list[0] = (struct node_t*)surely_malloc(sizeof (node_t));
    if (status == NULLNEXT) {
        ((node_t*)dlist.list[0])->t = NULL;
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        insertOp_llist(&p->t, x, value, status, &dlist);
        ((node_t*)dlist.list[0])->min = x;
        ((node_t*)dlist.list[0])->max = INT_MAX;
    }
    else{
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        ((node_t*)dlist.list[0])->t = p->t;
        ((node_t*)dlist.list[0])->max = p->max; 
        ((node_t*)dlist.list[0])->min = x;
        insertOp_llist(&(p->t), x, value, status, &dlist);
    }
}
*/
void insertOp_helper(node_t *p, int x, void* value, Status status){
    insertOp_giveup(p, x, value, status);
    //insertOp_list(p, x, value, status);
}

node_t * treebox_helper(node_t *newt){
    newt = (node_t *) surely_malloc(sizeof(node_t));
    lock_t l = makelock();
    newt->lock = l;
    newt->t = NULL;
    newt->min = INT_MIN;
    newt->max = INT_MAX;
    release(l);
    return newt;
}

lock_t getLock(node_t *p){
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
    printDS_giveup(t);
}


/*
void printDS_helper (void **t){
    struct node_t* tgt;
    tgt = *t;

    if (tgt == NULL) {
        return;
    }
    stack s;
    initStack(&s);
    node_t * current = tgt;
    while (current->t != NULL) {
        push(&s, current);
        current = (node_t *)getNext(current->t);
    }
    while (!isEmpty(&s)){   
        current = pop(&s);
        printKey(current->t);
    }
}
*/