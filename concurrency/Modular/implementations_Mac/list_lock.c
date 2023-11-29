#include "list_lock.h"

void insertOp_lock(node_t* p, int x, void* value, Status status){
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
        insertOp(&p->t, x, value, status, &dlist);
    }
    else{
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        ((node_t*)dlist.list[0])->t = p->t;
        insertOp(&(p->t), x, value, status, &dlist);
    }
} 

void printDS_lock(void **t){
    printf("For Linked-list - LOCK-COUPLING\n");
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