#include "list_giveup.h"

void insertOp_giveup(node_t* p, int x, void* value, Status status){
    DList dlist; 
    dlist.size = 1; // For Linked-list 
    dlist.list = (void**)surely_malloc(dlist.size * sizeof(node_t*));
    dlist.list[0] = (void*)surely_malloc(sizeof (node_t));
    if (status == NULLNEXT) {
        ((node_t*)dlist.list[0])->t = NULL;
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        insertOp(&p->t, x, value, status, &dlist);
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
        insertOp(&(p->t), x, value, status, &dlist);
    }
    free(dlist.list);
} 

void printDS_giveup(void **t){
    printf("For Linked-list - GIVEUP\n");
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