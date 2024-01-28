#include "bst_giveup.h"

void insertOp_giveup(node_t* p, int x, void* value, Status status){
    node_t* p1 = (struct node_t*)surely_malloc(sizeof (node_t));
    node_t* p2 = (struct node_t*)surely_malloc(sizeof (node_t));
    p1->t = NULL;
    p2->t = NULL;

    lock_t l1 = makelock();
    p1->lock = l1;
    release(l1);

    lock_t l2 = makelock();
    p2->lock = l2;
    release(l2);

    DList dlist; 
    dlist.size = 2; // For BST 
    dlist.list = (void**)surely_malloc(dlist.size * sizeof(node_t *));
    dlist.list[0] = (void*)p1;
    dlist.list[1] = (void*)p2;

    insertOp(&p->t, x, value, status, &dlist);

    ((node_t*)dlist.list[0])->min = p->min;
    ((node_t*)dlist.list[0])->max = x;
    ((node_t*)dlist.list[1])->min = x;
    ((node_t*)dlist.list[1])->max = p->max;
    free(dlist.list);
} 

void printDS_giveup(void **t){
    printf("For BST - GIVEUP\n");
    struct node_t* tgt;
    tgt = *t;

    if (tgt == NULL) {
        return;
    }
    stack s;
    initStack(&s);
    node_t * current = tgt;

    while (current->t != NULL || !isEmpty(&s)) {
        while (current->t != NULL) {
            push(&s, current);
            current = (node_t *)getLeftChild(current->t);
        }

        current = pop(&s);
        printKey(current->t);
        current = (node_t *)getRightChild(current->t);
    }
}