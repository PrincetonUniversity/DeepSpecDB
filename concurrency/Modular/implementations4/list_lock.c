#include "lock_ds.h"

void insertOp_lock(css *c, node *p, int x, void *value, Status status){
    int signal; // Indicates left, right, or NULL
    node *new_node = insertOp(p, x, value);
    if (!new_node){
        return;
    }

    // Calculate index and allocate metadata for the new node
    int idx = hash(new_node);
    c->metadata[idx] = surely_malloc(sizeof(md_entry));

    // Initialize lock for the new node
    lock_t lock = makelock();
    c->metadata[idx]->lock = lock;
    release(lock);

    // Update root and metadata if status is CONTINUE
    if (status == CONTINUE) {
        c->root = new_node;
        return;
    }
}

void printDS_lock(css *t){
    printf("For Linked list - LOCK-COUPLING\n");
    struct node* tgt;
    tgt = get_root(t);

    if (tgt == NULL) {
        return;
    }
    stack s;
    initStack(&s);
    node * current = tgt;

    while (current != NULL){
        push(&s, current);
        current = (node*)get_next(current);
    }
    while (!isEmpty(&s)){   
        current = pop(&s);
        print_key_value(current);
    }
}