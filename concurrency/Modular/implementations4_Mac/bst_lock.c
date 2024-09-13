#include "lock_ds.h"

void insertOp_lock(css* c, node *p, int x, void* value, Status status){
    int signal;  // Tracks left, right, or NULL

    // Insert the new node and retrieve metadata for p
    node *new_node = insertOp(p, x, value, &signal);
    //md_entry* md = lookup_md(c, p);

    // Allocate metadata for the new node
    int idx = hash(new_node);
    c->metadata[idx] = surely_malloc(sizeof(md_entry));

    // Initialize and set lock for the new node
    lock_t *lock = surely_malloc(sizeof(lock_t));
    makelock(lock);
    c->metadata[idx]->lock = lock;
    release(lock);

    // Handle case where status is CONTINUE (p == NULL)
    if (status == CONTINUE) {
        c->root = new_node;
        return;
    }
}
void printDS_lock(css *t){
    printf("For BST - LOCK-COUPLING\n");
    struct node* tgt;
    tgt = get_root(t);

    if (tgt == NULL) {
        return;
    }
    stack s;
    initStack(&s);
    node * current = tgt;

    while (current != NULL || !isEmpty(&s)) {
        while (current != NULL) {
            push(&s, current);
            current = (node *)get_left(current);
        }

        current = pop(&s);
        print_key_value(current);
        current = (node *)get_right(current);
    }
}