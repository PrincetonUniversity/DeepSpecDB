#include "giveup_ds.h"

void insertOp_giveup(css *c, node *p, int x, void *value, Status status){
    int signal;  // Tracks left, right, or NULL

    // Insert the new node and retrieve metadata for p
    node *new_node = insertOp(p, x, value);
    if (!new_node){
        return;
    }
    
    md_entry* md = lookup_md(c, p);

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
        c->metadata[idx]->min = INT_MIN;
        c->metadata[idx]->max = INT_MAX;
        return;
    }

    // Set the min and max ranges based on the signal (left or right)
    if (x < get_key(p)){ //left insertion
        c->metadata[idx]->min = md->min;
        c->metadata[idx]->max = get_key(p);
    }
    else {// right insertion
        c->metadata[idx]->min = get_key(p);
        c->metadata[idx]->max = md->max;
    }
}

void printDS_giveup(css *t){
    printf("For BST - GIVEUP\n");
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