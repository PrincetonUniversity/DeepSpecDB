//
//  give_up_template.h
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"
#include "template.h"

typedef struct node_t {node *t; lock_t lock; } node_t;
/*
//void insertOp_bst(node_t* p, int x, void* value, Status status);
//void insertOp_list(node_t* p, int x, void* value, Status status);
*/

void insertOp_lock(node_t* p, int x, void* value, Status status);
void insertOp_helper(node_t* p, int x, void* value, Status status);
int inRange(node_t *p, int x);
Status traverse(pn *pn, int x);
node_t * treebox_helper(node_t *newt);
lock_t getLock(node_t *p);
void changeValue_helper(node_t * p, void * value);
void *getValue_helper(node_t* p_ds);
void printDS_lock (void **t);
void printDS_helper (void **t);


typedef struct stack {
    struct node_t * items[100]; // Assuming a maximum of 100 nodes
    int top;
} stack;

static void initStack(stack* s) {
    s->top = -1;
}

// Function to push a node onto the stack
static void push(stack* s, node_t * item) {
    s->items[++s->top] = item;
}

// Function to check if the stack is empty
static int isEmpty(stack* s) {
    return s->top == -1;
}

// Function to pop a node from the stack
static node_t* pop(stack* s) {
    if (!isEmpty(s)) {
        return s->items[s->top--];
    }
    return NULL;
}
