#include "data_structure.h"
#include "template.h"

typedef struct md_entry { lock_t lock; } md_entry;
typedef struct css { node* root; md_entry* metadata[16384]; } css;

int hash(node* p);

int inRange(md_entry* m, int x);
md_entry* lookup_md(css* c, node* p);
Status traverse(css* c, pn *pn, int x);

void insertOp_lock(css* c, node *p, int x, void* value, Status status);
void insertOp_helper(css* c, node *p, int x, void* value, Status status);

void change_value_helper(node* p_ds, void* value);
void *get_value_helper(node* p);

//support print ds
void printDS_lock (css *t);
void printDS_helper (css *t);

typedef struct stack {
    struct node * items[100]; // Assuming a maximum of 100 nodes
    int top;
} stack;

static void initStack(stack* s) {
    s->top = -1;
}

// Function to push a node onto the stack
static void push(stack* s, node * item) {
    s->items[++s->top] = item;
}

// Function to check if the stack is empty
static int isEmpty(stack* s) {
    return s->top == -1;
}

// Function to pop a node from the stack
static node* pop(stack* s) {
    if (!isEmpty(s)) {
        return s->items[s->top--];
    }
    return NULL;
}
