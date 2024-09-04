#include "data_structure.h"

typedef struct node { int key; void *value; node *left, *right; } node;

Status findNext(node* p, void** n_tree, int x) {
    int y = p->key;
    if (x < y) {
        *n_tree = p->left;
        return NULLNEXT;
    }
    else if (x > y) {
        *n_tree = p->right;
        return NULLNEXT;
    }
    else {
        return FOUND;
    }
}

node* insertOp(node* p, int x, void* value, Status status){
    node* new_node = malloc(sizeof(node));
    new_node->key = x;
    new_node->value = value;
    new_node->left = NULL;
    new_node->right = NULL;
    if(!p) return new_node;
    if(x < p->key)
        p->left = new_node;
    else
        p->right = new_node;
    return new_node;
}

void changeValue(node* p, void* value){
    p->value = value;
}

void* getValue(node* p){
    return p->value;
}


/*
void freeDS(void *p) {
    tree_t* tgp = (struct tree_t*)p;
    struct tree_t *pa, *pb;
    node* p;
    void *l = tgp->lock;
    acquire(l);
    p = tgp->t;
    if (p!=NULL) {
        pa=p->left;
        pb=p->right;
        free(p);
        freeDS(pa);
        freeDS(pb);
    }
    freelock2(l);
    free(l);
    free(tgp);
}
*/

void *getLeftChild(node *node) {
    if (node == NULL)
        return NULL; 
    return node->left;
}

void *getRightChild(node *node) {
    if (node == NULL)
        return NULL; 
    return node->right;
}

void printKey(node *node){
    printf ("(%d, %s) \n", node->key, (char*)node->value);
}
