//
//  data_structure.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"

typedef struct node {int key; void *value; void *left, *right;} node;

//typedef struct  tree_t {node *t; lock_t *lock; } tree_t;

Status findNext(node* p_tree, void** n_tree, int x) {
    int y = p_tree->key;
    if (x < y) {
        *n_tree = p_tree->left;
        return NULLNEXT;
    }
    else if (x > y) {
        *n_tree = p_tree->right;
        return NULLNEXT;
    }
    else {
        return FOUND;
    }
}

void insertOp(node** p_tree, int x, void* value, Status status, DList * dlist) {    
    struct node* new_node = (struct node*)surely_malloc(sizeof(struct node));
    new_node->key = x;
    new_node->value = value;
    new_node->left = dlist->list[0];
    new_node->right = dlist->list[1];
    *p_tree = new_node;  
}

void changeValue(void* p_tree, void* value){
    node* p = (node*)p_tree;
    p->value = value;
}

void * getValue(void* p_tree){
    node* p = (node*)p_tree;
    return p->value;
}


/*
void freeDS(void *p_tree) {
    tree_t* tgp = (struct tree_t*)p_tree;
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