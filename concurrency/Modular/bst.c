//
//  data_structure.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"

typedef struct node {int key; void *value; struct tree_t *left, *right;} node;
typedef struct tree_t {node *t; lock_t *lock; int min; int max; } tree_t;


void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

int findnext(void* p_tree, void** n_tree, int x) {
    tree_t* p = (tree_t*)p_tree;
    tree_t** n = (tree_t**)n_tree;
    int y = p->t->key;
    if (x < y) {
        *n = p->t->left;
        return 1;
    }
    else if (x > y) {
        *n = (struct tree_t*) p->t->right;
        return 1;
    }
    else {
        return 0;
    }
}


void insertOp(void* p_tree, int x, void* value) {
    tree_t* p = (struct tree_t*)p_tree;
    tree_t* p1 = (struct tree_t*)surely_malloc(sizeof (tree_t));
    tree_t* p2 = (struct tree_t*)surely_malloc(sizeof (tree_t));
    p1->t = NULL;
    p2->t = NULL;

    lock_t* l1 = (lock_t*)surely_malloc(sizeof(lock_t));
    makelock(l1);
    p1->lock = l1;
    release(l1);

    lock_t* l2 = (lock_t*)surely_malloc(sizeof(lock_t));
    makelock(l2);
    p2->lock = l2;
    release(l2);
    
    p->t = (struct node *) surely_malloc (sizeof *(p->t));
    p->t->key = x;
    p->t->value = value;
    p->t->left = (struct tree_t*)p1;
    p->t->right = (struct tree_t*)p2;
        //Range
    p1->min = p->min;
    p1->max = x;
    p2->min = x;
    p2->max = p->max;
}

void changeValue(void* p_tree, void* value){
    tree_t* p = (tree_t*)p_tree;
    p->t->value = value;
}

void * getValue(void* p_tree){
    tree_t* p = (tree_t*)p_tree;
    return p->t->value;
}

//Traverse

void Inorder(tree_t *p){
    if (p->t != NULL){
        Inorder(p->t->left);
        printf ("node->data %d %s \n", p->t->key, p->t->value);
        Inorder(p->t->right);
    }
}

void traverseInorder (void** t){
    struct tree_t* tgt;
    tgt = *t;
    Inorder(tgt);
}

void tree_free(void *p_tree) {
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
        tree_free(pa);
        tree_free(pb);
    }
    freelock2(l);
    free(l);
    free(tgp);
}


