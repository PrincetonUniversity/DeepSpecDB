#include "data_structure.h"

typedef struct node { int key; void *value; node *left, *right; } node;

Status findNext(node* p, void** n_tree, int x) {
    int y = p->key;
    if (x < y) {
        *n_tree = p->left;
        return CONTINUE;
    }
    else if (x > y) {
        *n_tree = p->right;
        return CONTINUE;
    }
    else {
        return FOUND;
    }
}

//status: 0 for NULL, 1 for going left, 2 for going right
node * insertOp(node* p, int x, void* value){
    if (p && p->key == x){
        p->value = value;
        return NULL;
    }
    node* new_node = surely_malloc(sizeof(node));
    new_node->key = x;
    new_node->value = value;
    new_node->left = NULL;
    new_node->right = NULL;

    // If the current node is NULL, place the new node here
    if(p == NULL){
        return new_node;
    }
    // Determine whether to insert to the left or right
    if(x < p->key){
        p->left = new_node;
    }
    else{
        p->right = new_node;
    }
    return new_node;
}

void change_value(node* p, void* value){
    p->value = value;
}

void* get_value(node* p){
    return p->value;
}

int get_key(node* p){
    return p->key;
}

void *get_left(node *node) {
    if (node == NULL)
        return NULL; 
    return node->left;
}

void *get_right(node *node) {
    if (node == NULL)
        return NULL; 
    return node->right;
}

void print_key_value(node *node){
    printf ("(%d, %s) \n", node->key, (char*)node->value);
}
