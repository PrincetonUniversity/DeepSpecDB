#include "data_structure.h"

typedef struct node { int key; void *value; node *next; } node;

Status findNext(node* p, void** n_list, int x) {
    int y = p->key;
    if (x > y) {
        *n_list = p->next;
        return CONTINUE;
    }
    else if (x < y) {
        return NOTFOUND;
    }
    else {
        return FOUND;
    }
}

node * insertOp(node* p, int x, void* value, int *signal){
    node* new_node = surely_malloc(sizeof(node));
    new_node->key = x;
    new_node->value = value;
    new_node->next = NULL;

    // If the current node is NULL, place the new node here
    if(p == NULL){
        return new_node;
    }

    // Determine whether to insert to the right or in the middle 
    if(x < p->key){
        new_node->next = p->next;
        p->next = new_node;
        // Swap keys and values with the new node
        int temp_key = p->key;
        p->key = x;
        new_node->key = temp_key;
        
        void* temp_value = p->value;
        p->value = value;
        new_node->value = temp_value;
        
        *signal = 0; // Inserted in the middle
    }
    else{
        // Insert after p
        new_node->next = p->next;
        p->next = new_node;
        *signal = 1; // Inserted to the right
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

void *get_next(node *node) {
    if (node == NULL)
        return NULL; 
    return node->next;
}

void print_key_value(node *node){
    printf ("(%d, %s) \n", node->key, (char*)node->value);
}
