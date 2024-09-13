#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "threads.h"
#include "common.h"

typedef struct node node;
Status findNext(node* p_ds, void** n_ds, int x);
node * insertOp(node* p_ds, int x, void* value, int * signal);
void change_value(node* p_ds, void* value);
void* get_value(node* p_ds);
int get_key(node* p_list);

//support print function 

void *get_left(node *node); //for BST
void *get_right(node *node); //for BST

void *get_next(node *node); //for list

void print_key_value(node *node);
