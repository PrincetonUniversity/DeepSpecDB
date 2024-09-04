#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "threads.h"
#include "common.h"

typedef struct node node;

Status findNext(node* p_ds, void** n_ds, int x);
void insertOp(node* p_ds, int x, void* value);
void changeValue(node* p_ds, void* value);
void* getValue(node* p_ds);
void printDS (node* tgt);
void freeDS(void* p_ds);
int getKey(void* p_list);

//support print function 

void *getLeftChild(node *node);
void *getRightChild(node *node);

void *getNext(node *node); //for list

void printKey(node *node);
