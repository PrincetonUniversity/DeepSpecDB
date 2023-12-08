//
//  list.c
//  BST
//
//  Created by Duc Than Nguyen on 6/4/23.
//

#include "data_structure.h"

typedef struct node {int key; void *value; void * next;} node;

Status findNext(node* p_list, void** n_list, int x) {
    int y = p_list->key;
    if (x > y) {
        *n_list = p_list->next;
        return NULLNEXT;
    }
    else if (x < y) {
        return NOTFOUND;
    }
    else {
        return FOUND;
    }
}
// pl has type of node
// then will pass pnext->t as an argument
/*
void insertOp_llist(node** p_list, int x, void* value, Status status, node *pl, void *pt) {    
    //node* pll = (struct node*)pl;
    
    struct node* new_node = (struct node*)surely_malloc(sizeof(struct node));
    //printf ("new_node->key = %d\n", x);
    if (status == NULLNEXT) {
        //printf ("insertOp_llist_1\n");
        //pl = NULL;
        (*p_list) = (struct node*)surely_malloc(sizeof(struct node));
        
    } else {
        //printf ("insertOp_llist_2\n");
        new_node = *p_list;
        pl = (struct node *) surely_malloc (sizeof(struct node));
        pl->key = new_node->key;
        pl->value = new_node->value;
        pl->next = new_node->next;
        printf ("new_node->key = %d\n", new_node->key);
    }
    new_node->key = x;
    new_node->value = value;
    new_node->next = pt;
    *p_list = new_node;  
}
*/

void insertOp(node** p_list, int x, void* value, Status status, DList * dlist) {    
    struct node* new_node = (struct node*)surely_malloc(sizeof(struct node));
    new_node->key = x;
    new_node->value = value;
    new_node->next = dlist->list[0];
    (*p_list) = new_node;   
}

/*
void insertOp(void* p_list, int x, void* value, Status status, DList *dlist){
    list_t* p = (struct list_t*)p_list;
    list_t* pl = (struct list_t*)surely_malloc(sizeof (list_t) + 1); //new pl
    pl->t = NULL;
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    pl->lock = l;
    release(l);

    if (status == NULLNEXT) {
        pl->t = NULL;
        p->t = (struct node *) surely_malloc (sizeof *(p->t));
    } else {
        pl->t = (struct node *) surely_malloc (sizeof *(pl->t));
        pl->t->key = p->t->key;
        pl->t->value = p->t->value;
        pl->t->next = p->t->next;
    }
    p->t->key = x;
    p->t->value = value;
    p->t->next = (struct list_t*)pl;
    dlist->size = 1; // Linked list

    dlist->list = (void**)surely_malloc(dlist->size * sizeof(list_t*));
    dlist->list[0] = pl;
}
*/

/*
void freeDS(void *p_list) {
    list_t* tgp = (struct list_t*)p_list;
    struct list_t *pn;
    node* p;
    void *l = tgp->lock;
    acquire(l);
    p = tgp->t;
    if (p!=NULL) {
        pn = p->next;
        free(p);
        freeDS(pn);
    }
    freelock(l);
    free(tgp);
}
*/

void changeValue(void* p_list, void* value){
    node* p = (node*)p_list;
    p->value = value;
}

void * getValue(void* p_list){
    node* p = (node*)p_list;
    return p->value;
}

int getKey(void* p_list){
    node* p = (node*)p_list;
    return p->key;
}

void *getNext(node *node) {
    if (node == NULL)
        return NULL; 
    return node->next;
}

void printKey(node *node){
    printf ("(%d, %s) \n", node->key, (char*)node->value);
}

/*

//Traverse
void printDS(void** t){
    struct list_t* tgt;
    tgt = *t;
    if (tgt->t != NULL) {
        printf("(%d, %s) \n", tgt->t->key, (char*)tgt->t->value);
        printDS((void*)&tgt->t->next);
    }
}

*/