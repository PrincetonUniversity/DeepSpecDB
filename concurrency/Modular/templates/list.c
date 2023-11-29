//
//  list.c
//  BST
//
//  Created by Duc Than Nguyen on 6/4/23.
//

#include "data_structure.h"

typedef struct node {int key; void *value; struct list_t *next;} node;
typedef struct list_t {node *t; lock_t lock; int min; int max; } list_t;

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

Status findNext(void* p_list, void** n_list, int x) {
    list_t* p = (list_t*)p_list;
    list_t** n = (list_t**)n_list;
    int y = p->t->key;
    if (x > y) {
        *n = (struct list_t*) p->t->next;
        return NULLNEXT;
    }
    else if (x < y) {
        return NOTFOUND;
    }
    else {
        return FOUND;
    }
}


void insertOp(void* p_list, int x, void* value, Status status){
    list_t* p = (struct list_t*)p_list;
    list_t* pl = (struct list_t*)surely_malloc(sizeof (list_t)); //new pl
    pl->t = NULL;
    //lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    //makelock(l);
    lock_t l = makelock();
    pl->lock = l;
    release(l);
    pl->min = INT_MIN;
    pl->max = INT_MAX;
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
    pl->min = x;
}


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


void changeValue(void* p_list, void* value){
    list_t* p = (list_t*)p_list;
    p->t->value = value;
}

void * getValue(void* p_list){
    list_t* p = (list_t*)p_list;
    return p->t->value;
}

//Traverse
void printDS(void** t){
    struct list_t* tgt;
    tgt = *t;
    if (tgt->t != NULL) {
        printf("(%d, %s) \n", tgt->t->key, (char*)tgt->t->value);
        printDS((void*)&tgt->t->next);
    }
}


