//
//  list.c
//  BST
//
//  Created by Duc Than Nguyen on 6/4/23.
//

#include "data_structure.h"

int findnext (pn *pn, int x){
    int y = pn->p->l-> key;

    if (x > y) {
        pn->n = pn->p->l->next;
        return 1;
    } else {
        return 0;
    }
}

void insertOp(pn *pn, int x, void *value){
    list_t *p = (list_t *) surely_malloc (sizeof *(pn->p));
    p->l = NULL;
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    p->lock = l;
    release(l);

    if (pn->p->l == NULL) {
        p->l = NULL;
        pn->p->l = (list *) surely_malloc (sizeof *(pn->p->l));
    } else {
        p->l = (list *) surely_malloc (sizeof *(pn->p->l));
        p->l->key = pn->p->l->key;
        p->l->value = pn->p->l->value;
        p->l->next = pn->p->l->next;
    }
    pn->p->l->key = x;
    pn->p->l->value = value;
    pn->p->l->next = p;
    //Range
    //p1->min = pn->p->min;
    //p1->max = x;
    //p2->min = x;
    //p2->max = pn->p->max;
}

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

listbox listbox_new(void) {
    listbox p = (listbox) surely_malloc(sizeof (*p));
    list_t *newl = (list_t *) surely_malloc(sizeof(list_t));
    *p = newl;
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    newl->lock = l;
    newl->l = NULL;
    newl->min = INT_MIN;
    newl->max = INT_MAX;
    release(l);
    return p;
}

void list_free(list_t *tgp) {
    list_t *pn;
    list* p;
    void *l = tgp -> lock;
    acquire(l);
    p = tgp -> l;
    if (p!=NULL) {
        pn = p -> next;
        free(p);
        list_free(pn);
    }
    freelock(l);
    free(tgp);
}

void listbox_free(listbox b) {
    struct list_t *t = *b;
    list_free(t);
    free(b);
}
