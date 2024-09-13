#include "lock_template.h"


int hash(node* p) {
    // Ensure the pointer is cast to a proper unsigned type before multiplication
    uintptr_t ptr_value = (uintptr_t)p;
    return (int)(ptr_value * 654435761ULL % TABLE_SIZE);
}

md_entry* lookup_md(css* c, node* p){
    return c->metadata[hash(p)];
}

//FOUND = 0, NOTFOUND = 1, CONTINUE = 2
Status traverse(css* c, pn *pn, int x) {
    Status status = NOTFOUND;
    if(!pn->n) return CONTINUE; // special case for empty data structure
    md_entry* md_n = lookup_md(c, pn->n);
    md_entry* md_p;
    acquire(md_n->lock); 
    for( ; ; ){
        pn->p = pn->n;
        status = findNext(pn->p, (void**)&pn->n, x);
        if(!pn->n) {
            return NOTFOUND;
        }
        if (status == FOUND){
            break;
        }
        else if (status == NOTFOUND){
            break;
        }
        else{
            md_n = lookup_md(c, pn->n);
            md_p = lookup_md(c, pn->p);
            acquire(md_n->lock); //acquire pn->n
            release(md_p->lock); // release pn->p
        }
    }
    return status;
}

void insertOp_helper(css* c, node *p, int x, void* value, Status status){
    insertOp_lock(c, p, x, value, status);
}

css* make_css(){
    css* new_css = (css*) surely_malloc(sizeof(css));
    new_css->root = NULL;
    return new_css;
}

lock_t * get_lock(css* c, node* p){
    md_entry* m = lookup_md(c, p);
    fflush(stdout);
    return m->lock;
}

node* get_root(css* t){
    return t->root;
}

void change_value_helper(node *p, void* value){
    change_value(p, value);
}

void *get_value_helper(node* p){
    return get_value(p);
}

//for BST

void printDS_helper (css *t){
    printDS_lock(t);
}