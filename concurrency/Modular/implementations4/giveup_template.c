#include "data_structure.h"
#include "template.h"

#define TABLE_SIZE 16384

int hash(node* p){
  return (unsigned int) p * (unsigned int) 654435761;
}

typedef struct md_entry { lock_t lock; int min; int max; } md_entry;
typedef struct css { node* root; md_entry* metadata[16384]; } css;

int inRange(md_entry* m, int x){
    if (x > m->min && x < m->max)
        return 1;
    else
        return 0;
}

md_entry* lookup_md(css* c, node* p){
    return c->metadata[hash(p) % TABLE_SIZE];
}

Status traverse(css* c, pn *pn, int x) {
    Status status = NOTFOUND;
    node* p = pn->n;
    for( ; ; ){
        if(!pn->n) return CONTINUE;
        md_entry* md = lookup_md(c->metadata, p);
        acquire(md->lock);
        pn->p = pn->n;
        if (inRange (md, x) == 1){
            status = findNext(pn->p, (void**)&pn->n, x);
            if (status == FOUND){
                break;
            }
            else if (status == NOTFOUND){
                break;
            }
            else{
                release(md->lock);
            }
        }
        else{
            release(md->lock);
            pn->n = p;
        }
    }
    return status;
}

/*
void insertOp_list(node_t* p, int x, void* value, Status status){
    struct node_t* pl; 
    pl = (struct node_t*)surely_malloc(sizeof (node_t));
    if (status == NULLNEXT) {
        pl->t = NULL;
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        pl->lock = l;
        release(l); 

        insertOp_llist(&p->t, x, value, status, pl);
        pl->max = INT_MAX;
        pl->min = x;
    }
    else{
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        pl->lock = l;
        release(l);
        pl->t = p->t;
        pl->max = p->max; 
        pl->min = x; 
        insertOp_llist(&(p->t), x, value, status, pl);
    }
} 
*/
/*
void insertOp_list(node_t* p, int x, void* value, Status status){
    DList dlist; 
    dlist.size = 1; // For Linked-list 
    dlist.list = (void**)surely_malloc(dlist.size * sizeof(node_t));
    dlist.list[0] = (struct node_t*)surely_malloc(sizeof (node_t));
    if (status == NULLNEXT) {
        ((node_t*)dlist.list[0])->t = NULL;
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        insertOp_llist(&p->t, x, value, status, &dlist);
        ((node_t*)dlist.list[0])->min = x;
        ((node_t*)dlist.list[0])->max = INT_MAX;
    }
    else{
        lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t));
        makelock(l);
        ((node_t*)dlist.list[0])->lock = l;
        release(l);
        ((node_t*)dlist.list[0])->t = p->t;
        ((node_t*)dlist.list[0])->max = p->max; 
        ((node_t*)dlist.list[0])->min = x;
        insertOp_llist(&(p->t), x, value, status, &dlist);
    }
}
*/
/*void insertOp_helper(node_t *p, int x, void* value, Status status){
    insertOp_giveup(p, x, value, status);
    //insertOp_list(p, x, value, status);
}*/

css* make_css(){
    css* new_css = malloc(sizeof(css));
    new_css->root = NULL;
    return new_css;
}

lock_t get_lock(css* c, node* p){
    md_entry* m = lookup_md(c, p);
    return m->lock;
}

void changeValue_helper(node *p, void* value){
    changeValue(p, value);
}

void *getValue_helper(node* p){
    return getValue(p);
}

//for BST

void printDS_helper (void **t){
    printDS_giveup(t);
}


/*
void printDS_helper (void **t){
    struct node_t* tgt;
    tgt = *t;

    if (tgt == NULL) {
        return;
    }
    stack s;
    initStack(&s);
    node_t * current = tgt;
    while (current->t != NULL) {
        push(&s, current);
        current = (node_t *)getNext(current->t);
    }
    while (!isEmpty(&s)){   
        current = pop(&s);
        printKey(current->t);
    }
}
*/