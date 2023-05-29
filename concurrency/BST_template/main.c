//
//  main.c
//  BST
//
//  Created by Duc Than Nguyen on 1/2/22.
//

#include <stdio.h>
#include <limits.h>
#include "give_up_template.h"

void insert (treebox t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;
    
    if (traverse(pn, x, value) == 0){
        pn->p->t->value = value;
    }
    else
    {
        insertOp(pn, x, value);
    }
    release(pn->n->lock);
    free(pn);
}

void *lookup (treebox t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = *t;
    if (traverse(pn, x, NULL) == 0){
        v = pn->p->t->value;
    }
    else
    {
        v = NULL;
    }
    release(pn->n->lock);
    free(pn);
    return v;
}

//Traverse

void Inorder(struct tree_t *p){
    if (p->t != NULL){
        Inorder(p->t->left);
        printf ("node->data %d %s \n", p->t->key, p->t->value);
        Inorder(p->t->right);
    }
}

void traverseInorder (treebox t){
    struct tree_t *tgt;
    tgt = *t;
    Inorder(tgt);
}

void *thread_func(void *args) {
    //lock_t *l = (lock_t*)args;
    lock_t *l = &thread_lock;
    
    // insert at key 1
    insert(tb,6,"ONE_FROM_THREAD");
    insert(tb,4,"FOUR");
    //   insert(tb,5,"FIVE");
    
    release((void*)l);
    return (void *)NULL;
}

int main (void) {
    tb = treebox_new();
    //lock_t *t_lock ;
    lock_t *t_lock = &thread_lock;
    insert(tb,3,"three");
    insert(tb,1,"One");
    insert(tb,4,"four");
    
    //t_lock = makelock();
    makelock((void*)t_lock);
    /* Spawn */
    spawn((void *)&thread_func, (void *)t_lock);
    /*JOIN */
    acquire((void*)t_lock);
    freelock((void*)t_lock);
    printf ("\nTraverse\n");
    traverseInorder(tb);
    

    printf ("\nTraverse\n");
    traverseInorder(tb);
    
    treebox_free(tb);
    fflush(stdout);
    
    return 0;
}
