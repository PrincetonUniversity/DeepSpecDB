//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "give_up_template.h"

int inrange(pn *pn, int x){
    if (x > pn->p->min && x < pn->p->max)
        return 1;
    else
        return 0;
}

int traverse(pn *pn, int x, void *value) {
    tree_t *p = (pn->n);
    int flag = 1;

    for( ; ; ){
        acquire(pn->n->lock);
        pn->p = pn->n;
        if (inrange (pn, x) == 1){
            if (pn->p->t == NULL)
                break;
            else{
                int b = findnext(pn, x, value);
                if (b == 0){
                    flag = 0;
                    break;
                }
                else{
                    release(pn->p->lock);
                }
            }
        }
        else{
            release(pn->p->lock);
            pn->n = p;
        }
            
    }
    return flag;
}
