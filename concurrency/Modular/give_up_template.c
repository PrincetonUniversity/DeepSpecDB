//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "give_up_template.h"

int inrange(node_t *p, int x){
    if (x > p->min && x < p->max)
        return 1;
    else
        return 0;
}

int traverse(pn *pn, int x) {
    void *p = (pn->n);
    int flag = 1;
    for( ; ; ){
        acquire(pn->n->lock);
        pn->p = pn->n;
        if (inrange (pn->p, x) == 1){
            if (pn->p->t == NULL)
                break;
            else{
                int b = findnext(pn->p, (void**)&pn->n, x);
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
