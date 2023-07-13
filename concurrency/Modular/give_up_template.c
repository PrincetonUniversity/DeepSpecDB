//
//  give_up_template.c
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "give_up_template.h"

int inRange(node_t *p, int x){
    if (x > p->min && x < p->max)
        return 1;
    else
        return 0;
}

Status traverse(pn *pn, int x) {
    Status status;
    void *p = (pn->n);
    for( ; ; ){
        acquire(pn->n->lock);
        pn->p = pn->n;
        if (inRange (pn->p, x) == 1){
            if (pn->p->t == NULL){
                return NULLNEXT;
            }
            else{
                status = findNext(pn->p, (void**)&pn->n, x);
                if (status == FOUND){
                    return FOUND;
                }
                else if (status == NOTFOUND)
                    return NOTFOUND;
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
}
