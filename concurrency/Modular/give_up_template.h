//
//  give_up_template.h
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"

typedef struct node_t {node *t; lock_t lock; int min; int max; } node_t;

//Template style
typedef struct pn {
    struct node_t *p;
    struct node_t *n;
} pn;

int inRange(node_t *p, int x);
Status traverse(pn *pn, int x);

