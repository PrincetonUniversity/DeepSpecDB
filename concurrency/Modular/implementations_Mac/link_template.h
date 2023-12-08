//
//  give_up_template.h
//  BST
//
//  Created by Duc Than Nguyen on 5/29/23.
//

#include "data_structure.h"

typedef struct node_t {node *t; lock_t *lock; int min; int max; } node_t;

//Template style
typedef struct pn {
    struct node_t *p;
    struct node_t *n;
} pn;

void insertOp_helper(void* p, int x, void* value, Status status);
Status traverse(pn *pn, int x);
node_t * treebox_helper(node_t *newt);
