typedef struct tree {int key; void *value; struct tree_t *left, *right;} tree;
typedef struct tree_t {tree *t; lock_t *lock; int min; int max; } tree_t;

typedef struct pn {
    struct tree_t *p;
    struct tree_t *n;
} pn;