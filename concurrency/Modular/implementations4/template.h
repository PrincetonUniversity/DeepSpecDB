#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "threads.h"
#include "common.h"
#include "data_structure.h"

typedef struct css css;

//Template style
typedef struct pn {
    struct node* p;
    struct node* n;
} pn;

lock_t get_lock(node* n);

css* make_css();
void free_css(css* t);
node* get_root(css* t);

Status traverse(pn* pn, int x);
void insert (css* t, int x, void *value);
void *lookup (css* t, int x);
