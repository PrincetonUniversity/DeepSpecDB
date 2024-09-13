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

lock_t * get_lock(css* c, node* p);

css* make_css();
//void free_css(css* t);
node* get_root(css* t);

Status traverse(css *t, pn* pn, int x);
void insert (css* t, int x, void *value);
void *lookup (css* t, int x);
void change_value_helper(node * p, void *value);
void insertOp_helper(css* c, node *p, int x, void* value, Status status);

//support print
void printDS_helper (css *t);