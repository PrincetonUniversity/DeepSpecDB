//
//  template.h
//  BST
//
//  Created by Duc Than Nguyen on 6/22/23.
//


#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "give_up_template.h"
#include "threads.h"


typedef struct node_t **treebox;
treebox tb;

void insert (treebox t, int x, void *value);
void *lookup (treebox t, int x);
treebox treebox_new(void);
void treebox_free(treebox b);

