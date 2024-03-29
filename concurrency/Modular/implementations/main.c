//
//  main.c
//  BST
//
//  Created by Duc Than Nguyen on 1/2/22.
//

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "template.h"
#include "data_structure.h"
#include "threads.h"

void *thread_func(void *args) {
    lock_t l = (lock_t)args;
    //lock_t l = &thread_lock;
    
    // insert at key 1
    insert(tb,6,"ONE_FROM_THREAD");
    insert(tb,4,"FOUR");
    insert(tb,5,"FIVE");
    
    release((void*)l);
    return (void *)NULL;
}


int main (void) {
    tb = treebox_new();
    //lock_t *t_lock ;
    lock_t t_lock = thread_lock;
    insert(tb,3,"three");
    insert(tb,2,"two");
    insert(tb,1,"One");
    insert(tb,6,"four");
    
    t_lock = makelock();
    //makelock((void*)t_lock);
    // Spawn
    spawn((void *)&thread_func, (void *)t_lock);
    // JOIN
    insert(tb,6,"six");
    acquire((void*)t_lock);
    freelock((void*)t_lock);
    printf ("\nTraverse\n");
    printDS_helper((void*)tb);
    int k = 1;
    printf("Lookup key = %d: %s\n", k, (void*)lookup(tb, k));
    //treebox_free(tb);
    fflush(stdout);

    return 0;
}
