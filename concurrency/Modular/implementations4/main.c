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

css * my_css;
lock_t thread_lock;

void *thread_func(void *args) {
    lock_t l = (lock_t)args;
    
    insert(my_css, 10, "ten");

    release((void*)l);
    return (void *)NULL;
}


int main (void) {
    my_css = make_css();
    
    lock_t t_lock = thread_lock;
    insert(my_css, 5, "five");

    insert(my_css, 7, "seven");
    
    insert(my_css, 6, "six");

    insert(my_css, 4, "four");

    insert(my_css, 8, "eight");

    insert(my_css, 4, "ten");
    
    t_lock = makelock();
    // Spawn
    spawn((void *)&thread_func, (void *)t_lock);
    // JOIN
    acquire((void*)t_lock);
    freelock((void*)t_lock);
    // TRAVERSE 
    printf ("\nTraverse\n");
    printDS_helper((void*)my_css);
    int k = 4;
    printf("Lookup key = %d: %s\n", k, (char*)lookup(my_css, k));
    //treebox_free(tb);
    fflush(stdout);

    return 0;
}
