#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

/* gcc -Wall -pthread pair_conc.c threads.c -o pair_conc */

typedef struct Pair {
    int fst;
    int snd;
} Pair;

typedef struct PairImpl {
    lock_t *lock;
    int data;
    unsigned int version;
} PairImpl;

PairImpl* pa;
PairImpl* pb;
lock_t thread_lock;

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

void write(PairImpl* p, int val) {
    void *l = p -> lock;
    acquire(l);
    p -> data = val;
    p -> version++;
    release2(l);
}

PairImpl* pair_new(int val) {
    PairImpl* pair = (PairImpl*) surely_malloc(sizeof(PairImpl));
    lock_t *l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    pair -> lock = l;
    pair -> data = val;
    pair -> version = 0;
    release2(l);
    return pair;
}

void pair_free(PairImpl* p) {
    void * l = p -> lock;
    acquire(l);
    freelock2(l);
    free(l);
    free(p);
}

Pair* read_pair(PairImpl* a, PairImpl* b) {
    int da, db;
    unsigned int va, va2;
    Pair* result = (Pair*)surely_malloc(sizeof(Pair));
    lock_t* l;
    for (;;) {
        l = a -> lock;
        acquire(l);
        da = a -> data;
        va = a -> version;
        release2(l);

        l = b -> lock;
        acquire(l);
        db = b -> data;
        release2(l);

        l = a -> lock;
        acquire(l);
        va2 = a -> version;
        release2(l);

        if (va == va2) {
            result -> fst = da;
            result -> snd = db;
            return result;
        } /* else { */
        /*     printf("Catch inconsistency!\n"); */
        /* } */
    }
}

void *thread_func(void *args) {
  lock_t *l = &thread_lock;

  write(pa, 2);

  release2((void*)l);
  return (void *)NULL;
}


int main(int argc, char *argv[]) {
    pa = pair_new(1);
    pb = pair_new(2);
    lock_t *t_lock = &thread_lock;

    makelock((void*)t_lock);
    /* Spawn */
    spawn((void *)&thread_func, (void *)NULL);

    Pair* result = read_pair(pa, pb);

    acquire((void*)t_lock);
    freelock2((void*)t_lock);

    /* printf("Result: (%d, %d)\n", result -> fst, result -> snd); */

    pair_free(pa);
    pair_free(pb);
    free(result);
    return 0;
}
