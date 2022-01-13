#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"

/* gcc -Wall -pthread kvnode.c threads.c -o kvnode */

#define SIZE 8

typedef struct node {
    lock_t* vlock;
    int version;
    lock_t** dlocks;
    int* data; } node;

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

node* one_node;
lock_t thread_lock;
int* first;
int* second;

node* node_new(int* values) {
    node* result = (node*) surely_malloc(sizeof(node));
    lock_t* l = (lock_t *) surely_malloc(sizeof(lock_t));
    makelock(l);
    lock_t** locks = (lock_t **) surely_malloc(SIZE * sizeof(lock_t*));
    int* data = (int *) surely_malloc(SIZE * sizeof(int));
    for (int i = 0; i < SIZE; i++) {
        lock_t* ll = (lock_t *) surely_malloc(sizeof(lock_t));
        makelock(ll);
        locks[i] = ll;
        data[i] = values[i];
        release(ll);
    }
    result -> vlock = l;
    result -> version = 0;
    result -> dlocks = locks;
    result -> data = data;
    release(l);
    return result;
}

void read(node *n, int *out) {
    lock_t* l;
    for(;;){
        l = n -> vlock;
        acquire(l);
        int ver = n -> version;
        release(l);
        if((ver & 1) == 1) continue; //already dirty
        for(int i = 0; i < SIZE; i++) {
            lock_t* dlock = n -> dlocks[i];
            acquire(dlock);
            out[i] = n->data[i];
            release(dlock);
        }
        acquire(l);
        int v = n -> version;
        release(l);
        if(v == ver) return;
    }
}

void write(node *n, int *in) {
    lock_t* l = n -> vlock;
    acquire(l);
    int ver = n -> version;
    n -> version = ver + 1;
    release(l);
    for(int i = 0; i < SIZE; i++){
        lock_t* dlock = n -> dlocks[i];
        acquire(dlock);
        n->data[i] = in[i];
        release(dlock);
    }
    acquire(l);
    n -> version = ver + 2;
    release(l);
}

void node_free(node* n) {
    lock_t* l = n -> vlock;
    acquire(l);
    freelock(l);
    free(l);
    for (int i = 0; i < SIZE; i++) {
        lock_t* ll = n -> dlocks[i];
        acquire(ll);
        freelock(ll);
        free(ll);
    }
    free(n -> dlocks);
    free(n -> data);
    free(n);
}

void *thread_func(void *args) {
  lock_t *l = &thread_lock;

  write(one_node, second);

  release2((void*)l);
  return (void *)NULL;
}

int main(int argc, char *argv[]) {
    first = (int *) surely_malloc(SIZE * sizeof(int));
    second = (int *) surely_malloc(SIZE * sizeof(int));
    for (int i = 0; i < SIZE; i++) {
        first[i] = i;
        second[i] = SIZE - i;
    }
    one_node = node_new(first);

    lock_t* t_lock = &thread_lock;
    makelock(t_lock);

    makelock((void*)t_lock);
    /* Spawn */
    spawn((void *)&thread_func, (void *)NULL);

    int* result = (int *) surely_malloc(SIZE * sizeof(int));
    read(one_node, result);
    for (int i = 0; i < SIZE; i++) {
        printf("%d, ", result[i]);
    }
    printf("\n");

    acquire((void*)t_lock);
    freelock2((void*)t_lock);
    node_free(one_node);
    free(result);
    return 0;
}
