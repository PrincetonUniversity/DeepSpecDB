//
//  data_structure.h
//  BST
//
//  Created by Duc Than Nguyen on 6/15/23.
//
#ifndef COMMON_H
#define COMMON_H
#define TABLE_SIZE 16384

typedef enum {
    FOUND,
    NOTFOUND,
    CONTINUE
} Status;

static void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

#endif