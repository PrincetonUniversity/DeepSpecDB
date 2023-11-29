//
//  data_structure.h
//  BST
//
//  Created by Duc Than Nguyen on 6/15/23.
//
#ifndef COMMON_H
#define COMMON_H

typedef enum {
    FOUND,
    NOTFOUND,
    NULLNEXT
} Status;

lock_t thread_lock;

// Define the DynamicList struct
typedef struct {
    void** list;         // Double pointer to store elements (can be BSTNode or ListNode)
    unsigned int size;   // Size of the list
} DList;

static void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}
#endif