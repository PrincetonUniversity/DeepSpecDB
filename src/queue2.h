#ifndef _QUEUE2H_
#define _QUEUE2H_

#include <stddef.h>
#include "surely_malloc.h"

extern void free(void *p);
extern void exit(int code);

struct elem {
  const void* data;
  struct elem *next;
};

typedef struct fifo {
  struct elem *head;
  struct elem *tail;
} fifo;

fifo *fifo_new(void);

void fifo_put (fifo *Q, struct elem *p);

int fifo_empty (fifo *Q);

struct elem *fifo_get (fifo *Q);

struct elem *make_elem(const void* data);

#endif