#include "queue2.h"

fifo *fifo_new(void) {
  struct fifo *Q = (fifo *) surely_malloc(sizeof (*Q));
  Q->head = NULL;
  Q->tail = NULL;
  return Q;
}

void fifo_put (fifo *Q, struct elem *p) {
  struct elem *h, *t;
  p->next=NULL;
  h = Q->head;
  if (h==NULL) {
    Q->head=p;
    Q->tail=p;
  }
  else {
    t = Q->tail;
    t->next=p;
    Q->tail=p;
  }
}

int fifo_empty (fifo *Q) {
  struct elem *h;
  h = Q->head;
  return (h == NULL);
}

struct elem *fifo_get (fifo *Q) {
  struct elem *h, *n;
  h=Q->head;
  n=h->next;
  Q->head=n;
  return h;
}

struct elem *make_elem(const void* data) {
  struct elem *p;
  p = surely_malloc(sizeof (*p));
  p->data=data;
  return p;
}
