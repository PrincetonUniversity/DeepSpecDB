#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"

/* main for rudimentary testing of prefillable memmgr */

/* client bss space for prefills */
enum {HEAPSIZE = 10 * BIGBLOCK};
static char heap[HEAPSIZE];

/* facilitate alignment check without changing malloc code */
void *tmalloc(size_t nbytes) {
  void *p = malloc(nbytes);
  assert ((long)p % (WORD*ALIGN) == 0);
  return p;
}

/* quick hack test - multiple prefills and freelist traversals */
void test_prefill() {
  void* last = &heap[HEAPSIZE-1];
  void* next = heap;
  /* set next to aligned location in heap */
  if ((uintptr_t)next%(WORD*ALIGN) != 0) 
    next = (void*) (next + WORD*ALIGN - (uintptr_t)next%(WORD*ALIGN));

  pre_fill(100, next);     
  next += BIGBLOCK;

  pre_fill(100, next);     
  next += BIGBLOCK;

  pre_fill(100, next);     
  next += BIGBLOCK;

  for (int i = 0; i < 100000000; i++)
    tmalloc(100);

  assert (BIGBLOCK <= last - next);
  pre_fill(100, next);     
  next += BIGBLOCK;

  for (int i = 0; i < 10000000; i++)
    tmalloc(100);
 
}

/* TODO make some sensible tests and build for 32bit as verified */

int main(void) {

  void *p = tmalloc(100);
  void *q = tmalloc(10);
  void *r = tmalloc(100);
  void *s = tmalloc(100);
  void *t = tmalloc(BIGBLOCK + 100000);

  *((int*)r + 7) = 42;
  *((char*)r + 99) = 'a';
  *((int*)t) = 42;
  *((int*)t + 7) = 42;
  *((char*)t + BIGBLOCK + 100000 - 1)  = 'a';

  free(r);
  free(q);
  free(t); 

  *((int*)r + 7) = 42;

  r = tmalloc(100); 
  free(p);
  q = tmalloc(100);
  free(q);
  free(p);

  p = tmalloc(0); q = tmalloc(0); r = tmalloc(0); s = tmalloc(0);
  free(q); free(s); free(p); free(r);

  test_prefill();

  printf("test done\n");

  return 0;
}

