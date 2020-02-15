#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"

/* main for rudimentary testing of prefillable memmgr
ALERT: clight produces main.v from this file, not test.v
*/

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
  char* last = &heap[HEAPSIZE-1];
  char* next = heap;
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

 
size_t bin2size(int b) {
    return ((b+1)*ALIGN - 1)*WORD; 
}

void test_try_prefill() {
  int s = bin2size(BINS-1);
  const int N = 1310; 
  assert (N == (BIGBLOCK - WASTE) / (s + WORD));  // 64bit, with BINS=50
  int r = try_pre_fill(s, 2*N + 1);
//  printf("s = %d, N = %d, reserved = %d\n", s, N, r);
  void* save[3935]; assert (3935 == 3*N + 5); // for clight
  for (int i = 0; i < 3*N + 5; i++) 
      save[i] = malloc(s);
  for (int i = 0; i < 3*N + 5; i+=2)
      free(save[i]);
  for (int i = 0; i < 4*N; i++)
      malloc(s);
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

  test_try_prefill();

  printf("test done\n");

  return 0;
}

