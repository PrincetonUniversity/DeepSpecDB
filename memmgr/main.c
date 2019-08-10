#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"


/* facilitate alignment check without changing malloc code */
void *tmalloc(size_t nbytes) {
  void *p = malloc(nbytes);
  assert ((long)p % (WORD*ALIGN) == 0);
  return p;
}

/* TODO make some sensible tests and build for 32bit as verified */

int main(void) {
  /*  testclaim(); */
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

/* posix: "If size is 0, either a null pointer or a unique pointer that can 
be successfully passed to free() shall be returned." */
  p = tmalloc(0); q = tmalloc(0); r = tmalloc(0); s = tmalloc(0);
  free(q); free(s); free(p); free(r);

  printf("done\n");

  return 0;
}

