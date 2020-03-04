#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"

/* client using bss space for prefill */

static char heap[BIGBLOCK + WORD*ALIGN];

int main(void) {
  /* set bb to aligned big block */
  char* bb = heap;
  if ((uintptr_t)bb%(WORD*ALIGN) != 0) 
     bb = (void*) (bb + WORD*ALIGN - (uintptr_t)bb%(WORD*ALIGN));
  assert ((uintptr_t)bb % (WORD*ALIGN) == 0);
  pre_fill(100, bb);     
  void *p = malloc(100);
  free(p);
  return 0;
}


