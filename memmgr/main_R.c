#include <stddef.h>
#include <stdio.h>
#include <sys/mman.h> 
#include "malloc.h"

int main(void) {
  char *m = (char *) mmap0(NULL, BIGBLOCK, 
                       PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  if (!m) return 0;
  pre_fill(50,m);
  void *p = malloc(50);
  free(p);
  return 0;
}

