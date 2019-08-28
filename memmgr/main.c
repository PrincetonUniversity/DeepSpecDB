#include <stddef.h>
#include <stdio.h>
#include <sys/mman.h> 
#include "malloc.h"

int main(void) {
  void *p = malloc(100);
  free(p);
  return 0;
}

