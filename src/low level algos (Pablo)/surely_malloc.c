#include "surely_malloc.h"
#include <stdlib.h>

void *surely_malloc(unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}
