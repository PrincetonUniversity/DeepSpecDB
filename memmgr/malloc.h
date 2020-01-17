#include "mmap0.h"

/* About format and alignment:
malloc returns a pointer aligned modulo ALIGN*WORD, preceded by the chunk
size as an unsigned integer in WORD bytes.  Given a well aligned large block
from the operating system, the first (WORD*ALIGN - WORD) bytes are wasted
in order to achieve the alignment.  The chunk size is at least the size
given as argument to malloc.
*/

/* TODO WASTE and ALIGN probably not needed here */ 

enum {WORD = sizeof(size_t)};

enum {ALIGN = 2};

enum {WASTE = WORD*ALIGN - WORD}; 

enum {BIGBLOCK = (2<<16)*WORD};

enum {BINS = 8};

void *malloc(size_t);

void free(void *);

void pre_fill(size_t, void *);


