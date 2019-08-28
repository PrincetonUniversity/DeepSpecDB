#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <sys/mman.h> 
#include "malloc.h"

/* ALERT: malloc doesn't zero the free-list pointer in allocated blocks,
   so it is easy for an un-verified client to trash the free lists. 
*/

/* max data size for blocks in bin b (not counting header),
   assuming 0<=b<BINS */
static size_t bin2size(int b) {
    return ((b+1)*ALIGN - 1)*WORD; 
}

/* bin index for blocks of size s (allowing for header and alignment) */
int size2bin(size_t s) {
  if (s > bin2size(BINS-1))
    return -1;
  else
    return (s+(WORD*(ALIGN-1)-1))/(WORD*ALIGN); 
}

/* for 0 <= b < BINS, bin[b] is null or points to 
   the first 'link field' of a list of blocks (sz,lnk,dat) 
   where sz is the length in bytes of (lnk,dat)
   and the link pointers point to lnk field not to sz.
*/
static void *bin[BINS];  /* initially nulls */


void *fill_bin(int b) {
  size_t s = bin2size(b);
  char *p = (char *) mmap0(NULL, BIGBLOCK, 
                       PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  if (p==NULL) 
      return NULL;
  else { 
    int Nblocks = (BIGBLOCK-WASTE) / (s+WORD);   
    char *q = p + WASTE; /* align q+WORD, wasting WASTE bytes */  
    int j = 0; 
    while (j != Nblocks - 1) {
      /* q points to start of (sz,lnk,dat), 
         q+WORD (i.e., lnk) is aligned,
         q+s+WORD is allocated, and 
         0 <= j < Nblocks 
      */
      ((size_t *)q)[0] = s;
      *((void **)(((size_t *)q)+1)) = q+WORD+(s+WORD); /* addr of next nxt field */
/* NOTE: the last +WORD was missing in the preceding store, 
   and was found during verification attempt. */
      q += s+WORD; 
      j++; 
    }
    /* finish last block, avoiding expression q+(s+WORD) going out of bounds */
    ((size_t *)q)[0] = s; 
    *((void **)(((size_t *)q)+1)) = NULL; /* lnk of last block */
    return (void*)(p+WASTE+WORD); /* lnk of first block */
  }
}

static void *malloc_small(size_t nbytes) {
  int b = size2bin(nbytes);
  void *q;
  void *p = bin[b];
  if (!p) {
    p = fill_bin(b);
    if (!p) 
      return NULL;
    else 
      bin[b] = p;
  }
  q = *((void **)p);
  bin[b] = q;
  return p;
}

static void *malloc_large(size_t nbytes) {
  char *p = (char *)mmap0(NULL, nbytes+WASTE+WORD,
                         PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0); 
  if (p==NULL) 
    return NULL;
  else { 
    ((size_t *)(p+WASTE))[0] = nbytes; 
   return (void*) (p+WASTE+WORD);
  }
}


static void free_small(void *p, size_t s) {
  int b = size2bin(s);
  void *q = bin[b];
  *((void **)p) = q;
  bin[b]=p;
}

void free(void *p) {
  if (p != NULL) {
    size_t s = (size_t)(((size_t *)p)[-1]);
    if (s <= bin2size(BINS-1))
      free_small(p,s);
    else
      munmap( ((char*)p) - (WASTE + WORD), s+WASTE+WORD );
  }
}

void *malloc(size_t nbytes) {
  if (nbytes > bin2size(BINS-1))
    return malloc_large(nbytes);
  else 
    return malloc_small(nbytes);
}

/* Claim 1:  0 <= s <= bin2size(BINS-1)   <==>   s <= bin2size(size2bin(s))
   Claim 2:  0 <= s <= bin2size(BINS-1)   ==>    0 <= size2bin(s) < BINS

   Claim 3:  0 <= s <= bin2size(BINS-1)   ==>   
                            size2bin(bin2size(size2bin(s))) == size2bin(s) 
  
   Claim 4:  0 <= b < BINS  ==>  (bin2size(b)+WORD) % (WORD*ALIGN) == 0
*/
static void testclaim(void) {
  int s,b;

  for (s=0;s<122;s++) {
    b = size2bin(s);
    printf("%3d  %3d  %3zu\n", s, b, bin2size(b));
    /*
    assert( s <= bin2size(BINS-1) ? 
            s <= bin2size(size2bin(s)) 
            && size2bin(s) < BINS 
            && size2bin(bin2size(size2bin(s)))==size2bin(s)
            && (bin2size(size2bin(s))+WORD) % (WORD*ALIGN) == 0 
            : 1);
    */
  }
}



