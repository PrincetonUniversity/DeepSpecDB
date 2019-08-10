/* ALERT: malloc doesn't zero the free-list pointer in allocated blocks,
   so it is easy for an un-verified client to trash the free lists. 
*/

/* restricted spec for our purposes
precond: addr == NULL 
         prot == PROT_READ|PROT_WRITE
         off == 0
         flags == MAP_PRIVATE|MAP_ANONYMOUS 
         fildes == -1 
postcond: 
  if ret != MAP_FAILED then ret points to page-aligned block of size len bytes 
*/ 
extern void *mmap(void *addr, size_t len, int prot, int flags, int fildes, off_t off);

/* restricted spec for our purposes
precond: addr through addr+len was allocated by mmap and is a multiple of PAGESIZE
postcond: if ret==0 then the memory was freed.
*/ 
extern int munmap(void *addr, size_t len);

/* About format and alignment:
malloc returns a pointer aligned modulo ALIGN*WORD, preceded by the chunk
size as an unsigned integer in WORD bytes.  Given a well aligned large block
from the operating system, the first (WORD*ALIGN - WORD) bytes are wasted
in order to achieve the alignment.  The chunk size is at least the size
given as argument to malloc.
*/

enum {WORD = sizeof(size_t)};

enum {ALIGN = 2};

enum {WASTE = WORD*ALIGN - WORD};  

enum {BIGBLOCK = (2<<16)*WORD};

enum {BINS = 8};

void *malloc(size_t);

void free(void *);


