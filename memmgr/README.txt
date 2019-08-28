This is an unfinished exploratory development of verified
malloc and free, by Dave Naumann and Andrew Appel.

It is being developed using 32 bit compilation.

mmap0.h - interface for externals (mmap, munmap) and the shim mmap0
mmap0.c - code for shim
malloc.h - interface for malloc/free
malloc.c - the code 
verif_memmgr.v - main file for verification
malloc_lemmas.v - background independent of the program file
spec_malloc.v - specs for mmap, munmap, malloc, free, and internal subroutines
verif_*.v - body lemmas
verif_external.v - body lemmas for un-verified functions (mmap0, munmap)

malloc_shares.v - lemmas and definitions about (comp Ews), also other stuff only needed for splittable token

mmSplitToken: tag for version with splittable malloc_token; incomplete and set aside 


