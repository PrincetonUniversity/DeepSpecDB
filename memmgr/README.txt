This is an unfinished exploratory development of verified
malloc and free, by Dave Naumann and Andrew Appel.

It is being developed using 32 bit compilation.

malloc.c - the code (currently there is no .h file)
verif_memmgr.v - main file for verification
malloc_lemmas.v - background independent of the program file
spec_malloc.v - specs for mmap, munmap, malloc, free, and internal subroutines
verif_*.v - body lemmas

verif_malloc_large 

