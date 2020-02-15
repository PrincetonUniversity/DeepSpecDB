This is a verified implementation of malloc and free, by Dave Naumann and Andrew Appel.

It is being developed using 32 bit compilation (see malloc_lemmas.WORD).

mmap0.h - interface for externals (mmap, munmap) and the shim mmap0
mmap0.c - code for shim
malloc.h - interface for malloc/free
malloc.c - the code 
verif_memmgr.v - main file for verification
malloc_lemmas.v - background independent of the program file
                  except for constants defined in malloc.h, in particular BINS 
malloc_shares.v - lemmas about splitting shares 
spec_malloc.v - specs for mmap, munmap, malloc, free, and internal subroutines
                and definitions of representation invariant
malloc_sep.v - lemmas about the representation invariant etc. 
verif_*.v - body lemmas
verif_external.v - body lemmas for un-verified functions (mmap0, munmap)

main.c spec_main.v verif_main.v link_main.vf - a simple test main
main_R.c *_R.v - another simple test, using pre_fill

Tagged versions 

mmSplitToken: tag for version with splittable malloc_token; incomplete and set aside 



Note: share_rebase.v had lemmas and definitions to support splittable malloc token.
It has been dropped after commit 6677d7748368205ffc2d720053774e96c34c3dd7 in branch malloc_resourced.
Same as the version in master branch as of commit 4af4b2eb7f27c7f53ae126e37d9e152bd2eae8a5



