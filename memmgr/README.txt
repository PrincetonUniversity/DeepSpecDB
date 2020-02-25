This is a verified implementation of malloc and free.

There is an accompanying paper.  See guide.txt for correspondences between 
the paper and in the Coq development.


BUILD INSTRUCTIONS

You need VST and Coq installed (see VST instructions).
Optionally, to run clightgen you need CompCert (but this distribution includes pre-compiled clight files).
We have used Coq 8.10, VST 2.5, and CompCert 3.4 among others.

In this directory, create a file CONFIGURE with these two lines:
VST_LOC=path_to_VST_installation
COMPCERT=path_to_CompCert_installation_if_any

To run the complete verification, in this directory, run:
make verif_memmgr.vo

Optionally, generate the clight files yourself:
make clight
make clight_R

The verification has been done using 32 bit compilation (see malloc_lemmas.WORD),
but the code also builds and runs in 64 bit.



FILES

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

main.c spec_main.v verif_main.v link_main.v - a simple test main
main_R.c *_R.v - another simple test, using pre_fill 

test.c - demonstrates pre_fill using the client's bss section instead of mmap


NOTES

The development includes verification of linked whole programs.  This is explained
in the paper "Abstraction and Subsumption in Modular Verification of C Programs"
by Lennart Beringer and Andrew W. Appel, in FM 2019.

The constants in malloc.h and malloc_lemmas.v (BINS, WORD, etc) must be consistent.
For BINS, the definition in malloc_lemmas is computed from malloc.v based on malloc.h.


Tagged versions 

mmFullyVerified: tag for version fully verified, with resource tracking

mmSplitToken: tag for version with splittable malloc_token; incomplete and set aside 

Note: share_rebase.v had lemmas and definitions to support splittable malloc token.
It has been dropped after commit 6677d7748368205ffc2d720053774e96c34c3dd7 in branch malloc_resourced.
Same as the version in master branch as of commit 4af4b2eb7f27c7f53ae126e37d9e152bd2eae8a5



