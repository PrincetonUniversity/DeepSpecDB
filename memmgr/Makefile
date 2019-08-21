# COMPCERT = ~/CompCert-3.4  # (should put this line in the CONFIGURE file)

FILES = $(wildcard *.v)

all: $(FILES:%.v=%.vo)

test:
	clang -g -O0 malloc.c main.c; ./a.out

FILES = malloc.v verif_memmgr.v malloc_lemmas.v spec_malloc.v verif_bin2size2bin.v verif_malloc_free.v verif_malloc_small.v verif_malloc_large.v verif_free_small.v verif_fill_bin.v malloc_shares.v \
	linking.v \
	main.v spec_main.v verif_main.v link_main.v 

memmgr: $(FILES:%.v=%.vo) 



CURRENT_LOC=.
# VST_LOC=../../VST     # should put this line in the CONFIGURE file
COQBIN=

-include CONFIGURE

CC_LOC=$(VST_LOC)/compcert

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
VST_DIRS= msl sepcomp veric floyd

CC_FLAGS= -R $(CC_LOC) compcert
VST_FLAGS=$(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

# COQ_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)
# DEP_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)

COQ_FLAG = $(CC_FLAGS) $(VST_FLAGS)
DEP_FLAG = $(CC_FLAGS) $(VST_FLAGS)

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

clight: _CoqProject malloc.c main.c
	$(COMPCERT)/clightgen -normalize malloc.c main.c; echo "Expect warning from cdefs.h about unsupported compiler."

.depend: Makefile
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f $(FILES:.v=.vo) $(FILES:.v=.glob) $(join $(dir $(FILES)),$(patsubst %.v,.%.aux,$(notdir $(FILES))))

_CoqProject: Makefile
	@echo $(COQ_FLAG) > _CoqProject

.DEFAULT_GOAL := all

include .depend
