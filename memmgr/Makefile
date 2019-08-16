COMPCERT = ~/CompCert-3.4

test:
	clang -g -O0 malloc.c main.c; ./a.out

clight: 
	$(COMPCERT)/clightgen -normalize malloc.c; echo "Expect warning from cdefs.h about unsupported compiler."; coqc `cat _CoqProject-export` malloc.v 
	$(COMPCERT)/clightgen -normalize main.c; echo "Expect warning from cdefs.h about unsupported compiler."; coqc `cat _CoqProject-export` main.v 

FILES = malloc.v verif_memmgr.v malloc_lemmas.v spec_malloc.v verif_bin2size2bin.v verif_malloc_free.v verif_malloc_small.v verif_malloc_large.v verif_free_small.v verif_fill_bin.v malloc_shares.v \
	linking.v \
	main.v spec_main.v verif_main.v link_main.v 

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) `cat _CoqProject-export` $*.v

memmgr: $(FILES:%.v=%.vo) 



CURRENT_LOC=.
VST_LOC=../../VST
CC_LOC=../../VST/compcert
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
VST_DIRS= msl sepcomp veric floyd

CC_FLAGS= -R $(CC_LOC) compcert
VST_FLAGS=$(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

COQ_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)
DEP_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)

FILES = $(wildcard *.v)

# $(FILES:%.v=%.vo): %.vo: %.v
#	@echo COQC $*.v
#	@$(COQC) $(COQ_FLAG) $*.v

all: \
  $(FILES:%.v=%.vo) \

.depend: Makefile
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f $(FILES:.v=.vo) $(FILES:.v=.glob) $(join $(dir $(FILES)),$(patsubst %.v,.%.aux,$(notdir $(FILES))))

_CoqProject: Makefile
	@echo $(COQ_FLAG) > _CoqProject

.DEFAULT_GOAL := all

include .depend
