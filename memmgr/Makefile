FILES = $(wildcard *.v)

target: link_main.vo

all: $(FILES:%.v=%.vo)

test:
	clang -g -O0 mmap0.c malloc.c test.c; ./a.out

main_R:
	clang -g -O0 mmap0.c malloc.c main_R.c; ./a.out


FILES = verif_external.v mmap0.v malloc.v verif_memmgr.v malloc_lemmas.v \
   spec_malloc.v verif_bin2size2bin.v verif_malloc_free.v verif_malloc_small.v \
   verif_malloc_large.v verif_free_small.v verif_free_large.v verif_fill_bin.v \
   verif_list_from_block.v verif_pre_fill.v malloc_sep.v malloc_shares.v \
	linking.v \
	main.v spec_main.v verif_main.v link_main.v spec_external.v verif_try_pre_fill.v \
	main_R.v verif_main_R.v verif_main_alt.v 

CURRENT_LOC=.
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

clight: _CoqProject mmap0.c malloc.c main.c
	$(COMPCERT)/clightgen -normalize mmap0.c malloc.c main.c; echo "Expect warning from cdefs.h about unsupported compiler."

clight_R: _CoqProject mmap0.c malloc.c main_R.c
	$(COMPCERT)/clightgen -normalize mmap0.c malloc.c main_R.c

clight_bss: _CoqProject mmap0.c malloc.c main_bss.c
	$(COMPCERT)/clightgen -normalize mmap0.c malloc.c main_bss.c

.depend: Makefile
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f $(FILES:.v=.vo) $(FILES:.v=.glob) $(join $(dir $(FILES)),$(patsubst %.v,.%.aux,$(notdir $(FILES))))

_CoqProject: Makefile
	@echo $(COQ_FLAG) > _CoqProject

include .depend
