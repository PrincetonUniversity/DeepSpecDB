VST_LOC=~/VST
CC_LOC=~/CompCert
COQBIN=
export COQVERSION := 8.7.1

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VST_DIRS= msl sepcomp veric floyd progs

CCFLAGS= -R $(CC_LOC) compcert
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

COQFLAGS = $(VSTFLAGS)

FILES = relation_mem.v verif_relation_mem.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v

all: _CoqProject .loadpath .depend $(FILES:%.v=%.vo)

relation_mem.v: relation_mem.c
	$(CC_LOC)/clightgen -normalize relation_mem.c

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob

_CoqProject: Makefile
	@echo $(COQFLAGS) > _CoqProject

.loadpath: Makefile
	@echo $(COQFLAGS) > .loadpath

.DEFAULT_GOAL := all

include .depend
