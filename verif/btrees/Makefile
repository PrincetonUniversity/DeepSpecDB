VST_LOC=~/VST
CC_LOC=~/CompCert
VFA_LOC=~/vfa
CC=gcc
COQBIN=
export COQVERSION := 8.8.0

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VST_DIRS= msl sepcomp veric floyd progs

CCFLAGS= -R $(CC_LOC) compcert
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))
DEP_FLAG= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

COQFLAGS = $(VSTFLAGS) -R $(VFA_LOC) Top -R ../../model Model

FILES = relation_mem.v index.v btrees.v btrees_sep.v btrees_spec.v verif_findindex.v verif_entryindex.v verif_currnode.v verif_isvalid.v verif_movetofirst.v verif_movetolast.v verif_movetokey.v verif_movetonext.v verif_getrecord.v verif_movetoprev.v verif_newnode.v verif_newrel.v verif_newcursor.v verif_splitnode.v verif_putrecord.v verif_isnodeparent.v verif_gotokey.v verif_relation_mem.v 

abstract.vo: abstract_spec.v
	@echo COQC abstract_spec.v
	@$(COQC) $(COQFLAGS) abstract_spec.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v

$(FILES:%.v=%.vio): %.vio: %.v
	@echo COQCQUICK $*.v
	@$(COQC) $(COQFLAGS) -quick $*.v

all: _CoqProject .loadpath .depend $(FILES:%.v=%.vo) # abstract.vo

quick: _CoqProject .loadpath .depend $(FILES:%.v=%.vio) # abstract.vo

relation_mem.v: relation_mem.c
	$(CC_LOC)/clightgen -normalize relation_mem.c

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vio
	@rm tests

_CoqProject: Makefile
	@echo $(COQFLAGS) > _CoqProject

.loadpath: Makefile
	@echo $(COQFLAGS) > .loadpath

tests: tests.c relation.h relation_mem.c
	$(CC) relation_mem.c tests.c -o tests

.DEFAULT_GOAL := all

include .depend
