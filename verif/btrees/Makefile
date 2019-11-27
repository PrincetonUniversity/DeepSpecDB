# VST_LOC=~/VST 
# CC_LOC=~/CompCert
# VFA_LOC=~/vfa
CC=gcc
COQBIN=
# export COQVERSION := 8.8.0
export COQVERSION := 8.10.1

include CONFIGURE
# IN THE CONFIGURE FILE, MUST DEFINE:
# VST_LOC= /path/to/vst
# CC_LOC= /path/to/compcert

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VST_DIRS= msl sepcomp veric floyd progs

CCFLAGS= -R $(CC_LOC) compcert
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))
DEP_FLAG= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))

COQFLAGS = $(VSTFLAGS) -R ../../model Model -R . btrees # -R $(VFA_LOC) Top 

FILES = relation_mem.v index.v btrees.v btrees_sep.v btrees_spec.v verif_findindex.v verif_entryindex.v verif_currnode.v verif_isvalid.v verif_movetofirst.v verif_movetolast.v verif_movetokey.v verif_movetonext.v verif_getrecord.v verif_movetoprev.v verif_newnode.v verif_newrel.v verif_newcursor.v \
    verif_splitnode_part0.v verif_splitnode_part1.v verif_splitnode_part2.v verif_splitnode_part3.v verif_splitnode_part4.v verif_splitnode.v \
    verif_putrecord.v verif_isnodeparent.v verif_gotokey.v verif_relation_mem.v 

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

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vio
	@rm tests

_CoqProject: Makefile
	echo $(COQFLAGS) > _CoqProject

.loadpath: Makefile
	@echo $(COQFLAGS) > .loadpath

tests: tests.c relation.h relation_mem.c
	$(CC) relation_mem.c tests.c -o tests

.DEFAULT_GOAL := all

include .depend
