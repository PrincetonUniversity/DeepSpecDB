VFA_LOC=~/vfa
CC=gcc
COQBIN=
export COQVERSION := 8.8.0

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

COQFLAGS = $(VSTFLAGS) -R $(VFA_LOC) Top -R . Model

FILES = BTrees.v BTreesModule.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v

$(FILES:%.v=%.vio): %.vio: %.v
	@echo COQCQUICK $*.v
	@$(COQC) $(COQFLAGS) -quick $*.v

all: _CoqProject .loadpath .depend $(FILES:%.v=%.vo)

quick: _CoqProject .loadpath .depend $(FILES:%.v=%.vio)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vio

_CoqProject: Makefile
	@echo $(COQFLAGS) > _CoqProject

.loadpath: Makefile
	@echo $(COQFLAGS) > .loadpath

.DEFAULT_GOAL := all

include .depend
