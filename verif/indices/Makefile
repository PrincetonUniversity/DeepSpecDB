CURRENT_LOC=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
VST_DIRS= msl floyd veric sepcomp

CC_FLAGS= -R $(VST_LOC)/compcert compcert
VST_FLAGS=$(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))
PROJ_FLAGS=-Q $(CURRENT_LOC) indices
BTREE_FLAGS=-Q $(BTREES) btrees

COQ_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS) $(BTREE_FLAGS)
DEP_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS) $(BTREE_FLAGS)

FILES = definitions.v stringlist.v unordered_flat.v unordered_interface.v verif_stringlist.v stringlist_instance.v ordered_interface.v btree_wrappers.v btree_instance.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

all: \
  $(FILES:%.v=%.vo) \

.depend: Makefile
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	rm -f $(FILES:.v=.vo) $(FILES:.v=.glob) $(join $(dir $(FILES)),$(patsubst %.v,.%.aux,$(notdir $(FILES))))

_CoqProject: Makefile
	echo $(COQ_FLAG) > _CoqProject

.DEFAULT_GOAL := all

include .depend
