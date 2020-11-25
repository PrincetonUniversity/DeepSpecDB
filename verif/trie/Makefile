CURRENT_LOC=.
VST_LOC=../VST
CC_LOC=../VST/compcert
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
VST_DIRS= msl sepcomp veric floyd

CC_FLAGS= -R $(CC_LOC) compcert
VST_FLAGS=$(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))
PROJ_FLAGS=-R $(CURRENT_LOC) DB

COQ_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)
DEP_FLAG = $(CC_FLAGS) $(VST_FLAGS) $(PROJ_FLAGS)

FILES = $(wildcard *.v) \
        $(wildcard clight/*.v) \
        $(wildcard functional/*.v) \
	$(wildcard representation/*.v) \
        $(wildcard verif/*.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

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
