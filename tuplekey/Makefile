ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CC=ccomp
CFLAGS=-O

HFILES = stdlib.h inthash.h stringlist.h inthash_schema.h stringlist_schema.h index.h tuple_schema.h fo_index.h

CFILES = inthash.c stringlist.c inthash_schema.c stringlist_schema.c main.c index.c tuple_schema.c fo_index.c

CVFILES = $(patsubst %.c,%.v,$(CFILES))
OFILES = $(patsubst %.c,%.o,$(CFILES))

VFILES = \
	spec_inthash.v \
	spec_stringlist.v \
	verif_inthash.v \
	verif_stringlist.v

VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))


target: $(OFILES)

stringlist.vo: stringlist.v

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

ifdef $(COMPCERT_LOC)
CLIGHTGEN= $(COMPCERT_LOC)/clightgen
$(CVFILES): $(CFILES) $(HFILES)
	$(CLIGHTGEN) -normalize $(CFILES)
endif


_CoqProject: Makefile
	@echo $(VSTFLAGS) > _CoqProject

clean:
	rm -f *.vo *.o .*.aux
