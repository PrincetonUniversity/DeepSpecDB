HFILES = relation.h
CFILES = relation_mem.c tests.c 
VFILES = relation_mem.v btrees.v btrees_sep.v btrees_spec.v \
         verif_findindex.v verif_entryindex.v verif_currnode.v \
         verif_isvalid.v verif_movetofirst.v verif_movetolast.v \
         verif_movetokey.v verif_movetonext.v verif_getrecord.v \
         verif_movetoprev.v verif_newnode.v verif_newrel.v verif_newcursor.v \
         verif_splitnode_part0.v verif_splitnode_part1.v \
         verif_splitnode_part2.v verif_splitnode_part3.v \
         verif_splitnode_part4.v verif_splitnode.v \
         verif_putrecord.v verif_isnodeparent.v verif_gotokey.v \
         verif_relation_mem.v verif_isempty.v verif_movetonextvalid.v \
         verif_numrecords.v verif_getkey.v 

#CC=gcc
CC=ccomp
CFLAGS=-O

ifeq ($(ls CONFIGURE),"")
  $(error Please create a CONFIGURE file defining VST_LOC and COMPCERT_LOC)
else
  include CONFIGURE
endif

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

CVFILES = $(patsubst %.c,%.v,$(CFILES))
OFILES = $(patsubst %.c,%.o,$(CFILES))
VOFILES = $(patsubst %.v,%.vo,$(CVFILES) $(VFILES))


VST_DIRS= msl sepcomp veric floyd concurrency progs
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -I . 

target: _CoqProject $(VOFILES) abstract_spec.v

cvfiles: $(CVFILES)

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

$(CVFILES): $(CFILES) $(HFILES)
	$(CLIGHTGEN) -normalize $(CFILES)

_CoqProject: Makefile CONFIGURE
	@echo $(VSTFLAGS) > _CoqProject

clean:
	rm -f *.vo *.o .*.aux *.vok *.vos

btrees_sep.vo: btrees.vo
btrees_spec.vo: relation_mem.vo btrees.vo btrees_sep.vo
verif_findindex.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_entryindex.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_currnode.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_isvalid.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_movetofirst.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_movetolast.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_movetokey.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_movetonext.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_getrecord.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_movetonext.vo
verif_movetoprev.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_newnode.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_newrel.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_newcursor.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_splitnode_part0.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_splitnode_part1.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part0.vo
verif_splitnode_part2.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part1.vo
verif_splitnode_part3.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part0.vo
verif_splitnode_part4.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part3.vo
verif_splitnode.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part2.vo verif_splitnode_part4.vo
verif_putrecord.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_splitnode_part0.vo
verif_isnodeparent.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_gotokey.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_relation_mem.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_findindex.vo verif_entryindex.vo verif_currnode.vo verif_isvalid.vo verif_movetofirst.vo verif_movetolast.vo verif_movetokey.vo verif_movetonext.vo verif_getrecord.vo verif_movetoprev.vo verif_newnode.vo verif_newrel.vo verif_newcursor.vo verif_splitnode.vo verif_putrecord.vo verif_isnodeparent.vo verif_gotokey.vo
verif_isempty.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_movetonextvalid.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_movetonext.vo
verif_numrecords.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo
verif_getkey.vo: relation_mem.vo btrees.vo btrees_sep.vo btrees_spec.vo verif_movetonext.vo