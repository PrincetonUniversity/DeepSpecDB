Require Import VST.floyd.proofauto.
Require Import linking. (* TODO I'm using local copy of pile/linking.v *)
Require Import main.
Require Import spec_malloc.

Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [malloc.prog; main.prog; mmap0.prog]).

Instance CompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined.

Local Open Scope assert.

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog nil gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

Definition specs := [main_spec].

