Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main_bss.
Require Import malloc_lemmas.
Require Import spec_malloc.


Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [malloc.prog; main_bss.prog]).

Instance CompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined.

Local Open Scope assert.

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt nil gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

(* proof using simple resource-tracking spec of malloc *)

Definition user_specs_R' := 
[pre_fill_spec'; try_pre_fill_spec'; malloc_spec_R_simple'; free_spec_R'].

Definition Gprog' : funspecs := [main_spec] ++ external_specs ++ user_specs_R'.

Lemma body_main': semax_body Vprog Gprog' f_main main_spec.
Proof.
start_function.
change 8 with BINS.
sep_apply (create_mem_mgr_R gv); auto.
forward. (* bb = heap *)
change 524296 with (BIGBLOCK + WORD*ALIGN).

forward_if (
    EX bb,
    (PROP (malloc_compatible BIGBLOCK bb)
     LOCAL (temp _bb bb; gvars gv)
     SEP (mem_mgr_R gv emptyResvec; 
          memory_block Tsh BIGBLOCK bb;
          has_ext tt))).

(* oops - have only Ews for bss, but pre_fill asks for Tsh *)




