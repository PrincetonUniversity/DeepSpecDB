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
replace Ews with Tsh by admit. (* TODO UNSOUND workaround *)
rewrite <- memory_block_data_at_.
forward_if (
    EX bb,
    (PROP (malloc_compatible BIGBLOCK bb)
     LOCAL (temp _bb bb; gvars gv)
     SEP (mem_mgr_R gv emptyResvec; 
          memory_block Tsh BIGBLOCK bb;
          has_ext tt))).
admit. 
(* case bb%(WORD*ALIGN) != 0 *) 
forward. (* bb = bb + WORD*ALIGN - (uintptr_t)bb%(WORD*ALIGN) *)
entailer!.
admit.
Exists (offset_val (WORD*ALIGN) (gv _heap)).
entailer!.
admit.
admit. (* use memory_block_split_offset *)
(* case bb%(WORD*ALIGN) == 0 *) 
forward.
Exists (gv _heap).
entailer!.
admit.
admit.
Intros bb.
rewrite <- seq_assoc.
forward_call (100, bb, gv, emptyResvec).
split; [rep_omega | auto].
admit.  (* WORKING HERE *)
Admitted.