Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
(* Require Import mmap0. *)
Require Import main.
Require Import malloc_lemmas.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs_R ++ private_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 


Lemma create_mem_mgr_R: 
  forall (gv: globals),
  !! (headptr (gv malloc._bin)) &&
   data_at_ Ews (tarray (tptr tvoid) BINS) (gv malloc._bin)
     |-- mem_mgr_R gv emptyResvec.
Admitted.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.  (* was formerly very slow, fixed now. *)
change 8 with BINS.
sep_apply (create_mem_mgr_R gv); auto.
admit.
all:fail.
Admitted.


Definition module := [mk_body body_main].



