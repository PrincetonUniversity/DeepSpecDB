Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main.
Require Import malloc_lemmas.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs ++ private_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
change 8 with BINS.
sep_apply (create_mem_mgr gv); auto.
forward_call(100,gv). (* t1 = malloc(100) *)
rep_omega.
Intros p.
forward_call(100,p,gv). (* free(100) *)
forward.
Qed.

Definition module := [mk_body body_main].



