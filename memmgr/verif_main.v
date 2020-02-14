Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main.
Require Import malloc_lemmas.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs_R ++ private_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
 start_function.
 change 8 with BINS.
sep_apply (create_mem_mgr_R gv); auto.
admit.
all:fail.
Admitted.


Definition module := [mk_body body_main].



