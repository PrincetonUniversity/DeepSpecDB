Require Import VST.floyd.proofauto.
Require Import VST.floyd.proofauto.
Require Import linking.
Require Import main.
Require Import malloc.
Require Import spec_main.
Require Import spec_malloc.

Definition Gprog : funspecs := 
 ltac:(with_library prog (user_specs ++ private_specs)).


Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
(*
sep_apply (create_mem_mgr gv).
assert (change_composite_env spec_onepile.CompSpecs CompSpecs).
*)
admit.
all:fail.
Admitted.


Definition module := [mk_body body_main].


