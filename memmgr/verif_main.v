Require Import VST.floyd.proofauto.
(*Require Import VST.floyd.library.*)
Require Import linking.
Require Import malloc.
Require Import mmap0.
Require Import main.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := user_specs ++ private_specs.

Definition Vprog : varspecs. mk_varspecs prog. Defined. 

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
(* TODO next line seems to work but takes 3 minutes.
start_function. 
*)

(*
sep_apply (create_mem_mgr gv).
assert (change_composite_env spec_onepile.CompSpecs CompSpecs).
*)
admit.
all:fail.
Admitted.


Definition module := [mk_body body_main].



