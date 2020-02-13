Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
(* Require Import mmap0. *)
Require Import main.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs ++ private_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.  (* was formerly very slow, fixed now. *)
(*
sep_apply (create_mem_mgr gv).
assert (change_composite_env spec_onepile.CompSpecs CompSpecs).
*)
admit.
all:fail.
Admitted.


Definition module := [mk_body body_main].



