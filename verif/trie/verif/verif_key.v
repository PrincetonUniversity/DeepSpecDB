(** * verif_key.v: Correctness proof of key *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import DB.common.
Require Import DB.tactics.

Require Import DB.functional.keyslice.

Require Import DB.representation.string.
Require Import DB.representation.key.

Require Import DB.specs.

Import Coq.Lists.List.ListNotations.

Definition Gprog : funspecs :=
  ltac:(with_library prog [
        surely_malloc_spec; (* KV_NewKey_spec; *)
        move_key_spec
       ]).

Lemma body_KV_MoveKey: semax_body Vprog Gprog f_move_key move_key_spec.
Proof.
  start_function.
  forward.
  forward_call (tkey).
  split3; auto; simpl; rep_lia.
  Intros k.
  forward.
  forward.
  forward.
  Exists k.
  fold_keyrep.
  entailer!.
Qed.
