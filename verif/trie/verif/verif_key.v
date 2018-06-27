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
        KV_MoveKey_spec; KV_GetCharArray_spec;
        KV_GetCharArraySize_spec
       ]).

Lemma body_KV_MoveKey: semax_body Vprog Gprog f_KV_MoveKey KV_MoveKey_spec.
Proof.
  start_function.
  forward.
  forward_if (True);
    [
      unfold cstring_len;
      forward_if (True);
      [forward; entailer! | assert_PROP (False) by entailer!; contradiction] |
      forward; entailer! |
    ].
  forward_call (tkey).
  split3; auto; simpl; rep_omega.
  Intros k.
  forward.
  forward.
  forward.
  Exists k.
  Exists s.
  fold_keyrep.
  entailer!.
Qed.

Lemma body_KV_GetCharArray: semax_body Vprog Gprog f_KV_GetCharArray KV_GetCharArray_spec.
Proof.
  start_function.
  unfold key_rep.
  Intros.
  forward_if (True); [forward; entailer! | assert_PROP (False) by entailer!; contradiction | ].
  forward.
  forward.
  fold_keyrep.
  entailer!.
Qed.

Lemma body_KV_GetCharArraySize: semax_body Vprog Gprog f_KV_GetCharArraySize KV_GetCharArraySize_spec.
Proof.
  start_function.
  unfold key_rep.
  Intros.
  forward_if (True); [forward; entailer! | assert_PROP (False) by entailer!; contradiction | ].
  forward.
  forward.
  fold_keyrep.
  entailer!.
Qed.
