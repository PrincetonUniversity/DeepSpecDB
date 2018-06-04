(** * verif_surely_malloc.v: Correctness proof of surely malloc *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import deepDB.clight.verifiable.
Require Import deepDB.specs.

Definition Gprog : funspecs :=
  ltac:(with_library prog [
                       surely_malloc_spec
       ]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call t.
  Intros p.
  forward_if (p <> nullval).
  if_tac; entailer!.
  - forward_call tt.
    entailer!.
  - forward.
    entailer!.
  - Intros.
    rewrite if_false by auto.
    forward.
    Exists p.
    entailer!.
Qed.
