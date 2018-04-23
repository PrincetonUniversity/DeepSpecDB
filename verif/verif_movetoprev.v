(** * verif_movetoprev.v : Correctness proof of lastpointer, moveToPrev and RL_MoveToPrevious *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_movetofirst.
Require Import verif_movetolast.

Lemma body_firstpointer: semax_body Vprog Gprog f_firstpointer firstpointer_spec.
Proof.
  start_function.
Admitted.

Lemma body_moveToPrev: semax_body Vprog Gprog f_moveToPrev moveToPrev_spec.
Proof.
  start_function.
Admitted.

Lemma body_RL_MoveToPrevious: semax_body Vprog Gprog f_RL_MoveToPrevious RL_MoveToPrevious_spec.
Proof.
  start_function.
Admitted.

  