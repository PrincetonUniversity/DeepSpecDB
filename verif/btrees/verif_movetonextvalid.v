(** * verif_movetonextvalid.v : Correctness proof of RL_MoveToNextValid *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_movetonext.

Lemma body_RL_MoveToNextValid: semax_body Vprog Gprog f_RL_MoveToNextValid RL_MoveToNextValid_spec.
Proof.
  start_function.
  forward_call(c, pc, r).
  forward_call(r, (RL_MoveToNext c r), pc).
  split3; auto. 
  { destruct c.
    { simpl. auto. }
    { simpl. destruct p. simple_if_tac.
      apply movetonext_complete. apply movetonext_complete. auto.
      apply movetonext_complete. auto. }}
  forward. entailer!. entailer!.
Qed.
