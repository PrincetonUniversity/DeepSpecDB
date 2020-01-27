(** * verif_movetoprev.v : Correctness proof of lastpointer, moveToPrev and RL_MoveToPrevious *)

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
Require Import verif_movetofirst.
Require Import verif_movetolast.

Lemma body_firstpointer: semax_body Vprog Gprog f_firstpointer firstpointer_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'1=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward.                    (* return 0 *)
    entailer!.
    entailer!.
    +
    destruct isLeaf; simpl; auto. inv H0.
    +
    destruct isLeaf; [ |  inv H0].
    fold n. rewrite unfold_btnode_rep with (n:=n). unfold n.
      Exists ent_end. cancel.
  - forward.
     entailer!.
     entailer!.
    +
    destruct isLeaf; simpl; auto. inv H0.
    +
    destruct isLeaf; simpl in H0. inv H0.
    fold n. rewrite unfold_btnode_rep with (n:=n). unfold n.
      Exists ent_end. cancel.
Qed.

Lemma body_moveToPrev: semax_body Vprog Gprog f_moveToPrev moveToPrev_spec.
Proof.
  start_function.
Admitted.

Lemma body_RL_MoveToPrevious: semax_body Vprog Gprog f_RL_MoveToPrevious RL_MoveToPrevious_spec.
Proof.
  start_function.
Admitted.

  