(** * verif_newrel.v: Correctness proof of NewRelation *)

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
Require Import btrees_sep.
Require Import btrees_spec.

Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec.
Proof.
start_function.
forward_call(true,true,true).
Intros vret.
forward_if(PROP (vret<>nullval)
     LOCAL (temp _pRootNode vret)
     SEP (btnode_rep (empty_node true true true vret))).
- apply denote_tc_test_eq_split.
  + assert (vret = getval(empty_node true true true vret)). simpl. auto. rewrite H1. entailer!.
  + entailer!.
- subst vret. forward.
- forward. entailer!.
- forward_call trelation.
  + split. unfold sizeof. simpl. rep_omega. split; auto.
  + Intros newrel.
    forward_if(PROP (newrel<>nullval)
     LOCAL (temp _pNewRelation newrel; temp _pRootNode vret)
     SEP (malloc_token Tsh trelation newrel * data_at_ Tsh trelation newrel;
          btnode_rep (empty_node true true true vret))).
    * subst newrel.
      forward_call (tbtnode, vret). (* free *)
      { unfold btnode_rep. simpl. Intros ent_end. cancel.
        unfold data_at_. unfold field_at_.
        simpl.
        change_compspecs CompSpecs. cancel. }
      { forward. }
    * forward.
      entailer!.
    * Intros.
      forward.                  (* pnewrelation->root = prootnode *)
      forward.                  (* pnewrelation->numrecords=0 *)
      forward.                  (* pnewRelation->depth=0 *)
      forward.                  (* return pnewrelation *)
      Exists newrel. Exists vret.
      entailer!. apply derives_refl.
Qed.