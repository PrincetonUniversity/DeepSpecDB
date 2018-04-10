(** * verif_curnode.v : Correctness proof of currNode  *)

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
Require Import verif_entryindex.

Lemma body_currNode: semax_body Vprog Gprog f_currNode currNode_spec.
Proof.
  start_function.
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  forward.                      (* t'1=cursor->level *)
  forward.                      (* t'2=cursor->ancestors[t'1] *)
  entailer!. inv H. split. omega. rewrite MTD_eq in H8. assert (Z.of_nat 20 = 20). simpl. auto. omega.
  entailer!. admit.
  destruct c.
  - inv H. inv H0.
  - rewrite Zlength_cons. assert (Zsucc (Zlength c) -1 = Zlength c) by omega. rewrite H0.
    autorewrite with norm. autorewrite with sublist. deadvars!.
    destruct r. destruct p0.
    pose (c':=map getval (map fst c)). fold c'.
    assert (Zlength c = Zlength c') by (unfold c'; rewrite Zlength_map; rewrite Zlength_map; auto).
    rewrite H1. rewrite Znth_rev_cons.
    forward. destruct p0. cancel. unfold cursor_rep. Exists anc_end. Exists idx_end.
    cancel. rewrite <- H1. assert (Zlength (p :: c) - 1 = Zlength c).
    rewrite Zlength_cons. rep_omega. rewrite H12. cancel.
Admitted.

