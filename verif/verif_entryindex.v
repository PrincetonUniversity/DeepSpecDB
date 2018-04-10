(** * verif_entryindex.v : Correctness proof of entryIndex  *)

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

Lemma Znth_rev_cons: forall p (c:list val),
    Znth (Zlength c) (rev (p::c)) = p.
Proof.
  intros.
  induction c.
  - simpl. auto.
  - simpl. assert (Zlength (a::c) = Zlength c +1) by apply Zlength_cons. rewrite H.
    rewrite <- app_assoc. rewrite app_Znth2.
    rewrite Zlength_rev. assert(Zlength c + 1 - Zlength c = 1) by omega. rewrite H0.
    simpl. auto. rewrite Zlength_rev. omega.
Qed.

Lemma rev_cons: forall X (p:X) c,
    rev c ++ [p] = rev (p::c).
Proof.
  intros. simpl. auto.
Qed.

Lemma body_entryIndex: semax_body Vprog Gprog f_entryIndex entryIndex_spec.
Proof.
  start_function.
  unfold cursor_rep.
  Intros anc_end. Intros Idx_end.
  forward.                      (* t'1=cursor->level *)
  destruct c.
  - inversion H. inversion H0.
  - forward.                      (* t'2=cursor->ancestorsIdx[t'1] *)
    + entailer!.
      unfold cursor_correct in H. destruct H.
      split. omega.
      assert (20=Z.of_nat MaxTreeDepth). rewrite MTD_eq. simpl. auto.
      rewrite H8. omega.
    + entailer!. autorewrite with sublist.
      assert (Z.succ (Zlength c) -1 - Zlength c = 0) by omega.
      rewrite H7. unfold Znth. simpl.
      unfold rep_index. destruct (snd p); auto.
    + autorewrite with sublist. deadvars!.
      destruct r. destruct p. destruct p0. autorewrite with norm.
      assert(Z.succ (Zlength c) -1 = Zlength c) by omega. rewrite H0.
      pose (c':=map (fun x : node val * index.index => rep_index (snd x)) c). fold c'.
      assert (Zlength c = Zlength c') by (unfold c'; rewrite Zlength_map; auto).
      rewrite H1.
      rewrite Znth_rev_cons.
      forward. cancel.
      unfold cursor_rep.
      Exists (anc_end). Exists (Idx_end). cancel.
      rewrite <- H1. assert (Zlength ((n, i) :: c) - 1 = Zlength c).
      rewrite Zlength_cons. omega. rewrite H12.
      cancel.
Qed.