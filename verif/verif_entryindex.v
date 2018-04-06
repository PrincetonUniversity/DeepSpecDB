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
  - admit.
  - forward.                      (* t'2=cursor->ancestorsIdx[t'1] *)
    + entailer!. admit.           (* how do we prove that we won't go deeper than max_tree_depth? *)
    + autorewrite with sublist. entailer!.
      autorewrite with sublist.
      assert (Z.succ (Zlength c) -1 - Zlength c = 0) by omega.
      rewrite H6. unfold Znth. simpl.
      unfold rep_index. destruct (snd p); auto.
    + autorewrite with sublist. deadvars!.
      destruct r. destruct p. destruct p0. autorewrite with norm.
      assert(Z.succ (Zlength c) -1 = Zlength c) by omega. rewrite H.
      pose (c':=map (fun x : node val * index.index => rep_index (snd x)) c). fold c'.
      assert (Zlength c = Zlength c') by (unfold c'; rewrite Zlength_map; auto).
      rewrite H0.
      rewrite Znth_rev_cons.
      unfold abbreviate in POSTCONDITION. admit.
      (* can't do forward here *)
Admitted.