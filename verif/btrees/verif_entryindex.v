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

Lemma Znth_rev_cons: forall p (c:list val) d,
    d = Zlength c -> 
    Znth d (rev (p::c)) = p.
Proof.
  intros.
  induction c; subst.
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
  destruct r as [root prel].
  pose (r:=(root,prel)).
  unfold cursor_rep. Intros anc_end. Intros Idx_end.
  forward.                      (* t'1=cursor->level *)
  destruct c as [|[n i ]c'].
  - inv H. inv H1. inv H. inv H2. inv H1. inv H. (* no empty cursor *)
  - forward.                      (* t'2=cursor->ancestorsIdx[t'1] *)
    + entailer!.
      apply partial_complete_length in H. auto. auto.
    + entailer!. autorewrite with sublist.
      replace (Z.succ (Zlength c') -1) with (Zlength c') by omega.
      rewrite app_Znth1, app_Znth2. autorewrite with sublist. auto.
      autorewrite with sublist. omega.
      autorewrite with sublist. omega.
    + autorewrite with sublist. deadvars!.
      destruct r. autorewrite with norm.
      assert(Z.succ (Zlength c') -1 = Zlength c') by omega. rewrite H1.
      pose (c'':=map (fun x : node val * index.index => Vint(Int.repr(rep_index (snd x)))) c'). fold c''.
      assert (Zlength c'' = Zlength c') by (unfold c''; rewrite Zlength_map; auto).
      rewrite <- H2.
      rewrite app_Znth1, Znth_rev_cons.
      forward. cancel.
      unfold cursor_rep.
      Exists (anc_end). Exists (Idx_end). cancel.
      rewrite H2. replace (Zlength ((n, i) :: c') - 1) with (Zlength c'). cancel.
      rewrite Zlength_cons ; omega. omega. autorewrite with sublist. omega.
Qed.
