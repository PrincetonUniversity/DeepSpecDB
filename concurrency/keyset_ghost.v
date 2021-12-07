Require Export VST.veric.bi.
Require Import VST.concurrency.ghosts.
Require Export bst.flows.

From stdpp Require Export sets gmap mapset.
Require Import stdpp.sorting.

Require Import Coq.Lists.ListDec.
Require Import Coq.Lists.List.

Lemma Permutation_incl: forall {A: Type} (l1 l1' l2 l2': list A),
    l1 ≡ₚ l1' -> l2 ≡ₚ l2' -> incl l1 l2 -> incl l1' l2'.
Proof. intros. unfold incl in *. intros. rewrite <- H0. rewrite <- H in H2. now apply H1. Qed.

#[global] Instance Permutation_incl': forall {A: Type}, Proper (@Permutation A ==> @Permutation A ==> iff) (@incl A).
Proof. repeat intro. split; intros; [|symmetry in H, H0]; eauto using Permutation_incl. Qed.

Lemma app_disjoint_1: forall {A: Type} (l1 l2 l3: list A), l1 ++ l2 ## l3 -> l1 ## l3.
Proof.
  intros. rewrite elem_of_disjoint in H. rewrite elem_of_disjoint. intros. apply (H x); auto.
  rewrite elem_of_app. now left.
Qed.

Lemma app_disjoint_2: forall {A: Type} (l1 l2 l3: list A), l1 ++ l2 ## l3 -> l2 ## l3.
Proof.
  intros. rewrite elem_of_disjoint in H. rewrite elem_of_disjoint. intros. apply (H x); auto.
  rewrite elem_of_app. now right.
Qed.

Lemma disjoint_app_NoDup: forall {A: Type} (l1 l2: list A), l1 ## l2 -> NoDup l1 -> NoDup l2 -> NoDup (l1 ++ l2).
Proof.
  intros. rewrite sublist.NoDup_app_iff. rewrite elem_of_disjoint in H.
  repeat (split; [done|]). repeat intro. rewrite <- elem_of_list_In in H2, H3. now apply (H x).
Qed.

Lemma disjoint_app: forall {A: Type} (l1 l2 l3: list A), l1 ## l2 -> l1 ## l3 -> l1 ## l2 ++ l3.
Proof.
  intros. rewrite elem_of_disjoint in H. rewrite elem_of_disjoint in H0.
  rewrite elem_of_disjoint. intros. rewrite elem_of_app in H2. destruct H2; [apply (H x) | apply (H0 x)]; done.
Qed.

Lemma perm_disjoint: forall {A: Type} (l1 l2 l3: list A), l1 ≡ₚ l2 -> l1 ## l3 -> l2 ## l3.
Proof.
  intros. rewrite elem_of_disjoint in H0. rewrite elem_of_disjoint. intros.
  apply (H0 x); auto. now rewrite H.
Qed.

Lemma Permutation_disjoint: forall {A: Type} (l1 l1' l2 l2': list A),
    l1 ≡ₚ l1' -> l2 ≡ₚ l2' -> l1 ## l2 -> l1' ## l2'.
Proof.
  intros. rewrite elem_of_disjoint in H1. rewrite elem_of_disjoint. intros.
  rewrite <- H in H2. rewrite <- H0 in H3. now apply (H1 x).
Qed.

#[global] Instance Permutation_disjoint':
  forall {A: Type}, Proper (@Permutation A ==> @Permutation A ==> iff) (@disjoint (list A) _).
Proof. repeat intro. split; intros; [|symmetry in H, H0]; eauto using Permutation_disjoint. Qed.

Section keyset_ghost.

  (* The set of keys. *)
  Context `{Countable K}.

  Context `{TO: TotalOrder K R}.

  Context `{OrdDec: forall x y, Decision (R x y)}.

  (* The keyspace is some arbitrary finite subset of K. *)
  Parameter KS : gset K.

  Definition set_pair := (list K * list K)%type.

  Canonical Structure pairRAC := leibnizO set_pair.

  Definition empty_pair: set_pair := ([], []).
  #[global] Instance pair_empty : Empty set_pair := empty_pair.

  #[global] Instance NoDup_dec: forall (l: list K), Decision (NoDup l).
  Proof. apply NoDup_dec. intros. apply (decide (x = y)). Defined.

  #[global] Instance incl_dec: forall (l1 l2: list K), Decision (incl l1 l2).
  Proof. apply incl_dec. intros. apply (decide (x = y)). Defined.

  #[global] Instance in_dec: forall (a: K) (l: list K), Decision (In a l).
  Proof. apply in_dec. intros. apply (decide (x = y)). Defined.

  #[global] Instance disj_dec: forall (l1 l2: list K), Decision (l1 ## l2).
  Proof.
    intros. induction l1.
    - left. rewrite elem_of_disjoint. intros. inversion H0.
    - destruct (decide (In a l2)).
      + right. rewrite elem_of_disjoint. intro. apply (H0 a).
        * left.
        * now rewrite elem_of_list_In.
      + destruct IHl1; [left | right]; rewrite elem_of_disjoint; intros.
        * apply n. rewrite elem_of_disjoint in d. inversion H0; subst.
          -- now rewrite <- elem_of_list_In.
          -- exfalso. now apply (d x).
        * intro. apply n0. rewrite elem_of_disjoint. intros. apply (H0 x); auto. now right.
  Defined.

  Definition setPairOp: set_pair -> set_pair -> option set_pair :=
    fun p1 p2 =>
      if (decide (p1 = ∅))
      then Some p2
      else if (decide (p2 = ∅))
           then Some p1
           else
             match p1, p2 with
             | (K1, C1), (K2, C2) =>
                 (if (decide (NoDup K1)) then
                    (if (decide (NoDup C1)) then
                       (if (decide (NoDup K2)) then
                          (if (decide (NoDup C2)) then
                             (if (decide (incl C1 K1)) then
                                (if (decide (incl C2 K2)) then
                                   (if (decide (K1 ## K2)) then
                                      (if (decide (C1 ## C2)) then Some (merge_sort R (K1 ++ K2),
                                                                          merge_sort R (C1 ++ C2))
                                       else None)
                                    else None)
                                 else None)
                              else None)
                           else None)
                        else None)
                     else None)
                  else None)
             end.

  #[global] Instance setPairValid : Valid set_pair :=
    fun p => match p with
             | (K, C) => NoDup K /\ NoDup C /\ incl C K
             end.

  Lemma empty_valid: setPairValid ∅.
  Proof.
    unfold empty, pair_empty, empty_pair. red. split; [|split].
    - apply NoDup_nil.
    - apply NoDup_nil.
    - apply incl_nil_l.
  Qed.

  #[global] Instance pairJoin: sepalg.Join set_pair :=
    fun p1 p2 p3 => setPairOp p1 p2 = Some p3.

  Lemma merge_sort_disjoint: forall (l1 l2: list K), merge_sort R l1 ## l2 -> l1 ## l2.
  Proof.
    intros. pose proof (merge_sort_Permutation R l1). eapply perm_disjoint in H0; eauto.
  Qed.

  Lemma merge_sort_unique: forall (l1 l2: list K), l1 ≡ₚ l2 -> merge_sort R l1 = merge_sort R l2.
  Proof.
    intros. pose proof (Sorted_merge_sort R l1). pose proof (Sorted_merge_sort R l2).
    pose proof (merge_sort_Permutation R l1). pose proof (merge_sort_Permutation R l2).
    eapply perm_trans in H0; eauto. symmetry in H4. eapply perm_trans in H4; eauto.
    destruct TO. destruct total_order_partial. destruct partial_order_pre. eapply Sorted_unique; eauto.
  Qed.

  Lemma merge_sort_app_assoc: forall (l1 l2 l3: list K),
      merge_sort R (merge_sort R (l1 ++ l2) ++ l3) = merge_sort R (l1 ++ merge_sort R (l2 ++ l3)).
  Proof.
    intros. apply merge_sort_unique. pose proof (merge_sort_Permutation R (l1 ++ l2)). rewrite H0.
    pose proof (merge_sort_Permutation R (l2 ++ l3)). rewrite H1. rewrite app_assoc. auto.
  Qed.

  Lemma merge_sort_nil: forall l, merge_sort R l = [] -> l = [].
  Proof.
    intros. pose proof (merge_sort_Permutation R l). rewrite H0 in H1. now apply Permutation_nil in H1.
  Qed.

  Lemma setPairOp_nil: forall a, setPairOp a ∅ = Some a.
  Proof.
    intros. unfold setPairOp. destruct (decide (a = ∅)). 1: now subst. now simpl.
  Qed.

  Lemma pairJoin_assoc:
    ∀ a b c d e : set_pair, pairJoin a b d → pairJoin d c e →
                            {f : set_pair & pairJoin b c f ∧ pairJoin a f e}.
  Proof.
    intros. unfold pairJoin in *. unfold setPairOp in H0.
    destruct (decide (a = ∅)). 1: inversion H0; subst; exists e; split; auto.
    destruct (decide (b = ∅)). 1: inversion H0; subst; exists c; split; auto.
    destruct a as [Ka Ca]. destruct b as [Kb Cb].
    repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
    unfold setPairOp in H1. destruct (decide (d = ∅)).
    - exfalso. inversion H0. rewrite e0 in H3. inversion H3. rewrite H4 in H5.
      apply merge_sort_nil, app_eq_nil in H4, H5. destruct H4, H5. subst. now apply n.
    - destruct (decide (c = ∅)).
      + inversion H1. subst. rewrite setPairOp_nil. exists (Kb, Cb). split; auto. unfold setPairOp.
        now repeat (match goal with | |- context [match ?E with _ => _ end] => destruct E end; try done).
      + destruct d as [Kd Cd]. destruct c as [Kc Cc].
        repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
        inversion H0; subst. clear H0. inversion H1; subst; clear H1.
        exists (merge_sort R (Kb ++ Kc), merge_sort R (Cb ++ Cc)). unfold setPairOp. split.
        * apply merge_sort_disjoint in d, d2. apply app_disjoint_2 in d, d2. 
          repeat (match goal with | |- context [match ?E with _ => _ end] => destruct E end; try done).
        * apply merge_sort_disjoint in d, d2. pose proof (app_disjoint_1 _ _ _ d).
          pose proof (app_disjoint_1 _ _ _ d2). apply app_disjoint_2 in d, d2.
          pose proof (merge_sort_Permutation R (Kb ++ Kc)).
          pose proof (merge_sort_Permutation R (Cb ++ Cc)).
          assert (NoDup (merge_sort R (Kb ++ Kc))) by (rewrite H2; apply disjoint_app_NoDup; auto).
          assert (NoDup (merge_sort R (Cb ++ Cc))) by (rewrite H3; apply disjoint_app_NoDup; auto).
          assert (incl (merge_sort R (Cb ++ Cc)) (merge_sort R (Kb ++ Kc))) by
            (rewrite H2 H3; apply incl_app_app; auto).
          assert (Ka ## merge_sort R (Kb ++ Kc)) by (rewrite H2; apply disjoint_app; auto).
          assert (Ca ## merge_sort R (Cb ++ Cc)) by (rewrite H3; apply disjoint_app; auto).
          repeat (match goal with | |- context [match ?E with _ => _ end] => destruct E end; try done).
          -- exfalso. inversion e. rewrite H10 in H11. apply merge_sort_nil, app_eq_nil in H10, H11.
             destruct H10, H11. subst. now apply n0.
          -- f_equal. rewrite !merge_sort_app_assoc. done.
  Qed.

  Lemma disjoint_comm: forall (l1 l2: list K), l1 ## l2 -> l2 ## l1.
  Proof.
    intros. rewrite elem_of_disjoint in H0. rewrite elem_of_disjoint. intros. now apply (H0 x).
  Qed.

  Lemma merge_sort_app_comm: forall (l1 l2: list K), merge_sort R (l1 ++ l2) = merge_sort R (l2 ++ l1).
  Proof. intros. apply merge_sort_unique. apply Permutation_app_comm. Qed.

  Lemma pairJoin_comm:
       ∀ a b c : set_pair, pairJoin a b c → pairJoin b a c.
  Proof.
    intros. unfold pairJoin in *. unfold setPairOp in H0.
    destruct (decide (a = ∅)). 1: inversion H0; subst; apply setPairOp_nil.
    destruct (decide (b = ∅)). 1: inversion H0; subst; now simpl.
    destruct a as [Ka Ca]. destruct b as [Kb Cb].
    repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
    apply disjoint_comm in d, d0. unfold setPairOp.
    repeat (match goal with | |- context [match ?E with _ => _ end] => destruct E end; try done).
    rewrite (merge_sort_app_comm Kb Ka). rewrite (merge_sort_app_comm Cb Ca). done.
  Qed.

  Lemma merge_sort_length: forall (l: list K), length (merge_sort R l) = length l.
  Proof. intros. pose proof (merge_sort_Permutation R l). now apply Permutation_length in H0. Qed.

  #[global] Instance pairPerm: sepalg.Perm_alg set_pair.
  Proof.
    constructor; unfold sepalg.join; intros.
    - unfold pairJoin in *. rewrite H0 in H1. now inversion H1.
    - eapply pairJoin_assoc; eauto.
    - now apply pairJoin_comm.
    - unfold pairJoin in *. unfold setPairOp in H0.
      destruct (decide (a = ∅)).
      + inversion H0; subst. unfold setPairOp in H1.
        repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; try done);
          inversion H1; auto. rewrite H3 in H4. apply merge_sort_nil, app_eq_nil in H3, H4.
        destruct H3, H4. subst. now cbn.
      + destruct (decide (a' = ∅)). 1: now inversion H0. destruct a as [Ka Ca]. destruct a' as [Ka' Ca'].
        repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
        unfold setPairOp in H1. destruct (decide (b = ∅)).
        * exfalso. subst. inversion H0. rewrite H3 in H4. apply merge_sort_nil, app_eq_nil in H3, H4.
          destruct H3, H4. subst. now apply n.
        * destruct (decide (b' = ∅)). 1: now inversion H1. destruct b as [Kb Cb]. destruct b' as [Kb' Cb'].
          repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
          inversion H0. clear H0. inversion H1. clear H1.
          pose proof (merge_sort_length (Ka ++ Ka')). rewrite H3 in H0. rewrite app_length in H0.
          pose proof (merge_sort_length (Kb ++ Kb')). rewrite H2 in H1. rewrite app_length in H1.
          assert (length Ka' = O) by lia. apply nil_length_inv in H6. subst Ka'.
          assert (length Kb' = O) by lia. apply nil_length_inv in H6. subst Kb'. clear H0 H1.
          pose proof (merge_sort_length (Ca ++ Ca')). rewrite H4 in H0. rewrite app_length in H0.
          pose proof (merge_sort_length (Cb ++ Cb')). rewrite H5 in H1. rewrite app_length in H1.
          assert (length Ca' = O) by lia. apply nil_length_inv in H6. subst Ca'.
          assert (length Cb' = O) by lia. apply nil_length_inv in H6. subst Cb'. clear H0 H1.
          rewrite !app_nil_r. f_equal; apply merge_sort_unique; symmetry; apply merge_sort_Permutation.
  Qed.

  #[global] Instance pairSep: sepalg.Sep_alg set_pair.
  Proof.
    exists (fun _ => ∅).
    - intros. repeat red. now simpl.
    - now intros.
  Defined.

  #[global] Instance pairSing: sepalg.Sing_alg set_pair.
  Proof. exists ∅. intros. done. Defined.

  #[global] Program Instance pairGhost: Ghost :=
    { G := set_pair; valid := setPairValid; Join_G := pairJoin }.
  Next Obligation.
    intros. do 2 red in H0. unfold setPairOp in H0.
    destruct (decide (a = ∅)).
    - subst. apply empty_valid.
    - destruct (decide (b = ∅)). 1: now inversion H0. destruct a as [Ka Ca]. destruct b as [Kb Cb]. 
      repeat (match goal with | H: context [match ?E with _ => _ end] |- _ => destruct E end; [|done]).
      red. split; auto.
  Qed.

End keyset_ghost.
