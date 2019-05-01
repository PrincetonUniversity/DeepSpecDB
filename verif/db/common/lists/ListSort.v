(************************************************************************************)
(**                                                                                 *)
(**                             The SQLEngines Library                              *)
(**                                                                                 *)
(**            LRI, CNRS & Université Paris-Sud, Université Paris-Saclay            *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import List Recdef Sorted Arith SetoidList Bool.

Require Import BasicFacts ListFacts OrderedSet ListPermut.

Lemma Sorted_incl :
  forall (A : Type) (o1 o2 : relation A) (l : list A),
    (forall a1 a2, In a1 l -> In a2 l -> o1 a1 a2 -> o2 a1 a2) ->
    Sorted o1 l -> Sorted o2 l.
Proof.
intros A o1 o2 l; induction l as [ | a l]; intros Hl HS.
- constructor 1.
- inversion HS; clear HS; subst.
  constructor 2.
  + apply IHl; [ | assumption].
    do 4 intro; apply Hl; right; assumption.
  + destruct l as [ | a1 l].
    * constructor 1.
    * constructor 2.
      apply Hl; [left | right; left | inversion H2]; trivial.
Qed.

Lemma sorted_list_eq :
  forall (A : Type) (OA : Oset.Rcd A) l1 l2, 
    (forall e : A, Oset.mem_bool OA e l1 = Oset.mem_bool OA e l2) -> 
    Sorted (fun x y : A => Oset.compare OA x y = Lt) l1 ->
    Sorted (fun x y : A => Oset.compare OA x y = Lt) l2 ->
    l1 = l2.
Proof.
intros A OA l1; induction l1 as [ | a1 l1]; intros l2 H H1 H2.
- case_eq l2.
  + exact (fun _ => refl_equal _).
  + intros a2 k2 Hl2.
    assert (Ha2 := H a2).
    rewrite Hl2, 2 Oset.mem_bool_unfold, Oset.compare_eq_refl in Ha2.
    discriminate Ha2.
- case_eq l2.
  + intro Hl2.
    assert (Ha2 := H a1).
    rewrite Hl2, Oset.mem_bool_unfold, Oset.compare_eq_refl in Ha2.
    discriminate Ha2.
  + assert (Heq : Equivalence (fun x y : A => Oset.compare OA x y = Eq)).
    {
      split.
      - intro b1; apply Oset.compare_eq_refl.
      - intros b1 b2 Hb; rewrite Oset.compare_lt_gt, Hb; apply refl_equal.
      - intros b1 b2 b3; apply Oset.compare_eq_trans.
    }
    assert (Hlt : StrictOrder (fun x y : A => Oset.compare OA x y = Lt)).
    {
      split.
      - intros b1.
        unfold complement.
        rewrite Oset.compare_eq_refl; discriminate.
      - intros b1 b2 b3; apply Oset.compare_lt_trans.
    } 
    assert (Heqlt : 
              Proper
                ((fun x y : A => Oset.compare OA x y = Eq) ==>
                   (fun x y : A => Oset.compare OA x y = Eq) ==> iff)
                (fun x y : A => Oset.compare OA x y = Lt)).
    {
      intros b1 b2 Hb c1 c2 Hc; split; intro Hbc.
      - rewrite Oset.compare_lt_gt, CompOpp_iff in Hb.
        apply Oset.compare_eq_lt_trans with b1; [assumption | ].
        apply Oset.compare_lt_eq_trans with c1; assumption.
      - apply Oset.compare_eq_lt_trans with b2; [assumption | ].
        apply Oset.compare_lt_eq_trans with c2; [assumption | ].
        rewrite Oset.compare_lt_gt, Hc; apply refl_equal.
    }
    intros a2 k2 Hl2; subst l2.
    assert (Aux1 :
              let ltA := (fun x y : A => Oset.compare OA x y = Lt) in
              forall (l : list A) (x : A), Sorted ltA l -> 
              (HdRel ltA x l <-> 
               (forall y, InA  (fun x y => Oset.compare OA x y = Eq) y l -> ltA x y))).
    {
      apply InfA_alt; assumption.
    }
    assert (Aux2 := SortA_InfA_InA Heq Hlt Heqlt).
    assert (K : a1 = a2 /\ (forall e : A, Oset.mem_bool OA e l1 = Oset.mem_bool OA e k2)).
    {
      inversion H1; clear H1.
      subst a l.
      inversion H2; clear H2.
      subst a l.
      assert (Ha1 := H a1).
      rewrite Oset.mem_bool_unfold, Oset.compare_eq_refl, Bool.orb_true_l in Ha1.
      generalize (sym_eq Ha1); clear Ha1; intro Ha1.
      rewrite Oset.mem_bool_unfold, Bool.orb_true_iff in Ha1.
      destruct Ha1 as [Ha1 | Ha1].
      - rewrite compare_eq_true in Ha1.
        generalize (Oset.eq_bool_ok OA a1 a2); rewrite Ha1; clear Ha1; intro; subst a2.
        split; [apply refl_equal | ].
        intros e.
        generalize (H e).
        rewrite Oset.mem_bool_unfold.
        case_eq (Oset.compare OA e a1).
        + intros He _.
          generalize (Oset.eq_bool_ok OA e a1); rewrite He; clear He; intro; subst a1.
          apply eq_trans with false; [ | apply sym_eq].
          * case_eq (Oset.mem_bool OA e l1); intro Ke; [ | apply refl_equal].
            rewrite (Aux1 l1 e H4) in H5.
            assert (Abs : Oset.compare OA e e = Lt).
            {
              apply (H5 e).
              rewrite InA_alt.
              exists e; split.
              - apply Oset.compare_eq_refl.
              - rewrite Oset.mem_bool_true_iff in Ke; apply Ke. 
            } 
            rewrite Oset.compare_eq_refl in Abs; discriminate Abs.
          * case_eq (Oset.mem_bool OA e k2); intro Ke; [ | apply refl_equal].
            rewrite (Aux1 k2 e H3) in H6.
            assert (Abs : Oset.compare OA e e = Lt).
            {
              apply (H6 e).
              rewrite InA_alt.
              exists e; split.
              - apply Oset.compare_eq_refl.
              - rewrite Oset.mem_bool_true_iff in Ke; apply Ke. 
            } 
            rewrite Oset.compare_eq_refl in Abs; discriminate Abs.
        + intros He Ke; simpl in Ke.
          rewrite Ke; unfold Oset.eq_bool.
          rewrite He; apply refl_equal.
        + intros He Ke; simpl in Ke.
          rewrite Ke; unfold Oset.eq_bool.
          rewrite He; apply refl_equal.
      - assert (Abs1 : Oset.compare OA a2 a1 = Lt).
        {
          apply (Aux2 k2 a1 a2 H3 H6).
          rewrite InA_alt.
          exists a1; split.
          - apply Oset.compare_eq_refl.
          - rewrite Oset.mem_bool_true_iff in Ha1; apply Ha1. 
        } 
        assert (Abs2 : Oset.compare OA a1 a2 = Lt).
        {
          rewrite (Aux1 _ _ H4) in H5; apply H5.
          rewrite InA_alt.
          exists a2; split.
          - rewrite Oset.compare_eq_refl; apply refl_equal.
          - rewrite <- (Oset.mem_bool_true_iff OA).
            generalize (H a2).
            rewrite Oset.mem_bool_unfold, Abs1, Bool.orb_false_l.
            rewrite (Oset.mem_bool_unfold OA a2 (_ :: _)), Oset.compare_eq_refl.
            exact (fun h => h).
        } 
        rewrite Oset.compare_lt_gt, Abs2 in Abs1.
        discriminate Abs1.
    }
    apply f_equal2; [apply (proj1 K) | ].
    apply IHl1.
    * apply (proj2 K).
    * inversion H1; subst; assumption.
    * inversion H2; subst; assumption.
Qed.

Lemma all_elements_equal :
  forall (A : Type) (OA : Oset.Rcd A) a l, 
    (forall x : A, In x l -> x = a) ->
    Sorted (fun x y : A => Oset.compare OA x y = Lt) l ->
    (l = nil \/ l = a :: nil).
Proof.
intros A OA a l1 H1 H2.
destruct l1 as [ | a1 l1]; [left; apply refl_equal | ].
right.
assert (Ha1 := H1 a1 (or_introl _ (refl_equal _))); subst a1.
apply f_equal.
destruct l1 as [ | a1 l1]; [apply refl_equal | ].
assert (Ha1 := H1 a1 (or_intror _ (or_introl _ (refl_equal _)))); subst a1.
inversion H2; clear H2; subst.
inversion H4; clear H4; subst.
rewrite Oset.compare_eq_refl in H0; discriminate H0.
Qed.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.

Lemma cardinal_subset_list :
  forall l1 l2,
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) l1 ->
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) l2 ->
    (forall e : A, Oeset.mem_bool OA e l1 = true -> Oeset.mem_bool OA e l2 = true) -> 
    length l1 <= length l2.
Proof.
intros l1.
induction l1 as [ | a1 l1]; intros [ | a2 l2] Hs1 Hs2 H.
- apply le_n.
- apply le_O_n.
- assert (Ha1 := H a1).
  rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl, Bool.orb_true_l in Ha1.
  generalize (Ha1 (refl_equal _)); clear Ha1; intro Ha1.
  discriminate Ha1.
- assert (Ha1 := H a1).
  rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl, Bool.orb_true_l in Ha1.
  generalize (Ha1 (refl_equal _)); clear Ha1; intro Ha1.
  rewrite Oeset.mem_bool_unfold, Bool.orb_true_iff in Ha1.
  destruct Ha1 as [Ha1 | Ha1].
  + rewrite compare_eq_true in Ha1.
    simpl; apply le_n_S.
    apply IHl1.
    * inversion Hs1; subst; assumption.
    * inversion Hs2; subst; assumption.
    * intros e He.
      generalize (H e).
      rewrite Oeset.mem_bool_unfold, He, Bool.orb_true_r.
      intro Ke; generalize (Ke (refl_equal _)); clear Ke; intro Ke.
      rewrite Oeset.mem_bool_unfold, Bool.orb_true_iff in Ke.
      destruct Ke as [Ke | Ke]; [ | assumption].
      rewrite compare_eq_true in Ke.
      assert (Abs : Oeset.mem_bool OA a1 l1 = true).
      {
        rewrite (Oeset.mem_bool_eq_1 OA a1 a2).
        - rewrite (Oeset.mem_bool_eq_1 OA a2 e).
          + assumption.
          + rewrite Oeset.compare_lt_gt, Ke; apply refl_equal.
        - assumption.
      } 
      apply False_rec; clear a2 l2 e He Ke Ha1 H Hs2 IHl1.
      induction l1 as [ | a l1]; [discriminate Abs | ].
      inversion Hs1; clear Hs1; subst.
      {
        rewrite Oeset.mem_bool_unfold, Bool.orb_true_iff in Abs; 
        destruct Abs as [Abs | Abs].
        - rewrite compare_eq_true in Abs.
          inversion H2; clear H2; subst.
          rewrite Abs in H0; discriminate H0.
        - apply IHl1; [ | assumption].
          inversion H1; clear H1; subst.
          constructor 2; [assumption | ].
          destruct l1 as [ | b l1].
          + constructor 1.
          + constructor 2.
            apply Oeset.compare_lt_trans with a.
            * inversion H2; intros; subst; assumption.
            * inversion H4; intros; subst; assumption.
      } 
  + simpl; apply le_n_S.
    apply IHl1.
    * inversion Hs1; intros; subst; assumption.
    * inversion Hs2; intros; subst; assumption.
    * intros e He.
      assert (Ke := H e); rewrite Oeset.mem_bool_unfold, He, Bool.orb_true_r in Ke.
      generalize (Ke (refl_equal _)); clear Ke; intro Ke.
      rewrite Oeset.mem_bool_unfold, Bool.orb_true_iff in Ke.
      destruct Ke as [Ke | Ke]; [ | assumption].
      rewrite compare_eq_true in Ke.
      assert (K : let ltA := (fun x y : A => Oeset.compare OA x y = Lt) in
                  forall (l : list A) (x a : A),
                    Sorted ltA l ->
                    HdRel ltA a l ->
                    InA (fun a1 a2 : A => Oeset.compare OA a1 a2 = Eq) x l ->
                    ltA a x).
      {
        intro; subst ltA; apply SortA_InfA_InA.
        - split.
          + intro b1; apply Oeset.compare_eq_refl.
          + intros b1 b2 Hb; rewrite Oeset.compare_lt_gt, Hb.
            apply refl_equal.
          + intros b1 b2 b3; apply Oeset.compare_eq_trans.
        - split. 
          + intro b1.
            unfold complement.
            rewrite Oeset.compare_eq_refl; discriminate.
          + intros b1 b2 b3; apply Oeset.compare_lt_trans.
        - intros b1 b2 Hb c1 c2 Hc.
          split; intro Hbc.
          + rewrite Oeset.compare_lt_gt, CompOpp_iff in Hb.
            apply Oeset.compare_eq_lt_trans with b1; [assumption | ].
            apply Oeset.compare_lt_eq_trans with c1; assumption.
          + apply Oeset.compare_eq_lt_trans with b2; [assumption | ].
            apply Oeset.compare_lt_eq_trans with c2; [assumption | ].
            rewrite Oeset.compare_lt_gt, Hc; apply refl_equal.
      }
      inversion Hs1; clear Hs1.
      subst a l.
      inversion Hs2; clear Hs2.
      subst a l.
      assert (Kl1 : Oeset.compare OA a2 a1 = Lt).
      {
        apply (K l2 a1 a2 H4 H5).
        rewrite InA_alt.
        rewrite Oeset.mem_bool_true_iff in Ha1.
        apply Ha1.
      }
      assert (Kl2 : Oeset.compare OA a1 a2 = Lt).
      {
        apply (K l1 a2 a1 H2 H3).
        rewrite InA_alt.
        rewrite Oeset.mem_bool_true_iff in He.
        destruct He as [e' [He He']].
        exists e'; split; [ | assumption].
        apply Oeset.compare_eq_trans with e; [ | assumption].
        rewrite Oeset.compare_lt_gt, Ke; apply refl_equal.
      }
      rewrite Oeset.compare_lt_gt, Kl1 in Kl2.
      discriminate Kl2.
Qed.

Fixpoint fold_inter_ (acc : list A) (l1 l2 : list A) :=
  match l2 with
    | nil => acc
    | a2 :: l2 =>
      if Oeset.mem_bool OA a2 l1
      then fold_inter_ (acc ++ a2 :: nil) l1 l2
      else fold_inter_ acc l1 l2
  end.

Lemma fold_inter_is_sorted_ :
  forall acc l1 l2,
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) l1 -> 
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) (acc ++ l2) ->
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) (fold_inter_ acc l1 l2).
Proof.
intros acc l1 l2; revert acc l1; 
induction l2 as [ | a2 l2]; intros acc l1; simpl.
- intros _; rewrite <- app_nil_end; exact (fun h => h).
- intros Sl1 H; case (Oeset.mem_bool OA a2 l1); apply IHl2.
  + assumption.
  + rewrite <- ass_app; apply H.
  + assumption.
  + revert H; clear; revert a2 l2; induction acc as [ | a1 acc]; intros a2 l2 H.
    * simpl in H; simpl; inversion H; assumption.
    * {
        simpl; constructor.
        - simpl in H.
          apply IHacc with a2.
          inversion H; assumption.
        - simpl in H; inversion H; subst.
          destruct acc as [ | a acc]; simpl in H, H2, H3; simpl.
          + destruct l2 as [ | a3 l2]; simpl in H, H2, H3; simpl.
            * constructor 1.
            * constructor 2.
              {
                apply Oeset.compare_lt_trans with a2.
                - inversion H3; assumption.
                - inversion H2; inversion H5; assumption.
              }
          + constructor 2; inversion H3; assumption.
      }
Qed.

Lemma length_fold_inter_ : 
   forall acc l1 l2, length (fold_inter_ acc l1 l2) = (length acc + length (fold_inter_ nil l1 l2))%nat.
Proof.
fix h 3.
intros acc l1 l2; case l2; clear l2; simpl.
rewrite <- plus_n_O; reflexivity.
intros a2 l2; case (Oeset.mem_bool OA a2 l1).
rewrite (h (acc ++ a2 :: nil) l1 l2).
rewrite (h (a2 :: nil) l1 l2); simpl.
rewrite app_length; simpl.
rewrite <- plus_assoc; simpl; apply refl_equal.
apply h.
Qed.

Lemma fold_inter_is_inter_list :
  forall e l1 l2 acc, 
    (Oeset.mem_bool OA e l1 && Oeset.mem_bool OA e l2) || Oeset.mem_bool OA e acc =
    Oeset.mem_bool OA e (fold_inter_ acc l1 l2).
Proof.
intros e l1 l2; revert e l1.
induction l2 as [ | a2 l2]; intros e l1 acc; simpl.
- rewrite Bool.andb_false_r; apply refl_equal.
- case_eq (Oeset.mem_bool OA a2 l1); intro Ha2.
  + rewrite <- IHl2, Oeset.mem_bool_app; simpl.
    rewrite Bool.orb_false_r.
    case_eq (Oeset.mem_bool OA e l1); intro He.
    * {
        unfold Oeset.eq_bool; case_eq (Oeset.compare OA e a2); intro Ke.
        - rewrite 2 Bool.orb_true_r; apply refl_equal.
        - rewrite Bool.orb_false_r; apply refl_equal.
        - rewrite Bool.orb_false_r; apply refl_equal.
      } 
    * {
        unfold Oeset.eq_bool; case_eq (Oeset.compare OA e a2); intro Ke.
        - rewrite (Oeset.mem_bool_eq_1 _ _ _ _ Ke) in He.
          rewrite He in Ha2; discriminate Ha2.
        - simpl; rewrite Bool.orb_false_r; apply refl_equal.
        - simpl; rewrite Bool.orb_false_r; apply refl_equal.
      }
  + rewrite <- IHl2.
    unfold Oeset.eq_bool; case_eq (Oeset.compare OA e a2); intro Ke.
    * rewrite <- (Oeset.mem_bool_eq_1 _ _ _ _ Ke) in Ha2.
      rewrite Ha2; apply refl_equal.
    * simpl; apply refl_equal.
    * simpl; apply refl_equal.
Qed.

Fixpoint insert_ a (l : list A) :=
  match l with
    | nil => a :: nil
    | a1 :: l1 =>
      match Oeset.compare OA a a1 with
          | Lt | Eq => a :: l
          | Gt => a1 :: (insert_ a l1)
      end
  end.

Lemma mem_insert_ :
  forall x a l, Oeset.mem_bool OA x (insert_ a l) = 
                (match Oeset.compare OA x a with Eq => true | _ => false end) 
                  || Oeset.mem_bool OA x l.
Proof.
intros x a l; induction l as [ | a1 l]; simpl.
- apply refl_equal.
- case_eq (Oeset.compare OA a a1); intro Ha; simpl.
  + apply refl_equal.
  + apply refl_equal.
  + rewrite IHl.
    unfold Oeset.eq_bool; case_eq (Oeset.compare OA x a1); intro Hx; simpl.
    * rewrite Bool.orb_true_r; apply refl_equal.
    * apply refl_equal.
    * apply refl_equal.
Qed.

Lemma length_insert_ : 
  forall a l, length (insert_ a l) = S (length l).
Proof.
intros a l; induction l as [ | a1 l]; simpl.
- apply refl_equal.
- case (Oeset.compare OA a a1); simpl.
  + apply refl_equal.
  + apply refl_equal.
  + rewrite IHl; apply refl_equal.
Qed.

Fixpoint fold_union_ (l1 l2 : list A) :=
  match l2 with
    | nil => l1
    | a2 :: l2 => 
      if Oeset.mem_bool OA a2 l1 
      then fold_union_ l1 l2
      else fold_union_ (insert_ a2 l1) l2
  end.

Lemma fold_union_is_sorted_ :
  forall l1 l2,
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) l1 -> 
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) l2 ->
    Sorted (fun x y : A => Oeset.compare OA x y = Lt) (fold_union_ l1 l2).
Proof.
intros l1 l2; revert l1; induction l2 as [ | a2 l2]; intros l1 Sl1 Sl2; simpl.
- assumption.
- case_eq (Oeset.mem_bool OA a2 l1); intro Ha2.
  + apply (IHl2 _ Sl1).
    inversion Sl2; assumption.
  + apply IHl2.
    clear l2 IHl2 Sl2.
    induction l1 as [ | a1 l1]; simpl.
    * constructor 2; constructor 1.
    * simpl in Ha2; rewrite Bool.orb_false_iff in Ha2; destruct Ha2 as [Ha2 Ka2].
      {
        revert Ha2; unfold Oeset.eq_bool; case_eq (Oeset.compare OA a2 a1).
        - intros _ Abs; discriminate Abs.
        - intros Ha2 _; constructor 2.
          + assumption.
          + constructor 2; assumption.
        - intros Ha2 _; constructor 2.
          + apply IHl1.
            * inversion Sl1; assumption.
            * assumption.
          + destruct l1 as [ | a l1]; simpl.
            * constructor 2; rewrite Oeset.compare_lt_gt, Ha2; apply refl_equal.
            * {
                case_eq (Oeset.compare OA a2 a); intro Ha.
                - constructor 2; rewrite Oeset.compare_lt_gt, Ha2; apply refl_equal.
                - constructor 2; rewrite Oeset.compare_lt_gt, Ha2; apply refl_equal.
                - constructor 2.
                  inversion Sl1; subst.
                  inversion H2; assumption.
              }
      }
    * inversion Sl2; assumption.
Qed.

Lemma fold_union_is_union_list :
 forall e l1 l2, 
   Oeset.mem_bool OA e l1 || Oeset.mem_bool OA e l2 = Oeset.mem_bool OA e (fold_union_ l1 l2).
Proof.
intros e l1 l2; revert e l1.
induction l2 as [ | a2 l2]; intros e l1; simpl.
- rewrite Bool.orb_false_r; apply refl_equal.
- case_eq (Oeset.mem_bool OA a2 l1); intro Ha2; rewrite <- IHl2.
  + case_eq (Oeset.mem_bool OA e l1); simpl.
    * exact (fun _ => refl_equal _).
    * {
        unfold Oeset.eq_bool; intro He; case_eq (Oeset.compare OA e a2); intro Ke.
        - rewrite (Oeset.mem_bool_eq_1 _ _ _ _ Ke) in He.
          rewrite He in Ha2; discriminate Ha2.
        - apply refl_equal.
        - apply refl_equal.
      }
  + rewrite mem_insert_.
    case (Oeset.mem_bool OA e l1); simpl.
    * rewrite Bool.orb_true_r; apply refl_equal.
    * unfold Oeset.eq_bool; case (Oeset.compare OA e a2); apply refl_equal.
Qed.


(** *** Definition of a sorted list. *)
Inductive is_sorted : list A -> Prop :=
  | is_sorted_nil : is_sorted nil
  | is_sorted_cons1 : forall t, is_sorted (t :: nil)
  | is_sorted_cons2 :
      forall t1 t2 l, Oeset.compare OA t1 t2 <> Gt -> is_sorted (t2 :: l) -> is_sorted (t1 :: t2 :: l).

Lemma is_sorted_Sorted :
  forall l, is_sorted l <-> Sorted (fun x y => Oeset.compare OA x y <> Gt) l.
Proof.
intro l; induction l as [ | a1 l].
- split; intro; constructor 1.
- split; intro H; inversion H; clear H; subst.
  + constructor 2; constructor 1.
  + constructor 2.
    * rewrite <- IHl; assumption.
    * constructor 2; assumption.
  + case_eq l.
    * intro; constructor 2.
    * intros a2 k H; subst l.
      inversion H3; clear H3; subst.
      constructor 3; [assumption | ].
      rewrite IHl; assumption.
Qed.

(** *** Decomposition of the list wrt a pivot. *)
Function partition (pivot : A) (l : list A) {struct l} : (list A) * (list A) :=
  match l with 
  | nil => (nil, nil)
  | a :: l' => 
	match partition pivot l' with (l1,l2) =>
	 match Oeset.compare OA a pivot with
         | Lt => (a :: l1, l2) 
         | _ => (l1, a :: l2)
         end
        end
end.

Function quicksort (l : list A) { measure (@length A) l} : list A :=
   match l with
	| nil => nil
	| h :: tl => 
             match partition h tl with (l1, l2) =>
             quicksort l1 ++ h :: quicksort l2
        end
    end. 
Proof. 
- (* 1 Second recursive call *)
  intros _l a l H; subst _l.
  induction l as [ | a1 l]; intros l1 l2 H; simpl in H.
  + injection H; clear H; intros; subst.
    apply le_n.
  + case_eq (partition a l); intros k1 k2 K; rewrite K in H.
    case_eq (Oeset.compare OA a1 a); 
      intro Ha; rewrite Ha in H; injection H; clear H; intros; subst.
    * simpl; apply le_n_S; apply (IHl _ _ K).
    * simpl; apply le_S; apply (IHl _ _ K).
    * simpl; apply le_n_S; apply (IHl _ _ K).
- intros _l a l H; subst _l.
  induction l as [ | a1 l]; intros l1 l2 H; simpl in H.
  + injection H; clear H; intros; subst.
    apply le_n.
  + case_eq (partition a l); intros k1 k2 K; rewrite K in H.
    case_eq (Oeset.compare OA a1 a); 
      intro Ha; rewrite Ha in H; injection H; clear H; intros; subst.
    * simpl; apply le_S; apply (IHl _ _ K).
    * simpl; apply le_n_S; apply (IHl _ _ K).
    * simpl; apply le_S; apply (IHl _ _ K).
Defined.

(** *** The result of quicksort is a permutation of the original list. *)

Notation permut := (_permut (fun x y => Oeset.compare OA x y = Eq)).

Lemma partition_list_permut1 :
 forall e l, let (l1,l2) := partition e l in permut (l1 ++ l2) l.
Proof.
intros e l; functional induction (partition e l)
   as [ | H1 e' l' H2 IH l1 l2 rec_res e'_lt_e _ | H1 e' l' H2 IH l1 l2 rec_res H3].
- apply Pnil.
- simpl app; rewrite rec_res in IH; apply (@Pcons _ _ _ e' e' (l1 ++ l2) nil l').
  + apply Oeset.compare_eq_refl.
  + assumption.
- simpl app; rewrite rec_res in IH.
  apply _permut_sym.
  + intros a b _ _ H; rewrite Oeset.compare_lt_gt; rewrite H; apply refl_equal.
  + apply (@Pcons _ _ _ e' e' l' l1 l2).
    * apply Oeset.compare_eq_refl.
    * apply _permut_sym; [ | assumption].
      intros a b _ _ H; rewrite Oeset.compare_lt_gt; rewrite H; apply refl_equal.
Qed.

Theorem quick_permut : forall l, permut l (quicksort l).
Proof.
intros l; functional induction (quicksort l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2]; auto.
- apply Pnil.
- apply Pcons.
  + apply Oeset.compare_eq_refl.
  + assert (P := partition_list_permut1 a' l'); rewrite H in P.
    apply _permut_trans with (l1 ++ l2).
    * do 6 intro; apply Oeset.compare_eq_trans.
    * apply _permut_sym; [ | assumption].
      intros a b _ _ K; rewrite Oeset.compare_lt_gt; rewrite K; apply refl_equal.
    * apply _permut_app; assumption.
Qed.

Theorem quick_permut_bis :
 forall l1 l2, permut l1 l2 -> permut (quicksort l1) l2.
Proof.
intros l1 l2 P; apply _permut_trans with l1.
- do 6 intro; apply Oeset.compare_eq_trans.
- apply _permut_sym.
  + intros a b _ _ H; rewrite Oeset.compare_lt_gt; rewrite H; apply refl_equal. 
  + apply quick_permut.
- assumption.
Qed.

(** *** The result of quicksort is a sorted list. *)
Lemma sorted_tl_sorted :
  forall e l, is_sorted (e :: l) -> is_sorted l.
Proof.
intros e l S; inversion S; subst.
apply is_sorted_nil.
assumption.
Qed.

Lemma quick_sorted_aux1 :
  forall l1 l2 e, is_sorted l1 -> is_sorted l2 ->
  (forall a, In a l1 -> Oeset.compare OA a e <> Gt) ->  
  (forall a, In a l2 -> Oeset.compare OA e a <> Gt) -> 
  is_sorted (l1 ++ e :: l2).
Proof.
induction l1 as [ | e1 l1 ]; intros l2 e S1 S2 L1 L2.
simpl; destruct l2 as [ | e2 l2]; intros; 
[apply is_sorted_cons1 | apply is_sorted_cons2 ]; trivial;
apply (L2 e2); simpl; left; apply refl_equal.
destruct l1 as [ | e1' l1] ; simpl; intros; apply is_sorted_cons2.
apply L1; left; apply refl_equal.
simpl in IHl1; apply IHl1; trivial.
apply is_sorted_nil.
contradiction.
inversion S1; trivial.
rewrite app_comm_cons; apply IHl1; trivial.
inversion S1; trivial.
intros; apply L1; trivial; right; trivial.
Qed.

Lemma quick_sorted_aux3 :
  forall l e, let (l1,_) := partition e l in forall a, In a l1 -> Oeset.compare OA a e <> Gt.
Proof.
intros l e; 
functional induction (partition e l) 
    as [ | l a' l' l_eq_a'_l' IH l1' l2' H a'_lt_e _ | l a' l' l_eq_a'_l' IH l1' l2' H _H _ ].
contradiction.
intros a [a_eq_a' | a_in_l1']; [idtac | rewrite H in IH; apply IH; trivial].
subst a'; rewrite a'_lt_e; discriminate.
intros; rewrite H in IH; apply IH; trivial.
Qed.

Lemma quick_sorted_aux4 :
  forall l e, let (_,l2) := partition e l in forall a, In a l2 -> Oeset.compare OA e a <> Gt.
Proof.
fix h 1.
intro l; case l; clear l.
intros e a H; contradiction H.
intros a1 l e; simpl.
case_eq (partition e l); intros l1 l2 Hl.
case_eq (Oeset.compare OA a1 e); intro He.
simpl; intros a [Ha | Ha]; [subst a1; rewrite Oeset.compare_lt_gt, He; discriminate | ].
assert (IH := h l e); rewrite Hl in IH; apply (IH a Ha).
assert (IH := h l e); rewrite Hl in IH; apply IH.
simpl; intros a [Ha | Ha]; [subst a1; rewrite Oeset.compare_lt_gt, He; discriminate | ].
assert (IH := h l e); rewrite Hl in IH; apply (IH a Ha).
Qed.

Theorem quick_sorted : forall l, is_sorted (quicksort l).
Proof.
intros l; 
functional induction (quicksort l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2].
- apply is_sorted_nil.
- apply quick_sorted_aux1; trivial.
  + intros a a_in_ql1.
    assert (H1 := quick_sorted_aux3 l' a'); rewrite H in H1.
    assert (K : Oeset.mem_bool OA a l1 = true).
    {
      rewrite (mem_permut_mem OA a (quick_permut l1)).
      rewrite Oeset.mem_bool_true_iff.
      exists a; split; [apply Oeset.compare_eq_refl | assumption].
    } 
    rewrite Oeset.mem_bool_true_iff in K.
    destruct K as [_a [K1 K2]].
    assert (Ha := H1 _ K2).
    intro Ka; apply Ha.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in Ka.
    rewrite Oeset.compare_lt_gt, (Oeset.compare_lt_eq_trans _ _ _ _ Ka K1).
    apply refl_equal.
  + intros a a_in_ql2.
    assert (H1 := quick_sorted_aux4 l' a'); rewrite H in H1.
    assert (K : Oeset.mem_bool OA a l2 = true).
    {
      rewrite (mem_permut_mem OA a (quick_permut l2)).
      rewrite Oeset.mem_bool_true_iff.
      exists a; split; [apply Oeset.compare_eq_refl | assumption].
    } 
    rewrite Oeset.mem_bool_true_iff in K.
    destruct K as [_a [K1 K2]].
    assert (Ha := H1 _ K2).
    intro Ka; apply Ha.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in K1, Ka.
    rewrite Oeset.compare_lt_gt, (Oeset.compare_eq_lt_trans _ _ _ _ K1 Ka).
    apply refl_equal.
Qed.

(** ***  There is a unique sorted list equivalent up to a permutation to a given list.*)
Lemma sorted_cons_min : 
 forall l e, is_sorted (e :: l) -> (forall e', In e' (e :: l) -> Oeset.compare OA e e' <> Gt).
Proof.
simpl; intros l e S e' [e'_eq_e | e'_in_l].
- subst e'; rewrite Oeset.compare_eq_refl; discriminate.
- revert e S e' e'_in_l; induction l as [ | a l ].
  + intros e _ e' e'_in_nil; elim e'_in_nil.
  + simpl; intros e S e' [e'_eq_a | e'_in_l].
    * subst; inversion S; assumption.
    * inversion S; subst.
      assert (IH := IHl _ H3 _ e'_in_l).
      {
        case_eq (Oeset.compare OA e a); intro Hea.
        - apply IHl; [ | assumption].
          inversion H3; subst.
          + contradiction e'_in_l.
          + constructor 3; [ | assumption].
            intro H; rewrite Oeset.compare_lt_gt, CompOpp_iff in H.
            apply H2.
            rewrite Oeset.compare_lt_gt.
            rewrite (Oeset.compare_lt_eq_trans _ _ _ _ H Hea).
            apply refl_equal.
        - intro H; rewrite Oeset.compare_lt_gt, CompOpp_iff in H.
          apply IH.
          rewrite Oeset.compare_lt_gt.
          rewrite (Oeset.compare_lt_trans _ _ _ _ H Hea).
          apply refl_equal.
        - intro H.
          apply H1; assumption.
      }
Qed.

Theorem sort_is_unique :
  forall l1 l2, 
    is_sorted l1 -> is_sorted l2 -> permut l1 l2 -> 
    Oeset.compare (mk_oelists OA) l1 l2 = Eq.
Proof.
intros l1; induction l1 as [ | e1 l1 ]; intros l2 S1 S2 P.
- inversion P; trivial.
- inversion P as [ | a b l k1 k2 a_eq_b P' H1 H']; 
  destruct k1 as [ | a1 k1]; subst.
  + simpl; rewrite a_eq_b.
    assert (IH := IHl1 k2); simpl in IH; apply IH.
    * apply sorted_tl_sorted with e1; assumption.
    * apply sorted_tl_sorted with b; assumption.
    * refine (_permut_cons_inside _ _ _ _ _ P); [ | assumption].
      intros a1 b1 a2 b2 _ _ _ _ H1 H2 H3.
      apply Oeset.compare_eq_trans with b1; [assumption | ].
      apply Oeset.compare_eq_trans with a2; [ | assumption].
      rewrite Oeset.compare_lt_gt, H2; apply refl_equal.
  + assert (e1_eq_a1 : Oeset.compare OA e1 a1 = Eq).
    {
      assert (Ha1 : Oeset.mem_bool OA a1 (e1 :: l1) = true).
      {
        rewrite (mem_permut_mem OA _ P).
        simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
      } 
      rewrite Oeset.mem_bool_true_iff in Ha1.
      destruct Ha1 as [a1' [Ha1 Ha1']].
      assert (Ka1 := sorted_cons_min S1 Ha1').
      assert (He1 : Oeset.mem_bool OA e1 ((a1 :: k1) ++ b :: k2) = true).
      {
        rewrite <- (mem_permut_mem OA _ P).
        simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
      }
      rewrite Oeset.mem_bool_true_iff in He1.
      destruct He1 as [e1' [He1 He1']].
      assert (Ke1 := sorted_cons_min S2 He1').
      {
        case_eq (Oeset.compare OA e1 a1'); intro H1; rewrite H1 in Ka1.
        - rewrite Oeset.compare_lt_gt, CompOpp_iff in Ha1.
          rewrite (Oeset.compare_eq_trans _ _ _ _ H1 Ha1).
          apply refl_equal.
        - rewrite Oeset.compare_lt_gt in Ke1.
          rewrite Oeset.compare_lt_gt, CompOpp_iff in Ha1, He1.
          rewrite (Oeset.compare_eq_lt_trans 
                     _ _ _ _ He1 
                     (Oeset.compare_lt_eq_trans _ _ _ _ H1 Ha1)) in Ke1.
          apply False_rec; apply Ke1; apply refl_equal.
        - apply False_rec; apply Ka1; apply refl_equal.
      }
    }
    assert (IH := IHl1 (k1 ++ b :: k2)); simpl in IH.
    simpl; rewrite e1_eq_a1, IH.
    * apply refl_equal.
    * apply sorted_tl_sorted with e1; assumption.
    * apply sorted_tl_sorted with a1; assumption.
    * simpl in P.
      apply (@_permut_cons_inside _ _ _ e1 a1 l1 nil (k1 ++ b :: k2)); 
        [ | assumption | assumption].
      intros _a1 b1 a2 b2 _ _ _ _ H1 H2 H3.
      apply Oeset.compare_eq_trans with b1; [assumption | ].
      apply Oeset.compare_eq_trans with a2; [ | assumption].
      rewrite Oeset.compare_lt_gt, H2; apply refl_equal.
Qed.

(** Some usefull properties on the result of quicksort. *)
Lemma length_quicksort : forall l, length (quicksort l) = length l.
Proof.
intro l; apply sym_eq.
apply (_permut_length (R:= fun x y => Oeset.compare OA x y = Eq)).
apply quick_permut.
Qed.

Lemma mem_quick_mem : forall a l, Oeset.mem_bool OA a l = Oeset.mem_bool OA a (quicksort l).
Proof.
intros; apply mem_permut_mem.
apply quick_permut.
Qed.

Lemma mem_quicksort_cons : forall a l, Oeset.mem_bool OA a (quicksort (a :: l)) = true.
Proof.
intros a l; rewrite <- mem_quick_mem; simpl.
unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
Qed.

(** What happens when a sorted list is removed from another one.*)
Function remove_list (eq_bool : A -> A -> bool) (la l : list A) {struct l} : option (list A) :=
  match la with
  | nil => Some l
  | a :: la' => 
	match l with 
	| nil => None
	| b :: l' => 
	   if eq_bool a b
	   then remove_list eq_bool la' l'
	   else 
	     match remove_list eq_bool la l' with
	     | None => None
	     | Some rmv => Some (b :: rmv)
	     end
        end
  end.

(*
Lemma in_remove_list :
  forall (eq_bool : A -> A -> bool), (forall a b, if eq_bool a b then a = b else a <> b) ->
  forall l la, is_sorted la -> is_sorted l -> 
  match remove_list eq_bool la l with
  | None => forall rmv, ~ (permut (la ++ rmv) l)
  | Some rmv => permut (la ++ rmv) l
  end.
Proof.
intros eq_bool eq_bool_ok.
fix 1.
intro l; case l; clear l.
(* l = [] *)
intro la; simpl; case la; clear la.
intros _ _; apply Pnil.
intros a la Sla _ rmv P; assert (H := _permut_length P); discriminate.
(* l = _ :: _ *)
intros e l la; simpl; case la; clear la.
intros _ _; apply _permut_refl; intros; apply refl_equal.
intros a la Sala Sel ; assert (Sl := sorted_tl_sorted Sel).
assert (Sla := sorted_tl_sorted Sala).
generalize (eq_bool_ok a e); case (eq_bool a e).
intros a_eq_e; generalize (in_remove_list l la Sla Sl); case (remove_list eq_bool la l).
intros rmv P; simpl; refine (Pcons a e nil l _ _); assumption.
intros H rmv P; apply (H rmv); simpl in P.
apply (_permut_cons_inside (a := a) e nil l).
intros; subst; trivial.
assumption.
assumption.
intros a_diff_e; generalize (in_remove_list l (a :: la) Sala Sl); case (remove_list eq_bool (a :: la) l).
intros rmv P; apply _permut_sym.
intros; apply sym_eq; assumption.
apply Pcons.
apply refl_equal.
apply _permut_sym.
intros; apply sym_eq; assumption.
assumption.
intros H rmv P.
assert (e_in_larm : In e ((a :: la) ++ rmv)).
rewrite (in_permut_in P); left; reflexivity.
simpl in e_in_larm; case e_in_larm; clear e_in_larm.
intro e_eq_a; apply a_diff_e; assumption.
intro e_in_larmv; destruct (in_app_or _ _ _ e_in_larmv) as [e_in_la | e_in_rmv]; clear e_in_larmv.
apply a_diff_e.
assert (H1 : Oset.compare DOS a e <> Gt).
apply (sorted_cons_min Sala (or_intror _ e_in_la)).
assert (H2 : In a (e :: l)).
rewrite <- (in_permut_in P); simpl; left; apply refl_equal.
assert (H3 := sorted_cons_min Sel H2).
rewrite Oset.compare_lt_gt in H3.
revert H1 H3; generalize (Oset.eq_bool_ok DOS a e); case (Oset.compare DOS a e).
exact (fun h _ _ => h).
intros _ _ Abs; apply False_rec; apply Abs; apply refl_equal.
intros _ Abs; apply False_rec; apply Abs; apply refl_equal.
generalize (in_split_set DOS _ _ e_in_rmv).
intros [l1 M]; case M; clear M.
intros l2 M; subst rmv.
apply (H (l1 ++ l2)).
rewrite ass_app; apply (_permut_add_inside (R := @eq A) e e (a :: la ++ l1) l2 nil l).
intros; subst; trivial.
apply refl_equal.
simpl; rewrite <- ass_app; simpl; assumption.
Qed.
*)

End Sec.

Section Strong.

Lemma quick_permut_strong :
  forall (A : Type) (OA : Oeset.Rcd A) l, _permut (@eq A) l (quicksort OA l). 
Proof.
intros A OA l; functional induction (quicksort OA l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2]; auto.
- apply Pnil.
- apply Pcons; [apply refl_equal | ].
  apply _permut_trans with (l1 ++ l2).
  + intros; subst; trivial.
  + clear S1 S2; revert l1 l2 H.
    induction l' as [ | a1 l']; intros l1 l2 H; simpl in H.
    * injection H; clear H; intros; subst l1 l2; apply _permut_refl; intros; trivial.
    * case_eq (partition OA a' l'); intros k1 k2 Hk.
      assert (IH := IHl' _ _ Hk).
      rewrite Hk in H.
      {
        case_eq (Oeset.compare OA a1 a'); intro Ha1; rewrite Ha1 in H.
        - injection H; clear H; intros H1 H2; subst l1 l2.
          apply Pcons; trivial.
        - injection H; clear H; intros H1 H2; subst l1 l2; simpl.
          apply (Pcons (B := A) (R := @eq A) a1 a1 (l := l') nil _ (refl_equal _) IH).
        - injection H; clear H; intros H1 H2; subst l1 l2.
          apply Pcons; trivial.
      }         
  + apply _permut_app; assumption.
Qed.

Lemma In_quicksort :
  forall (A : Type) (OA : Oeset.Rcd A) l a, In a l <-> In a (quicksort OA l).
Proof.
intros A OA l; functional induction (quicksort OA l)
   as [ | l a' l' l_eq_a'_l' l1 l2 H S1 S2]; auto.
- intro; split; exact (fun h => h).
- intros a.
  assert (Ka : In a l' <-> In a (l1 ++ l2)).
  {
    clear S1 S2.
    revert l1 l2 H; induction l' as [ | a1 l']; intros l1 l2 H.
    - simpl in H; injection H; clear H; do 2 intro; subst l1 l2.
      split; exact (fun h => h).
    - simpl in H.
      case_eq (partition OA a' l'); intros k1 k2 Hk; rewrite Hk in H.
      assert (IH := IHl' _ _ Hk).
      simpl; rewrite IH.
      revert H; case (Oeset.compare OA a1 a'); 
      intro H; injection H; clear H; do 2 intro; subst l1 l2.
      + rewrite 2 In_app; simpl; intuition.
      + rewrite 2 In_app; simpl; intuition.
      + rewrite 2 In_app; simpl; intuition.
  }
  simpl; rewrite Ka, 2 In_app; simpl; rewrite <- S1, <- S2.
  intuition.
Qed.

End Strong.

Section Cardinal.

  Hypothesis A B : Type.
  Hypothesis OA : Oeset.Rcd A.
  Hypothesis OB : Oeset.Rcd B.
  Hypothesis f : A -> B.

  Lemma inject_sorted :
    forall l,
      Sorted (fun x y => Oeset.compare OA x y = Lt) l ->
      (forall a1 a2, In a1 l -> In a2 l -> Oeset.compare OB (f a1) (f a2) = Eq -> Oeset.compare OA a1 a2 = Eq) ->
      exists fl, _permut (fun x y => Oeset.compare OB x y = Eq) fl (List.map f l) /\
                 Sorted (fun x y =>  Oeset.compare OB x y = Lt) fl.
  Proof.
    intros l HS Hf.
    exists (quicksort OB (map f l)); split.
    + apply permut_sym; apply quick_permut.
    + assert (H := quick_sorted OB (map f l)).
      rewrite is_sorted_Sorted in H.
      revert H.
      assert (H : forall fl1 fl2 fl3 b1 b2, map f l = fl1 ++ b1 :: fl2 ++ b2 :: fl3 -> Oeset.compare OB b1 b2 <> Eq).
      {
        intro fl1; revert l HS Hf.
        induction fl1 as [ | c1 fl1]; intros l HS Hf fl2 fl3 b1 b2 H.
        - simpl in H.
          destruct l as [ | a1 l]; [discriminate H | ].
          rewrite map_unfold in H; injection H; clear H.
          intro H; intro; subst b1.
          revert a1 l HS Hf fl3 b2 H.
          induction fl2 as [ | c2 fl2]; intros a1 l HS Hf fl3 b2 H.
          + destruct l as [ | a2 l]; [discriminate H | ].
            rewrite map_unfold in H; injection H; clear H.
            intro H; intro; subst b2.
            intro K.
            assert (Kf := Hf a1 a2
                             (or_introl _ (refl_equal _))
                             (or_intror _ (or_introl _ (refl_equal _))) K).
            inversion HS; clear HS; subst.
            inversion H3; clear H3; subst.
            rewrite Kf in H0; discriminate H0.
          + destruct l as [ | a2 l]; [discriminate H | ].
            rewrite map_unfold in H; injection H; clear H.
            intro H; intro; subst c2.
            revert H; apply IHfl2.
            * inversion HS; clear HS; subst.
              inversion H1; clear H1; subst.
              inversion H2; clear H2; subst.
              constructor 2; [assumption | ].
              destruct l as [ | a3 l]; [constructor 1 | ].
              constructor 2.
              inversion H4; clear H4; subst.
              apply Oeset.compare_lt_trans with a2; assumption.
            * intros x y Hx Hy; apply Hf.
              destruct Hx as [Hx | Hx]; [left | right; right]; assumption.
              destruct Hy as [Hy | Hy]; [left | right; right]; assumption.
        - destruct l as [ | a1 l]; [discriminate H | ].
          rewrite map_unfold in H; injection H; clear H.
          intro H; intro; subst c1.
          revert H; apply IHfl1.
          + inversion HS; clear HS; subst; assumption.
          + do 4 intro; apply Hf; right; assumption.
      } 
      set (fl := map f l) in *; clearbody fl.
      clear l HS Hf.
      assert (K : forall (fl1 fl2 fl3 : list B) (b1 b2 : B),
      quicksort OB fl = fl1 ++ b1 :: fl2 ++ b2 :: fl3 -> Oeset.compare OB b1 b2 <> Eq).
      {
        intros fl1 fl2 fl3 b1 b2 K.
        assert (J := quick_permut OB fl).
        rewrite K in J.
        destruct (_permut_inv_right_strong _ _ _ J) as [_b1 [fl' [fl'' [H1 [H2 H3]]]]].
        rewrite ass_app in H3.
        destruct (_permut_inv_right_strong _ _ _ H3) as [_b2 [fl1' [fl1'' [K1 [K2 K3]]]]].
        destruct (split_list _ _ _ _ K2) as [l [[J1 J2] | [J1 J2]]]; subst.
        - intro Hb1b2.
          apply (H fl' l fl1'' _b1 _b2 (refl_equal _)).
          apply Oeset.compare_eq_trans with b1; [assumption | ].
          apply Oeset.compare_eq_trans with b2; [assumption | ].
          rewrite Oeset.compare_lt_gt, K1; apply refl_equal.
        - intro Hb1b2.
          destruct l as [ | __b2 l].
          + simpl in J2; subst fl''.
            rewrite <- app_nil_end in H.
            apply (H fl1' nil fl1'' _b1 _b2 (refl_equal _)).
            apply Oeset.compare_eq_trans with b1; [assumption | ].
            apply Oeset.compare_eq_trans with b2; [assumption | ].
            rewrite Oeset.compare_lt_gt, K1; apply refl_equal.
          + simpl in J2; injection J2; clear J2.
            intro J2; intro; subst fl1'' __b2.
            rewrite <- ass_app in H.
            apply (H fl1' l fl'' _b2 _b1 (refl_equal _)).
            rewrite Oeset.compare_lt_gt, CompOpp_iff.
            apply Oeset.compare_eq_trans with b1; [assumption | ].
            apply Oeset.compare_eq_trans with b2; [assumption | ].
            rewrite Oeset.compare_lt_gt, K1; apply refl_equal.
      } 
      set (qfl := quicksort OB fl) in *; clearbody qfl.
      clear fl H.
      induction qfl as [ | b1 l].
      * intros _; constructor 1.
      * intro HS; inversion HS; clear HS; subst.
        {
          constructor 2.
          - apply IHl.
            + intros fl1 fl2 fl3 c1 c2 H; apply (K (b1 :: fl1) fl2 fl3 c1 c2 (f_equal _ H)).
            + assumption.
          - destruct l as [ | b2 l].
            + constructor 1.
            + constructor 2.
              inversion H2; clear H2; subst.
              assert (Kb1b2 := K nil nil l b1 b2 (refl_equal _)).
              destruct (Oeset.compare OB b1 b2).
              * apply False_rec; apply Kb1b2; apply refl_equal.
              * apply refl_equal.
              * apply False_rec; apply H0; apply refl_equal.
        }
  Qed.
  
End Cardinal.
  
Require Import NArith.

Section NbOcc.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.

Lemma nb_occ_quicksort : forall x l, Oeset.nb_occ OA x (quicksort OA l) = Oeset.nb_occ OA x l.
Proof.
intros x l1; apply sym_eq; apply permut_nb_occ; apply quick_permut.
Qed.

Lemma nb_occ_sorted :
  forall l x a, Oeset.compare OA x a = Lt -> is_sorted OA (a :: l) -> Oeset.nb_occ OA x l = 0%N.
Proof.
intro l; induction l as [ | a1 l]; intros x a Hx Hl; [apply refl_equal | ].
rewrite Oeset.nb_occ_unfold.
inversion Hl; clear Hl; subst.
case_eq (Oeset.compare OA a a1); intro Ha.
- rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Hx Ha), (IHl x a); trivial.
  inversion H3; clear H3; subst.
  + constructor 2.
  + constructor 3; [ | trivial].
    intro H; apply H2.
    apply (Oeset.compare_eq_gt_trans _ _ a); [ | assumption].
    apply Oeset.compare_eq_sym; apply Ha.
- rewrite (Oeset.compare_lt_trans _ _ _ _ Hx Ha), (IHl x a); trivial.
  inversion H3; clear H3; subst.
  + constructor 2.
  + constructor 3; [ | trivial].
    intro H; apply H2.
    apply (Oeset.compare_gt_trans _ _ a); [ | assumption].
    rewrite Oeset.compare_lt_gt, Ha; apply refl_equal.
- rewrite Ha in H1; apply False_rec; apply H1; apply refl_equal.
Qed.

Lemma nb_occ_sorted_lt :
  forall x l a, Oeset.compare OA x a = Lt -> 
                Sorted (fun x y =>  Oeset.compare OA x y = Lt) (a :: l) ->
                Oeset.nb_occ OA x (a :: l) = 0%N.
Proof.
intros x l;  induction l as [ | a1 l]; intros a Ha Hl.
- simpl; rewrite Ha; apply refl_equal.
- rewrite Oeset.nb_occ_unfold, Ha, IHl.
  + apply refl_equal.
  + inversion Hl; subst.
    refine (Oeset.compare_lt_trans _ _ _ _ Ha _).
    inversion H2; subst; trivial.
  + inversion Hl; subst; trivial.
Qed.

End NbOcc.
