(** * kvfun.v : Functional model KV Table *)
Require Import VST.floyd.functional_base.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import common.

Module Type KV_TABLE.
  Parameter table: Type -> Type.
  Parameter key: Type.
  Section Types.
    Context {elt: Type}.
    Parameter empty: table elt.
    Parameter get: key -> table elt -> option elt.
    Parameter put: key -> elt -> table elt -> table elt.
    Axiom get_empty: forall k,
        get k empty = None.
    Axiom get_put_same: forall k v s,
        get k (put k v s) = Some v.
    Axiom get_put_diff: forall k1 k2 v s,
        k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
  End Types.
End KV_TABLE.

Module SortedListTable (KeyType: UsualOrderedType) <: KV_TABLE.
  Import ListNotations.
  Module Facts := OrderedTypeFacts KeyType.
  Definition key: Type := KeyType.t.
  Definition table (elt: Type): Type := list (key * elt).
  Section Types.
    Context {elt: Type}.
    Definition empty: table elt := [].
    Fixpoint get (k: key) (t: table elt) :=
      match t with
      | (k', v') :: l' =>
        if Facts.eq_dec k k' then
          Some v'
        else get k l'
      | nil => None
      end.

    Fixpoint put (k: key) (v: elt) (t: table elt) :=
    match t with
    | (k', v') :: l' =>
      if Facts.lt_dec k k' then
          (k, v) :: (k', v') :: l'
      else
        if Facts.eq_dec k k' then
          (k, v) :: l'
        else
        (k', v') :: (put k v l')
    | nil => (k, v) :: nil
    end.

    Theorem get_empty: forall k, get k empty = None.
    Proof.
      intros.
      reflexivity.
    Qed.

    Theorem get_put_same: forall k v s,
        get k (put k v s) = Some v.
    Proof.
      induction s as [ | [k' v'] ?].
      - simpl.
        rewrite if_true by auto.
        reflexivity.
      - simpl.
        if_tac; simpl; if_tac; simpl.
        + reflexivity.
        + pose proof (KeyType.eq_refl k).
          exfalso. auto.
        + rewrite if_true by auto.
          reflexivity.
        + rewrite if_false by auto.
          assumption.
    Qed.

    Theorem get_put_diff: forall k1 k2 v s,
        k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
    Proof.
      induction s as [ | [k' v'] ?]; intros.
      - simpl.
        rewrite if_false by auto.
        reflexivity.
      - simpl.
        if_tac; simpl; if_tac; simpl; subst.
        + contradiction.
        + reflexivity.
        + rewrite ?if_false by auto.
          reflexivity.
        + specialize (IHs H).
          rewrite IHs.
          reflexivity.
    Qed.

    Import KeyType.
    Notation "x < y" := (lt x y).

    (* sorted invariant *)
    Inductive sorted: table elt -> Prop :=
    | sorted_nil: sorted nil
    | sorted_cons: forall k v l,
        Forall (fun binding => lt k (fst binding)) l -> 
        sorted l ->
        sorted ((k, v) :: l).

    Lemma put_sorted_aux (k k': key) (v: elt) (s: table elt):
      k < k' ->
      Forall (fun binding => lt k (fst binding)) s ->
      Forall (fun binding => lt k (fst binding)) (put k' v s).
    Proof.
      induction s as [ | [k'' v''] ?]; intros.
      - simpl.
        constructor; [ | constructor].
        assumption.
      - simpl.
        if_tac; simpl.
        + auto.
        + inversion H0; subst; clear H0.
          if_tac; auto.
    Qed.
    Hint Resolve get_empty: sortedtable.
    Hint Resolve get_put_same: sortedtable.
    Hint Resolve get_put_diff: sortedtable.
    Hint Constructors sorted: sortedtable.

    Lemma empty_sorted:
      sorted empty.
    Proof.
      constructor.
    Qed.

    Lemma put_sorted (k: key) (v: elt) (s: table elt):
      sorted s -> sorted (put k v s).
    Proof.
      induction s as [ | [k' v'] ?]; intros.
      - simpl.
        auto with sortedtable.
      - simpl.
        if_tac; simpl.
        + constructor; [ | assumption].
          apply Forall_forall.
          intros.
          inversion H1; subst; clear H1; [assumption | ].
          inversion H; subst; clear H.
          rewrite Forall_forall in H4.
          apply H4 in H2.
          apply lt_trans with k'; auto.
        + if_tac; subst.
          * inversion H.
            auto with sortedtable.
          * inversion H; subst; clear H.
            constructor; [ | auto].
            apply put_sorted_aux; repeat first [ Facts.order | auto ].
    Qed.

    Lemma get_in_aux (k: key) (s: table elt):
      Forall (fun binding : key * elt => k < fst binding) s ->
      get k s = None.
    Proof.
      induction s as [ | [k' v'] ?]; intros.
      - reflexivity.
      - simpl.
        inversion H; subst; clear H.
        if_tac.
        + exfalso.
          apply Facts.gt_not_eq in H2.
          simpl in H2.
          auto.
        + specialize (IHs H3).
          assumption.
    Qed.

    Lemma get_in (k: key) (v: elt) (s: table elt):
      sorted s -> get k s = Some v <-> In (k, v) s.
    Proof.
      split.
      - induction s as [ | [k' v'] ?]; intros.
        + inversion H0.
        + simpl in H0.
          if_tac in H0.
          * inversion H0; subst; clear H0.
            left.
            reflexivity.
          * right.
            inversion H; subst; clear H.
            auto.
      - induction s as [ | [k' v'] ?]; intros.
        + simpl in H0.
          contradiction.
        + inversion H0; subst; clear H0.
          * inversion H1; subst; clear H1.
            simpl.
            rewrite if_true by auto.
            reflexivity.
          * inversion H; subst; clear H.
            specialize (IHs H5 H1).
            simpl.
            if_tac; subst.
            -- apply get_in_aux in H3.
               congruence.
            -- assumption.
    Qed.

    Lemma put_Prop (P: elt -> Prop) (k: key) (v: elt) (s: table elt):
      P v ->
      Forall (fun b => P (snd b)) s ->
      Forall (fun b => P (snd b)) (put k v s).
    Proof.
      induction s as [ | [k' v'] ?]; intros.
      - simpl. auto.
      - inversion H0; subst; clear H0.
        specialize (IHs H H4).
        simpl.
        repeat first [if_tac | auto].
    Qed.

    Lemma get_Prop (P: elt -> Prop) (k: key) (v: elt) (s: table elt):
      Forall (fun b => P (snd b)) s ->
      get k s = Some v ->
      P v.
    Proof.
      induction s as [ | [k' v'] ?]; intros.
      - simpl in H0.
        congruence.
      - inversion H; subst; clear H.
        simpl in H0.
        if_tac in H0.
        + inversion H0; subst; clear H0.
          assumption.
        + specialize (IHs H4 H0).
          assumption.
    Qed.

    Lemma get_eq (s1 s2: table elt):
      (forall k, get k s1 = get k s2) ->
      sorted s1 ->
      sorted s2 ->
      s1 = s2.
    Proof.
      generalize dependent s2.
      induction s1 as [ | [] ?]; intros.
      - destruct s2 as [ | [] ?].
        + reflexivity.
        + assert (get k ((k, e) :: s2) = Some e). {
            simpl.
            rewrite if_true; reflexivity.
          }
          specialize (H k).
          simpl in *.
          congruence.
      - destruct s2 as [ | [] ?].
        + assert (get k ((k, e) :: s1) = Some e). {
            simpl.
            rewrite if_true; reflexivity.
          }
          specialize (H k).
          simpl in *.
          congruence.
        + destruct (eq_dec k k0).
          * subst.
            assert (e = e0). {
              specialize (H k0).
              simpl in H.
              rewrite ?if_true in H by auto.
              inv H.
              reflexivity.
            }
            change (eq k k0) with (k = k0) in e1.
            subst.
            f_equal.
            inv H0.
            inv H1.
            apply IHs1; try assumption.
            intros.
            specialize (H k).
            destruct (eq_dec k k0).
            -- subst.
               simpl in H.
               simpl in H.
               rewrite ?if_true in H by auto.
               pose proof (get_in_aux k0 s1 H4).
               pose proof (get_in_aux k0 s2 H3).
               congruence.
            -- simpl in H.
               rewrite ?if_false in H by auto.
               congruence.
          * inv H0.
            inv H1.
            destruct (Facts.lt_dec k k0).
            -- specialize (H k).
               simpl in H.
               rewrite if_true in H by auto.
               rewrite if_false in H by auto.
               assert (Forall (fun binding : key * elt => k < fst binding) s2). {
                 apply Forall_forall.
                 rewrite Forall_forall in H3.
                 intros.
                 apply lt_trans with k0; auto.
               }
               pose proof (get_in_aux k s2 H0).
               congruence.
            -- specialize (H k0).
               simpl in H.
               rewrite if_false in H by auto.
               rewrite if_true in H by auto.
               assert (Forall (fun binding : key * elt => k0 < fst binding) s1). {
                 apply Forall_forall.
                 rewrite Forall_forall in H4.
                 intros.
                 apply lt_trans with k; auto.
                 Facts.order.
               }
               pose proof (get_in_aux k0 s1 H0).
               congruence.
    Qed.
  End Types.

  Hint Resolve get_empty: sortedtable.
  Hint Resolve get_put_same: sortedtable.
  Hint Resolve get_put_diff: sortedtable.
  Hint Constructors sorted: sortedtable.
  Hint Resolve empty_sorted: sortedtable.
  Hint Resolve put_sorted: sortedtable.
  Hint Resolve get_in: sortedtable.
End SortedListTable.
