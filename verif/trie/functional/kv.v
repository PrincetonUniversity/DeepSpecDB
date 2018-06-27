(** * kvfun.v : Functional model KV Store *)
Require Import VST.floyd.functional_base.
Require Import common.

Module Type KV_STORE (KeyType: KEY_TYPE) (ValueType: VALUE_TYPE).
  Parameter store: Type.
  Definition key: Type := KeyType.type.
  Definition value: Type := ValueType.type.
  Definition inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Parameter empty: store.
  Parameter get: key -> store -> option value.
  Parameter put: key -> value -> store -> store.
  Axiom get_empty: forall k,
      get k empty = None.
  Axiom get_put_same: forall k v s,
      get k (put k v s) = Some v.
  Axiom get_put_diff: forall k1 k2 v s,
      k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
End KV_STORE.

Module SortedListStore (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) <: KV_STORE KeyType ValueType.
  Definition key: Type := KeyType.type.
  Definition value: Type := ValueType.type.

  Instance inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Instance EqDec_key: EqDec key := KeyType.EqDec.
  Definition store: Type := list (key * value).
  Definition empty: store := nil.
  Fixpoint get (k: key) (s: store) :=
    match s with
    | (k', v') :: l' =>
      if eq_dec k k' then
        Some v'
      else get k l'
    | nil => None
    end.

  Fixpoint put (k: key) (v: value) (s: store) :=
    match s with
    | (k', v') :: l' =>
      if KeyType.lt_dec k k' then
          (k, v) :: (k', v') :: l'
      else
        if eq_dec k k' then
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
  Hint Resolve get_empty: sortedstore.

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
      + contradiction.
      + rewrite if_true by auto.
        reflexivity.
      + rewrite if_false by auto.
        assumption.
  Qed.
  Hint Resolve get_put_same: sortedstore.

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
  Hint Resolve get_put_diff: sortedstore.

  Import KeyType.

  (* sorted invariant *)
  Inductive sorted: store -> Prop :=
  | sorted_nil: sorted nil
  | sorted_cons: forall k v l,
      Forall (fun binding => lt k (fst binding)) l -> 
      sorted l ->
      sorted ((k, v) :: l).

  Hint Constructors sorted: sortedstore.

  Lemma put_sorted_aux (k k': key) (v: value) (s: store):
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

  Lemma put_sorted (k: key) (v: value) (s: store):
    sorted s -> sorted (put k v s).
  Proof.
    induction s as [ | [k' v'] ?]; intros.
    - simpl.
      auto with sortedstore.
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
          auto with sortedstore.
        * inversion H; subst; clear H.
          constructor; [ | auto].
          apply put_sorted_aux; repeat first [ apply KeyType.ge_neq_lt | auto ].
  Qed.
  Hint Resolve put_sorted: sortedstore.

  Lemma get_in_aux (k: key) (s: store):
    Forall (fun binding : type * value => k < fst binding) s ->
    get k s = None.
  Proof.
    induction s as [ | [k' v'] ?]; intros.
    - reflexivity.
    - simpl.
      inversion H; subst; clear H.
      if_tac.
      + apply KeyType.lt_neq in H2.
        contradiction.
      + specialize (IHs H3).
        assumption.
  Qed.

  Lemma get_in (k: key) (v: value) (s: store):
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
  Hint Resolve get_in: sortedstore.

  Lemma put_Prop (P: value -> Prop) (k: key) (v: value) (s: store):
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

  Lemma get_Prop (P: value -> Prop) (k: key) (v: value) (s: store):
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

  Lemma get_eq (s1 s2: store):
    (forall k, get k s1 = get k s2) ->
    sorted s1 ->
    sorted s2 ->
    s1 = s2.
  Proof.
    generalize dependent s2.
    induction s1 as [ | [] ?]; intros.
    - destruct s2 as [ | [] ?].
      + reflexivity.
      + assert (get k ((k, v) :: s2) = Some v). {
          simpl.
          rewrite if_true; reflexivity.
        }
        specialize (H k).
        simpl in *.
        congruence.
    - destruct s2 as [ | [] ?].
      + assert (get k ((k, v) :: s1) = Some v). {
          simpl.
          rewrite if_true; reflexivity.
        }
        specialize (H k).
        simpl in *.
        congruence.
      + destruct (eq_dec k k0).
        * subst.
          assert (v = v0). {
            specialize (H k0).
            simpl in H.
            rewrite ?if_true in H by auto.
            inv H.
            reflexivity.
          }
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
          destruct (lt_dec k k0).
          -- specialize (H k).
             simpl in H.
             rewrite if_true in H by auto.
             rewrite if_false in H by auto.
             assert (Forall (fun binding : type * value => k < fst binding) s2). {
               apply Forall_forall.
               rewrite Forall_forall in H3.
               intros.
               apply lt_trans with k0; auto.
             }
             pose proof (get_in_aux k s2 H0).
             congruence.
          -- pose proof (ge_neq_lt _ _ n0 ltac:(congruence)).
             specialize (H k0).
             simpl in H.
             rewrite if_false in H by auto.
             rewrite if_true in H by auto.
             assert (Forall (fun binding : type * value => k0 < fst binding) s1). {
               apply Forall_forall.
               rewrite Forall_forall in H4.
               intros.
               apply lt_trans with k; auto.
             }
             pose proof (get_in_aux k0 s1 H1).
             congruence.
  Qed.
End SortedListStore.

Module Flatten (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) (Source: KV_STORE KeyType ValueType).
  Module SortedStore := SortedListStore KeyType ValueType.
  Definition flatten_invariant (s1: Source.store) (s2: SortedStore.store): Prop :=
    SortedStore.sorted s2 /\
    forall (k: KeyType.type), Source.get k s1 = SortedStore.get k s2.
  Parameter flatten: Source.store -> SortedStore.store.
  Theorem put_permute (k: KeyType.type) (v: ValueType.type) (s: Source.store):
    (forall s', flatten_invariant s' (flatten s')) ->
    flatten (Source.put k v s) = SortedStore.put k v (flatten s).
  Proof.
    intros.
    apply SortedStore.get_eq.
    - intros.
      pose proof H.
      specialize (H (Source.put k v s)).
      inv H.
      rewrite <- H2.
      specialize (H0 s).
      inv H0.
      destruct (eq_dec k k0).
      + subst.
        rewrite Source.get_put_same.
        rewrite SortedStore.get_put_same.
        reflexivity.
      + rewrite Source.get_put_diff by auto.
        rewrite SortedStore.get_put_diff by auto.
        rewrite H3.
        reflexivity.
    - specialize (H (Source.put k v s)).
      inv H.
      assumption.
    - apply SortedStore.put_sorted.
      specialize (H s).
      inv H.
      assumption.
  Qed.
End Flatten.
