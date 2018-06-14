(** * kvfun.v : Functional model KV Store *)
Require Import VST.floyd.functional_base.
Require Import common.

Module Type KEY_TYPE.
  Parameter type: Type.
End KEY_TYPE.

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

(* Transforming a standard kv-store into a list representation *)
(* 1. we need to make sure that this module conforms KV_STORE, for convenience of client *)
(* 2. we need to make sure that the operations commutes *)

Module Type ORD_KEY_TYPE <: KEY_TYPE.
  Include KEY_TYPE.
  Parameter lt: type -> type -> Prop.
  Notation "A < B" := (lt A B).
  Notation "A >= B" := (~ (lt A B)).
  Parameter lt_dec: forall (x y: type), {x < y} + {x >= y}.
  Axiom lt_trans: forall (x y z: type), x < y -> y < z -> x < z.
  Axiom lt_neq: forall (x y: type), x < y -> x <> y.
  Axiom ge_neq_lt: forall (x y: type), y >= x -> x <> y -> x < y.
  Parameter EqDec: EqDec type.
End ORD_KEY_TYPE.

Module SortedListStore (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) <: KV_STORE KeyType ValueType.
  Definition key: Type := KeyType.type.
  Definition value: Type := ValueType.type.
  (* Definition default_val: value := ValueType.default. *)
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
  Hint Resolve put_Prop: sortedstore.

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
  (* Hint Resolve get_Prop: sortedstore. *)
End SortedListStore.

Module Transform (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) (Source: KV_STORE KeyType ValueType).
  Module SortedStore := SortedListStore KeyType ValueType.
  Parameter transform: Source.store -> {store: SortedStore.store | SortedStore.sorted store }.
  Theorem put_permute (k: KeyType.type) (v: ValueType.type) (s: Source.store):
    proj1_sig (transform (Source.put k v s)) = SortedStore.put k v(proj1_sig (transform s)). 
  Admitted.
End Transform.
