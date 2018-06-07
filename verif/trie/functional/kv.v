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
  Definition default_val: value := ValueType.default.
  Definition inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Parameter empty: store.
  Parameter get: key -> store -> value.
  Parameter put: key -> value -> store -> store.
  Axiom get_empty: forall k,
      get k empty = default_val.
  Axiom get_put_same: forall k v s,
      get k (put k v s) = v.
  Axiom get_put_diff: forall k1 k2 v s,
      k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
End KV_STORE.

(* Transforming a standard kv-store into a list representation *)
(* 1. we need to make sure that this module conforms KV_STORE, for convenience of client *)
(* 2. we need to make sure that the operations commutes *)

Module Type ORD_KEY_TYPE <: KEY_TYPE.
  Include KEY_TYPE.
  Parameter le: type -> type -> Prop.
  Notation "A <= B" := (le A B).
  Notation "A > B" := (~ (le A B)).
  Parameter le_dec: forall (x y: type), {x <= y} + {x > y}.
  Axiom le_antisym: forall (x y: type), x <= y -> y <= x -> x = y.
  Axiom le_refl: forall (x: type), x <= x.
  Axiom le_trans: forall (x y z: type), x <= y -> y <= z -> x <= z.
  Axiom gt_le: forall (x y: type), y > x -> x <= y.
  Parameter EqDec: EqDec type.
End ORD_KEY_TYPE.

Module SortedListStore (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) <: KV_STORE KeyType ValueType.
  Definition key: Type := KeyType.type.
  Definition value: Type := ValueType.type.
  Definition default_val: value := ValueType.default.
  Instance inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Instance EqDec_key: EqDec key := KeyType.EqDec.
  Definition store: Type := list (key * value).
  Definition empty: store := nil.
  Fixpoint get (k: key) (s: store) :=
    match s with
    | (k', v') :: l' =>
      if eq_dec k k' then
        v'
      else get k l'
    | nil => default_val
    end.

  Fixpoint put (k: key) (v: value) (s: store) :=
    match s with
    | (k', v') :: l' =>
      if KeyType.le_dec k k' then
        if eq_dec k k' then
          (k, v) :: l'
        else
          (k, v) :: (k', v') :: l'
      else
        (k', v') :: (put k v l')
    | nil => (k, v) :: nil
    end.

  Theorem get_empty: forall k, get k empty = default_val.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem get_put_same: forall k v s,
      get k (put k v s) = v.
  Proof.
    induction s as [ | [k' v'] ?].
    - simpl.
      rewrite if_true by auto.
      reflexivity.
    - simpl.
      if_tac; simpl; if_tac; simpl.
      + rewrite if_true by auto.
        reflexivity.
      + rewrite if_true by auto.
        reflexivity.
      + subst.
        exfalso.
        apply H.
        apply KeyType.le_refl.
      + assumption.
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
      + rewrite ?if_false by auto.
        reflexivity.
      + rewrite if_false by auto.
        reflexivity.
      + reflexivity.
      + specialize (IHs H).
        assumption.
  Qed.

  Import KeyType.

  (* sorted invariant *)
  Inductive sorted: store -> Prop :=
  | sorted_nil: sorted nil
  | sorted_cons: forall k v l,
      Forall (fun binding => le k (fst binding)) l -> 
      sorted l ->
      sorted ((k, v) :: l).

  Hint Constructors sorted.

  Lemma put_sorted_aux (k k': key) (v: value) (s: store):
    k' > k ->
    Forall (fun binding => le k (fst binding)) s ->
    Forall (fun binding => le k (fst binding)) (put k' v s).
  Proof.
    induction s as [ | [k'' v''] ?]; intros.
    - simpl.
      constructor; [ | constructor].
      apply gt_le.
      assumption.
    - simpl.
      if_tac; simpl.
      + if_tac; simpl.
        * subst.
          inversion H0; subst; clear H0.
          constructor; assumption.
        * constructor; [ | assumption].
          apply gt_le in H.
          assumption.
      + inversion H0; subst; clear H0.
        specialize (IHs H H5).
        constructor; assumption.
  Qed.

  Lemma put_sorted (k: key) (v: value) (s: store):
    sorted s -> sorted (put k v s).
  Proof.
    induction s as [ | [k' v'] ?]; intros.
    - simpl.
      auto.
    - simpl.
      if_tac; simpl.
      + if_tac; simpl.
        * inversion H; subst; clear H.
          constructor; assumption.
        * constructor; [ | assumption].
          inversion H; subst; clear H.
          apply Forall_forall.
          rewrite Forall_forall in H4.
          intros.
          assert (k' <= fst x). {
            inversion H.
            - subst.
              apply le_refl.
            - apply H4.
              assumption.
          }
          apply le_trans with k'; assumption.
      + inversion H; subst; clear H.
        constructor; [ | auto].
        apply put_sorted_aux; assumption.
  Qed.

End SortedListStore.

Module Transform (KeyType: ORD_KEY_TYPE) (ValueType: VALUE_TYPE) (Source: KV_STORE KeyType ValueType).
  Module SortedStore := SortedListStore KeyType ValueType.
  Parameter transform: Source.store -> {store: SortedStore.store | SortedStore.sorted store }.
  Theorem put_permute (k: KeyType.type) (v: ValueType.type) (s: Source.store):
    proj1_sig (transform (Source.put k v s)) = SortedStore.put k v(proj1_sig (transform s)). 
  Admitted.
End Transform.
