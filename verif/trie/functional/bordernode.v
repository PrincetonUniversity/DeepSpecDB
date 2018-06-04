(** * bordernode_fun.v : Functional Model of BorderNode*)
Require Import VST.floyd.functional_base.
Require Import deepDB.common.
Require Import deepDB.functional.keyslice.

Module BorderNode (ValueType: DEC_VALUE_TYPE).
  Definition prefix_key := Z.
  Definition suffix_key := option string.
  Definition value := ValueType.type.
  Definition default_val := ValueType.default.

  Definition store: Type := list value * option string * value.

  Definition empty: store := (list_repeat (Z.to_nat keyslice_length) default_val, None, default_val).

  Instance inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Instance EqDec_value: EqDec value := ValueType.EqDec_value.

  Definition put_prefix (k: prefix_key) (v: value) (s: store): store :=
    match s with
    | (prefixes, suffix, value) =>
      (upd_Znth k prefixes v, suffix, value)
    end.

  Definition get_prefix (k: prefix_key) (s: store): value :=
    match s with
    | (prefixes, _, _) => Znth k prefixes
    end.

  Definition put_suffix (k: suffix_key) (v: value) (s: store): store :=
    match s with
    | (prefixes, suffix, value) =>
      (prefixes, k, v)
    end.

  Definition get_suffix (k: suffix_key) (s: store): value :=
    match s with
    | (_, k', v) =>
      if eq_dec k k' then v else default_val
    end.

  Definition test_suffix (k: suffix_key) (s: store): bool :=
    match s with
    | (_, k', _) =>
      if eq_dec k k' then true else false
    end.

  Definition get_suffix_pair (s: store): suffix_key * value :=
    match s with
    | (_, k, v) => (k, v)
    end.

  Definition is_link (s: store): bool :=
    match s with
    | (_, k, v) =>
      if eq_dec k None then
        if eq_dec v default_val then
          false
        else
          true
      else
        false
    end.

  Definition is_suffix (s: store): bool :=
    negb (test_suffix None s).

  Definition put_value (k: prefix_key + suffix_key) (v: value) (s: store): store :=
    match k with
    | inl prefix =>
      put_prefix prefix v s
    | inr suffix =>
      put_suffix suffix v s
    end.

  Definition invariant (s: store) := Zlength (fst (fst s)) = keyslice_length.

  Lemma empty_invariant: invariant empty.
  Proof.
    unfold invariant.
    simpl.
    rewrite Zlength_list_repeat; rep_omega.
  Qed.

  Lemma get_prefix_empty: forall k,
      0 <= k < keyslice_length -> get_prefix k empty = default_val.
  Proof.
    intros.
    simpl. 
    rewrite Znth_list_repeat_inrange by assumption.
    reflexivity.
  Qed.

  Lemma get_suffix_empty: forall k,
      get_suffix k empty = default_val.
  Proof.
    intros.
    simpl.
    if_tac; reflexivity.
  Qed.

  Lemma put_prefix_invariant: forall k v s,
      invariant s -> 0 <= k < keyslice_length -> invariant (put_prefix k v s).
  Proof.
    intros.
    destruct s as [[]].
    unfold invariant in *.
    simpl in *.
    rewrite upd_Znth_Zlength by list_solve.
    assumption.
  Qed.

  Lemma put_suffix_invariant: forall k v s,
      invariant s -> invariant (put_suffix k v s).
  Proof.
    intros.
    destruct s as [[]].
    unfold invariant in *.
    simpl in *.
    assumption.
  Qed.

  Lemma get_put_prefix_same: forall k v s,
      invariant s -> 0 <= k < keyslice_length -> get_prefix k (put_prefix k v s) = v.
  Proof.
    intros.
    destruct s as [[]].
    unfold invariant in *.
    simpl in *.
    rewrite upd_Znth_same by list_solve.
    reflexivity.
  Qed.

  Lemma get_put_prefix_diff: forall k1 k2 v s,
      invariant s -> 0 <= k1 < keyslice_length -> 0 <= k2 < keyslice_length -> k1 <> k2 ->
      get_prefix k1 (put_prefix k2 v s) = get_prefix k1 s.
  Proof.
    intros.
    destruct s as [[]].
    unfold invariant in *.
    simpl in *.
    rewrite upd_Znth_diff by list_solve.
    reflexivity.
  Qed.

  Lemma get_put_suffix_same: forall k v s,
      get_suffix k (put_suffix k v s) = v.
  Proof.
    intros.
    destruct s as [[]].
    simpl.
    rewrite if_true by auto.
    reflexivity.
  Qed.

  Lemma get_put_suffix_diff: forall k1 k2 v s,
      k1 <> k2 -> get_suffix k1 (put_suffix k2 v s) = default_val.
  Proof.
    intros.
    destruct s as [[]].
    simpl.
    rewrite if_false by auto.
    reflexivity.
  Qed.

  Lemma get_put_suffix_pair_same: forall k v s,
      get_suffix_pair (put_suffix k v s) = (k, v).
  Proof.
    intros.
    destruct s as [[]].
    simpl.
    reflexivity.
  Qed.

  Lemma put_permute: forall k1 k2 v1 v2 s,
      put_prefix k1 v1 (put_suffix k2 v2 s) = put_suffix k2 v2 (put_prefix k1 v1 s).
  Proof.
    intros.
    destruct s as [[]].
    reflexivity.
  Qed.

  Lemma put_permute': forall k1 k2 v1 v2 s,
      0 <= k1 < keyslice_length ->
      0 <= k2 < keyslice_length ->
      invariant s ->
      k1 <> k2 ->
      put_prefix k1 v1 (put_prefix k2 v2 s) = put_prefix k2 v2 (put_prefix k1 v1 s).
  Proof.
    intros.
    destruct s as [[]].
    simpl.
    f_equal.
    f_equal.
  Abort.

  Lemma get_put_non_interference1: forall k1 k2 v s,
      get_prefix k1 (put_suffix k2 v s) = get_prefix k1 s.
  Proof.
    intros.
    destruct s as [[]]; reflexivity.
  Qed.

  Lemma get_put_non_interference2: forall k1 k2 v s,
      get_suffix k1 (put_prefix k2 v s) = get_suffix k1 s.
  Proof.
    intros.
    destruct s as [[]]; reflexivity.
  Qed.

  Hint Rewrite get_put_prefix_same: bordernode.
  Hint Rewrite get_put_prefix_diff: bordernode.
  Hint Rewrite get_put_prefix_same: bordernode.
  Hint Rewrite get_put_suffix_diff: bordernode.
  Hint Rewrite get_put_non_interference1: bordernode.
  Hint Rewrite get_put_non_interference2: bordernode.
End BorderNode.
