(** * bordernode_fun.v : Functional Model of BorderNode*)
Require Import VST.floyd.functional_base.
Require Import common.
Require Import keyslice_fun.

Module BorderNode (ValueType: VALUE_TYPE).
  Definition prefix_key := Z.
  Definition suffix_key := string.
  Definition value := ValueType.type.
  Definition default_val := ValueType.default.
  
  Definition store: Type := list value * option (string * value).
  
  Definition empty: store := (list_repeat (Z.to_nat keyslice_length) default_val, None).

  Instance inhabitant_value: Inhabitant value := ValueType.inhabitant_value.
  Definition get_prefix (k: prefix_key) (s: store): value :=
    let (prefixes, _) := s in
    Znth k prefixes.

  Definition get_suffix (k: suffix_key) (s: store): value :=
    match s with
    | (_, Some (s, v)) =>
      if eq_dec k s then v else default_val
    | _ => default_val
    end.

  Definition put_prefix (k: prefix_key) (v: value) (s: store): store :=
    let (prefixes, suffix) := s in
    (upd_Znth k prefixes v, suffix).

  Definition put_suffix (k: suffix_key) (v: value) (s: store): store :=
    let (prefixes, _) := s in
    (prefixes, Some (k, v)).

  Definition invariant (s: store) := let (prefixes, _) := s in Zlength prefixes = keyslice_length.

  Lemma empty_invariant: invariant empty.
  Proof.
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
    reflexivity.
  Qed.

  Lemma put_prefix_invariant: forall k v s,
      invariant s -> 0 <= k < keyslice_length -> invariant (put_prefix k v s).
  Proof.
    intros.
    destruct s.
    simpl in *.
    rewrite upd_Znth_Zlength by list_solve.
    assumption.
  Qed.

  Lemma put_suffix_invariant: forall k v s,
      invariant s -> invariant (put_suffix k v s).
  Proof.
    intros.
    destruct s.
    simpl in *.
    assumption.
  Qed.

  Lemma get_put_prefix_same: forall k v s,
      invariant s -> 0 <= k < keyslice_length -> get_prefix k (put_prefix k v s) = v.
  Proof.
    intros.
    destruct s.
    simpl in *.
    rewrite upd_Znth_same by list_solve.
    reflexivity.
  Qed.

  Lemma get_put_prefix_diff: forall k1 k2 v s,
      invariant s -> 0 <= k1 < keyslice_length -> 0 <= k2 < keyslice_length -> k1 <> k2 ->
      get_prefix k1 (put_prefix k2 v s) = get_prefix k1 s.
  Proof.
    intros.
    destruct s.
    simpl in *.
    rewrite upd_Znth_diff by list_solve.
    reflexivity.
  Qed.

  Lemma get_put_suffix_same: forall k v s,
      get_suffix k (put_suffix k v s) = v.
  Proof.
    intros.
    destruct s.
    simpl.
    rewrite if_true by auto.
    reflexivity.
  Qed.

  Lemma get_put_suffix_diff: forall k1 k2 v s,
      k1 <> k2 -> get_suffix k1 (put_suffix k2 v s) = default_val.
  Proof.
    intros.
    destruct s.
    simpl.
    rewrite if_false by auto.
    reflexivity.
  Qed.

  Lemma get_put_non_interference1: forall k1 k2 v s,
      get_prefix k1 (put_suffix k2 v s) = get_prefix k1 s.
  Proof.
    intros.
    destruct s; reflexivity.
  Qed.

  Lemma get_put_non_interference2: forall k1 k2 v s,
      get_suffix k1 (put_prefix k2 v s) = get_suffix k1 s.
  Proof.
    intros.
    destruct s; reflexivity.
  Qed.

  Hint Rewrite get_put_prefix_same: bordernode.
  Hint Rewrite get_put_prefix_diff: bordernode.
  Hint Rewrite get_put_prefix_same: bordernode.
  Hint Rewrite get_put_suffix_diff: bordernode.
  Hint Rewrite get_put_non_interference1: bordernode.
  Hint Rewrite get_put_non_interference2: bordernode.
End BorderNode.
