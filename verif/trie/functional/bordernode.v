(** * bordernode_fun.v : Functional Model of BorderNode*)
Require Import VST.floyd.functional_base.
Require Import DB.common.
Require Import DB.functional.keyslice.

Class DefaultValue (A: Type) := default_val: A.

Module BorderNode.
  Definition prefix_key := Z.
  Definition suffix_key := option string.
  Section Parametrized.
    Context {value: Type}.
    Context {inh: Inhabitant value}.
    Context {dft: DefaultValue value}.
    Definition table: Type := list value * option string * value.

    Definition empty: table := (list_repeat (Z.to_nat keyslice_length) default_val, None, default_val).

    Definition put_prefix (k: prefix_key) (v: value) (t: table): table :=
      match t with
      | (prefixes, suffix, value) =>
        (upd_Znth (k - 1) prefixes v, suffix, value)
      end.

    Definition get_prefix (k: prefix_key) (t: table): value :=
      match t with
      | (prefixes, _, _) => Znth (k - 1) prefixes
      end.

    Definition put_suffix (k: suffix_key) (v: value) (t: table): table :=
      match t with
      | (prefixes, suffix, value) =>
        (prefixes, k, v)
      end.

    Definition get_suffix (k: suffix_key) (t: table): value :=
      match t with
      | (_, k', v) =>
        if eq_dec k k' then v else default_val
      end.

    Definition test_suffix (k: suffix_key) (t: table): {k = (snd (fst t))} + {k <> (snd (fst t))} :=
      match t with
      | (_, k', _) =>
        eq_dec k k'
      end.

    Definition get_suffix_pair (t: table): suffix_key * value :=
      match t with
      | (_, k, v) => (k, v)
      end.

    Definition is_link (t: table): {None = (snd (fst t))} + {None <> (snd (fst t))} :=
      test_suffix None t.

    Definition put_value (key: string) (v: value) (t: table): table :=
      if (Z_le_dec (Zlength key) keyslice_length) then
        put_prefix (Zlength key) v t
      else
        put_suffix (Some (sublist keyslice_length (Zlength key) key)) v t.

    Definition invariant (t: table) := Zlength (fst (fst t)) = keyslice_length.

    Lemma empty_invariant: invariant empty.
    Proof.
      unfold invariant.
      simpl.
      rewrite Zlength_list_repeat; rep_omega.
    Qed.

    Lemma get_prefix_empty: forall k,
        0 < k <= keyslice_length -> get_prefix k empty = default_val.
    Proof.
      intros.
      simpl. 
      rewrite Znth_list_repeat_inrange by rep_omega.
      reflexivity.
    Qed.

    Lemma get_suffix_empty: forall k,
        get_suffix k empty = default_val.
    Proof.
      intros.
      simpl.
      if_tac; reflexivity.
    Qed.

    Lemma put_prefix_invariant: forall k v t,
        invariant t -> 0 < k <= keyslice_length -> invariant (put_prefix k v t).
    Proof.
      intros.
      destruct t as [[]].
      unfold invariant in *.
      simpl in *.
      rewrite upd_Znth_Zlength by list_solve.
      assumption.
    Qed.

    Lemma put_suffix_invariant: forall k v t,
        invariant t -> invariant (put_suffix k v t).
    Proof.
      intros.
      destruct t as [[]].
      unfold invariant in *.
      simpl in *.
      assumption.
    Qed.

    Lemma get_put_prefix_same: forall k v t,
        invariant t -> 0 < k <= keyslice_length -> get_prefix k (put_prefix k v t) = v.
    Proof.
      intros.
      destruct t as [[]].
      unfold invariant in *.
      simpl in *.
      rewrite upd_Znth_same by list_solve.
      reflexivity.
    Qed.

    Lemma get_put_prefix_diff: forall k1 k2 v t,
        invariant t -> 0 < k1 <= keyslice_length -> 0 < k2 <= keyslice_length -> k1 <> k2 ->
        get_prefix k1 (put_prefix k2 v t) = get_prefix k1 t.
    Proof.
      intros.
      destruct t as [[]].
      unfold invariant in *.
      simpl in *.
      rewrite upd_Znth_diff by list_solve.
      reflexivity.
    Qed.

    Lemma get_put_suffix_same: forall k v t,
        get_suffix k (put_suffix k v t) = v.
    Proof.
      intros.
      destruct t as [[]].
      simpl.
      rewrite if_true by auto.
      reflexivity.
    Qed.

    Lemma get_put_suffix_diff: forall k1 k2 v t,
        k1 <> k2 -> get_suffix k1 (put_suffix k2 v t) = default_val.
    Proof.
      intros.
      destruct t as [[]].
      simpl.
      rewrite if_false by auto.
      reflexivity.
    Qed.

    Lemma get_put_suffix_pair_same: forall k v t,
        get_suffix_pair (put_suffix k v t) = (k, v).
    Proof.
      intros.
      destruct t as [[]].
      simpl.
      reflexivity.
    Qed.

    Lemma put_permute: forall k1 k2 v1 v2 t,
        put_prefix k1 v1 (put_suffix k2 v2 t) = put_suffix k2 v2 (put_prefix k1 v1 t).
    Proof.
      intros.
      destruct t as [[]].
      reflexivity.
    Qed.

    Lemma put_permute': forall k1 k2 v1 v2 t,
        0 < k1 <= keyslice_length ->
        0 < k2 <= keyslice_length ->
        invariant t ->
        k1 <> k2 ->
        put_prefix k1 v1 (put_prefix k2 v2 t) = put_prefix k2 v2 (put_prefix k1 v1 t).
    Proof.
      intros.
      destruct t as [[]].
      simpl.
      f_equal.
      f_equal.
    Abort.

    Lemma get_put_non_interference1: forall k1 k2 v t,
        get_prefix k1 (put_suffix k2 v t) = get_prefix k1 t.
    Proof.
      intros.
      destruct t as [[]]; reflexivity.
    Qed.

    Lemma get_put_non_interference2: forall k1 k2 v t,
        get_suffix k1 (put_prefix k2 v t) = get_suffix k1 t.
    Proof.
      intros.
      destruct t as [[]]; reflexivity.
    Qed.

    Hint Rewrite get_put_prefix_same: bordernode.
    Hint Rewrite get_put_prefix_diff: bordernode.
    Hint Rewrite get_put_prefix_same: bordernode.
    Hint Rewrite get_put_suffix_diff: bordernode.
    Hint Rewrite get_put_non_interference1: bordernode.
    Hint Rewrite get_put_non_interference2: bordernode.
  End Parametrized.
End BorderNode.
