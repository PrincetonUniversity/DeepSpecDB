(** * bordernode_fun.v : Functional Model of BorderNode*)
Require Import VST.floyd.functional_base.
Require Import DB.common.
Require Import DB.functional.keyslice.

Class BorderNodeValue (A: Type) :=
  {
    default_val: A;
    default_or_not: forall a: A, {a = default_val} + {a <> default_val}
  }.

Module BorderNode.
  Definition prefix_key := Z.
  Definition suffix_key := option string.
  Section Parametrized.
    Context {value: Type}.
    Context {inh: Inhabitant value}.
    Context {dft: BorderNodeValue value}.
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
        put_suffix (Some (keyslice.get_suffix key)) v t.

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

    (* extra definitions and lemmas for cursor *)

    Inductive cursor: Type :=
    | before_prefix: Z -> cursor
    | before_suffix: cursor
    | after_suffix: cursor.

    (* for this function, [after_suffix] actually means a fail *)
    Fixpoint next_cursor' (bnode_cursor: cursor) (bnode: table) (n: nat) :=
      match n with
      | S n' =>
        match bnode_cursor with
        | before_prefix len =>
          if default_or_not (get_prefix len bnode) then
            if Z_lt_dec len keyslice_length then
              next_cursor' (before_prefix (len + 1)) bnode n'
            else
              next_cursor' before_suffix bnode n'
          else
            before_prefix len
        | before_suffix =>
          if default_or_not (snd (get_suffix_pair bnode)) then
            after_suffix
          else
            before_suffix
        | after_suffix => after_suffix
        end
      | O => after_suffix
      end.

    Definition next_cursor (bnode_cursor: cursor) (bnode: table) :=
      next_cursor' bnode_cursor bnode (Z.to_nat (keyslice_length + 2)).

    Definition first_cursor (bnode: table) :=
      next_cursor (before_prefix 1) bnode.

    Definition cursor_correct (bnode_cursor: cursor): Prop :=
      match bnode_cursor with
      | before_prefix len => 0 < len <= keyslice_length
      | _ => True
      end.

    Lemma next_cursor_prefix_correct': forall bnode_cursor bnode len n,
        next_cursor' bnode_cursor bnode n = before_prefix len ->
        get_prefix len bnode <> default_val.
    Proof.
      intros.
      generalize dependent bnode_cursor.
      induction n; intros.
      - inv H.
      - simpl in H.
        destruct bnode_cursor.
        + if_tac in H.
          * if_tac in H; eauto.
          * inv H.
            eauto.
        + if_tac in H; congruence.
        + congruence.
    Qed.

    Lemma next_cursor_prefix_correct: forall bnode_cursor bnode len,
        next_cursor bnode_cursor bnode = before_prefix len ->
        get_prefix len bnode <> default_val.
    Proof.
      intros.
      eapply next_cursor_prefix_correct'; eauto.
    Qed.

    Lemma next_cursor_suffix_correct': forall bnode_cursor bnode n,
        next_cursor' bnode_cursor bnode n = before_suffix ->
        snd (get_suffix_pair bnode) <> default_val.
    Proof.
      intros.
      generalize dependent bnode_cursor.
      induction n; intros.
      - inv H.
      - simpl in H.
        destruct bnode_cursor.
        + if_tac in H; try congruence.
          if_tac in H.
          * apply IHn in H.
            assumption.
          * destruct n; simpl in H; try congruence.
            if_tac in H; congruence.            
        + if_tac in H; congruence.
        + congruence.
    Qed.

    Lemma next_cursor_suffix_correct: forall bnode_cursor bnode,
        next_cursor bnode_cursor bnode = before_suffix ->
        snd (get_suffix_pair bnode) <> default_val.
    Proof.
      intros.
      eapply next_cursor_suffix_correct'; eauto.
    Qed.

    Lemma next_cursor_idempotent: forall bnode_cursor bnode_cursor' bnode,
        next_cursor bnode_cursor bnode = bnode_cursor' ->
        next_cursor bnode_cursor' bnode = bnode_cursor'.
    Proof.
      intros.
      unfold next_cursor in *.
      remember (Z.to_nat (keyslice_length + 2)).
      clear Heqn.
      destruct n.
      - simpl in H.
        simpl.
        congruence.
      - simpl in *. subst.
        destruct bnode_cursor; simpl.
        + if_tac; rewrite ?Heqn in *; try congruence.
          if_tac.
          * destruct (next_cursor' (before_prefix (z + 1)) bnode n) eqn:Heqn';
              try congruence.
            -- apply next_cursor_prefix_correct' in Heqn'.
               if_tac; congruence.
            -- apply next_cursor_suffix_correct' in Heqn'.
               if_tac; congruence.
          * destruct n; simpl; try congruence.
            if_tac; congruence.
          * repeat if_tac; congruence.
        + if_tac; reflexivity.
        + reflexivity.
    Qed.

    Lemma next_cursor_bnode_correct: forall bnode_cursor bnode,
        cursor_correct bnode_cursor ->
        cursor_correct (next_cursor bnode_cursor bnode).
    Proof.
      intros.
      generalize dependent bnode.
      generalize dependent bnode_cursor.
      unfold next_cursor.
      remember (Z.to_nat (keyslice_length + 2)).
      clear Heqn.
      induction n; intros.
      - firstorder.
      - simpl.
        destruct bnode_cursor.
        + repeat if_tac.
          * apply IHn.
            simpl.
            simpl in H.
            omega.
          * firstorder.
          * assumption.
        + if_tac; auto.
        + auto.
    Qed.

    Lemma next_cursor_terminate: forall len bnode v,
        0 < len <= keyslice_length ->
        invariant bnode ->
        v <> default_val ->
        next_cursor (before_prefix len) (put_prefix len v bnode) = before_prefix len.
    Proof.
      intros.
      unfold next_cursor.
      assert (Z.to_nat (keyslice_length + 2) > 0)%nat. {
        rewrite <- Nat2Z.id.
        apply Z2Nat.inj_lt; rep_omega.
      }
      destruct (Z.to_nat (keyslice_length + 2)).
      - omega.
      - simpl.
        rewrite if_false.
        + reflexivity.
        + destruct bnode as [[]].
          unfold get_prefix, put_prefix, invariant in *.
          simpl in *.
          rewrite upd_Znth_same by rep_omega.
          congruence.
    Qed.

    Lemma next_cursor_terminate_permute: forall len1 len2 bnode v,
        0 < len1 <= keyslice_length ->
        0 < len2 <= keyslice_length ->
        len1 <> len2 ->
        invariant bnode ->
        next_cursor (before_prefix len1) bnode = before_prefix len1 ->
        next_cursor (before_prefix len1) (put_prefix len2 v bnode) = before_prefix len1.
    Proof.
      intros.
      pose proof (next_cursor_prefix_correct _ _ _ H3).
      unfold next_cursor.
      assert (Z.to_nat (keyslice_length + 2) > 0)%nat. {
        rewrite <- Nat2Z.id.
        apply Z2Nat.inj_lt; rep_omega.
      }
      destruct (Z.to_nat (keyslice_length + 2)).
      - omega.
      - simpl.
        rewrite if_false.
        + reflexivity.
        + destruct bnode as [[]].
          unfold get_prefix, put_prefix, invariant in *.
          simpl in *.
          rewrite upd_Znth_diff by rep_omega.
          congruence.
    Qed.
  End Parametrized.
End BorderNode.
