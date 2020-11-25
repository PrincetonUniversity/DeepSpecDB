(** * bordernode_fun.v : Functional Model of BorderNode*)
Require Import VST.floyd.functional_base.
Require Import DB.common.
Require Import DB.tactics.
Require Import DB.functional.keyslice.
Require Import DB.functional.key.

(* For now, client values are well-distinguished, therefore option type should be fine *)
(* However, internal nodes are only distinguishable by nullptr *)

Module BorderNode.
  Section Parametrized.
    (* [ext_value] are the values for clients, [int_value] are the values for internal nodes *)
    Context {ext_value int_value: Type}.
    Definition table: Type := list (option ext_value) * (option ((string * ext_value) + int_value)).
    Definition empty: table := (list_repeat (Z.to_nat keyslice_length) None, None).

    Instance inh_option_ext_value: Inhabitant (option ext_value) := None.

    Definition put_prefix (k: Z) (v: ext_value) (t: table): table :=
      match t with
      | (prefixes, suffix) =>
        (upd_Znth (k - 1) prefixes (Some v), suffix)
      end.

    Definition get_prefix (k: Z) (t: table): option ext_value :=
      match t with
      | (prefixes, _) => Znth (k - 1) prefixes
      end.

    Definition put_suffix (k: string) (v: ext_value) (t: table): table :=
      match t with
      | (prefixes, _) =>
        (prefixes, Some (inl (k, v)))
      end.

    Definition get_suffix (k: string) (t: table): option ext_value :=
      match t with
      | (_, Some (inl (k', v))) =>
        if eq_dec k k' then Some v else None
      | _ => None
      end.

    Definition put_link (v: int_value) (t: table): table :=
      match t with
      | (prefixes, _) =>
        (prefixes, Some (inr v))
      end.

    Definition get_link (t: table): option int_value :=
      match t with
      | (prefixes, Some (inr v)) =>
        Some v
      | _ => None
      end.

    Definition test_suffix (k: string) (t: table): bool :=
      match t with
      | (_, Some (inl (k', v))) =>
        if eq_dec k k' then true else false
      | _ => false
      end.

    Definition get_suffix_pair (t: table): option (string * ext_value) :=
      match t with
      | (_, Some (inl (k, v))) => Some (k, v)
      | _ => None
      end.

    Definition is_link (t: table): bool :=
      match t with
      | (_, Some (inr _)) => true
      | _ => false
      end.

    Definition put_value (key: string) (v: ext_value) (t: table): table :=
      if (Z_le_dec (Zlength key) keyslice_length) then
        put_prefix (Zlength key) v t
      else
        put_suffix (keyslice.get_suffix key) v t.

    Definition invariant (t: table) := Zlength (fst t) = keyslice_length.
    (* This is not a complete invariant:
     * if a bordernode associate with keyslice 'abcdefgh', then all of the prefix field should be empty *)

    Lemma empty_invariant: invariant empty.
    Proof.
      unfold invariant.
      simpl.
      rewrite Zlength_list_repeat; rep_lia.
    Qed.

    Lemma get_prefix_empty: forall k,
        0 < k <= keyslice_length -> get_prefix k empty = None.
    Proof.
      intros.
      simpl. 
      rewrite Znth_list_repeat_inrange by rep_lia.
      reflexivity.
    Qed.

    Lemma get_suffix_empty: forall k,
        get_suffix k empty = None.
    Proof.
      intros.
      simpl.
      reflexivity.
    Qed.

    Lemma put_prefix_invariant: forall k v t,
        invariant t -> 0 < k <= keyslice_length -> invariant (put_prefix k v t).
    Proof.
      intros.
      destruct t as [].
      unfold invariant in *.
      simpl in *.
      rewrite upd_Znth_Zlength by list_solve.
      assumption.
    Qed.

    Lemma put_suffix_invariant: forall k v t,
        invariant t -> invariant (put_suffix k v t).
    Proof.
      intros.
      destruct t as [].
      unfold invariant in *.
      simpl in *.
      assumption.
    Qed.

    Lemma get_put_prefix_same: forall k v t,
        invariant t -> 0 < k <= keyslice_length -> get_prefix k (put_prefix k v t) = Some v.
    Proof.
      intros.
      destruct t as [].
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
      destruct t as [].
      unfold invariant in *.
      simpl in *.
      rewrite upd_Znth_diff by list_solve.
      reflexivity.
    Qed.

    Lemma get_put_suffix_same: forall k v t,
        get_suffix k (put_suffix k v t) = Some v.
    Proof.
      intros.
      destruct t as [].
      simpl.
      rewrite if_true by auto.
      reflexivity.
    Qed.

    Lemma get_put_suffix_diff: forall k1 k2 v t,
        k1 <> k2 -> get_suffix k1 (put_suffix k2 v t) = None.
    Proof.
      intros.
      destruct t as [].
      simpl.
      rewrite if_false by auto.
      reflexivity.
    Qed.

    Lemma get_put_suffix_pair_same: forall k v t,
        get_suffix_pair (put_suffix k v t) = Some (k, v).
    Proof.
      intros.
      destruct t as [].
      simpl.
      reflexivity.
    Qed.

    Lemma put_permute: forall k1 k2 v1 v2 t,
        put_prefix k1 v1 (put_suffix k2 v2 t) = put_suffix k2 v2 (put_prefix k1 v1 t).
    Proof.
      intros.
      destruct t as [].
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
      destruct t as [].
      simpl.
      f_equal.
      f_equal.
    Abort.

    Lemma get_put_non_interference1: forall k1 k2 v t,
        get_prefix k1 (put_suffix k2 v t) = get_prefix k1 t.
    Proof.
      intros.
      destruct t as []; reflexivity.
    Qed.

    Lemma get_put_non_interference2: forall k1 k2 v t,
        get_suffix k1 (put_prefix k2 v t) = get_suffix k1 t.
    Proof.
      intros.
      destruct t as []; reflexivity.
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
          if (get_prefix len bnode) then
            before_prefix len
          else
            if Z_lt_dec len keyslice_length then
              next_cursor' (before_prefix (len + 1)) bnode n'
            else
              next_cursor' before_suffix bnode n'
        | before_suffix =>
          if (snd bnode) then
            before_suffix
          else
            after_suffix
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
        get_prefix len bnode <> None.
    Proof.
      intros.
      generalize dependent bnode_cursor.
      induction n; intros.
      - inv H.
      - simpl in H.
        destruct bnode_cursor.
        + if_tac Heqn in H.
          * congruence.
          * if_tac in H; eauto.
        + destruct (snd bnode); congruence.
        + congruence.
    Qed.

    Lemma next_cursor_prefix_correct: forall bnode_cursor bnode len,
        next_cursor bnode_cursor bnode = before_prefix len ->
        get_prefix len bnode <> None.
    Proof.
      intros.
      eapply next_cursor_prefix_correct'; eauto.
    Qed.

    Lemma next_cursor_suffix_correct': forall bnode_cursor bnode n,
        next_cursor' bnode_cursor bnode n = before_suffix ->
        snd bnode <> None.
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
        snd bnode <> None.
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
        + repeat first [if_tac | match_tac];
            repeat match goal with
            | H: next_cursor' _ bnode _ = before_prefix _ |- _ => apply next_cursor_prefix_correct' in H
            | H: next_cursor' _ bnode _ = before_suffix |- _ => apply next_cursor_suffix_correct' in H
            end; try first [congruence | eauto].
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
          * assumption.
          * apply IHn.
            simpl.
            simpl in H.
            lia.
          * apply IHn.
            constructor.
        + if_tac; auto.
        + auto.
    Qed.

    Lemma next_cursor_terminate: forall len bnode v,
        0 < len <= keyslice_length ->
        invariant bnode ->
        next_cursor (before_prefix len) (put_prefix len v bnode) = before_prefix len.
    Proof.
      intros.
      unfold next_cursor.
      assert (Z.to_nat (keyslice_length + 2) > 0)%nat. {
        rewrite <- Nat2Z.id.
        apply Z2Nat.inj_lt; rep_lia.
      }
      destruct (Z.to_nat (keyslice_length + 2)).
      - lia.
      - simpl.
        destruct bnode as [].
        unfold get_prefix, put_prefix, invariant in *.
        simpl in *.
        rewrite upd_Znth_same by rep_lia.
        congruence.
    Qed.

    Lemma next_cursor_terminate_permute1: forall len1 len2 bnode v,
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
        apply Z2Nat.inj_lt; rep_lia.
      }
      destruct (Z.to_nat (keyslice_length + 2)).
      - lia.
      - simpl.
        destruct bnode as [].
        unfold get_prefix, put_prefix, invariant in *.
        simpl in *.
        rewrite upd_Znth_diff by rep_lia.
        if_tac; congruence.
    Qed.

    Lemma next_cursor_terminate_permute2: forall len bnode k v,
        0 < len <= keyslice_length ->
        invariant bnode ->
        next_cursor (before_prefix len) bnode = before_prefix len ->
        next_cursor (before_prefix len) (put_suffix k v bnode) = before_prefix len.
    Proof.
      intros.
      pose proof (next_cursor_prefix_correct _ _ _ H1).
      unfold next_cursor.
      assert (Z.to_nat (keyslice_length + 2) > 0)%nat. {
        rewrite <- Nat2Z.id.
        apply Z2Nat.inj_lt; rep_lia.
      }
      destruct (Z.to_nat (keyslice_length + 2)).
      - lia.
      - simpl.
        destruct bnode as [].
        unfold get_prefix, put_prefix, invariant in *.
        simpl in *.
        if_tac; congruence.
    Qed.

    Definition length_to_cursor (len: Z): cursor :=
      if Z_le_dec len keyslice_length then
        before_prefix len
      else
        before_suffix.

    Definition cursor_to_int (c: cursor): Z :=
      match c with
      | before_prefix len => len
      | before_suffix => keyslice_length + 1
      | after_suffix => keyslice_length + 2
      end.

  End Parametrized.

  Arguments table: clear implicits.
End BorderNode.
