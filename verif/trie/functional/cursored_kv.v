(** * cursored_kv.v: Interface and Specification for general KV Store with ordered keys and cursors*)
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapInterface.
Require Import VST.floyd.proofauto.
Require Import DB.common.

(* This file is mainly based on Brian's paper and his BTreesModule.v, with some improvement and generalization *)
(* Also, this file takes the FMap Module as reference for interface *)
Module Type ABSTRACT_TABLE (KeyType: UsualOrderedType).
  Definition key := KeyType.t.
  Hint Transparent key.
  Parameter table: Type -> Type.
  Parameter cursor: Type -> Type.
  Definition allocator: Type := list val.

  Section Types.
    Context {elt: Type}.
    (* Predicate rather than variable because of possible addresses in the data type *)
    Parameter empty: allocator -> table elt * allocator.

    (* Functions *)
    (* Sematics: cursor should point to a place where to the left, all keys are less than the key,
     * to the right, all keys are no less than the key *)
    (* Therefore [make_cursor] should always return one, but not always the expected one *)
    Parameter make_cursor: key -> table elt -> cursor elt.
    (* By [get] functions, we always access the first key to the right *)
    Parameter get: cursor elt -> table elt -> option (key * elt).
    Definition get_key (c: cursor elt) (t: table elt): option key :=
      match get c t with
      | Some (k, _) => Some k
      | None => None
      end.

    Definition get_value (c: cursor elt) (t: table elt): option elt :=
      match get c t with
      | Some (_, v) => Some v
      | None => None
      end.
    (* we do expect that the cursor is moved when insertion is performed,
     * but where it is afterwards remains to be discussed *)
    Parameter put: key -> elt -> cursor elt -> table elt * allocator -> cursor elt * (table elt * allocator).
    Parameter next_cursor: cursor elt -> table elt -> cursor elt.
    Parameter prev_cursor: cursor elt -> table elt -> cursor elt.
    Parameter first_cursor: table elt -> cursor elt.
    (* last cursor is defined to be one position past the table, which means maps to nothing *)
    Parameter last_cursor: table elt -> cursor elt.
    (* TODO: do we need a [move_cursor]?
     * From the client's view, it does not matter whether it is [make] or [move], but it might increase
     * difficulty in proof *)
    (* Parameter move_cursor: key -> cursor elt -> table elt -> cursor elt. *)

    (* Relations between keys, cursors and tables *)
    (* [abs_rel] means that the table and the cursor are binded together (might need better name) *)
    (* In implementation, it's translated to correct cursor with get tree from cursor works *)
    Parameter abs_rel: cursor elt -> table elt -> Prop.
    (* Do we need this? This just sounds like [abs_rel c t /\ get_key c t = Some k] *)
    (* Not true, in btree, the cursor created with non-existing keys will not return the key with [get_key],
     * but rather, a bunch of keys can still be associated with the cursor *)
    Parameter key_rel: key -> cursor elt -> table elt -> Prop.
    (* DO we need this again? What about [abs_rel c1 t /\ abs_rel c2 t /\ get_key c1 t = get_key c2 t] *)
    Parameter eq_cursor : cursor elt -> cursor elt -> table elt -> Prop.
    (* Definition eq_cursor (c1 c2: cursor elt) (t: table elt) := *)
    (*   abs_rel c1 t /\ abs_rel c2 t /\ get_key c1 t = get_key c2 t. *)
    (* What do we need to ensure about the previous two definition? Should they be transitive? *)
    Parameter cursor_correct: cursor elt -> Prop.
    Parameter table_correct: table elt -> Prop.

    Section Specs.
      Variable t t1 t2: table elt.
      Variable c c1 c2 c3: cursor elt. 
      Variable k k1 k2 k3: key.
      Variable e e1 e2: elt.
      Variable a: allocator.

      Axiom abs_correct: abs_rel c t -> cursor_correct c /\ table_correct t.

      (* table-cursor relations *)
      (* We need to make sure that the cursor and the table are actually working with each other *)
      (* This is actually implied by [make_cursor_key] *)
      (* Axiom make_cusor_abs: abs_rel (make_cursor k t) t. *)
      (* Do we need this? *)
      (* Axiom put_abs: *)
      (*   let (new_cursor, new_table) := put c e t in *)
      (*   abs_rel new_cursor new_table. *)
      (* TODO: What about at the end of range? *)
      Axiom next_cursor_abs: abs_rel c t -> abs_rel (next_cursor c t) t.
      Axiom prev_cursor_abs: abs_rel c t -> abs_rel (prev_cursor c t) t.
      Axiom first_cursor_abs: table_correct t -> abs_rel (first_cursor t) t.
      Axiom last_cursor_abs: table_correct t -> abs_rel (last_cursor t) t.
      Axiom put_correct: table_correct t -> table_correct (fst (snd (put k e c (t, a)))).
      Axiom empty_correct: table_correct (fst (empty a)).

      (* permute of get and insert operations *)
      (* Assume [key_rel] does entail [abs_rel] *)
      Axiom get_put_same:
        abs_rel c1 (fst (snd (put k e c2 (t, a)))) ->
        abs_rel c2 t ->
        key_rel k c1 (fst (snd (put k e c2 (t, a)))) ->
        get c1 (fst (snd (put k e c2 (t, a)))) = Some (k, e).
      Axiom get_put_diff:
        k1 <> k2 ->
        abs_rel c1 (fst (snd (put k2 e c2 (t, a)))) ->
        abs_rel c2 t ->
        abs_rel c3 t ->
        key_rel k1 c1 (fst (snd (put k2 e c2 (t, a)))) ->
        key_rel k1 c3 t ->
        get c1 (fst (snd (put k2 e c2 (t, a)))) = get c3 t.

      (* get in specific conditions *)
      Axiom get_last:
        get (last_cursor t) t = None.
      Axiom get_empty: 
        abs_rel c (fst (empty a)) -> get c (fst (empty a)) = None.

      (* Cursor and keys *)

      Axiom key_rel_eq_cursor:
        key_rel k c1 t ->
        key_rel k c2 t ->
        abs_rel c1 t ->
        abs_rel c2 t ->
        eq_cursor c1 c2 t.

      Axiom eq_cursor_get:
        abs_rel c1 t ->
        abs_rel c2 t ->
        eq_cursor c1 c2 t ->
        get c1 t = get c2 t.

      Axiom make_cursor_key:
        table_correct t -> key_rel k (make_cursor k t) t.
      Axiom make_cursor_abs:
          table_correct t -> abs_rel (make_cursor k t) t.
      
      (* cursor movement with respect to the order of key *)
      Axiom next_prev:
        abs_rel c t -> ~ eq_cursor c (last_cursor t) t -> eq_cursor c (prev_cursor (next_cursor c t) t) t.
      Axiom prev_next:
        abs_rel c t -> ~ eq_cursor c (first_cursor t) t -> eq_cursor c (next_cursor (prev_cursor c t) t) t.
      Axiom next_order:
        ~ eq_cursor c (last_cursor t) t -> key_rel k1 c t -> key_rel k2 (next_cursor c t) t -> KeyType.lt k1 k2.
      Axiom prev_order:
        ~ eq_cursor c (first_cursor t) t -> key_rel k1 c t -> key_rel k2 (prev_cursor c t) t -> KeyType.lt k2 k1.
      (* TODO: does this definition work? *)
      Axiom next_compact:
        ~ eq_cursor c (last_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (next_cursor c t) t ->
        ~ key_rel k3 c t -> KeyType.lt k1 k3 /\ KeyType.lt k3 k2.
      Axiom prev_compact:
        ~ eq_cursor c (first_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (prev_cursor c t) t ->
        ~ key_rel k3 c t -> KeyType.lt k2 k3 /\ KeyType.lt k3 k1.
    End Specs.
  End Types.
End ABSTRACT_TABLE.

Module AbstractTableFacts (KeyType: UsualOrderedType) (AbstractTable: ABSTRACT_TABLE KeyType).
  Import AbstractTable.

  Section Implication.
    Context {elt: Type}.
    Variable t: table elt.
    Variable c c1 c2 c3: cursor elt.
    Variable k k1 k2 k3: key.
    Variable e e1 e2: elt.

    (* Lemma key_abs: *)
    (*   key_rel k c t -> abs_rel c t. *)
    (* Proof. *)
    (*   intros. *)
    (*   destruct H. *)
    (*   assumption. *)
    (* Qed. *)

    (* Lemma eq_cursor_refl: *)
    (*   abs_rel c t -> eq_cursor c c t. *)
    (* Proof. *)
    (*   unfold eq_cursor. *)
    (*   split3; auto. *)
    (* Qed. *)
  End Implication.
End AbstractTableFacts.

Module SortedListTable (KeyType: UsualOrderedType) <: ABSTRACT_TABLE KeyType.
  Definition key := KeyType.t.
  Definition table (elt: Type) := list (key * elt).
  Definition cursor (elt: Type) := Z.
  Definition allocator := list val.

  Module KeyFacts := OrderedTypeFacts KeyType.

  Import ListNotations.
  Section Types.
    Context {elt: Type}.
    (* Predicate rather than variable because of possible addresses in the data type *)
    Definition empty (a: allocator): table elt * allocator :=
      ([], a).

    Fixpoint make_cursor (k: key) (t: table elt): cursor elt :=
      match t with
      | [] => 0
      | (k', _) :: t' =>
        if KeyFacts.lt_dec k' k then
          1 + make_cursor k t'
        else
          0
      end.

    Instance option_key_inh: Inhabitant (option key) := None.
    Instance option_elt_inh: Inhabitant (option elt) := None.
    Instance option_binding_inh: Inhabitant (option (key * elt)) := None.

    Definition get (c: cursor elt) (t: table elt): option (key * elt) :=
      Znth c (map Some t).

    Definition get_key (c: cursor elt) (t: table elt): option key :=
      match get c t with
      | Some (k, _) => Some k
      | None => None
      end.

    Definition get_value (c: cursor elt) (t: table elt): option elt :=
      match get c t with
      | Some (_, v) => Some v
      | None => None
      end.

    Fixpoint put_aux (k: key) (v: elt) (t: table elt) :=
      match t with
      | (k', v') :: l' =>
        if KeyFacts.lt_dec k k' then
          (k, v) :: (k', v') :: l'
        else
          if KeyFacts.eq_dec k k' then
            (k, v) :: l'
          else
            (k', v') :: (put_aux k v l')
      | nil => (k, v) :: nil
      end.

    Definition put (k: key) (v: elt) (c: cursor elt) (table_with_allocator: table elt * allocator) :=
      let (t, a) := table_with_allocator in
      (c, (put_aux k v t, a)).

    Definition next_cursor (c: cursor elt) (t: table elt) :=
      if Z_lt_dec c (Zlength t) then c + 1 else c.
    Definition prev_cursor (c: cursor elt) (t: table elt) :=
      if Z_gt_dec c 0 then c - 1 else c.
    Definition first_cursor (t: table elt) := 0.
    Definition last_cursor (t: table elt) := Zlength t.
    
    Definition key_rel (k: key) (c: cursor elt) (t: table elt) := forall c',
      (0 <= c' < c -> exists k', get_key c' t = Some k' /\ KeyFacts.TO.lt k' k) /\
      (c <= c' < Zlength t -> exists k', get_key c' t = Some k' /\ ~ KeyFacts.TO.lt k' k).

    Definition eq_cursor (c1 c2: cursor elt) (t: table elt) := c1 = c2.
    Definition cursor_correct (c: cursor elt) := True.
    Definition table_correct (t: table elt) := Sorted KeyType.lt (map fst t).
    Definition abs_rel (c: cursor elt) (t: table elt) := table_correct t /\ 0 <= c <= Zlength t.

    Section Specs.
      Theorem abs_correct: forall t c,
        abs_rel c t -> cursor_correct c /\ table_correct t.
      Proof. firstorder. Qed.

      Theorem next_cursor_abs: forall t c,
          abs_rel c t -> abs_rel (next_cursor c t) t.
      Proof.
        (* This does not necessarily make sense at the end *)
        unfold abs_rel; unfold next_cursor; intros ? ? [].
        split; auto.
        split.
        - if_tac; omega.
        - if_tac.
          + omega.
          + omega.
      Qed.

      Theorem prev_cursor_abs: forall t c,
          abs_rel c t -> abs_rel (prev_cursor c t) t.
      Proof.
        (* This does not necessarily make sense at the end *)
        unfold abs_rel; unfold prev_cursor; intros ? ? [].
        split; auto.
        split.
        - if_tac; omega.
        - if_tac.
          + omega.
          + omega.
      Qed.

      Theorem first_cursor_abs: forall t,
          table_correct t -> abs_rel (first_cursor t) t.
      Proof.
        unfold abs_rel; unfold first_cursor; intros.
        split;
          [ auto | list_solve ].
      Qed.
        
      Theorem last_cursor_abs: forall t,
          table_correct t -> abs_rel (last_cursor t) t.
      Proof.
        unfold abs_rel; unfold last_cursor; intros.
        split;
          [ auto | list_solve ].
      Qed.
      
      Theorem get_last: forall t,
          get (last_cursor t) t = None.
      Proof.
        unfold get, last_cursor; intros.
        rewrite Znth_overflow.
        - reflexivity.
        - rewrite Zlength_map.
          rep_omega.
      Qed.

      Lemma table_correct_strong: forall t,
          table_correct t <-> StronglySorted KeyType.lt (map fst t).
      Proof.
        split; intros.
        - apply Sorted_StronglySorted;
            [ unfold Relations_1.Transitive; apply KeyType.lt_trans | auto ].
        - apply StronglySorted_Sorted.
          assumption.
      Qed.

      Lemma get_inrange: forall t c,
          abs_rel c t -> ~ eq_cursor (last_cursor t) c t -> exists kv, get c t = Some kv.
      Proof.
        unfold abs_rel, eq_cursor, last_cursor, get; intros.
        assert (0 <= c < Zlength t) by (change (cursor elt) with Z in *; list_solve).
        pose proof (Znth_In c (map Some t) ltac:(rewrite Zlength_map; list_solve)).
        destruct (Znth c (map Some t)) eqn:Heqn.
        + exists p.
          reflexivity.
        + clear H H0 H1 Heqn.
          exfalso.
          induction t.
          * inversion H2.
          * inversion H2; congruence.
      Qed.

      Lemma get_ge: forall t c k1 k2,
        abs_rel c t -> key_rel k1 c t -> get_key c t = Some k2 -> ~ KeyFacts.TO.lt k2 k1.
      Proof.
        unfold abs_rel, key_rel, get_key; intros.
        specialize (H0 c) as [_ ?].
        destruct (eq_dec c (last_cursor t)).
        + subst.
          rewrite get_last in H1.
          congruence.
        + unfold last_cursor in n.
          specialize (H0 ltac:(change (cursor elt) with Z in *; omega)) as [k2' []].
          rewrite H1 in H0.
          inversion H0.
          assumption.
      Qed.

      Theorem key_rel_eq_cursor: forall t c1 c2 k,
        key_rel k c1 t -> key_rel k c2 t ->
        abs_rel c1 t -> abs_rel c2 t ->
        eq_cursor c1 c2 t.
      Proof.
        unfold key_rel; unfold abs_rel; unfold eq_cursor.
        intros.
        destruct (eq_dec c1 c2); [ assumption | ].
        assert (c1 < c2 \/ c1 > c2) by (change (cursor elt) with Z in *; omega); clear n; destruct H3.
        - specialize (H0 c1) as [? _].
          specialize (H0 ltac:(omega)) as [k0 []].
          pose proof (get_ge _ _ _ _ H1 H H0).
          KeyFacts.order.
        - specialize (H c2) as [? _].
          specialize (H ltac:(omega)) as [k0 []].
          pose proof (get_ge _ _ _ _ H2 H0 H).
          KeyFacts.order.
      Qed.

      Theorem eq_cursor_get: forall t c1 c2,
        abs_rel c1 t ->
        abs_rel c2 t ->
        eq_cursor c1 c2 t ->
        get c1 t = get c2 t.
      Admitted.

      Lemma make_cursor_inrange: forall t k,
          0 <= make_cursor k t <= Zlength t.
      Proof.
        intros; unfold make_cursor.
        induction t as [ | [] ?]; intros.
        - rewrite Zlength_nil; omega.
        - if_tac.
          + rewrite Zlength_cons.
            omega.
          + list_solve.
      Qed.

      Lemma make_cursor_continuous: forall t k k' v',
          make_cursor k t <= make_cursor k (t ++ [(k', v')]) <= make_cursor k t + 1.
      Proof.
        induction t as [ | [] ?]; intros; simpl.
        - if_tac; omega.
        - specialize (IHt k0 k' v').
          if_tac; omega.
      Qed.

      Theorem make_cursor_abs: forall t k,
          table_correct t -> abs_rel (make_cursor k t) t.
      Proof.
        intros.
        induction t as [ | [] ?]; intros; simpl.
        - split; auto.
          rewrite Zlength_nil; omega.
        - split; auto.
          pose proof (make_cursor_inrange t k).
          if_tac.
          + rewrite Zlength_cons.
            omega.
          + rewrite Zlength_cons.
            omega.
      Qed.

      Theorem make_cursor_key: forall t k,
          table_correct t -> key_rel k (make_cursor k t) t.
      Proof.
        intros.
        unfold key_rel, make_cursor, get_key, get.
        induction t as [ | [] ?]; intros.
        - split; intros.
          + omega.
          + rewrite Zlength_nil in H0; omega.
        - split; intros; fold make_cursor in *.
          + if_tac in H0.
            * inv H.
              specialize (IHt ltac:(auto) (c' - 1)) as [? _].
              destruct (eq_dec c' 0).
              -- subst.
                 simpl.
                 exists k0.
                 auto.
              -- specialize (H ltac:(omega)) as [k' []].
                 simpl.
                 rewrite Znth_pos_cons by omega.
                 exists k'.
                 rewrite H.
                 auto.
            * omega.
          + if_tac in H0.
            * inv H.
              specialize (IHt ltac:(auto) (c' - 1)) as [_ ?].
              rewrite Zlength_cons in H0.
              specialize (H ltac:(omega)) as [k' []].
              exists k'.
              simpl.
              pose proof (make_cursor_inrange t k).
              rewrite Znth_pos_cons by omega.
              rewrite H.
              auto.
            * destruct (Znth c' (map Some ((k0, e) :: t))) eqn:Heqn.
              -- destruct p.
                 exists k1.
                 split; auto.
                 apply table_correct_strong in H.
                 inv H.
                 destruct (eq_dec c' 0).
                 ++ subst.
                    simpl in Heqn.
                    rewrite Znth_0_cons in Heqn.
                    inv Heqn.
                    KeyFacts.order.
                 ++ rewrite Forall_forall in H5.
                    simpl in Heqn.
                    rewrite Znth_pos_cons in Heqn by omega.
                    rewrite Zlength_cons in H0.
                    pose proof (Znth_In (c' - 1) (map Some t) ltac:(list_solve)).
                    assert (In k1 (map fst t)). {
                      rewrite Heqn in H.
                      clear -H.
                      induction t.
                      - simpl in H.
                        auto.
                      - inv H.
                        + inv H0.
                          simpl.
                          auto.
                        + simpl.
                          right.
                          auto.
                    }
                    specialize (H5 k1 H2).
                    KeyFacts.order.
              -- pose proof (Znth_In (c') (map Some ((k0, e) :: t)) ltac:(rewrite Zlength_map; omega)).
                 rewrite Heqn in H2.
                 clear - H2.
                 exfalso.
                 simpl in H2.
                 inv H2; [congruence | ].
                 induction t.
                 ++ inv H.
                 ++ apply IHt.
                    inv H; congruence.
      Qed.

      Lemma get_in_weak: forall t c k v,
          get c t = Some (k, v) ->
          In (k, v) t.
      Proof.
        intros.
        change (cursor elt) with Z in *.
        unfold get in H.
        destruct (Z_le_dec 0 c); [ | rewrite Znth_outofbounds in H by rep_omega; inv H].
        destruct (Z_le_gt_dec (Zlength t) c); [rewrite Znth_outofbounds in H by list_solve; inv H | ].
        pose proof (Znth_In c (map Some t) ltac:(list_solve)).
        rewrite H in H0.
        clear -H0.
        induction t.
        - inv H0.
        - inv H0.
          + inv H.
            left.
            reflexivity.
          + right.
            eauto.
      Qed.

      Theorem get_in: forall t c k v,
        abs_rel c t ->
        key_rel k c t ->
        In (k, v) t <->
        get c t = Some (k, v).
      Proof.
        induction t as [ | [] ?]; intros; split; intros.
        - inv H1.
        - unfold get in H1.
          simpl in H1.
          rewrite Znth_nil in H1.
          inv H1.
        - destruct (KeyType.eq_dec k k0) as [Heq | Heq]; change (KeyType.eq k k0) with (k = k0) in Heq.
          + subst.
            destruct (eq_dec c 0).
            * subst. unfold get.
              simpl.
              rewrite Znth_0_cons.
              f_equal.
              inv H.
              apply table_correct_strong in H2.
              inv H2.
              inv H1.
              -- assumption.
              -- rewrite Forall_forall in H6.
                 apply in_map with (f := fst) in H.
                 apply H6 in H.
                 simpl in H.
                 KeyFacts.order.
            * unfold key_rel in H0.
              specialize (H0 0) as [? _].
              inv H.
              specialize (H0 ltac:(change (cursor elt) with Z in *; omega)) as [k' []].
              unfold get_key, get in H.
              simpl in H.
              inv H.
              KeyFacts.order.
          + destruct (eq_dec c 0).
            * subst.
              exfalso.
              unfold key_rel in H0.
              inv H.
              (* [k < k0], [in_nth] *)
              apply table_correct_strong in H2.
              inv H2.
              assert (KeyType.lt k k0). {
                rewrite Forall_forall in H6.
                apply in_map with (f := fst) in H1.
                simpl in H1.
                inv H1; [congruence | ].
                apply H6 in H.
                assumption.
              }
              specialize (H0 0) as [_ ?].
              specialize (H0 ltac:(list_solve)) as [k' []].
              unfold get_key, get in H0.
              simpl in H0.
              inv H0.
              KeyFacts.order.
            * unfold get.
              simpl.
              inv H.
              rewrite Znth_pos_cons by (change (cursor elt) with Z in *; omega).
              apply IHt.
              -- apply table_correct_strong in H2.
                 inv H2.
                 apply table_correct_strong in H5.
                 split; [ assumption | ].
                 change (cursor elt) with Z in *.
                 rewrite Zlength_cons in H3.
                 list_solve.
              -- unfold key_rel in *.
                 intros; split; intros.
                 ++ specialize (H0 (c' + 1)) as [? _].
                    change (cursor elt) with Z in *.
                    specialize (H0 ltac:(omega)) as [k' []].
                    exists k'.
                    unfold get_key, get in H0.
                    simpl in H0.
                    rewrite Znth_pos_cons in H0 by omega.
                    replace (c' + 1 - 1) with c' in H0 by omega.
                    auto.
                 ++ specialize (H0 (c' + 1)) as [_ ?].
                    change (cursor elt) with Z in *.
                    rewrite Zlength_cons in *.
                    specialize (H0 ltac:(omega)) as [k' []].
                    exists k'.
                    unfold get_key, get in H0.
                    simpl in H0.
                    rewrite Znth_pos_cons in H0 by omega.
                    replace (c' + 1 - 1) with c' in H0 by omega.
                    auto.
              -- inv H1; congruence.
        - unfold get in H1.
          inv H.
          assert (c <> Zlength ((k, e) :: t)). {
            intro.
            rewrite Znth_overflow in H1 by
                (rewrite Zlength_map; change (cursor elt) with Z in *; omega).
            inv H1.
          }
          pose proof (Znth_In c (map Some ((k, e) :: t))
                              ltac:(rewrite Zlength_map; change (cursor elt) with Z in *; omega)).
          rewrite H1 in H4.
          clear -H4.
          inv H4.
          + inv H.
            left.
            auto.
          + right.
            induction t.
            * inv H.
            * inv H.
              -- left.
                 congruence.
              -- right.
                 auto.
      Qed.

      (* permute of get and insert operations *)
      (* Assume [key_rel] does entail [abs_rel] *)
      Theorem get_put_same: forall t c1 c2 k e a,
          abs_rel c1 (fst (snd (put k e c2 (t, a)))) ->
          abs_rel c2 t ->
          key_rel k c1 (fst (snd (put k e c2 (t, a)))) ->
          get c1 (fst (snd (put k e c2 (t, a)))) = Some (k, e).
      Proof.
        intros t c1 c2 k e a.
        generalize dependent c1.
        generalize dependent c2.
        generalize dependent k.
        generalize dependent e.
        generalize dependent a.
        induction t as [ | [] ?]; intros.
        - simpl.
          simpl in H.
          inv H.
          rewrite Zlength_cons in H3.
          simpl in H3.
          simpl in H1.
          assert (c1 = 0 \/ c1 = 1) by (change (cursor elt) with Z in *; omega).
          destruct H; subst.
          + reflexivity.
          + unfold key_rel in H1.
            specialize (H1 0) as [? _].
            specialize (H ltac:(omega)) as [? []].
            unfold get_key, get in H.
            simpl in H.
            inv H.
            KeyFacts.order.
        - simpl.
          simpl put in *.
          repeat if_tac.
          + destruct (eq_dec c1 0).
            * subst.
              unfold get.
              reflexivity.
            * unfold key_rel in H1.
              specialize (H1 0) as [? _].
              inv H.
              specialize (H1 ltac:(change (cursor elt) with Z in *; omega)) as [? []].
              simpl in H.
              unfold get_key, get in H.
              simpl in H.
              inv H.
              KeyFacts.order.
          + subst.
            destruct (eq_dec c1 0).
            * subst.
              reflexivity.
            * unfold key_rel in H1.
              specialize (H1 0) as [? _].
              inv H.
              specialize (H1 ltac:(change (cursor elt) with Z in *; omega)) as [? []].
              inv H.
              KeyFacts.order.
          + unfold put in IHt.
            specialize (IHt a e0 k0 0 (c1 - 1)).
            destruct (eq_dec c1 0).
            * subst.
              unfold key_rel in H1.
              specialize (H1 0) as [_ ?].
              simpl in H1.
              rewrite Zlength_cons in H1.
              specialize (H1 ltac:(change (cursor elt) with Z in *; list_solve)) as [? []].
              unfold get_key, get in H1.
              simpl in H1.
              inv H1.
              KeyFacts.order.
            * unfold get.
              simpl.
              inv H.
              rewrite Znth_pos_cons by (change (cursor elt) with Z in *; omega).
              unfold get in IHt.
              simpl in IHt.
              apply IHt.
              -- split.
                 ++ simpl in H4.
                    apply table_correct_strong in H4.
                    inv H4.
                    apply table_correct_strong in H7.
                    assumption.
                 ++ simpl in H5.
                    rewrite Zlength_cons in H5.
                    change (cursor elt) with Z in *.
                    omega.
              -- split.
                 ++ inv H0.
                    apply table_correct_strong in H.
                    inv H.
                    apply table_correct_strong in H8.
                    assumption.
                 ++ list_solve.
              -- split; intros.
                 ++ unfold key_rel in H1.
                    specialize (H1 (c' + 1)) as [? _].
                    specialize (H1 ltac:(omega)) as [k' []].
                    exists k'.
                    unfold get_key, get in *.
                    simpl in *.
                    rewrite Znth_pos_cons in H1 by omega.
                    replace (c' + 1 - 1) with c' in H1 by omega.
                    auto.
                 ++ unfold key_rel in H1.
                    specialize (H1 (c' + 1)) as [_ ?].
                    simpl in *.
                    rewrite Zlength_cons in H1.
                    specialize (H1 ltac:(omega)) as [k' []].
                    exists k'.
                    unfold get_key, get in *.
                    simpl in *.
                    rewrite Znth_pos_cons in H1 by (change (cursor elt) with Z in *; omega).
                    replace (c' + 1 - 1) with c' in H1 by omega.
                    auto.
      Qed.

      Lemma key_rel_0': forall k1 k2 e t,
          ~ KeyType.lt k1 k2 ->
          table_correct ((k1, e) :: t) ->
          key_rel k2 0 ((k1, e) :: t).
      Proof.
        intros.
        split; intros.
        - omega.
        - assert (exists kv, get c' ((k1, e) :: t) = Some kv). {
            apply get_inrange.
            - split; [ auto | omega ].
            - unfold eq_cursor, last_cursor.
              change (cursor elt) with Z in *.
              omega.
          }
          destruct H2 as [[k' v'] ?].
          apply table_correct_strong in H0.
          inv H0.
          eexists.
          split.
          + unfold get_key.
            rewrite H2.
            reflexivity.
          + destruct (KeyType.eq_dec k1 k'); change (KeyType.eq k1 k') with (k1 = k') in *.
            * subst.
              KeyFacts.order.
            * destruct (eq_dec c' 0).
              -- subst.
                 inv H2.
                 congruence.
              -- unfold get in H2.
                 simpl in H2.
                 rewrite Znth_pos_cons in H2 by omega.
                 assert (abs_rel (c' - 1) t). {
                   split.
                   - apply table_correct_strong.
                     assumption.
                   - rewrite Zlength_cons in H1.
                     list_solve.
                 }
                 assert (In (k', v') t). {
                   apply get_in_weak with (c := c' - 1).
                   assumption.
                 }
                 rewrite Forall_forall in H6.
                 apply in_map with (f := fst) in H3.
                 simpl in H3.
                 apply H6 in H3.
                 KeyFacts.order.
      Qed.

      Lemma key_rel_0: forall k e t,
          table_correct ((k, e) :: t) ->
          key_rel k 0 ((k, e) :: t).
      Proof.
        intros.
        split; intros.
        - omega.
        - assert (exists kv, get c' ((k, e) :: t) = Some kv). {
            apply get_inrange.
            - split; [ auto | omega ].
            - unfold eq_cursor, last_cursor.
              change (cursor elt) with Z in *.
              omega.
          }
          destruct H1 as [[k' v'] ?].
          apply table_correct_strong in H.
          inv H.
          eexists.
          split.
          + unfold get_key.
            rewrite H1.
            reflexivity.
          + destruct (KeyType.eq_dec k k'); change (KeyType.eq k k') with (k = k') in *.
            * subst.
              KeyFacts.order.
            * destruct (eq_dec c' 0).
              -- subst.
                 inv H1.
                 congruence.
              -- unfold get in H1.
                 simpl in H1.
                 rewrite Znth_pos_cons in H1 by omega.
                 assert (abs_rel (c' - 1) t). {
                   split.
                   - apply table_correct_strong.
                     assumption.
                   - rewrite Zlength_cons in H0.
                     omega.
                 }
                 assert (In (k', v') t). {
                   apply get_in_weak with (c := c' - 1).
                   assumption.
                 }
                 rewrite Forall_forall in H5.
                 apply in_map with (f := fst) in H2.
                 simpl in H2.
                 apply H5 in H2.
                 KeyFacts.order.
      Qed.

      Lemma key_rel_cons: forall k0 k v c t,
          table_correct ((k, v) :: t) ->
          abs_rel c t ->
          KeyType.lt k k0 ->
          key_rel k0 c t ->
          key_rel k0 (c + 1) ((k, v) :: t).
      Proof.
        split; intros.
        - destruct (eq_dec c 0).
          + subst.
            assert (c' = 0) by omega.
            subst.
            exists k.
            auto.
          + destruct (eq_dec c' 0).
            * subst.
              exists k.
              auto.
            * specialize (H2 (c' - 1)) as [? _].
              specialize (H2 ltac:(change (cursor elt) with Z in *; omega)) as [k' []].
              exists k'.
              unfold get_key, get in *.
              simpl.
              rewrite Znth_pos_cons by omega.
              auto.
        - specialize (H2 (c' - 1)) as [_ ?].
          rewrite Zlength_cons in H3.
          specialize (H2 ltac:(omega)) as [k' []].
          exists k'.
          unfold get_key, get in *.
          simpl.
          inv H0.
          rewrite Znth_pos_cons by omega.
          auto.
      Qed.

      Theorem get_eq (t1 t2: table elt):
        table_correct t1 ->
        table_correct t2 ->
        (forall k c1 c2,
            key_rel k c1 t1 ->
            abs_rel c1 t1 ->
            key_rel k c2 t2 ->
            abs_rel c2 t2 ->
            get c1 t1 = get c2 t2)
        -> t1 = t2.
      Proof.
        generalize dependent t2.
        induction t1 as [ | [] ?]; intros.
        - destruct t2 as [ | [] ?].
          + reflexivity.
          + specialize (H1 k 0 0).
            assert (key_rel k 0 []). {
              split; intros.
              - omega.
              - rewrite Zlength_nil in H2.
                omega.
            }
            assert (abs_rel 0 []). {
              split; intros.
              - assumption.
              - rewrite Zlength_nil.
                omega.
            }
            assert (key_rel k 0 ((k, e) :: t2)). {
              apply key_rel_0.
              assumption.
            }
            assert (abs_rel 0 ((k, e) :: t2)). {
              split; intros.
              - assumption.
              - list_solve.
            }
            specialize (H1 H2 H3 H4 H5).
            inv H1.
        - destruct t2 as [ | [] ?].
          + specialize (H1 k 0 0).
            assert (key_rel k 0 ((k, e) :: t1)). {
              apply key_rel_0.
              assumption.
            }
            assert (abs_rel 0 ((k, e) :: t1)). {
              split; intros.
              - assumption.
              - list_solve.
            }
            assert (key_rel k 0 []). {
              split; intros.
              - omega.
              - rewrite Zlength_nil in H4.
                omega.
            }
            assert (abs_rel 0 []). {
              split; intros.
              - assumption.
              - rewrite Zlength_nil.
                omega.
            }
            specialize (H1 H2 H3 H4 H5).
            inv H1.
          + remember (if KeyFacts.lt_dec k k0 then k else k0) as k'.
            assert (key_rel k' 0 ((k, e) :: t1)). {
              apply key_rel_0'.
              - if_tac in Heqk'; subst; KeyFacts.order.
              - assumption.
            }
            assert (abs_rel 0 ((k, e) :: t1)). {
              split; intros.
              - assumption.
              - list_solve.
            }
            assert (key_rel k' 0 ((k0, e0) :: t2)). {
              apply key_rel_0'.
              - if_tac in Heqk'; subst; KeyFacts.order.
              - assumption.
            }
            assert (abs_rel 0 ((k0, e0) :: t2)). {
              split; intros.
              - assumption.
              - list_solve.
            }
            pose proof (H1 _ _ _ H2 H3 H4 H5).
            inv H6.
            f_equal.
            destruct (nil_or_non_nil t1); destruct (nil_or_non_nil t2); subst.
            * unfold get.
              simpl.
              rewrite ?Znth_nil.
              reflexivity.
            * destruct t2 as [ | [] ?]; [ congruence | ].
              clear n.
              specialize (H1 k 1 1).
              assert (KeyFacts.TO.lt k0 k). {
                inv H5.
                apply table_correct_strong in H6.
                inv H6.
                inv H10.
                assumption.
              }
              assert (key_rel k 1 [(k0, e0)]). {
                split; intros.
                + assert (c' = 0) by omega.
                  subst.
                  exists k0.
                  split; auto.
                + change (Zlength _) with 1 in H7.
                  omega.
              }
              assert (abs_rel 1 [(k0, e0)]). {
                split; [auto | change (Zlength _) with 1; omega].
              }
              assert (key_rel k 1 ((k0, e0) :: (k, e) :: t2)). {
                split; intros.
                + assert (c' = 0) by omega.
                  subst.
                  exists k0.
                  split; auto.
                + pose proof (get_inrange
                                ((k0, e0) :: (k, e) :: t2)
                                c'
                                ltac:(split; [ auto | omega])
                                ltac:(unfold eq_cursor, last_cursor; change (cursor elt) with Z in *; omega)).
                  destruct H10 as [[] ?].
                  exists k1.
                  unfold get_key.
                  rewrite H10.
                  unfold get in H10.
                  simpl in H10.
                  rewrite Znth_pos_cons in H10 by omega.
                  pose proof (get_in_weak ((k, e) :: t2) (c' -1) k1 e1 H10).
                  inv H5.
                  apply table_correct_strong in H12.
                  inv H12.
                  inv H15.
                  rewrite Forall_forall in H17.
                  apply in_map with (f := fst) in H11.
                  simpl in H11.
                  destruct H11; auto.
              }
              assert (abs_rel 1 ((k0, e0) :: (k, e) :: t2)). {
                split; [auto | list_solve].
              }
              specialize (H1 H7 H8 H9 H10).
              inv H1.
            * destruct t1 as [ | [] ?]; [ congruence | ].
              clear n.
              specialize (H1 k 1 1).
              assert (KeyFacts.TO.lt k0 k). {
                inv H3.
                apply table_correct_strong in H6.
                inv H6.
                inv H10.
                assumption.
              }
              assert (key_rel k 1 [(k0, e0)]). {
                split; intros.
                + assert (c' = 0) by omega.
                  subst.
                  exists k0.
                  split; auto.
                + change (Zlength _) with 1 in H7.
                  omega.
              }
              assert (abs_rel 1 [(k0, e0)]). {
                split; [auto | change (Zlength _) with 1; omega].
              }
              assert (key_rel k 1 ((k0, e0) :: (k, e) :: t1)). {
                split; intros.
                + assert (c' = 0) by omega.
                  subst.
                  exists k0.
                  split; auto.
                + pose proof (get_inrange
                                ((k0, e0) :: (k, e) :: t1)
                                c'
                                ltac:(split; [ auto | omega])
                                ltac:(unfold eq_cursor, last_cursor; change (cursor elt) with Z in *; omega)).
                  destruct H10 as [[] ?].
                  exists k1.
                  unfold get_key.
                  rewrite H10.
                  unfold get in H10.
                  simpl in H10.
                  rewrite Znth_pos_cons in H10 by omega.
                  pose proof (get_in_weak ((k, e) :: t1) (c' -1) k1 e1 H10).
                  inv H3.
                  apply table_correct_strong in H12.
                  inv H12.
                  inv H15.
                  rewrite Forall_forall in H17.
                  apply in_map with (f := fst) in H11.
                  simpl in H11.
                  destruct H11; auto.
              }
              assert (abs_rel 1 ((k0, e0) :: (k, e) :: t1)). {
                split; [auto | list_solve].
              }
              specialize (H1 H9 H10 H7 H8).
              inv H1.
            * apply IHt1.
              -- apply table_correct_strong in H.
                 inv H.
                 apply table_correct_strong.
                 assumption.
              -- apply table_correct_strong in H0.
                 inv H0.
                 apply table_correct_strong.
                 assumption.
              -- intros.
                 destruct t1 as [ | [] ? ]; destruct t2 as [ | [] ? ]; try congruence.
                 clear H4 H2 H3 H5 n n0.
                 destruct (KeyFacts.lt_dec k0 k).
                 ++ apply key_rel_cons with (k := k0) (v := e0) in H6; auto.
                    apply key_rel_cons with (k := k0) (v := e0) in H8; auto.
                    assert (abs_rel (c1 + 1) ((k0, e0) :: (k1, e) :: t1)). {
                      split; auto.
                      inv H7.
                      rewrite ?Zlength_cons in *.
                      omega.
                    }
                    assert (abs_rel (c2 + 1) ((k0, e0) :: (k2, e1) :: t2)). {
                      split; auto.
                      inv H9.
                      rewrite ?Zlength_cons in *.
                      omega.
                    }
                    specialize (H1 _ _ _ H6 H2 H8 H3).
                    inv H7.
                    inv H9.
                    unfold get in *.
                    simpl in H1.
                    rewrite (Znth_pos_cons (c1 + 1)) in H1 by omega.
                    rewrite (Znth_pos_cons (c2 + 1)) in H1 by omega.
                    replace (c1 + 1 - 1) with c1 in H1 by (change (cursor elt) with Z in *; omega).
                    replace (c2 + 1 - 1) with c2 in H1 by (change (cursor elt) with Z in *; omega).
                    assumption.
                 ++ remember (if KeyFacts.lt_dec k1 k2 then k1 else k2) as k'.
                    specialize (H1 k' 1 1).
                    assert (c1 = 0). {
                      destruct (eq_dec c1 0); auto; exfalso.
                      specialize (H6 0) as [? _].
                      inv H7.
                      specialize (H2 ltac:(change (cursor elt) with Z in *; omega)) as [k' []].
                      inv H2.
                      apply table_correct_strong in H.
                      inv H.
                      inv H10.
                      KeyFacts.order.
                    }
                    subst c1.
                    assert (c2 = 0). {
                      destruct (eq_dec c2 0); auto; exfalso.
                      specialize (H8 0) as [? _].
                      inv H9.
                      specialize (H2 ltac:(change (cursor elt) with Z in *; omega)) as [k' []].
                      inv H2.
                      apply table_correct_strong in H0.
                      inv H0.
                      inv H10.
                      KeyFacts.order.
                    }
                    subst c2.
                    assert (KeyType.lt k0 k'). {
                      subst.
                      if_tac.
                      - apply table_correct_strong in H.
                        inv H.
                        inv H10.
                        KeyFacts.order.
                      - apply table_correct_strong in H0.
                        inv H0.
                        inv H10.
                        KeyFacts.order.
                    }
                    assert (key_rel k' 1 ((k0, e0) :: (k1, e) :: t1)). {
                      split; intros.
                      - assert (c' = 0) by omega.
                        subst.
                        exists k0.
                        split; auto.
                      - pose proof (get_inrange
                                      ((k0, e0) :: (k1, e) :: t1)
                                      c'
                                      ltac:(split; [ auto | omega])
                                      ltac:(unfold eq_cursor, last_cursor; change (cursor elt) with Z in *; omega)).
                        destruct H4 as [[] ?].
                        exists k3.
                        unfold get_key.
                        rewrite H4.
                        unfold get in H4.
                        simpl in H4.
                        rewrite Znth_pos_cons in H4 by omega.
                        pose proof (get_in_weak ((k1, e) :: t1) (c' -1) k3 e2 H4).
                        inv H7.
                        apply table_correct_strong in H10.
                        inv H10.
                        rewrite Forall_forall in H14.
                        apply in_map with (f := fst) in H5.
                        simpl in H5.
                        destruct H5; if_tac; split; auto; try KeyFacts.order.
                        apply H14 in H5.
                        KeyFacts.order.
                    }
                    assert (key_rel k' 1 ((k0, e0) :: (k2, e1) :: t2)). {
                      split; intros.
                      - assert (c' = 0) by omega.
                        subst.
                        exists k0.
                        split; auto.
                      - pose proof (get_inrange
                                      ((k0, e0) :: (k2, e1) :: t2)
                                      c'
                                      ltac:(split; [ auto | omega])
                                      ltac:(unfold eq_cursor, last_cursor; change (cursor elt) with Z in *; omega)).
                        destruct H5 as [[] ?].
                        exists k3.
                        unfold get_key.
                        rewrite H5.
                        unfold get in H5.
                        simpl in H5.
                        rewrite Znth_pos_cons in H5 by omega.
                        pose proof (get_in_weak ((k2, e1) :: t2) (c' -1) k3 e2 H5).
                        inv H9.
                        apply table_correct_strong in H11.
                        inv H11.
                        rewrite Forall_forall in H15.
                        apply in_map with (f := fst) in H10.
                        simpl in H10.
                        destruct H10; if_tac; split; auto; try KeyFacts.order.
                        apply H15 in H9.
                        KeyFacts.order.
                    }
                    assert (abs_rel 1 ((k0, e0) :: (k1, e) :: t1)) by (split; auto; list_solve).
                    assert (abs_rel 1 ((k0, e0) :: (k2, e1) :: t2)) by (split; auto; list_solve).
                    specialize (H1 H3 H5 H4 H10).
                    unfold get in H1.
                    simpl in H1.
                    rewrite ?(Znth_pos_cons 1) in H1 by omega.
                    change (1 - 1) with 0 in H1.
                    assumption.
      Qed.

      Theorem get_put_diff: forall t c1 c2 c3 k1 k2 e a,
        k1 <> k2 ->
        abs_rel c1 (fst (snd (put k2 e c2 (t, a)))) ->
        abs_rel c2 t ->
        abs_rel c3 t ->
        key_rel k1 c1 (fst (snd (put k2 e c2 (t, a)))) ->
        key_rel k1 c3 t ->
        get c1 (fst (snd (put k2 e c2 (t, a)))) = get c3 t.
      Proof.
      Admitted.

      Theorem empty_correct: forall a,
          table_correct (fst (empty a)).
      Proof.
        intros.
        constructor.
      Qed.

      Theorem simple_empty_correct:
        table_correct [].
      Proof.
        intros.
        constructor.
      Qed.

      Theorem put_correct: forall t c k e a,
          table_correct t -> table_correct (fst (snd (put k e c (t, a)))).
      Proof.
      Admitted.

      Theorem get_empty: forall c a,
          abs_rel c (fst (empty a)) -> get c (fst (empty a)) = None.
      Proof.
      Admitted.

      (* cursor movement with respect to the order of key *)
      Theorem next_prev: forall t c,
          abs_rel c t -> ~ eq_cursor c (last_cursor t) t -> eq_cursor c (prev_cursor (next_cursor c t) t) t.
      Proof.
      Admitted.
      Theorem prev_next: forall t c,
          abs_rel c t -> ~ eq_cursor c (first_cursor t) t -> eq_cursor c (next_cursor (prev_cursor c t) t) t.
      Proof.
      Admitted.
      Theorem next_order: forall t c k1 k2,
          ~ eq_cursor c (last_cursor t) t -> key_rel k1 c t -> key_rel k2 (next_cursor c t) t -> KeyType.lt k1 k2.
      Proof.
      Admitted.
      Theorem prev_order: forall t c k1 k2,
          ~ eq_cursor c (first_cursor t) t -> key_rel k1 c t -> key_rel k2 (prev_cursor c t) t -> KeyType.lt k2 k1.
      Proof.
      Admitted.
      Theorem next_compact: forall t c k1 k2 k3,
          ~ eq_cursor c (last_cursor t) t ->
          key_rel k1 c t -> key_rel k2 (next_cursor c t) t ->
          ~ key_rel k3 c t -> KeyType.lt k1 k3 /\ KeyType.lt k3 k2.
      Proof.
      Admitted.
      Theorem prev_compact: forall t c k1 k2 k3,
          ~ eq_cursor c (first_cursor t) t ->
          key_rel k1 c t -> key_rel k2 (prev_cursor c t) t ->
          ~ key_rel k3 c t -> KeyType.lt k2 k3 /\ KeyType.lt k3 k1.
      Proof.
      Admitted.
    End Specs.
  End Types.

  Theorem same_key_result {e1: Type} {e2: Type}:
    forall (t1: table e1) (t2: table e2) (c1: cursor e1) (c2: cursor e2) (k: KeyType.t),
      map fst t1 = map fst t2 ->
      key_rel k c1 t1 ->
      abs_rel c1 t1 ->
      key_rel k c2 t2 ->
      abs_rel c2 t2 ->
      get_key c1 t1 = get_key c2 t2.
  Proof.
    intros.
    assert (Zlength t1 = Zlength t2). {
      rewrite <- ?(Zlength_map _ _ fst).
      rewrite H.
      reflexivity.
    }
    generalize dependent c1.
    generalize dependent c2.
    generalize dependent t2.
    generalize dependent k.
    induction t1; intros; simpl in *.
    - destruct t2; [ | simpl in H; congruence].
      assert (c1 = 0). {
        destruct H1.
        change (cursor e1) with Z in *.
        rewrite Zlength_nil in H5.
        omega.
      }
      assert (c2 = 0). {
        destruct H3.
        change (cursor e2) with Z in *.
        rewrite Zlength_nil in H6.
        omega.
      }
      subst.
      unfold get_key, get.
      reflexivity.
    - destruct t2; simpl in *; [congruence | ].
      inv H.
      rewrite ?Zlength_cons in H4.
      assert (Zlength t1 = Zlength t2) by omega.
      clear H4.
      destruct a; destruct p; simpl in *; subst.
      change (cursor e1) with Z in *.
      change (cursor e2) with Z in *.
      destruct (eq_dec c1 0); destruct (eq_dec c2 0); simpl in *; subst.
      + reflexivity.
      + destruct H1. destruct H3.
        specialize (H2 0) as [? _].
        specialize (H2 ltac:(omega)) as [k' []].
        unfold get_key, get in H2.
        inv H2.
        specialize (H0 0) as [_ ?].
        specialize (H0 ltac:(list_solve)) as [k'' []].
        unfold get_key, get in H0.
        inv H0.
        KeyFacts.order.
      + destruct H1. destruct H3.
        specialize (H2 0) as [_ ?].
        specialize (H2 ltac:(list_solve)) as [k' []].
        unfold get_key, get in H2.
        inv H2.
        specialize (H0 0) as [? _].
        specialize (H0 ltac:(omega)) as [k'' []].
        unfold get_key, get in H0.
        inv H0.
        KeyFacts.order.
      + destruct H1. destruct H3.
        apply table_correct_strong in H3.
        simpl in H3.
        inv H3.
        apply table_correct_strong in H9.
        apply table_correct_strong in H1.
        simpl in H1.
        inv H1.
        apply table_correct_strong in H8.
        rewrite ?Zlength_cons in *.
        assert (key_rel k (c2 - 1) t2). {
          split; intros.
          - specialize (H2 (c' + 1)) as [? _].
            specialize (H2 ltac:(omega)) as [k' []].
            exists k'.
            unfold get_key, get in *; simpl in *.
            rewrite Znth_pos_cons in H2 by omega.
            replace (c' + 1 - 1) with c' in H2 by omega.
            eauto.
          - specialize (H2 (c' + 1)) as [_ ?].
            specialize (H2 ltac:(list_solve)) as [k' []].
            exists k'.
            unfold get_key, get in *; simpl in *.
            rewrite Znth_pos_cons in H2 by omega.
            replace (c' + 1 - 1) with c' in H2 by omega.
            eauto.
        }
        assert (key_rel k (c1 - 1) t1). {
          split; intros.
          - specialize (H0 (c' + 1)) as [? _].
            specialize (H0 ltac:(omega)) as [k' []].
            exists k'.
            unfold get_key, get in *; simpl in *.
            rewrite Znth_pos_cons in H0 by omega.
            replace (c' + 1 - 1) with c' in H0 by omega.
            eauto.
          - specialize (H0 (c' + 1)) as [_ ?].
            specialize (H0 ltac:(list_solve)) as [k' []].
            exists k'.
            unfold get_key, get in *; simpl in *.
            rewrite Znth_pos_cons in H0 by omega.
            replace (c' + 1 - 1) with c' in H0 by omega.
            eauto.
        }
        specialize (IHt1 k _ H7 H (c2 - 1) H1 ltac:(split; [eauto | omega])
                                  (c1 - 1) H3 ltac:(split; [eauto | omega])).
        unfold get_key, get in *.
        simpl.
        rewrite ?Znth_pos_cons by omega.
        assumption.
  Qed.
End SortedListTable.

Module Type CONCRETE_TABLE (KeyType: UsualOrderedType) <: ABSTRACT_TABLE KeyType.
  (* A concrete table requires all the features of an abstract table
   * (actually not, it does not require parametrized value), and additionally, it requires some rep predicates *)
  Include ABSTRACT_TABLE KeyType.
  Definition elt: Type := val.

  Parameter table_rep: table elt -> val -> mpred.
  (* should [cursor_rep] be some form of magic wand exposed to client, or just leave it there? *)
  Parameter cursor_rep: cursor elt -> table elt -> val -> mpred.
End CONCRETE_TABLE.

(* For now, only usual ordered types are proved to be flattenable *)
Module Type FLATTENABLE_TABLE (KeyType: UsualOrderedType) <: ABSTRACT_TABLE KeyType.
  Include ABSTRACT_TABLE KeyType.
  Module Flattened := SortedListTable KeyType.
  Section Spec.
    Context {elt: Type}.
    Parameter flatten: table elt -> Flattened.table elt.
    Axiom flatten_invariant: forall t,
        table_correct t ->
        Flattened.table_correct (flatten t) /\
        forall (k: key) (c1: cursor elt) (c2: Flattened.cursor elt),
          key_rel k c1 t -> Flattened.key_rel k c2 (flatten t) ->
          abs_rel c1 t -> Flattened.abs_rel c2 (flatten t) ->
          get c1 t = Flattened.get c2 (flatten t).
  End Spec.
End FLATTENABLE_TABLE.

Module FlattenableTableFacts (KeyType: UsualOrderedType) (FlattenableTable: FLATTENABLE_TABLE KeyType).
  Include FlattenableTable.
  Section Implication.
    Context {elt: Type}.
    Theorem put_permute (k: key) (v: elt) (c1: cursor elt) (c2: Flattened.cursor elt) (t: table elt) (l: list val) (a1 a2: allocator):
      table_correct t ->
      abs_rel c1 t ->
      Flattened.abs_rel c2 (flatten t) ->
      flatten (fst (snd (put k v c1 (t, a1)))) = fst (snd (Flattened.put k v c2 ((flatten t), a2))).
    Proof.
      pose proof (@flatten_invariant elt).
      intros.
      apply Flattened.get_eq.
      - specialize (H (fst (snd (put k v c1 (t, a1))))).
        specialize (H ltac:(apply put_correct; auto)).
        destruct H.
        assumption.
      - apply Flattened.put_correct.
        specialize (H t H0) as [? _].
        assumption.
      - intros.
        pose proof H.
        specialize (H (fst (snd (put k v c1 (t, a1))))).
        specialize (H ltac:(apply put_correct; auto)).
        destruct H.
        pose (c4 := make_cursor k0 (fst (snd (put k v c1 (t, a1))))).
        assert (key_rel k0 c4 (fst (snd (put k v c1 (t, a1))))) by (apply make_cursor_key; apply put_correct; auto).
        assert (abs_rel c4 (fst (snd (put k v c1 (t, a1))))) by (apply make_cursor_abs; apply put_correct; auto).
        erewrite <- H8 with (c2 := c4); eauto.
        + destruct (KeyType.eq_dec k0 k); change (KeyType.eq k0 k) with (k0 = k) in *.
          * subst.
            rewrite get_put_same; auto.
            rewrite Flattened.get_put_same; auto.
          * subst.
            pose (c4' := make_cursor k0 t).
            rewrite get_put_diff with (k1 := k0) (c7 := c4') by
                repeat first [
                         apply make_cursor_key
                       | apply make_cursor_abs
                       | apply put_correct
                       | solve [auto] ].
            specialize (H7 t H0) as [].
            pose (c3' := Flattened.make_cursor k0 (flatten t)).
            rewrite Flattened.get_put_diff with (k1 := k0) (c7 := c3') by
                repeat first [
                         solve [auto]
                       | apply Flattened.make_cursor_key
                       | apply Flattened.make_cursor_abs ].
            apply H11 with k0;
              repeat first [
                       solve [auto] 
                     | apply make_cursor_key
                     | apply make_cursor_abs
                     | apply Flattened.make_cursor_key
                     | apply Flattened.make_cursor_abs
                     ].
    Qed.
  End Implication.
End FlattenableTableFacts.
