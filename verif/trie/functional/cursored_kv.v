(** * cursored_kv.v: Interface and Specification for general KV Store with ordered keys and cursors*)
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import VST.floyd.proofauto.
Require Import DB.common.
Require Import DB.functional.kv.

(* This file is mainly based on Brian's paper and his BTreesModule.v, with some improvement and generalization *)
(* Also, this file takes the FMap Module as reference for interface *)
Module Type ABSTRACT_TABLE (KeyType: UsualOrderedType).

  Definition key := KeyType.t.
  Hint Transparent key.
  Parameter table: Type -> Type.
  Parameter cursor: Type -> Type.

  Section Types.
    Context {elt: Type}.
    Parameter empty: table elt.

    (* Functions *)
    Parameter make_cursor: key -> table elt -> cursor elt.
    (* no more get_table, cause they are separated defs now *)
    Parameter get_key: cursor elt -> table elt -> option key.
    Parameter get: cursor elt -> table elt -> option elt.
    (* we do expect that the cursor is moved when insertion is performed,
     * but where it is afterwards remains to be discussed *)
    Parameter put: cursor elt -> elt -> table elt -> cursor elt * table elt.
    Parameter next_cursor: cursor elt -> table elt -> cursor elt.
    Parameter prev_cursor: cursor elt -> table elt -> cursor elt.
    Parameter first_cursor: table elt -> cursor elt.
    (* last cursor is defined to be one position past the table, which means maps to nothing *)
    Parameter last_cursor: table elt -> cursor elt.
    (* TODO: do we need a [move_cursor]?
     * From the client's view, it does not matter whether it is [make] or [move], but it might increase
     * difficulty in proof *)
    Parameter move_cursor: key -> cursor elt -> table elt -> cursor elt.


    (* Correctness Relations *)
    (* originally [abs_rel], meaning that the table and the cursor are binded together (might need better name) *)
    (* In implementation, it's translated to correct cursor with get tree from cursor works *)
    Parameter bind_rel: cursor elt -> table elt -> Prop.
    (* Do we need this? This just sounds like [bind_rel c t /\ get_key c t = Some k] *)
    Parameter key_rel: key -> cursor elt -> table elt -> Prop.
    (* DO we need this again? What about [bind_rel c1 t /\ bind_rel c2 t /\ get_key c1 t = get_key c2 t] *)
    Parameter eq_cursor : cursor elt -> cursor elt -> table elt -> Prop.
    (* What do we need to ensure about the previous two definition? Should they be transitive? *)
    (* This might make sense since *)
    Parameter cursor_correct: cursor elt -> Prop.
    Parameter table_correct: table elt -> Prop.

    Section Specs.
      Variable t: table elt.
      Variable c c1 c2 c3: cursor elt.
      Variable k k1 k2 k3: key.
      Variable e e1 e2: elt.
      Hypothesis Htable_correct: table_correct t.
      (* table-cursor relations *)
      (* We need to make sure that the cursor and the table are actually working with each other *)
      Axiom make_cusor_binded: bind_rel (make_cursor k t) t.
      Axiom put_bind:
        let (new_cursor, new_table) := put c e t in
        bind_rel new_cursor new_table.
      (* TODO: What about at the end of range? *)
      Axiom next_cursor_bind: bind_rel c t -> bind_rel (next_cursor c t) t.
      Axiom prev_cursor_bind: bind_rel c t -> bind_rel (prev_cursor c t) t.
      Axiom first_cursor_bind: bind_rel (first_cursor t) t.
      Axiom last_cursor_bind: bind_rel (last_cursor t) t.
      Axiom move_cursor_bind: bind_rel c t -> bind_rel (move_cursor k c t) t.

      (* TODO: is this proper? *)
      Axiom key_bind: key_rel k c t -> bind_rel c t.

      (* permute of get and insert operations *)
      (* Assume [key_rel] does entail [bind_rel] *)
      Axiom get_put_same:
        key_rel k c1 (snd (put c2 e t)) ->
        key_rel k c2 t ->
        get c1 (snd (put c2 e t)) = Some e.
      Axiom get_put_diff:
        k1 <> k2 ->
        key_rel k1 c1 (snd (put c2 e t)) ->
        key_rel k2 c2 t ->
        key_rel k1 c3 t ->
        get c1 (snd (put c2 e t)) = get c3 t.

      (* get in specific conditions *)
      Axiom get_last:
        get (last_cursor t) t = None.
      Axiom get_empty:
        get c empty = None.

      (* Cursor creation and keys *)

      Axiom make_cursor_key:
        key_rel k (make_cursor k t) t.
      Axiom move_cursor_key:
        key_rel k (move_cursor k c t) t.

      (* cursor movement with respect to the order of key *)
      Axiom next_prev:
        bind_rel c t -> ~ eq_cursor c (last_cursor t) t -> eq_cursor c (prev_cursor (next_cursor c t) t) t.
      Axiom prev_next:
        bind_rel c t -> ~ eq_cursor c (first_cursor t) t -> eq_cursor c (next_cursor (prev_cursor c t) t) t.
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

Module Type CONCRETE_TABLE (KeyType: UsualOrderedType) <: ABSTRACT_TABLE KeyType.
  (* A concrete table requires all the features of an abstract table
   * (actually not, it does not require parametrized value), and additionally, it requires some rep predicates *)
  Include ABSTRACT_TABLE KeyType.
  Definition elt: Type := val.

  Parameter table_rep: table elt -> val -> mpred.
  Parameter cursor_rep: cursor elt -> table elt -> val -> mpred.
  Section Specs.
    Variable ttable tcursor: type.
    Definition new_cursor: funspec :=
      WITH t: table elt, pt: val
      PRE [ 1%positive OF tptr ttable ]
      PROP (table_correct t)
      LOCAL (temp 1%positive pt)
      SEP (table_rep t pt)
      POST [ tptr tcursor ]
      EX p': val, EX c: cursor elt,
      PROP (eq_cursor (first_cursor t) c t)
      LOCAL (temp ret_temp p')
      SEP (table_rep t pt; cursor_rep c t p').

    (* TODO: should I define what property is expected here? *)
    (* thing like:
     * [
          WITH t: table elt, c: cursor elt, v: elt,
               pt: val, pc: val
          PRE [_table OF tptr ttable, _cursor OF tptr tcursor]
          PROP (get c t = Some v)
          LOCAL (local _table pt; local _cursor pc)
          SEP (table_rep t pt; cursor_rep t pc)
          POST [ telt ]
          PROP ()
          LOCAL (local ret_temp v)
          SEP (table_rep t pt; cursor_rep t pc)
          ]
     *)
    (* problems: the return type telt cannot be determined well *)

    (* TODO: do we always need two instance of such module? One for the abstract model one for the rep relation? *)
  End Specs.
End CONCRETE_TABLE.

(* For now, only usual ordered types are proved to be flattenable *)
Module Type FLATTENABLE_CONCRETE_TABLE (KeyType: UsualOrderedType) <: ABSTRACT_TABLE KeyType.
  Include ABSTRACT_TABLE KeyType.
  Module Flattened := SortedListTable KeyType.
  Section Spec.
    Context {elt: Type}.
    Parameter flatten: table elt -> Flattened.table elt.
    Axiom flatten_invariant: forall t,
        Flattened.sorted (flatten t) /\
        forall (k: key) (c: cursor elt), key_rel k c t -> get c t = Flattened.get k (flatten t).

    Theorem put_permute (k: key) (v: elt) (c: cursor elt) (t: table elt):
      key_rel k c t ->
      flatten (snd (put c v t)) = Flattened.put k v (flatten t).
    Proof.
      pose proof flatten_invariant.
      intros.
      apply Flattened.get_eq.
      - intros.
        pose proof H.
        specialize (H (snd (put c v t))).
        inv H.
        pose (c' := make_cursor k (snd (put c v t))).
        pose proof (make_cursor_key (snd (put c v t)) k).
        pose (c'' := make_cursor k0 (snd (put c v t))).
        specialize (H3 k0 c'' ltac:(apply make_cursor_key; auto)).
        rewrite <- H3.
        destruct (KeyType.eq_dec k k0); change (KeyType.eq k k0) with (k = k0) in *.
        + subst.
          rewrite Flattened.get_put_same.
          erewrite get_put_same; eauto.
        + rewrite Flattened.get_put_diff by auto.
          pose (c''' := make_cursor k0 t).
          rewrite get_put_diff with (c3 := c''') (k1 := k0) (k2 := k); auto.
          * specialize (H1 t).
            inv H1.
            apply H5.
            apply make_cursor_key.
          * apply make_cursor_key.
          * apply make_cursor_key.
      - specialize (H (snd (put c v t))).
        inv H.
        assumption.
      - apply Flattened.put_sorted.
        specialize (H t).
        inv H.
        assumption.
    Qed.
  End Spec.
End FLATTENABLE_CONCRETE_TABLE.
