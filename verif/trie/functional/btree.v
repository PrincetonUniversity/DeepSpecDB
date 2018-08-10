Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import VST.floyd.functional_base.
Require Import common.
Require Import DB.lemmas.

Require Import DB.functional.kv.
Require Import DB.functional.cursored_kv.

Module BTree (KeyType: UsualOrderedType) <: FLATTENABLE_TABLE KeyType.
  Definition key := KeyType.t.
  Parameter table: Type -> Type.
  Parameter cursor: Type -> Type.

  Module Flattened := SortedListTable KeyType.

  Section Types.
    Context {value: Type}.
    (* Predicate rather than variable because of possible addresses in the data type *)
    Parameter empty: table value -> Prop.

    (* Functions *)
    (* Sematics: cursor should point to a place where to the left, all keys are less than the key,
     * to the right, all keys are no less than the key *)
    (* Therefore [make_cursor] should always return one, but not always the expected one *)
    Parameter make_cursor: key -> table value -> cursor value.
    (* By [get] functions, we always access the first key to the right *)
    Parameter get: cursor value -> table value -> option (key * value).
    Definition get_key (c: cursor value) (t: table value): option key :=
      match get c t with
      | Some (k, _) => Some k
      | None => None
      end.

    Definition get_value (c: cursor value) (t: table value): option value :=
      match get c t with
      | Some (_, v) => Some v
      | None => None
      end.
    (* we do expect that the cursor is moved when insertion is performed,
     * but where it is afterwards remains to be discussed *)
    Parameter put: key -> value -> cursor value -> table value -> cursor value -> table value -> Prop.
    Parameter next_cursor: cursor value -> table value -> cursor value.
    Parameter prev_cursor: cursor value -> table value -> cursor value.
    Parameter first_cursor: table value -> cursor value.
    (* last cursor is defined to be one position past the table, which means maps to nothing *)
    Parameter last_cursor: table value -> cursor value.
    (* TODO: do we need a [move_cursor]?
     * From the client's view, it does not matter whether it is [make] or [move], but it might increase
     * difficulty in proof *)
    (* Parameter move_cursor: key -> cursor elt -> table elt -> cursor elt. *)

    (* Relations between keys, cursors and tables *)
    (* [abs_rel] means that the table and the cursor are binded together (might need better name) *)
    (* In implementation, it's translated to correct cursor with get tree from cursor works *)
    Parameter abs_rel: cursor value -> table value -> Prop.
    (* Do we need this? This just sounds like [abs_rel c t /\ get_key c t = Some k] *)
    (* Not true, in btree, the cursor created with non-existing keys will not return the key with [get_key],
     * but rather, a bunch of keys can still be associated with the cursor *)
    Parameter key_rel: key -> cursor value -> table value -> Prop.
    (* DO we need this again? What about [abs_rel c1 t /\ abs_rel c2 t /\ get_key c1 t = get_key c2 t] *)
    Parameter eq_cursor : cursor value -> cursor value -> table value -> Prop.
    (* Definition eq_cursor (c1 c2: cursor elt) (t: table elt) := *)
    (*   abs_rel c1 t /\ abs_rel c2 t /\ get_key c1 t = get_key c2 t. *)
    (* What do we need to ensure about the previous two definition? Should they be transitive? *)
    Parameter cursor_correct: cursor value -> Prop.
    Parameter table_correct: table value -> Prop.
    Parameter flatten: table value -> Flattened.table value.

    Section Specs.
      Variable t t1 t2: table value.
      Variable c c1 c2 c3 c4: cursor value. 
      Variable k k1 k2 k3: key.
      Variable v v1 v2: value.

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
      Axiom put_correct:
        abs_rel c1 t1 ->
        put k v c1 t1 c2 t2 ->
        table_correct t2.
      Axiom empty_correct:
        empty t ->
        table_correct t.

      (* permute of get and insert operations *)
      (* Assume [key_rel] does not entail [abs_rel] *)
      Axiom get_put_same:
        put k v c1 t1 c2 t2 ->
        abs_rel c1 t1 ->
        abs_rel c3 t2 ->
        key_rel k c3 t2 ->
        get c3 t2 = Some (k, v).

      Axiom get_put_diff:
        k1 <> k2 ->
        put k1 v c1 t1 c2 t2 ->
        abs_rel c1 t1 ->
        abs_rel c4 t1 ->
        key_rel k2 c4 t1 ->
        abs_rel c3 t2 ->
        key_rel k2 c3 t2 ->
        get c3 t2 = get c4 t1.

      (* get in specific conditions *)
      Axiom get_last:
        get (last_cursor t) t = None.
      Axiom get_empty:
        empty t ->
        abs_rel c t ->
        get c t = None.

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

    Axiom flatten_invariant: forall t,
        table_correct t ->
        Flattened.table_correct (flatten t) /\
        forall (k: key) (c1: cursor value) (c2: Flattened.cursor value),
          key_rel k c1 t -> Flattened.key_rel k c2 (flatten t) ->
          abs_rel c1 t -> Flattened.abs_rel c2 (flatten t) ->
          get c1 t = Flattened.get c2 (flatten t).
  End Types.
End BTree.
