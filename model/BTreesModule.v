Require Import BTrees.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Export ListNotations.

(** Table version *)

Module Type CURSOR_TABLE.
 Parameter V: Type.
 Definition key := Z.
 Parameter table: Type.
 Parameter cursor : Type.
 Parameter empty_t: table.

 Parameter make_cursor: key -> table -> cursor.
 Parameter get_key: cursor -> option key.
 Parameter get: cursor -> option V.
 Parameter set: cursor -> V -> table. (* Should these return cursors instead? Since cursor holds all info of the table *)
 Parameter insert: cursor -> key -> V -> table.
 Parameter next: cursor -> cursor.
 Parameter prev: cursor -> cursor.
 Parameter first_cursor: table -> cursor.
 Parameter last_cursor: table -> cursor.

 Parameter abs_rel: table -> cursor -> Prop. (* Relationship between table and cursor *)
 Parameter key_rel: key -> cursor -> Prop. (* Is the key in this cursor's range? *)
  (* get_key c >= k /\ get_key (prev c) < k, with special cases for first_cursor and last_cursor *)
 Parameter cursor_correct: cursor -> Prop.
 Parameter table_correct: table -> Prop.

 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom first_rel: forall t,
       abs_rel t (first_cursor t).
 Axiom last_rel: forall t,
       abs_rel t (last_cursor t).
 Axiom next_rel: forall t c,
       abs_rel t c -> abs_rel t (next c).
 Axiom prev_rel: forall t c,
       abs_rel t c -> abs_rel t (prev c).
 Axiom correct_rel: forall t c,
       abs_rel t c -> (cursor_correct c <-> table_correct t).

 Axiom insert_correct: forall k v c,
       cursor_correct c -> key_rel k c -> table_correct (insert c k v).
 Axiom set_correct: forall v c,
       cursor_correct c -> table_correct (set c v).

 Axiom glast: forall t,        (* get-last *)
       get (last_cursor t) = None.
 Axiom gss: forall k v c,      (* get-set-same *)
       cursor_correct c -> get_key c = Some k -> get (make_cursor k (set c v)) = Some v.
 Axiom gso: forall j v c t,    (* get-set-other *)
       cursor_correct c -> abs_rel t c -> ~ key_rel j c -> get (make_cursor j (set c v)) = get (make_cursor j t).
 Axiom gis: forall k v c,      (* get-insert-same *)
       cursor_correct c -> key_rel k c -> get (make_cursor k (insert c k v)) = Some v.
 Axiom gio: forall j k v c t,    (* get-insert-other *)
       cursor_correct c -> key_rel k c -> ~ key_rel j c -> abs_rel t c -> get (make_cursor j (insert c k v)) = get (make_cursor j t).

 Axiom next_prev: forall c t,
       abs_rel t c -> ~ (c = last_cursor t) -> prev (next c) = c.
 Axiom prev_next: forall c t,
       abs_rel t c -> ~ (c = first_cursor t) -> next (prev c) = c.
 Axiom cursor_order: forall c k1 k2, (* I don't love the use of lt_key here *)
       cursor_correct c -> get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
End CURSOR_TABLE.


(** cursor version *)
Module Type MOD_CURSOR_TABLE.
 Parameter V: Type.
 Definition key := Z.
 Parameter table: Type.
 Parameter cursor : Type.
 Parameter empty_t: table.

 Parameter make_cursor: key -> table -> cursor.
 Parameter make_table: cursor -> table. (* new *)
 Parameter get_key: cursor -> option key.
 Parameter get: cursor -> option V.
 Parameter set: cursor -> V -> cursor. (* mod *)
 Parameter insert: cursor -> key -> V -> cursor. (* mod *)
 Parameter next: cursor -> cursor.
 Parameter prev: cursor -> cursor.
 Parameter first_cursor: table -> cursor.
 Parameter last_cursor: table -> cursor.

 Parameter abs_rel: table -> cursor -> Prop.
 Parameter key_rel: key -> cursor -> Prop.
 Parameter cursor_correct: cursor -> Prop.
 Parameter table_correct: table -> Prop.

 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom make_table_rel: forall t c, (* new *)
       abs_rel t c <-> make_table c = t.
 Axiom first_rel: forall t,
       abs_rel t (first_cursor t).
 Axiom last_rel: forall t,
       abs_rel t (last_cursor t).
 Axiom next_rel: forall t c,
       abs_rel t c -> abs_rel t (next c).
 Axiom prev_rel: forall t c,
       abs_rel t c -> abs_rel t (prev c).
 Axiom correct_rel: forall t c,
       abs_rel t c -> (cursor_correct c <-> table_correct t).

 Axiom insert_correct: forall k v c, (* mod *)
       cursor_correct c -> key_rel k c -> cursor_correct (insert c k v) /\ key_rel k c.
 Axiom set_correct: forall k v c, (* mod *) 
       cursor_correct c -> key_rel k c -> cursor_correct (set c v) /\ key_rel k c.

 Axiom glast: forall t,
       get (last_cursor t) = None.
 Axiom gss: forall k v c, (* mod *)
       cursor_correct c -> get_key c = Some k -> get (set c v) = Some v.
 Axiom gso: forall j v c t, (* mod *)
       cursor_correct c -> abs_rel t c -> ~ key_rel j c -> get (make_cursor j (make_table (set c v))) = get (make_cursor j t).
 Axiom gis: forall k v c, (* mod *)
       cursor_correct c -> key_rel k c -> get (insert c k v) = Some v /\ get_key (insert c k v) = Some k.
 Axiom gio: forall j k v c t, (* mod *)
       cursor_correct c -> key_rel k c -> ~ key_rel j c -> abs_rel t c ->
       get (make_cursor j (make_table (insert c k v))) = get (make_cursor j t).

 Axiom next_prev: forall c t,
       abs_rel t c -> ~ (c = last_cursor t) -> prev (next c) = c.
 Axiom prev_next: forall c t,
       abs_rel t c -> ~ (c = first_cursor t) -> next (prev c) = c.
 Axiom cursor_order: forall c k1 k2,
       cursor_correct c -> get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
End MOD_CURSOR_TABLE.

(** BTrees! *)

(* NOT up to date *)
Module BT_Table <: CURSOR_TABLE.
 Definition b : nat. Admitted.
 Definition key := Z.

 Definition V := Type.
 Definition table := forest V.
 Definition cursor := BTrees.cursor V.
 Definition empty_t : table := (BTrees.nil V).

 Definition make_cursor (k: key) (m: table) : cursor := BTrees.make_cursor V b k m [].
 Definition get_key (c: cursor) : option key := BTrees.get_key c.
 Definition get (c: cursor) : option V := BTrees.get c.
 Definition set (c: cursor) (v: V) : table := Btrees.set v c.
 Definition insert (c: cursor) (k: key) (v: V) : table := BTrees.insert V b k v c.
 Definition next (c: cursor) : cursor := BTrees.move_to_next c.
 Definition prev (c: cursor) : cursor := []. (* complete this *)
 Definition first_cursor (m: table) : cursor := []. (* complete this *)
 Definition last_cursor (m: table) : cursor := []. (* complete this *)

 Definition abs_rel (m: table) (c: cursor) : Prop := True. (* complete this *)
 Definition key_rel (k: key) (c: cursor) : Prop := True. (* complete this *)

 Theorem make_cursor_rel: forall t k,
   abs_rel t (make_cursor k t).
 Proof. Admitted.

 Theorem glast: forall t,        (* get-last *)
   get (last_cursor t) = None.
 Proof. Admitted.
 Theorem gss: forall k v c,      (* get-set-same *)
   get_key c = Some k -> get (make_cursor k (set c v)) = Some v.
 Proof. Admitted.
 Theorem gso: forall j v c t,    (* get-set-other *)
   abs_rel t c -> ~ key_rel j c -> get (make_cursor j (set c v)) = get (make_cursor j t).
 Proof. Admitted.
 Theorem gis: forall k v c,      (* get-insert-same *)
   key_rel k c -> get (make_cursor k (insert c k v)) = Some v.
 Proof. Admitted.
 Theorem gio: forall j k v c t,    (* get-insert-other *)
   key_rel k c -> ~ key_rel j c -> abs_rel t c -> get (make_cursor j (insert c k v)) = get (make_cursor j t).
 Proof. Admitted.

 Theorem next_prev: forall c t,
       abs_rel t c -> ~ (c = last_cursor t) -> prev (next c) = c.
 Proof. Admitted.
 Theorem prev_next: forall c t,
       abs_rel t c -> ~ (c = first_cursor t) -> next (prev c) = c.
 Proof. Admitted.
 Theorem cursor_order: forall c k1 k2, (* I don't love the use of lt_key here *)
       get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
 Proof. Admitted.
End BT_Table.