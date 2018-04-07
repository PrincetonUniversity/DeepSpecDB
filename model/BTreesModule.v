Require Import BTrees.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Export ListNotations.

(** Abstract module type *)
Module Type CURSOR_TABLE.
 Parameter V: Type.
 Definition key := Z.
 Parameter table: Type.
 Parameter cursor : Type.
 Parameter empty_t: table.

 (* Functions of the implementation *)
 Parameter make_cursor: key -> table -> cursor.
 Parameter make_table: cursor -> table.
 Parameter get_key: cursor -> option key.
 Parameter get: cursor -> option V.
 Parameter insert: cursor -> key -> V -> cursor.
 Parameter next: cursor -> cursor.
 Parameter prev: cursor -> cursor.
 Parameter first_cursor: table -> cursor.
 Parameter last_cursor: table -> cursor.

 (* Props defining correctness *)
 Parameter abs_rel: table -> cursor -> Prop.
 Parameter key_rel: key -> cursor -> Prop.
 Parameter cursor_correct: cursor -> Prop.
 Parameter table_correct: table -> Prop.

 (* table-cursor relations *)
 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom make_table_rel: forall t c,
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

 (* correctness preservation *)
 Axiom insert_correct: forall k v c,
       cursor_correct c -> key_rel k c -> cursor_correct (insert c k v).

 (* get/insert correctness *)
 Axiom glast: forall t,
       get (last_cursor t) = None.
 Axiom gis: forall k v c,
       cursor_correct c -> key_rel k c ->
       get (make_cursor k (make_table (insert c k v))) = Some v.
 Axiom gio: forall j k v c t,
       cursor_correct c -> key_rel k c -> ~ key_rel j c -> abs_rel t c ->
       get (make_cursor j (make_table (insert c k v))) = get (make_cursor j t).

 (* cursor movement *)
 Axiom next_prev: forall c t,
       abs_rel t c -> ~ (c = last_cursor t) -> prev (next c) = c.
 Axiom prev_next: forall c t,
       abs_rel t c -> ~ (c = first_cursor t) -> next (prev c) = c.
 Axiom cursor_order: forall c k1 k2,
       cursor_correct c -> get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
End CURSOR_TABLE.

(** B+tree specific module *)

(* NOT up to date *)
Module BT_Table <: CURSOR_TABLE.
 Definition b : nat. Admitted.
 Definition key := Z.

 Definition V := Type.
 Definition table := treelist V.
 Definition cursor := BTrees.cursor V.
 Definition empty_t : table := (BTrees.tl_nil V).

 Definition make_cursor (k: key) (m: table) : cursor := BTrees.make_cursor V k m [].
 Definition get_key (c: cursor) : option key := BTrees.get_key V c.
 Definition get (c: cursor) : option V := BTrees.get V c.
 Definition set (c: cursor) (v: V) : table := BTrees.set V b v c.
 Definition insert (c: cursor) (k: key) (v: V) : table := BTrees.insert V b k v c.
 Definition next (c: cursor) : cursor := BTrees.move_to_next V c.
 Definition prev (c: cursor) : cursor := []. (* complete this *)
 Definition first_cursor (m: table) : cursor := []. (* complete this *)
 Definition last_cursor (m: table) : cursor := []. (* complete this *)

 Definition abs_rel (m: table) (c: cursor) : Prop := True. (* complete this *)
 Definition key_rel (k: key) (c: cursor) : Prop := True. (* complete this *)
 Definition cursor_correct (c: cursor) : Prop := True. (* complete this *)
 Definition table_correct (t: table) : Prop := True. (* complete this *)

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