Require Import BTrees.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Export ListNotations.

(** Abstract module type *)
Module Type CURSOR_TABLE.
 Parameter V: Type.
 Parameter key : Type.
 Parameter lt_key: key -> key -> bool.
 Parameter table: Type.
 Parameter cursor : Type.
 Parameter empty_t: table.

 (* Functions of the implementation *)
 Parameter make_cursor: key -> table -> cursor.
 Parameter get_table: cursor -> table.
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
 Parameter eq_cursor : cursor -> cursor -> Prop.
 Parameter cursor_correct: cursor -> Prop.
 Parameter table_correct: table -> Prop.

 (* table-cursor relations *)
 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom get_table_rel: forall t c,
       abs_rel t c <-> get_table c = t.
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
       get (make_cursor k (get_table (insert c k v))) = Some v.
 Axiom gio: forall j k v c,
       cursor_correct c -> key_rel k c -> ~ key_rel j c ->
       get (make_cursor j (get_table (insert c k v))) =
       get (make_cursor j (get_table c)).

 (* cursor movement *)
 Axiom next_prev: forall c t,
       cursor_correct c -> abs_rel t c -> ~ (c = last_cursor t) -> eq_cursor c (prev (next c)).
 Axiom prev_next: forall c t,
       cursor_correct c -> abs_rel t c -> ~ (c = first_cursor t) -> eq_cursor c (next (prev c)).
 Axiom cursor_order: forall c k1 k2,
       cursor_correct c -> get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
End CURSOR_TABLE.

(** B+tree specific module *)
Module BT_Table <: CURSOR_TABLE.
 Definition b : nat. Admitted.
 Definition key := Z.
 Definition lt_key := BTrees.lt_key.

 Definition V := Type.
 Definition table := treelist V.
 Definition cursor := BTrees.cursor V.
 Definition empty_t : table := (BTrees.tl_nil V).

 Definition make_cursor (k: key) (m: table) : cursor := BTrees.make_cursor V k m.
 Definition get_table (c : cursor) : table := BTrees.get_treelist V c.
 Definition get_key (c: cursor) : option key := BTrees.get_key V c.
 Definition get (c: cursor) : option V := BTrees.get V c.
 Definition insert (c: cursor) (k: key) (v: V) : cursor := BTrees.insert V b k v c.
 Definition next (c: cursor) : cursor := BTrees.move_to_next V c.
 Definition prev (c: cursor) : cursor := BTrees.move_to_prev V c.
 Definition first_cursor (m: table) : cursor := BTrees.first_cursor V m.
 Definition last_cursor (m: table) : cursor := BTrees.last_cursor V m.

 Definition abs_rel (m: table) (c: cursor) : Prop := BTrees.abs_rel V m c.
 Definition key_rel (k: key) (c: cursor) : Prop := BTrees.key_rel V k c = true.
 Definition eq_cursor c1 c2 : Prop := cursor_elements V c1 = cursor_elements V c2.
 Definition cursor_correct (c: cursor) : Prop := BTrees.cursor_correct V b c.
 Definition table_correct (t: table) : Prop :=
  BTrees.balanced V t /\ BTrees.fanout V b t /\ BTrees.sorted V t.

 (* table-cursor relations *)
 Theorem make_cursor_rel: forall t k,
   abs_rel t (make_cursor k t).
 Proof. Admitted.
 Theorem get_table_rel: forall t c,
   abs_rel t c <-> get_table c = t.
 Proof. Admitted.
 Theorem first_rel: forall t,
   abs_rel t (first_cursor t).
 Proof. Admitted.
 Theorem last_rel: forall t,
   abs_rel t (last_cursor t).
 Proof. Admitted.
 Theorem next_rel: forall t c,
   abs_rel t c -> abs_rel t (next c).
 Proof. Admitted.
 Theorem prev_rel: forall t c,
   abs_rel t c -> abs_rel t (prev c).
 Proof. Admitted.
 Theorem correct_rel: forall t c,
   abs_rel t c -> (cursor_correct c <-> table_correct t).
 Proof. Admitted.

 (* correctness preservation *)
 Theorem insert_correct: forall k v c,
   cursor_correct c -> key_rel k c -> cursor_correct (insert c k v).
 Proof. Admitted.

 (* get/insert correctness *)
 Theorem glast: forall t,
   get (last_cursor t) = None.
 Proof. Admitted.
 Theorem gis: forall k v c,
   cursor_correct c -> key_rel k c ->
   get (make_cursor k (get_table (insert c k v))) = Some v.
 Proof. Admitted.
 Theorem gio: forall j k v c,
   cursor_correct c -> key_rel k c -> ~ key_rel j c ->
   get (make_cursor j (get_table (insert c k v))) =
   get (make_cursor j (get_table c)).
 Proof. Admitted.

 (* cursor movement *)
 Theorem next_prev: forall c t,
   cursor_correct c -> abs_rel t c -> ~ (c = last_cursor t) -> eq_cursor c (prev (next c)).
 Proof. Admitted.
 Theorem prev_next: forall c t,
   cursor_correct c -> abs_rel t c -> ~ (c = first_cursor t) -> eq_cursor c (next (prev c)).
 Proof. Admitted.
 Theorem cursor_order: forall c k1 k2,
   cursor_correct c -> get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
 Proof. Admitted.
End BT_Table.
