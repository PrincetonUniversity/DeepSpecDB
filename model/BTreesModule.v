Require Import BTrees.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Export ListNotations.

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

 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).

 Axiom glast: forall t,        (* get-last *)
       get (last_cursor t) = None.
 Axiom gss: forall k v c,      (* get-set-same *)
       get_key c = Some k -> get (make_cursor k (set c v)) = Some v.
 Axiom gso: forall j v c t,    (* get-set-other *)
       abs_rel t c -> ~ key_rel j c -> get (make_cursor j (set c v)) = get (make_cursor j t).
 Axiom gis: forall k v c,      (* get-insert-same *)
       key_rel k c -> get (make_cursor k (insert c k v)) = Some v.
 Axiom gio: forall j k v c t,    (* get-insert-other *)
       key_rel k c -> ~ key_rel j c -> abs_rel t c -> get (make_cursor j (insert c k v)) = get (make_cursor j t).

 Axiom next_prev: forall c t,
       abs_rel t c -> ~ (c = last_cursor t) -> prev (next c) = c.
 Axiom prev_next: forall c t,
       abs_rel t c -> ~ (c = first_cursor t) -> next (prev c) = c.
 Axiom cursor_order: forall c k1 k2, (* I don't love the use of lt_key here *)
       get_key c = Some k1 -> get_key (next c) = Some k2 -> lt_key k1 k2 = true.
End CURSOR_TABLE.

(* NOT up to date *)
Module BT_Table <: CURSOR_TABLE.
 Definition b : nat. Admitted.
 Definition key := Z.

 Definition V := Type.
 Definition table := forest V.
 Definition cursor := BTrees.cursor V.
 Definition empty_t : table := (BTrees.nil V).

 Definition make_cursor (k: key) (m: table) : cursor := BTrees.make_cursor V b k m [].
 Definition get_key (c: cursor) : option key := None. (* complete this *)
 Definition get (c: cursor) : option V := None. (* complete this *) (* lookup V b k m. *)
 Definition set (c: cursor) (v: V) : table := empty_t. (* complete this *)
 Definition insert (c: cursor) (k: key) (v: V) : table := insert V b k v c.
 Definition next (c: cursor) : cursor := []. (* complete this *)
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