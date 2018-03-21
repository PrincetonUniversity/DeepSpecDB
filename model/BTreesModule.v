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
 Definition V := Type.
 Definition table := forest V.
 Definition cursor := BTrees.cursor V.
 Definition b : nat. Admitted.
 Definition key := Z.
 Definition empty_t : table := (BTrees.nil V).
 Definition empty_c : cursor := [].
 Definition get (k: key) (m: table) : option V := lookup V b k m.
 Definition set (k: key) (v: V) (m: table) : table := insert V b k v (make_cursor V b k m []).
 Theorem gempty: forall k, get k empty_t = None.
   Proof. intros. unfold get. unfold empty. Admitted.
 Theorem gss: forall k v t,  get k (set k v t) = Some v.
   Proof. Admitted.
 Theorem gso: forall j k v t, j<>k -> get j (set k v t) = get j t.
   Proof. Admitted.
End BT_Table.