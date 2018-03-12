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
 Parameter empty_c: cursor.
 Parameter make_cursor: key -> table -> cursor.
 Parameter key_rel: key -> cursor -> bool.
 Parameter get: cursor -> option V.
 Parameter set: cursor -> V -> table.
 Parameter insert: cursor -> key -> V -> table.
 Parameter next: cursor -> cursor.
 Parameter prev: cursor -> cursor.
 Parameter abs_rel: table -> cursor -> Prop. (* Relationship between table and cursor *)
 Parameter cursor_valid: cursor -> Prop.
 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom make_cursor_empty: forall k,
       make_cursor k empty_t = empty_c.
 Axiom gempty:                 (* get-empty *)
       get empty_c = None.
 Axiom gss: forall k v t,      (* get-set-same *)
       get (make_cursor k (set (make_cursor k t) v)) = Some v.
 Axiom gso: forall j k v t,    (* get-set-other *)
       j <> k -> get (make_cursor j (set (make_cursor k t) v)) = get (make_cursor j t).
 Axiom gis: forall k v t,      (* get-insert-same *)
       get (make_cursor k (insert (make_cursor k t) k v)) = Some v.
 Axiom gio: forall j k v t,    (* get-insert-other *)
       j <> k -> get (make_cursor j (insert (make_cursor k t) k v)) = get (make_cursor j t).
 Axiom next_prev: forall c,
       cursor_valid c -> prev (next c) = c.
End CURSOR_TABLE.

(* Currently missing some parts of the module specification because of cursor-key question *)
Module BT_Table <: CURSOR_TABLE.
 Definition V := Type.
 Definition table := forest V.
 Definition cursor := BTrees.cursor V.
 Definition b : nat. Admitted.
 Definition key := Z.
 Definition empty : table := (BTrees.nil V).
 Definition get (k: key) (m: table) : option V := lookup V b k m.
 Definition set (k: key) (v: V) (m: table) : table := insert V b k v (make_cursor V b k m []).
 Theorem gempty: forall k, get k empty = None.
   Proof. intros. unfold get. unfold empty. Admitted.
 Theorem gss: forall k v t,  get k (set k v t) = Some v.
   Proof. Admitted.
 Theorem gso: forall j k v t, j<>k -> get j (set k v t) = get j t.
   Proof. Admitted.
End BT_Table.