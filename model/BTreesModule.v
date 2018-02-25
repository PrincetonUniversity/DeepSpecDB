Require Import BTrees.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Export ListNotations.

Module Type CURSOR_TABLE.
 Parameter V: Type.
 Parameter table: Type.
 Parameter cursor : Type.
 Parameter b : nat.
 Definition key := Z.
 Parameter empty_t: table.
 Parameter empty_c: cursor.
 Parameter make_cursor: key -> table -> cursor.
 Parameter get: cursor -> option V.
 Parameter set: cursor -> V -> table.
 Parameter next: cursor -> cursor.
 Parameter abs_rel: table -> cursor -> Prop. (* Relationship between table and cursor *)
 Axiom make_cursor_rel: forall t k,
       abs_rel t (make_cursor k t).
 Axiom rel_empty:
       abs_rel empty_t empty_c. (* Is this good? Or should I tie it to make_cursor? Is this even needed? *)
 Axiom gempty:                 (* get-empty *)
       get empty_c = None.
 Axiom gss: forall k v t,      (* get-set-same *)
      get (make_cursor k (set (make_cursor k t) v)) = Some v. (* Should I tie this to the rel instead? *)
 Axiom gso: forall j k v t,    (* get-set-other *)
      j <> k -> get (make_cursor j (set (make_cursor k t) v)) = get (make_cursor j t).
 (* Axiom about next? What is the abstract spec for "next thing"? *)
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