(*  *)
Require Import index.
Require Import btrees.
Require Import btrees_sep.
Require Import Int.
Require Import BTrees.
Require Import BTreesModule.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Int.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Module BTree <: CURSOR_TABLE.
 Definition key := btrees.key.

 Definition lt_key := Int.lt. 
  
 Definition V := btrees.V.

 Definition table := btrees.relation unit. (* unit? X? *)
 Definition cursor := prod (btrees.cursor unit) (btrees.relation unit).
 Definition empty_t : table := btrees.empty_relation tt tt.

 Definition make_cursor (k: key) (m: table) : cursor :=
   (btrees.moveToKey unit (btrees.get_root m) k [], m).
 
 Definition get_table (c : cursor) : table := snd c.
 
 Definition get_key (c: cursor) : option key :=
   GetKey (fst c) (snd c).
   
 Definition get (c: cursor) : option V :=
   GetRecord (fst c) (snd c).
   
 Definition insert (c: cursor) (k: key) (v: V) : cursor :=
   RL_PutRecord (fst c) (snd c) k v tt [] tt.
   
 Definition next (c: cursor) : cursor :=
   (moveToNext (fst c) (snd c), snd c).
   
 Definition prev (c: cursor) : cursor :=
   (moveToPrev (fst c) (snd c), snd c).
   
 Definition first_cursor (m: table) : cursor :=
   (btrees.first_cursor (btrees.get_root m),m).
   
 Definition last_cursor (m: table) : cursor :=
   (btrees.last_cursor (btrees.get_root m),m).
 
 Definition abs_rel (m: table) (c: cursor) : Prop :=
   m = snd c.
   
 Definition key_rel (k: key) (c: cursor) : Prop := True. (* TODO *)
 
 Definition eq_cursor c1 c2 : Prop :=
   btrees.normalize (fst c1) (snd c2) = btrees.normalize (X:=unit) (fst c2) (snd c2) /\ snd c1 = snd c2.
   
 Definition cursor_correct (c: cursor) : Prop :=
   complete_cursor (fst c) (snd c).
 
 Definition table_correct (t: table) : Prop :=
   True.

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
End BTree.
