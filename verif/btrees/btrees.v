(** * btrees.v : Formal Model of BTrees  *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.

(**
    BTREES FORMAL MODEL
 **)

Ltac evaluate x :=
  let x := eval compute in x in exact x.

(* Maximum number of entries in a node *)
Definition Fanout := 15%Z.
Lemma Fanout_eq : Fanout = ltac:(evaluate Fanout).
Proof. reflexivity. Qed.
Hint Rewrite Fanout_eq : rep_omega.
(* Middle = Fanout +1  /2, for splitting nodes *)
Definition Middle := ltac:(evaluate ((Fanout+1)/2)).
Lemma Middle_eq: Middle = ltac:(evaluate Middle).
Proof. reflexivity. Qed.
Global Opaque Fanout.
Global Opaque Middle.
Hint Rewrite Middle_eq : rep_omega.

(* Maximum tree depth *)
Definition MaxTreeDepth := 20%Z.
Lemma MTD_eq : MaxTreeDepth = ltac:(evaluate MaxTreeDepth).
Proof. reflexivity. Qed.
Global Opaque MaxTreeDepth.
Hint Rewrite MTD_eq : rep_omega.

Definition key := Ptrofs.int.
Definition V := Ptrofs.int.
Definition k_ := Ptrofs.unsigned.
Definition v_ := Ptrofs.unsigned.

Lemma key_unsigned_repr : forall key,
    Ptrofs.unsigned (Ptrofs.repr (k_ key)) = (k_ key).
Proof.
  intros. apply Ptrofs.unsigned_repr. unfold k_. rep_omega.
Qed.  

Lemma record_unsigned_repr : forall rec,
    Ptrofs.unsigned (Ptrofs.repr (v_ rec)) = (v_ rec).
Proof.
  intros. apply Ptrofs.unsigned_repr. unfold v_. rep_omega.
Qed.

(* Variable X:Type.                (* val or unit *) *)

(* Btree Types *)
Inductive entry (X:Type): Type :=
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: option (node X) -> listentry X -> bool -> bool -> bool -> X -> node X
with listentry (X:Type): Type :=
     | nil: listentry X
     | cons: entry X -> listentry X -> listentry X.

Definition cursor (X:Type): Type := list (node X * Z). (* ancestors and index *)
Definition relation (X:Type): Type := node X * X.  (* root and address *)

(* Abstracting a Btree to an ordered list of (key,value) pairs *)
Fixpoint abs_node {X:Type} (n:node X) : list (key * V) :=
  match n with
    btnode o le isLeaf First Last x =>
    match o with
    | Some n' => abs_node n' ++ abs_le le
    | None => abs_le le
    end
  end
with abs_le {X:Type} (le:listentry X) : list (key * V) :=
       match le with
       | nil => []
       | cons e le' => abs_entry e ++ abs_le le'
       end
with abs_entry {X:Type} (e:entry X) : list (key * V) :=
       match e with
       | keyval k v x => [(k,v)]
       | keychild k n => abs_node n
       end.         

(* Btrees depth *)
Fixpoint node_depth {X:Type} (n:node X) : Z :=
  match n with
    btnode ptr0 le _ _ _ _ => Z.max (listentry_depth le)
                                (match ptr0 with
                                 | None => 0
                                 | Some n' => Z.succ (node_depth n') end)
  end
with listentry_depth {X:Type} (le:listentry X) : Z :=
       match le with
       | nil => 0
       | cons e le' => Z.max (entry_depth e) (listentry_depth le')
       end
with entry_depth {X:Type} (e:entry X) : Z :=
       match e with
       | keyval _ _ _ => 0
       | keychild _ n => Z.succ (node_depth n)
       end.

(* root of the relation *)
Definition get_root {X:Type} (rel:relation X) : node X := fst rel.

(* cursor depth used for putentry. the entry_depth should be equal the cursor depth *)
Definition cursor_depth {X:Type} (c:cursor X) (r:relation X) : Z :=
  match c with
  | [] => Z.succ (node_depth (get_root r))
  | (n,i)::c' => node_depth n
  end.

(* Number of Records *)
Fixpoint node_numrec {X:Type} (n:node X) : Z :=
  match n with
    btnode ptr0 le _ _ _ _ => listentry_numrec le + match ptr0 with
                                                   | None => 0
                                                   | Some n' => node_numrec n'
                                                   end
  end
with listentry_numrec {X:Type} (le:listentry X) : Z :=
       match le with
       | nil => 0
       | cons e le' => entry_numrec e + listentry_numrec le'
       end
with entry_numrec {X:Type} (e:entry X) : Z :=
       match e with
       | keyval _ _ _ => 1
       | keychild _ n => node_numrec n
       end.         

(* numRecords of the relation *)
Definition get_numrec {X:Type} (rel:relation X) : Z := node_numrec (get_root rel).

(* depth of the relation *)
Definition get_depth {X:Type} (rel:relation X) : Z := node_depth (get_root rel).
  
(* Index at the current level *)
Definition entryIndex {X:Type} (c:cursor X) : Z :=
  match c with
  | [] => 0
  | (n,i)::c' => i
  end.

(* Ancestor at the current level *)
Definition currNode {X:Type} (c:cursor X) (r:relation X) : node X :=
  match c with
  | [] => get_root r
  | (n,i)::c' => n
  end.

(* number of keys in a listentry *)
Fixpoint numKeys_le {X:Type} (le:listentry X) : Z :=
  match le with
  | nil => 0
  | cons _ le' => Z.succ (numKeys_le le')
  end.

(* number of keys in a node *)
Definition numKeys {X:Type} (n:node X) : Z :=
  match n with btnode ptr0 le _ _ _ x => numKeys_le le end.

(* is a cursor valid? invalid if the cursor is past the very last key *)
Definition isValid {X:Type} (c:cursor X) (r:relation X): bool :=
  match currNode c r
  with btnode ptr0 le b First Last x =>
       match Last with
       | false => true
       | true =>
         match (Z.eqb (entryIndex c) (numKeys_le le)) with
               | false => true
               | true => false
                end
       end
  end.

(* does the cursor point to the very first key? *)
Definition isFirst {X:Type} (c:cursor X) : bool :=
  match c with
  | [] => false
  | (n,i)::c' =>
    match n with btnode ptr0 le isLeaf First Last x =>
                 First && (Z.eqb i 0)
    end
  end.

(* Is a given node a leaf node *)
Definition LeafNode {X:Type} (n:node X) : Prop :=
  match n with btnode _ _ b _ _ _ =>
               match b with
               | true => True
               | false => False
               end
  end.

(* Is a given node an intern node *)
Definition InternNode {X:Type} (n:node X) : Prop :=
  match n with btnode _ _ b _ _ _ =>
               match b with
               | true => False
               | false => True
               end
  end.

(* Leaf entries have values *)
Definition LeafEntry {X:Type} (e:entry X) : Prop :=
  match e with
  | keyval _ _ _ => True
  | keychild _ _ => False
  end.

(* nth entry of a listentry *)
Fixpoint nth_entry_le {X:Type} (i:Z) (le:listentry X): option (entry X) :=
  if zlt i 0 then None
  else if zle i 0
  then match le with
         | nil => None
         | cons e _ => Some e
         end
  else match le with
            | nil => None
            | cons _ le' => nth_entry_le (Z.pred i) le'
            end.

Lemma numKeys_le_nonneg: forall {X: Type} (le: listentry X),  0 <= numKeys_le le.
Proof.
induction le; simpl; intros; omega.
Qed.

Lemma nth_entry_le_some : forall (X:Type) (le:listentry X) i e,
    nth_entry_le i le = Some e -> (0 <= i < numKeys_le le).
Proof.
  intros.
  revert i H; induction le; simpl; intros.
  repeat if_tac in H; inv H.
  if_tac in H. inv H. if_tac in H. 
  pose proof (numKeys_le_nonneg le); omega.
  apply IHle in H. omega.
Qed. 

Lemma nth_entry_le_in_range: forall (X:Type) i (le:listentry X),
    0 <= i < numKeys_le le ->
    exists e, nth_entry_le i le = Some e.
Proof.
  intros. generalize dependent i.
  induction le.
  - intros. simpl in H. omega.
  - intros.
     destruct (zle i 0). exists e; simpl. rewrite zle_true by omega. rewrite zlt_false by omega. auto.
    destruct (IHle (Z.pred i)) as [e' ?]. simpl in H. omega.
   exists e'; simpl; auto. rewrite zle_false by omega. rewrite zlt_false by omega. auto.
Qed.

(* nth entry of a node *)
Definition nth_entry {X:Type} (i:Z) (n:node X): option (entry X) :=
  match n with btnode ptr0 le b First Last x => nth_entry_le i le end.

Lemma nth_entry_some : forall (X:Type) (n:node X) i e,
    nth_entry i n = Some e ->  (i < numKeys n).
Proof.
  intros. unfold nth_entry in H. destruct n. apply nth_entry_le_some in H. simpl. omega.
Qed.

(* nth child of a listentry *)
Fixpoint nth_node_le {X:Type} (i:Z) (le:listentry X): option (node X) :=
  if zlt i 0 then None else
  if zle i 0 
  then match le with
         | nil => None
         | cons e _ => match e with
                       | keychild _ n => Some n
                       | keyval _ _ _ => None
                       end
         end
  else  match le with
            | nil => None
            | cons _ le' => nth_node_le (Z.pred i) le'
            end.

Lemma nth_entry_child: forall i le k child,
    nth_entry_le i le = Some (keychild val k child) ->
    nth_node_le i le = Some child.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - unfold nth_entry_le in H. destruct i; inv H.
  - simpl in H|-*. if_tac in H; inv H.
      if_tac in H2. inv H2. auto. auto.
Qed.

Lemma nth_node_le_some : forall (X:Type) (le:listentry X) i n,
    nth_node_le i le = Some n -> (0 <= i < numKeys_le le).
Proof.
  intros.
  revert i n H; induction le; simpl; intros.
  repeat if_tac in H; inv H.
  repeat if_tac in H. inv H.
  pose proof (numKeys_le_nonneg le); omega.
  apply IHle in H. omega.
Qed.
    
Lemma nth_node_le_decrease: forall X (le:listentry X) (n:node X) i,
    nth_node_le i le = Some n ->
    (node_depth n < listentry_depth le).
Proof.
  induction le; intros.
  - unfold nth_node_le in H. repeat if_tac in H; inv H.
  -
    simpl in H. repeat if_tac in H. inv H.  destruct e; inv H.
    simpl.
   apply Z.max_lt_iff. left. omega.
   apply IHle in H. simpl.
   apply Z.max_lt_iff. right. omega.
Qed.

(* nth child of a node *)
Definition nth_node {X:Type} (i:Z) (n:node X): option (node X) :=
  match n with
  | btnode (Some ptr0) le false _ _ _ =>
               if zeq i (-1) then Some ptr0 else nth_node_le i le
  | _ => None
  end.

Lemma nth_node_some: forall (X:Type) (n:node X) i n',
    nth_node i n = Some n' -> -1 <= i < numKeys n.
Proof.
  intros.
  unfold nth_node in H. destruct n. destruct o. destruct b; inv H.
  if_tac in H1. inv H1.
  simpl. pose proof (numKeys_le_nonneg l); omega.
  simpl. apply nth_node_le_some in H1; auto. omega.  inv H.
Qed.

Lemma nth_node_decrease: forall X (n:node X) (n':node X) i,
    nth_node i n = Some n' ->
    (node_depth n' < node_depth n).
Proof.
  intros. unfold nth_node in H.
  destruct n. destruct o, b; try easy.
  if_tac in H.
  - subst. inv H. simpl. apply Z.max_lt_iff; right. omega.
  - apply nth_node_le_decrease in H. simpl.
     apply Z.max_lt_iff; left. omega.
Qed.

(* the node that the cursor points to *)
Definition next_node {X:Type} (c:cursor X) (root:node X) : option (node X) :=
  match c with
  | [] => Some root
  | (n,i)::c' => nth_node i n
  end.    

(* entry pointed to by a cursor. Leaf entry for a complete cursor. Keychild entry for a partial cursor *)
Definition getCEntry {X:Type} (c:cursor X) : option (entry X) :=
  match c with
  | [] => None
  | (n,i)::c' => if zeq i (-1) then None else nth_entry i n
  end.

(* get Key pointed to by cursor *)
Definition getCKey {X:Type} (c:cursor X) : option key :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some k
              end
  end.

(* get record pointed to by cursor *)
Definition getCRecord {X:Type} (c:cursor X) : option V  :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some v
              end
  end.

(* get address pointed to by cursor *)
Definition getCVal {X:Type} (c:cursor X) : option X :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some x
              end
  end.

(* findChildIndex for an intern node *)
Fixpoint findChildIndex' {X:Type} (le:listentry X) (key:key) (i:Z): Z :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (k_ key) <? (k_ k) with
      | true => i
      | false => findChildIndex' le' key (Z.succ i)
      end
    | keychild k c =>
      match (k_ key) <? (k_ k) with
      | true => i
      | false => findChildIndex' le' key (Z.succ i)
      end
    end
  end.

Definition findChildIndex {X:Type} (n:node X) (key:key): Z :=
  match n with btnode ptr0 le b F L x =>
               findChildIndex' le key (-1) end.

(* findRecordIndex for a leaf node *)
Fixpoint findRecordIndex' {X:Type} (le:listentry X) (key:key) (i:Z): Z :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (k_ key) <=? (k_ k) with
      | true => i
      | false => findRecordIndex' le' key (Z.succ i)
      end
    | keychild k c =>
      match (k_ key) <=? (k_ k) with
      | true => i
      | false => findRecordIndex' le' key (Z.succ i)
      end
    end
  end.

Definition findRecordIndex {X:Type} (n:node X) (key:key) : Z :=
    match n with btnode ptr0 le b F L x =>
                 findRecordIndex' le key 0 end.

(* nth key of a listentry *)
Fixpoint nth_key {X:Type} (i:nat) (le:listentry X): option key :=
  match le with
  | nil => None
  | cons e le' => match i with
                  | O => match e with
                         | keychild k _ => Some k
                         | keyval k _ _ => Some k
                         end
                  | S i' => nth_key i' le'
                  end
  end.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to first key *)
Fixpoint moveToFirst {X:Type} (n:node X) (c:cursor X) (level:nat): cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => (n, 0)::c
    | false => match ptr0 with
               | None => c      (* not possible, isLeaf is false *)
               | Some n' => moveToFirst n' ((n, -1)::c) (level+1)
               end
    end
  end.

Lemma node_depth_nonneg: forall {X} (n: node X), 0 <= node_depth n
   with listentry_depth_nonneg: forall {X} (le: listentry X), 0 <= listentry_depth le
   with entry_depth_nonneg: forall {X} (e: entry X), 0 <= entry_depth e.
Proof.
-
destruct n.
simpl. 
apply Zmax_bound_l.
auto.
-
induction le; simpl.
omega.
apply Zmax_bound_r; apply IHle.
-
destruct e; simpl.
omega.
pose proof (node_depth_nonneg _ n); omega.
Qed.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to last key *)
Function moveToLast {X:Type} (n:node X) (c:cursor X) (level:Z) {measure (Z.to_nat oo node_depth) n}: cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => (n, numKeys n)::c
    | false => match (nth_node (numKeys n -1) n)  with
               | None => c      (* not possible, isLeaf is false *)
               | Some n' => moveToLast n' ((n, numKeys n -1)::c) (level+1)
               end
    end
  end.
Proof.
  intros. apply nth_node_decrease in teq1.
  unfold Basics.compose.
  pose proof (node_depth_nonneg n').
  zify.
  rewrite !Z2Nat.id by omega. rewrite Z2Nat.id in * by omega. omega.
Qed.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to the key, or where it should be inserted *)
Function moveToKey {X:Type} (n:node X) (key:key) (c:cursor X) {measure (Z.to_nat oo node_depth) n} : cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => (n,findRecordIndex n key)::c
    | false => match (nth_node (findChildIndex n key) n) with (* next child *)
               | None => c                                    (* not possible *)
               | Some n' => moveToKey n' key ((n,findChildIndex n key)::c)
               end
    end
  end.
Proof.
  intros. apply nth_node_decrease in teq1.
  unfold Basics.compose.
  pose proof (node_depth_nonneg n').
  zify.
  rewrite !Z2Nat.id by omega. rewrite Z2Nat.id in * by omega. omega.
Qed.

(* Returns node->isLeaf *)
Definition isnodeleaf {X:Type} (n:node X) : bool :=
  match n with btnode _ _ isLeaf _ _ _ => isLeaf end.

(* The key of an entry *)
Definition entry_key {X:Type} (e:entry X) : key :=
  match e with
  | keychild k c => k
  | keyval k v x => k
  end.

(* Child of an entry *)
Definition entry_child {X:Type} (e:entry X) : option (node X) :=
  match e with
  | keychild k c => Some c
  | keyval k v x => None
  end.

(* Returns true if we know for sure that the node is a parent of the key *)
Definition isNodeParent {X:Type} (n:node X) (key:key): bool :=
  match n with btnode ptr0 le isLeaf First Last x =>
  if isLeaf then
    let numkeys := numKeys_le le in
    if zle numkeys 0 then true
    else 
      match nth_entry_le 0 le with
      | None => false                 (* impossible *)
      | Some e0 =>
        let lowest := entry_key e0 in
        match nth_entry_le (Z.pred numkeys) le with
        | None => false         (* impossible *)
        | Some el =>
          let highest := entry_key el in
          andb ( orb (k_ key >=? k_ lowest) (First))
               ( orb (k_ key <=? k_ highest) (Last))
        end
    end
  else let i := findChildIndex n key
           in if zeq i (-1) then false 
            else negb (Z.eqb (Z.succ i) (numKeys n))
  end.

(* Ascend to parent in a cursor *)
Fixpoint AscendToParent {X:Type} (c:cursor X) (key:key): cursor X :=
  match c with
  | [] => []
  | [(n,i)] => [(n,i)]          (* root is parent *)
  | (n,i)::c' => match isNodeParent n key with
                 | true => c
                 | false => AscendToParent c' key
                 end
  end.

(* go to a Key from any position in the cursor: ascendtoparent then movetokey *)
Definition goToKey {X:Type} (c:cursor X) (r:relation X) (key:key) : cursor X :=
  let partialc := AscendToParent c key in
  match partialc with
  | [] => moveToKey X (get_root r) key []
  | (n,i)::c' => moveToKey X n key c'
  end.

(* Returns the index of the last pointer of a node *)
Definition lastpointer {X:Type} (n:node X): Z :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               if isLeaf
               then numKeys_le le
               else Z.pred (numKeys_le le)
   end.


(* Returns the index of the first pointer of a node *)
Definition firstpointer {X:Type} (n:node X): Z :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               if isLeaf then 0 else -1
  end.

(* Goes up in the cursor as long as the index is the last possible one for the current node *)
Fixpoint up_at_last {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | [(n,i)] => [(n,i)]
  | (n,i)::c' => match Z.eqb i (lastpointer n) with
                 | false => c
                 | true => up_at_last c'
                 end
  end.

(* Increments current index of the cursor. The current index should not be the last possible one *)
Definition next_cursor {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,Z.succ i)::c'
  end.

(* moves the cursor to the next position (possibly an equivalent one)
   takes a FULL cursor as input *)
Definition moveToNext {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match isValid c r with
  | false => c                (* invalid cursor: no change to the cursor *)
  | _ =>
    let cincr := next_cursor (up_at_last c) in
    match cincr with
    | [] => moveToFirst (get_root r) [] O 
    | (n,i)::c' =>
      match isnodeleaf n with
      | true => cincr         (* if we did not go up *)
      | false =>
        match (nth_node i n) with
        | None => cincr       (* impossible *)
        | Some n' =>
          moveToFirst n' cincr (length cincr) (* going down on the left if we had to go up *)
        end
      end
    end
  end.

(* Goes up in the cursor as long as the index is the first possible one for the current node *)
Fixpoint up_at_first {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => match Z.eqb i (firstpointer n) with
                 | false => c
                 | true => up_at_first c'
                 end
  end.

(* Decrements current index of the cursor. The current index should not be the first possible one *)
Definition prev_cursor {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,Z.pred i)::c'
  end.

(* moves the cursor to the previous position (possibly an equivalent one) 
 takes a FULL cursor as input *)
Definition moveToPrev {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match isFirst c with
  | true => c                (* first cursor: no change to the cursor *)
  | _ =>
    let cdecr := prev_cursor (up_at_first c) in
    match cdecr with
    | [] => moveToFirst (get_root r) [] O 
    | (n,i)::c' =>
      match isnodeleaf n with
      | true => cdecr         (* if we did not go up *)
      | false =>
        match (nth_node i n) with
        | None => cdecr       (* impossible *)
        | Some n' =>
          moveToLast X n' cdecr (Zlength cdecr) (* going down on the left if we had to go up *)
        end
      end
    end
  end.

Definition normalize {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c
  | (n,i)::c' => match (Z.eqb i (numKeys n)) with
                 | true => moveToNext c r
                 | false => c
                 end
  end.

(* moves the cursor to the next non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToNext {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c' => match (Z.eqb i (numKeys n)) with
                 | true => moveToNext (moveToNext c r) r (* at last position, move twice *)
                 | false => moveToNext c r
                 end
  end.

(* move the cursor to the previous non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToPrevious {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c => match (Z.eqb i 0) with
                | true => moveToPrev (moveToPrev c r) r (* at first position, move twice *)
                | false => moveToPrev c r
                end
  end.

(* the nth first entries of a listentry *)
Program Fixpoint nth_first_le {X:Type} (le:listentry X) (i:Z) : listentry X :=
  if zle i 0 then nil X
   else  match le with
           | cons e le' => cons X e (nth_first_le le' (Z.pred i))
           | nil => nil X
           end.

(* number of first keys *)
Lemma numKeys_nth_first: forall (X:Type) (le:listentry X) i,
    (0 <= i <= numKeys_le le) ->
    numKeys_le (nth_first_le le i) = i.
Proof.
  intros. generalize dependent i.
  induction le; intros. simpl in *. if_tac; simpl; omega.
  simpl in *. if_tac. simpl; omega. simpl. rewrite IHle by omega. omega.
Qed.

(* selecting all keys of a listentry *)
Lemma nth_first_same: forall X (l:listentry X) m,
    m = numKeys_le l ->
    nth_first_le l m = l.
Proof.
  intros. generalize dependent m.
  induction l; intros.
  - destruct m; simpl; auto.
  - simpl  in H. subst. simpl. if_tac. pose proof (numKeys_le_nonneg l); omega.
    f_equal. rewrite Z.pred_succ. auto.
Qed.

(* skips the nth first entries of a listentry *)
Fixpoint skipn_le {X:Type} (le:listentry X) (i:Z) : listentry X :=
  if zle i 0 then le else 
     match le with
           | nil => nil X
           | cons e le' => skipn_le le' (Z.pred i)
           end.

(* number of keys when skipping *)
Lemma numKeys_le_skipn: forall X (l:listentry X) m,
  0 <= m <= numKeys_le l ->
    numKeys_le (skipn_le l m) = numKeys_le l - m.
Proof.
  intros. generalize dependent m.
  induction l; intros.
  - simpl in *. if_tac; simpl; auto; omega.
  - simpl in *. if_tac; simpl; auto; try omega.
      rewrite (IHl (Z.pred m)) by omega. omega.
Qed.

(* nth_entry when skipping entries *)
Lemma nth_entry_skipn: forall X i le (e:entry X),
    nth_entry_le i le = Some e ->
    nth_entry_le 0 (skipn_le le i) = Some e.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl in *. repeat if_tac in H; inv H.
  - simpl in *;  if_tac.
    +  if_tac in H; inv H; auto. 
    + if_tac in H; inv H; rewrite IHle; auto.
Qed.

(* skipping 0 entries *)
Lemma skipn_0: forall X (le:listentry X),
    skipn_le le 0 = le.
Proof.
  destruct le.
  - simpl. auto.
  - simpl. auto.
Qed.

Lemma nth_entry_skipn': forall X m n le (e:entry X),
    nth_entry_le m le = Some e ->
    (0 <= n <= m) ->
    nth_entry_le (m-n) (skipn_le le n) = Some e.
Proof.
  intros. generalize dependent m. generalize dependent n.
  induction le; intros.
  - simpl in H; repeat if_tac in H; inv H.
  - simpl in *. repeat if_tac in H. inv H.
     assert (n=0) by omega. assert (m=0) by omega. subst. simpl. auto.
     if_tac. simpl. if_tac; try omega. assert (n=0) by omega. subst.
     eapply (IHle 0) in H; try omega. rewrite skipn_0 in H.
     rewrite zle_false by omega.
     rewrite <- H. f_equal. omega.
     rewrite <- (IHle (Z.pred n) (Z.pred m) H) by omega.
     f_equal. omega.
Qed.

(* tl of a listentry *)
Definition tl_le {X:Type} (le:listentry X): listentry X :=
  match le with
  | nil => nil X
  | cons _ le' => le'
  end.


(* skipping all entries *)
Lemma skipn_full: forall X (le:listentry X),
    skipn_le le (numKeys_le le) = nil X.
Proof.
  intros. induction le.
  - simpl. auto.
  - simpl. rewrite zle_false. rewrite Z.pred_succ. auto. pose proof (numKeys_le_nonneg le); omega.
Qed.

(* skipping one more entry *)
Lemma skip_S: forall X (le:listentry X) i,
    0 <= i  ->
    skipn_le le (Z.succ i) = tl_le (skipn_le le i).
Proof.
  intros.
  revert i H; induction le; intros; simpl; auto. if_tac. if_tac; auto.
  if_tac; auto.
  if_tac; if_tac; auto; try omega.
  simpl. assert (i=0) by omega. subst. simpl in *. rewrite skipn_0. auto.
  rewrite Z.pred_succ; auto.
  rewrite <- IHle by omega. 
  rewrite Z.succ_pred; auto.
Qed.

(* sublist of a listentry *)
Definition suble {X:Type} (lo hi: Z) (le:listentry X) : listentry X :=
  nth_first_le (skipn_le le lo) (hi-lo).

Lemma suble_nil: forall X (le:listentry X) lo,
    suble lo lo le = nil X.
Proof.
  intros. unfold suble. rewrite Z.sub_diag.
  destruct (skipn_le le lo); simpl; auto.
Qed.

Lemma suble_nil': forall X (le:listentry X) m n,
    m <= n ->
    suble n m le = nil X.
Proof.
  intros. unfold suble.
  destruct (skipn_le le n); simpl; rewrite zle_true by omega; auto.
Qed.

Lemma suble_skip: forall A m f (l:listentry A),
    0 <= m <= numKeys_le l->
    f = numKeys_le l -> 
    suble m f l = skipn_le l m.
Proof.
  intros. unfold suble. subst.
  destruct l; simpl. if_tac; simpl; auto; if_tac; auto.
  if_tac. simpl. if_tac. pose proof (numKeys_le_nonneg l); omega.
  f_equal. assert (m=0) by omega. subst. rewrite Z.sub_0_r.
  rewrite Z.pred_succ. 
  apply nth_first_same; auto.
   rewrite nth_first_same; auto.
   rewrite numKeys_le_skipn.
   omega. split. omega. simpl in H. omega.
Qed.

Lemma numKeys_suble: forall A m f (l:listentry A),
    0 <= m -> m <= f <= numKeys_le l ->
    numKeys_le (suble m f l) = f - m.
Proof.
  intros. destruct H0.
  unfold suble.
  rewrite numKeys_nth_first. auto.
  rewrite numKeys_le_skipn. omega. omega.
Qed.  

(* appending two listentries *)
Fixpoint le_app {X:Type} (l1:listentry X) (l2:listentry X) :=
  match l1 with
  | nil => l2
  | cons e le => cons X e (le_app le l2)
  end.

Lemma nth_first_0:
  forall X (le: listentry X), nth_first_le le 0 = nil X.
Proof.
intros.
destruct le; reflexivity.
Qed. 

Lemma nth_first_increase: forall X n (le:listentry X) e,
    nth_entry_le n le = Some e ->
    nth_first_le le (Z.succ n) = le_app (nth_first_le le n) (cons X e (nil X)).
Proof.
  intros.
   revert n e H; induction le; simpl; intros.
   repeat if_tac in H; inv H.
   if_tac in H; try discriminate.
   if_tac in H. inv H. rewrite zle_false by omega. simpl. f_equal.
   assert (n=0) by omega. subst; simpl.
   apply nth_first_0.
   rewrite zle_false by omega.
   simpl. f_equal.
   rewrite Z.pred_succ.
  apply IHle in H.
  rewrite Z.succ_pred in H; auto.
Qed.

Lemma skipn_increase: forall X n (le:listentry X) e,
    Z.succ n < numKeys_le le ->
    nth_entry_le n le = Some e ->
    skipn_le le n = cons X e (skipn_le le (Z.succ n)).
Proof.
  intros.
  generalize dependent n; induction le; simpl; intros.
  - rewrite zle_true in * by omega. if_tac in H0; inv H0.
  - if_tac.
   + if_tac in H0; inv H0. assert (n=0) by omega. subst n. simpl. f_equal. rewrite skipn_0. auto.
   + rewrite zle_false by omega.
       if_tac in H0; try discriminate.
       apply IHle in H0. 2: omega.
       rewrite Z.pred_succ. rewrite Z.succ_pred in H0; auto.
Qed.

Lemma suble_increase: forall X n m (le:listentry X) e,
    0 <= n ->
    n <= m < numKeys_le le ->
    nth_entry_le m le = Some e ->
    suble n (Z.succ m) le = le_app (suble n m le) (cons X e (nil X)).
Proof.
  intros. unfold suble. replace (Z.succ m - n) with (Z.succ (m - n)) by omega.
  rewrite nth_first_increase with (e:=e).
  auto.
  apply nth_entry_skipn'. auto. omega.
Qed.  

(* Inserts an entry in a list of entries (that doesnt already has the key) *)
Fixpoint insert_le {X:Type} (le:listentry X) (e:entry X) : listentry X :=
  match le with
  | nil => cons X e (nil X)
  | cons e' le' => if k_ (entry_key e) <=? k_ (entry_key e') 
                          then cons X e le 
                          else cons X e' (insert_le le' e)
  end.

(* inserting adds one entry *)
Lemma numKeys_le_insert: forall X (l:listentry X) e,
    numKeys_le (insert_le l e) = Z.succ (numKeys_le l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct (k_ (entry_key e) <=? k_ (entry_key e0)).
    + simpl. auto.
    + simpl. rewrite IHl. auto.
Qed.

(* Inserts an entry e in a full node n. This function returns the right node containing the first 
   values after the split. e should have a key not already contained by the node *)
Definition splitnode_left {X:Type} (n:node X) (e:entry X) : (node X) :=
  match n with btnode ptr0 le isLeaf First Last x =>
               btnode X ptr0
                      (nth_first_le (insert_le le e) Middle)
                      isLeaf
                      First
                      false    (* the right node can't be the last one *)
                      x end.

Definition splitnode_leafnode {X:Type} (le:listentry X) (e:entry X) (newx:X) Last :=
  (btnode X None (* Leaf node has no ptr0 *)
          (skipn_le (insert_le le e) Middle)
          true   (* newnode is at same level as old one *)
          false  (* newnode can't be first node *)
          Last   (* newnode is last leaf if the split node was *)
          newx).

Definition splitnode_internnode {X:Type} (le:listentry X) (e:entry X) newx Last child :=
  (btnode X (Some child) (* ptr0 of the new node is the previous child of the pushed up entry *)
          (skipn_le (insert_le le e) (Z.succ Middle)) (* the middle entry isn't copied *)
          false  (* newnode is at the same level as old one *)
          false  (* newnode can't be first node *)
          Last   (* newnode is last leaf if the split node was *)
          newx).

(* This function contains the new entry to be pushed up after splitting the node
   Its child is the new node from splinode, containing the last entries 
   newx is the the address of the new node *)
Definition splitnode_right {X:Type} (n:node X) (e:entry X) (newx:X) : (entry X) :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true =>                    (* in a leaf the middle key is copied up *)
      match nth_entry_le Middle (insert_le le e) with
      | None => e     (* not possible: the split node should be full *)
      | Some e' =>
        keychild X (entry_key e') (splitnode_leafnode le e newx Last)
      end
    | false =>
      match nth_entry_le Middle (insert_le le e) with
      | None => e                (* not possible: the split node should be full *)
      | Some e' =>
        match (entry_child e') with
        | None => e              (* not possible: at intern leaf, each entry has a child *)
        | Some child =>
          keychild X (entry_key e')
                   (splitnode_internnode le e newx Last child)
        end
      end
    end
  end.

(* The key that is copied up when splitting a node *)
Definition splitnode_key {X:Type} (n:node X) (e:entry X) : key :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match nth_entry_le Middle (insert_le le e) with
    | None => Ptrofs.repr 0     (* splitnode should be full *)
    | Some e' =>
      match e' with
      | keyval k _ _ => k
      | keychild k _ => k
      end
    end
  end.
  
(* returns true if the node is full and should be split on insertion *)
Definition fullnode {X:Type} (n:node X) : bool :=
  (Fanout <=? numKeys n).

(* Is a key already in a listentry? *)
Fixpoint key_in_le {X:Type} (key:key) (le:listentry X) : bool :=
  match le with
  | nil => false
  | cons e le' => match (k_ (entry_key e) =? k_ key) with
                 | true => true
                 | false => key_in_le key le'
                 end
  end.

(* listentry should contain an entry with the same key as e
   the child or record of this entry will be updated to the one of the entry 
   this is useful when inserting a (key,record) in a tree where the key has already been inserted *)
Fixpoint update_le {X:Type} (e:entry X) (le:listentry X) : listentry X :=
  match le with
  | nil => nil X                 (* not possible *)
  | cons e' le' => match (k_ (entry_key e) =? k_ (entry_key e')) with
                  | true => cons X e le'
                  | false => cons X e' (update_le e le')
                  end
  end.

(* updates a child in a listentry *)
Fixpoint update_le_nth_child {X:Type} (i:Z) (le:listentry X) (n:node X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' => if zle i 0 
                          then  match e with
                         | keychild k c => cons X (keychild X k n) le'
                         | keyval k v x => cons X (keychild X k n) le' (* shouldnt happen *)
                         end
                         else update_le_nth_child (Z.pred i) le' n
  end.  

(* updates value in a listentry *)
Fixpoint update_le_nth_val {X:Type} (i:Z) (le:listentry X) (newv:V) (newx:X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' =>  if zle i 0 
                          then match e with
                         | keychild k c => cons X (keyval X k newv newx) le' (* shouldnt happen *)
                         | keyval k v x => cons X (keyval X k newv newx) le'
                         end
                         else update_le_nth_val (Z.pred i) le' newv newx
  end.

(* updates nth child of a node *)
Definition update_node_nth_child {X:Type} (i:Z) (oldn:node X) (n:node X) : node X :=
  match oldn with btnode ptr0 le isLeaf First Last x =>
  if zeq i (-1) 
  then btnode X (Some n) le isLeaf First Last x
  else btnode X ptr0 (update_le_nth_child i le n) isLeaf First Last x
  end.

(* recursively updates a partial cursor and the corresponding relation wih a new node (to be put where the cursor points to) 
   the new cursor will point to n *)
Fixpoint update_partial_cursor_rel {X:Type} (c:cursor X) (r:relation X) (n:node X) : (cursor X * relation X) :=
  match r with (root,prel) =>
  match c with
  | [] => ([], (n,prel))
  | (oldn,i)::c' =>
    let newn := update_node_nth_child i oldn n in
    let (newc',newrel) := update_partial_cursor_rel c' r newn in
    ((newn, i)::newc', newrel)
  end
  end.

Lemma update_partial_same_length: forall X (c:cursor X) r n,
    length c = length (fst (update_partial_cursor_rel c r n)).
Proof.
  intros. destruct r as [root prel].
  generalize dependent n.
  induction c as [|[n' i] c'].
  - simpl. auto.
  - intros. simpl.
    pose (u:= update_partial_cursor_rel c' (root, prel) (update_node_nth_child i n' n)).
    fold u.
    destruct u as [newc' newrel] eqn:HU. simpl.
    assert (length c' = length (fst u)). unfold u. apply IHc'. rewrite H. rewrite HU. simpl.
    auto.
Qed.
  
(* recursively updates a cursor and the relation with a new node (that should replace the currNode) 
   this need a non-empty cursor
   the index is unchanged. Should it be updated somehow?*)
Definition update_currnode_cursor_rel {X:Type} (c:cursor X) (r:relation X) (n:node X) : (cursor X * relation X) :=
  match c with
  | [] => (c,r)                  (* impossible, we ask for a non-empty cursor *)
  | (oldn, i)::c' =>
    let (newc',newrel) := update_partial_cursor_rel c' r n in
    ((n,i)::newc', newrel)
  end.

Lemma update_currnode_same_length: forall X (c:cursor X) r n,
    length c = length (fst (update_currnode_cursor_rel c r n)).
Proof.
  intros. destruct c as [|[n' i] c'].
  - simpl. auto.
  - simpl.
    pose (u:= update_partial_cursor_rel c' r n). fold u.
    destruct u as [newc' newrel] eqn:HU. simpl.
    assert(length c' = length (fst u)). unfold u. apply update_partial_same_length. rewrite H.
    rewrite HU. simpl. auto.
Qed.
    
(* inserts a new entry in a relation
   the cursor should point to where the entry has to be inserted
   newx is the addresses of the new nodes for splitnode. d is default value (shouldn't be used)
   we remember with oldk the key that was inserted in the tree: the cursor should point to it *)
Function putEntry {X:Type} (c:cursor X) (r:relation X) (e:entry X) (oldk:key) (newx:list X) (d:X) {measure length c}: (cursor X * relation X) :=
  match r with
    (root, prel) =>
    match c with
    | [] => let relation := ((btnode X (Some root) (* root has been split *)
                                    (cons X e (nil X))
                                    false       (* new root can't be leaf *)
                                    true
                                    true
                                    (hd d newx)), prel) in
           let cursor := moveToKey X (get_root relation) oldk [] in
           (cursor, relation)
    | (n,i)::c' =>
      match n with
        btnode ptr0 le isLeaf First Last x =>
        match isLeaf with
        | true =>
          match (key_in_le (entry_key e) le) with
          | true =>              (* the key is already in the tree, we only update the listentry *)
            let newle := update_le e le in
            let newn := btnode X ptr0 newle isLeaf First Last x in
            update_currnode_cursor_rel c r newn
          | false =>
            match (fullnode n) with
            | false =>           (* we insert e in le, because the node isn't full *)
              let newle := insert_le le e in
              let newn := btnode X ptr0 newle isLeaf First Last x in
              update_currnode_cursor_rel c r newn
            | true =>
              let newn := splitnode_left n e in
              let newe := splitnode_right n e (hd d newx) in
              let (newc,newr) := update_currnode_cursor_rel c r newn in
              putEntry (tl newc) newr newe oldk (tl newx) d (* recursive call on previous level *)
            end
          end
        | false =>
          match (fullnode n) with
          | false =>
            let newle := insert_le le e in
            let newn := btnode X ptr0 newle isLeaf First Last x in
            let (newc,newr) := update_currnode_cursor_rel c r newn in
            let movec := moveToKey X newn oldk (tl newc) in
            (movec,newr)
          | true =>
            let newn := splitnode_left n e in
            let newe := splitnode_right n e (hd d newx) in
            let (newc,newr) := update_currnode_cursor_rel c r newn in
            putEntry (tl newc) newr newe oldk (tl newx) d (* recusive call on previous level *)
          end
        end
      end
    end
  end.
Proof.
  intros.
  - pose (c'':=((btnode X ptr0 le true First Last x, i) :: c')). fold c''. fold c'' in teq6.
    assert (length c'' = length(fst(newc,newr))).
    rewrite <- teq6. apply update_currnode_same_length. rewrite H. simpl.
    destruct newc eqn:HC.
    + simpl in H. inv H.
    + simpl. omega.
  - intros.
    pose (c'':=((btnode X ptr0 le false First Last x, i) :: c')). fold c''. fold c'' in teq5.
    assert (length c'' = length(fst(newc,newr))).
    rewrite <- teq5. apply update_currnode_same_length. rewrite H. simpl.
    destruct newc eqn:HC.
    + simpl in H. inv H.
    + simpl. omega.
Qed.

(* Add a new (key,record) in a btree, updating cursor and relation
   x is the address of the new entry to insert 
   newx is the list of addresses for the new nodes of splitnode *)
Definition RL_PutRecord {X:Type} (c:cursor X) (r:relation X) (key:key) (record:V) (x:X) (newx:list X) (d:X) : (cursor X * relation X) :=
  let c' := goToKey c r key in
  let e := keyval X key record x in
  let (putc, putr) := putEntry X c' r e key newx d in
  (RL_MoveToNext putc putr, putr).

(* Gets the record pointed to by the cursor *)
Definition RL_GetRecord (c:cursor val) r : val :=
  let normc := normalize c r in
  match getCVal normc with
  | None => nullval
  | Some x => x
  end.
