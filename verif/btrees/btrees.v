(** * btrees.v : Formal Model of BTrees  *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.

Instance Inhabitant_option {X: Type} : Inhabitant (option X) := @None X.

Definition Znth_option {X : Type} (i : Z) (l : list X) : option X :=
     Znth i (map Some l).

Lemma Znth_option_e {X: Type} (i: Z) (l: list X):
   Znth_option i l = 
  if zle 0 i then
    if zlt i (Zlength (map Some l)) then
      (@Znth _ None i (map Some l))
    else
      None
  else
    None.
Proof.
unfold Znth_option, Znth.
if_tac.
rewrite zle_false by lia.
auto.
rewrite zle_true by lia.
if_tac.
auto.
autorewrite with sublist in H0.
rewrite Zlength_correct in H0.
apply nth_overflow.
rewrite map_length.
zify.
rewrite ?Z2Nat.id by lia.  (* This line not needed in Coq 8.11 or after *)
lia.
Qed.

Lemma Znth_option_e' {X: Type} {d: Inhabitant X} (i: Z) (l: list X) (x: X):
   Znth_option i l = Some x -> Znth i l = x.
Proof.
intros.
rewrite Znth_option_e in H.
repeat if_tac in H; inv H.
autorewrite with sublist in *.
rewrite Znth_map in H3 by list_solve.
inv H3; auto.
Qed.

(**
    BTREES FORMAL MODEL
 **)
 
Ltac evaluate x :=
  let x := eval compute in x in exact x.

(* Maximum number of entries in a node *)
Definition Fanout := 15%Z.
Lemma Fanout_eq : Fanout = ltac:(evaluate Fanout).
Proof. reflexivity. Qed.
Hint Rewrite Fanout_eq : rep_lia.
(* Middle = Fanout +1  /2, for splitting nodes *)
Definition Middle := ltac:(evaluate ((Fanout+1)/2)).
Lemma Middle_eq: Middle = ltac:(evaluate Middle).
Proof. reflexivity. Qed.
Global Opaque Fanout.
Global Opaque Middle.
Hint Rewrite Middle_eq : rep_lia.

(* Maximum tree depth *)
Definition MaxTreeDepth := 20%Z.
Lemma MTD_eq : MaxTreeDepth = ltac:(evaluate MaxTreeDepth).
Proof. reflexivity. Qed.
Global Opaque MaxTreeDepth.
Hint Rewrite MTD_eq : rep_lia.

Definition key := Ptrofs.int.
Definition V := Ptrofs.int.

(* Variable X:Type.                (* val or unit *) *)

(* Btree Types *)
Inductive entry (X:Type): Type :=
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: forall (entryzero: option (node X)) (le: list (entry X))  (isLeaf: bool) (First: bool) (Last: bool) (x: X), node X.

Definition node_entryzero {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => entryzero end.

Definition node_le {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => le end.

Definition node_isLeaf {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => isLeaf end.

Definition node_First {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => First end.

Definition node_Last {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => Last end.

Definition node_x {X} (n: node X) :=
  match n with btnode entryzero le isLeaf First Last x => x end.

Definition cursor (X:Type): Type := list (node X * Z). (* ancestors and index *)
Definition relation (X:Type): Type := node X * X.  (* root and address *)

(* Abstracting a Btree to an ordered list of (key,value) pairs *)
Fixpoint abs_node {X:Type} (n:node X) : list (key * V) :=
  match n with
    btnode o le isLeaf First Last x =>
    match o with
    | Some n' => abs_node n' ++ concat (map abs_entry le)
    | None => concat (map abs_entry le)
    end
  end
with abs_entry {X:Type} (e:entry X) : list (key * V) :=
       match e with
       | keyval k v x => [(k,v)]
       | keychild k n => abs_node n
       end.

(* Btrees depth *)
Fixpoint node_depth {X:Type} (n:node X) : Z :=
  match n with
    btnode ptr0 le _ _ _ _ =>
      Z.max (fold_right Z.max 0 (map entry_depth le))
        (match ptr0 with
         | None => 0
         | Some n' => Z.succ (node_depth n')
         end)
  end
with entry_depth {X:Type} (e:entry X) : Z :=
       match e with
       | keyval _ _ _ => 0
       | keychild _ n => Z.succ (node_depth n)
       end.

Definition listentry_depth {X} (le: list (entry X)) : Z :=
  fold_right Z.max 0 (map entry_depth le).

Lemma node_depth_nonneg: forall {X} (n: node X), 0 <= node_depth n
   with entry_depth_nonneg: forall {X} (e: entry X), 0 <= entry_depth e.
Proof.
-
destruct n.
simpl. 
apply Zmax_bound_l.
induction (map entry_depth le).
simpl. lia.
simpl.
apply Zmax_bound_r. auto.
-
destruct e; simpl.
lia.
pose proof (node_depth_nonneg _ n); lia.
Qed.

Lemma listentry_depth_nonneg: forall {X} (le: list (entry X)), 0 <= listentry_depth le.
Proof.
unfold listentry_depth.
induction le; simpl.
lia.
apply Zmax_bound_r; auto.
Qed.

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
    btnode ptr0 le _ _ _ _ =>
      fold_left Z.add (map entry_numrec le)
        (match ptr0 with
         | None => 0
         | Some n' => node_numrec n'
         end)
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

Definition currNode' {X:Type} (c:cursor X) (root:node X) : node X :=
  match c with
  | [] => root
  | (n,i)::c' => n
  end.
Lemma currNode_currNode' {X:Type} (c:cursor X) r: currNode c r = currNode' c (get_root r).
Proof. destruct c; simpl; trivial. Qed.

Instance Inhabitant_node {X: Type} (x: Inhabitant X): Inhabitant (node X) :=
  btnode X None nil true true true x.

Instance Inhabitant_entry {X: Type} (x: Inhabitant X): Inhabitant (entry X) := keychild _ Ptrofs.zero (Inhabitant_node _).

Instance Inhabitant_entry_val : Inhabitant (entry val) := Inhabitant_entry _.

(* is a cursor valid? invalid if the cursor is past the very last key *)
Definition isValid {X:Type} (c:cursor X) (r:relation X): bool :=
  match currNode c r
  with btnode ptr0 le b First Last x =>
       match Last with
       | false => true
       | true =>
         match (Z.eqb (entryIndex c) (Zlength le)) with
               | false => true
               | true => false
                end
       end
  end.

Definition isValid' {X:Type} (c:cursor X) root: bool :=
  match currNode' c root
  with btnode ptr0 le b First Last x =>
       negb (andb Last (Z.eqb (entryIndex c) (Zlength le))) end.
Lemma is_valid_isValid' {X} (c:cursor X) r: isValid c r = isValid' c (get_root r).
Proof. unfold isValid, isValid'. rewrite currNode_currNode'.
  destruct (currNode' c (get_root r)). destruct Last; simpl; trivial. 
Qed.

(* does the cursor point to the very first key? *)
Definition isFirst {X:Type} (c:cursor X) : bool :=
  match c with
  | [] => false
  | (n,i)::c' =>
    match n with btnode ptr0 le isLeaf First Last x =>
                 First && (Z.eqb i 0)
    end
  end.

(* Leaf entries have values *)
Definition LeafEntry {X:Type} (e:entry X) : Prop :=
  match e with
  | keyval _ _ _ => True
  | keychild _ _ => False
  end.

Hint Rewrite @Znth_pos_cons using rep_lia : sublist.

Section nth_option.
Context {X : Type} .

Lemma Znth_option_in_range: forall i (le:list (entry X)),
    0 <= i < Zlength le ->
    exists e, Znth_option i le = Some e.
Proof.
  intros.
  rewrite Znth_option_e.
  autorewrite with sublist. rewrite if_true by lia.
  rewrite zle_true by lia.
 generalize dependent i.
  induction le; intros; autorewrite with sublist in *.
  - lia.
  - destruct (zeq i 0); subst; simpl; autorewrite with sublist. eauto.
     apply IHle; auto; lia.
Qed.

(* nth child of a listentry *)
Definition nth_node_le (i:Z) (le:list (entry X)): option (node X) :=
  match Znth_option i le with
  | Some (keychild k child) => Some child
  | _ => None
  end.

Lemma Znth_option_some : forall X (le:list X) i e,
    Znth_option i le = Some e -> (0 <= i < Zlength le).
Proof.
  intros.
  rewrite Znth_option_e in H.
  repeat if_tac in H; inv H.
  autorewrite with sublist in *. lia.
Qed.
 
Lemma nth_node_le_some : forall  (le:list (entry X)) i n,
    nth_node_le i le = Some n -> (0 <= i < Zlength le).
Proof.
  intros.
  unfold nth_node_le in H.
  destruct (Znth_option i le) eqn:?H; try discriminate.
  eapply Znth_option_some; eauto.
Qed.

Definition nth_node (i:Z) (n:node X): option (node X) :=
  match n with
  | btnode (Some ptr0) le false _ _ _ =>
               if zeq i (-1) then Some ptr0 else nth_node_le i le
  | _ => None
  end.

Lemma nth_node_some: forall (n:node X) i n',
    nth_node i n = Some n' -> -1 <= i < Zlength (node_le n).
Proof.
  intros.
  unfold nth_node in H. destruct n. simpl. destruct entryzero, isLeaf; inv H.
  if_tac in H1. inv H1.
  simpl. rep_lia.
  simpl. apply nth_node_le_some in H1; auto. lia.
Qed.

Lemma nth_node_le_decrease: forall (le:list (entry X)) (n:node X) i,
    nth_node_le i le = Some n ->
    (node_depth n < listentry_depth le).
Proof.
  intros.
  unfold nth_node_le in H. 
  destruct (Znth_option i le) as [[|]|] eqn:?H; inv H.
  rename H0 into H.
  rewrite Znth_option_e in H.
  revert i k n H; 
  induction le; intros.
  - repeat if_tac in H; inv H. autorewrite with sublist in H1; lia.
  -
    repeat if_tac in H; inv H. autorewrite with sublist in H1.
    unfold listentry_depth.
    simpl.
    destruct (zeq i 0).
   + subst. autorewrite with sublist in H3. inv H3. simpl.
      apply Z.max_lt_iff. left. lia.
   + apply Z.max_lt_iff. right. apply (IHle (i-1) k).
      autorewrite with sublist in H3|-*.
      rewrite zle_true by lia. rewrite zlt_true by lia. auto.
Qed.

Lemma nth_node_decrease: forall (n:node X) (n':node X) i,
    nth_node i n = Some n' ->
    (node_depth n' < node_depth n).
Proof.
  intros. unfold nth_node, Znth_option in H.
  destruct n.
 destruct isLeaf, entryzero; try easy.
  if_tac in H.
  - subst. inv H. simpl. apply Z.max_lt_iff; right. lia.
  - apply nth_node_le_decrease in H. simpl.
     apply Z.max_lt_iff; left. auto.
Qed.

Definition next_node (c:cursor X) (root:node X) : option (node X) :=
  match c with
  | [] => Some root
  | (n,i)::c' => nth_node i n
  end.

(* entry pointed to by a cursor. Leaf entry for a complete cursor. Keychild entry for a partial cursor *)
Definition getCEntry (c:cursor X) : option (entry X) :=
  match c with
  | [] => None
  | (n,i)::c' => Znth_option i (node_le n)
  end.

(* get Key pointed to by cursor *)
Definition getCKey (c:cursor X) : option key :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some k
              end
  end.

(* get record pointed to by cursor *)
Definition getCRecord (c:cursor X) : option V  :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some v
              end
  end.

(* get address pointed to by cursor *)
Definition getCVal (c:cursor X) : option X :=
  match (getCEntry c) with
  | None => None
  | Some e => match e with
              | keychild _ _ => None
              | keyval k v x => Some x
              end
  end.

End nth_option.

Lemma nth_entry_child: forall i le k child,
    Znth_option i le = Some (keychild val k child) ->
    nth_node_le i le = Some child.
Proof.
  intros.
  unfold nth_node_le. rewrite H; auto.
Qed.

(* findChildIndex for an intern node *)
Fixpoint findChildIndex' {X:Type} (le:list (entry X)) (key:key) (i:Z): Z :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (Ptrofs.ltu key k) with
      | true => i
      | false => findChildIndex' le' key (Z.succ i)
      end
    | keychild k c =>
      match (Ptrofs.ltu key k) with
      | true => i
      | false => findChildIndex' le' key (Z.succ i)
      end
    end
  end.

Definition findChildIndex {X:Type} (n:node X) (key:key): Z :=
  match n with btnode ptr0 le b F L x =>
               findChildIndex' le key (-1) end.

(* The key of an entry *)
Definition entry_key {X:Type} (e:entry X) : key :=
  match e with
  | keychild k c => k
  | keyval k v x => k
  end.

(* findRecordIndex for a leaf node *)
Fixpoint findRecordIndex' {X:Type} (le:list (entry X)) (key:key) (i:Z): Z :=
  match le with
  | nil => i
  | cons e le' =>
      if (Ptrofs.cmpu Cle key (entry_key e)) 
      then i 
      else findRecordIndex' le' key (Z.succ i)
  end.

Definition findRecordIndex {X:Type} (n:node X) (key:key) : Z :=
    match n with btnode ptr0 le b F L x =>
                 findRecordIndex' le key 0 end.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to first key *)
Fixpoint moveToFirst {X:Type} (n:node X) (c:cursor X) (level:nat): cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    if isLeaf 
    then (n, 0)::c
    else match ptr0 with
           | None => c      (* not possible, isLeaf is false *)
           | Some n' => moveToFirst n' ((n, -1)::c) (level+1)
           end
  end.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to last key *)
Function moveToLast {X:Type} (n:node X) (c:cursor X) (level:Z) {measure (Z.to_nat oo node_depth) n}: cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    if isLeaf
    then (n, Zlength (node_le n))::c
    else match (nth_node (Zlength (node_le n) -1) n)  with
           | None => c      (* not possible, isLeaf is false *)
           | Some n' => moveToLast n' ((n, Zlength (node_le n) -1)::c) (level+1)
           end
  end.
Proof.
  intros. apply nth_node_decrease in teq1.
  unfold Basics.compose.
  pose proof (node_depth_nonneg n').
  zify.
  rewrite ?Z2Nat.id by lia.  (* this line not needed in Coq 8.11 or after *)
 rewrite ?Z2Nat.id in * by lia.  (* this line not needed in Coq 8.11 or after *)
 lia.
Qed.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to the key, or where it should be inserted *)
Function moveToKey {X:Type} (n:node X) (key:key) (c:cursor X) {measure (Z.to_nat oo node_depth) n} : cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    if isLeaf
    then (n,findRecordIndex n key)::c
    else match (nth_node (findChildIndex n key) n) with (* next child *)
            | None => c                                    (* not possible *)
            | Some n' => moveToKey n' key ((n,findChildIndex n key)::c)
            end
  end.
Proof.
  intros. apply nth_node_decrease in teq1.
  unfold Basics.compose.
  pose proof (node_depth_nonneg n').
  zify.
  rewrite ?Z2Nat.id by lia.   (* this line not needed in Coq 8.11 or after *)
 rewrite ?Z2Nat.id in * by lia.   (* this line not needed in Coq 8.11 or after *)
 lia.
Qed.

(* Returns node->isLeaf *)
Definition isnodeleaf {X:Type} (n:node X) : bool :=
  match n with btnode _ _ isLeaf _ _ _ => isLeaf end.

(* Child of an entry *)
Definition entry_child {X:Type} (e:entry X) : option (node X) :=
  match e with
  | keychild k c => Some c
  | keyval k v x => None
  end.

Section Foo.
Context {X: Type}.

(* Returns true if we know for sure that the node is a parent of the key *)
Definition isNodeParent (n:node X) (key:key): bool :=
  match n with btnode ptr0 le isLeaf First Last x =>
  if isLeaf then
    let numkeys := Zlength le in
    if zle numkeys 0 then true
    else 
      match Znth_option 0 le with
      | None => false                 (* impossible *)
      | Some e0 =>
        let lowest := entry_key e0 in
        match Znth_option (Z.pred numkeys) le with
        | None => false         (* impossible *)
        | Some el =>
          let highest := entry_key el in
          andb ( orb (Ptrofs.cmpu Cge key lowest) (First))
               ( orb (Ptrofs.cmpu Cle key highest) (Last))
        end
    end
  else let i := findChildIndex n key
           in if zeq i (-1) then false 
            else negb (Z.eqb (Z.succ i) (Zlength (node_le n)))
  end.

(* Ascend to parent in a cursor *)
Fixpoint AscendToParent (c:cursor X) (key:key): cursor X :=
  match c with
  | [] => []
  | [(n,i)] => [(n,i)]          (* root is parent *)
  | (n,i)::c' => match isNodeParent n key with
                 | true => c
                 | false => AscendToParent c' key
                 end
  end.

(* go to a Key from any position in the cursor: ascendtoparent then movetokey *)
Definition goToKey (c:cursor X) (r:relation X) (key:key) : cursor X :=
  let partialc := AscendToParent c key in
  match partialc with
  | [] => moveToKey X (get_root r) key []
  | (n,i)::c' => moveToKey X n key c'
  end.

(* Returns the index of the last pointer of a node *)
Definition lastpointer (n:node X): Z :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               if isLeaf
               then Zlength le
               else Z.pred (Zlength le)
   end.


(* Returns the index of the first pointer of a node *)
Definition firstpointer (n:node X): Z :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               if isLeaf then 0 else -1
  end.

(* Goes up in the cursor as long as the index is the last possible one for the current node *)
Fixpoint up_at_last (c:cursor X): cursor X :=
  match c with
  | [] => []
  | [(n,i)] => [(n,i)]
  | (n,i)::c' => if Z.eqb i (lastpointer n) then up_at_last c' else c
  end.

(* Increments current index of the cursor. The current index should not be the last possible one *)
Definition next_cursor (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,Z.succ i)::c'
  end.

(* moves the cursor to the next position (possibly an equivalent one)
   takes a FULL cursor as input *)
Definition moveToNext (c:cursor X) (r:relation X) : cursor X :=
  if isValid c r
  then let cincr := next_cursor (up_at_last c) in
    match cincr with
    | [] => moveToFirst (get_root r) [] O 
    | (n,i)::c' =>
      if isnodeleaf n
      then cincr         (* if we did not go up *)
      else match (nth_node i n) with
             | None => cincr       (* impossible *)
             | Some n' =>
               moveToFirst n' cincr (length cincr) (* going down on the left if we had to go up *)
        end
    end
  else c.  (* invalid cursor: no change to the cursor *)


(* Goes up in the cursor as long as the index is the first possible one for the current node *)
Fixpoint up_at_first (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => if Z.eqb i (firstpointer n) then up_at_first c' else c
  end.

(* Decrements current index of the cursor. The current index should not be the first possible one *)
Definition prev_cursor (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,Z.pred i)::c'
  end.

(* moves the cursor to the previous position (possibly an equivalent one) 
 takes a FULL cursor as input *)
Definition moveToPrev (c:cursor X) (r:relation X) : cursor X :=
  if isFirst c
  then c              (* first cursor: no change to the cursor *)
  else
    let cdecr := prev_cursor (up_at_first c) in
    match cdecr with
    | [] => moveToFirst (get_root r) [] O 
    | (n,i)::c' =>
      if isnodeleaf n
      then cdecr         (* if we did not go up *)
      else match (nth_node i n) with
             | None => cdecr       (* impossible *)
             | Some n' =>
          moveToLast X n' cdecr (Zlength cdecr) (* going down on the left if we had to go up *)
        end
    end.

Definition normalize (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c
  | (n,i)::c' => if Z.eqb i (Zlength (node_le n)) then moveToNext c r else c
  end.

(* moves the cursor to the next non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToNext (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c' => if Z.eqb i (Zlength (node_le n))
                 then moveToNext (moveToNext c r) r (* at last position, move twice *)
                 else moveToNext c r
  end.

(* move the cursor to the previous non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToPrevious (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c => if Z.eqb i 0
                then moveToPrev (moveToPrev c r) r (* at first position, move twice *)
                else moveToPrev c r
  end.

End Foo.

Lemma Znth_option_nil: forall {X: Type } i,
  @Znth_option X i nil = None.
Proof.
intros.
apply Znth_nil.
Qed.

Lemma Znth_option_0: forall {X} (a: X) l i, i=0 -> Znth_option i (a::l) = Some a.
Proof.
intros. subst.
unfold Znth_option; simpl.
autorewrite with sublist.
auto.
Qed.

Lemma Znth_option_cons: forall {X} (a: X) l i, 0 <> i -> Znth_option i (a::l) = Znth_option (i-1) l.
Proof.
intros.
rewrite !Znth_option_e; simpl.
autorewrite with sublist.
repeat if_tac; try lia; auto.
autorewrite with sublist; auto.
Qed.

Hint Rewrite @Znth_option_nil : sublist.
Hint Rewrite @Znth_option_0 using rep_lia : sublist.
Hint Rewrite @Znth_option_cons using rep_lia : sublist.

Lemma Zlength_sublist_hack:
  forall {X: Type} i j (al: list X),
    i <= j ->
    Zlength (sublist i j al) <= j-i.
Proof.
intros.
unfold sublist.
rewrite Zlength_correct.
assert (j = (j-i) + i) by lia.
assert (0 <= (j-i)) by lia.
forget (j-i) as k.
subst j.
rewrite <- (Z2Nat.id k) in * by lia.
forget (Z.to_nat k) as k'; clear k; rename k' into k.
apply inj_le.
destruct (zlt i 0).
rewrite Z2Nat_neg by auto.
simpl.
rewrite firstn_le_length. zify; lia.
rewrite skipn_length.
rewrite Z2Nat.inj_add by lia.
rewrite Nat2Z.id.
pose proof (firstn_le_length (k + Z.to_nat i) al).
lia.
Qed.

(* nth_entry when skipping entries *)
Lemma nth_entry_skipn: forall X i le (e:entry X),
    Znth_option i le = Some e ->
    Znth_option 0 (sublist i (Zlength le) le) = Some e.
Proof.
  intros.
  rewrite !Znth_option_e in H|-*.
  repeat if_tac in H; inv  H.
  autorewrite with sublist in H1.
  rewrite zle_true by lia.
  rewrite zlt_true by list_solve.
  replace (map Some le) with (map Some (sublist 0 (Zlength le) le)).
  rewrite (sublist_split 0 i) by list_solve.
  rewrite map_app.
  rewrite app_Znth2 by list_solve.
  autorewrite with sublist. auto.
  rewrite sublist_same; auto.
Qed.

(* Inserts an entry in a list of entries (that doesnt already has the key) *)
Fixpoint insert_le {X:Type} (le:list (entry X)) (e:entry X) : list (entry X) :=
  match le with
  | nil => e :: nil
  | cons e' le' => if Ptrofs.cmpu Cle (entry_key e) (entry_key e') 
                          then e :: le 
                          else e' :: insert_le le' e
  end.

(* inserting adds one entry *)
Lemma Zlength_insert_le: forall X (l:list (entry X)) e,
    Zlength (insert_le l e) = Z.succ (Zlength l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct (Ptrofs.ltu (entry_key a) (entry_key e)); simpl.
    + Zlength_solve.
    + Zlength_solve.
Qed.

Hint Rewrite @Zlength_insert_le : sublist.

(* Inserts an entry e in a full node n. This function returns the right node containing the first 
   values after the split. e should have a key not already contained by the node *)
Definition splitnode_left {X:Type} (n:node X) (e:entry X) : (node X) :=
  match n with btnode ptr0 le isLeaf First Last x =>
               btnode X ptr0
                      (sublist 0 Middle (insert_le le e))
                      isLeaf
                      First
                      false    (* the right node can't be the last one *)
                      x end.

Definition splitnode_leafnode {X:Type} (le:list (entry X)) (e:entry X) (newx:X) Last :=
  (btnode X None (* Leaf node has no ptr0 *)
          (sublist Middle (Zlength (insert_le le e)) (insert_le le e))
          true   (* newnode is at same level as old one *)
          false  (* newnode can't be first node *)
          Last   (* newnode is last leaf if the split node was *)
          newx).

Definition splitnode_internnode {X:Type} (le:list (entry X)) (e:entry X) newx Last child :=
  (btnode X (Some child) (* ptr0 of the new node is the previous child of the pushed up entry *)
          (sublist (Z.succ Middle) (Zlength (insert_le le e)) (insert_le le e)) (* the middle entry isn't copied *)
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
    if isLeaf
    then                  (* in a leaf the middle key is copied up *)
      match Znth_option Middle (insert_le le e) with
      | None => e     (* not possible: the split node should be full *)
      | Some e' =>
        keychild X (entry_key e') (splitnode_leafnode le e newx Last)
      end
    else
      match Znth_option Middle (insert_le le e) with
      | None => e                (* not possible: the split node should be full *)
      | Some e' =>
        match (entry_child e') with
        | None => e              (* not possible: at intern leaf, each entry has a child *)
        | Some child =>
          keychild X (entry_key e') (splitnode_internnode le e newx Last child)
        end
      end
  end.

(* The key that is copied up when splitting a node *)
Definition splitnode_key {X:Type}(n:node X) (e:entry X) : key :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match Znth_option Middle (insert_le le e) with
    | None => Ptrofs.repr 0     (* splitnode should be full *)
    | Some e' => entry_key e'
    end
  end.
  
(* returns true if the node is full and should be split on insertion *)
Definition fullnode {X:Type} (n:node X) : bool :=
  (Fanout <=? Zlength (node_le n)).

(* Is a key already in a listentry? *)
Fixpoint key_in_le {X:Type} (key:key) (le:list (entry X)) : bool :=
  match le with
  | nil => false
  | cons e le' => if Ptrofs.eq (entry_key e) key then true else key_in_le key le'
  end.

(* listentry should contain an entry with the same key as e
   the child or record of this entry will be updated to the one of the entry 
   this is useful when inserting a (key,record) in a tree where the key has already been inserted *)
Fixpoint update_le {X:Type} (e:entry X) (le:list (entry X)) : list (entry X) :=
  match le with
  | nil => nil                (* not possible *)
  | cons e' le' => if Ptrofs.eq (entry_key e) (entry_key e')
                  then cons e le'
                  else cons e' (update_le e le')
  end.

(* updates a child in a listentry *)
Fixpoint update_le_nth_child {X:Type} (i:Z) (le:list (entry X)) (n:node X) : list (entry X) :=
  match le with
  | nil => nil
  | cons e le' => if zle i 0 
                          then  cons (keychild X (entry_key e) n) le'
                                 (* e is not expected to be a keyval *)
                         else update_le_nth_child (Z.pred i) le' n
  end.  

(* updates value in a listentry *)
Fixpoint update_le_nth_val {X:Type} (i:Z) (le:list (entry X)) (newv:V) (newx:X) : list (entry X) :=
  match le with
  | nil => nil
  | cons e le' =>  if zle i 0 
                          then cons (keyval X (entry_key e) newv newx) le'
                                  (* e is not expected to be a keychild *)
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

Lemma update_partial_snd_r X r: forall (c:cursor X) n,
      snd r = snd(snd (update_partial_cursor_rel c r n)).
Proof. 
  destruct r. induction c; simpl; intros; trivial. 
  destruct a; simpl in *.  remember (update_partial_cursor_rel c (n, x) (update_node_nth_child z n1 n0) ) .
  destruct p. simpl. specialize (IHc (update_node_nth_child z n1 n0)). rewrite <- Heqp in IHc. apply IHc.
Qed.

Lemma update_partial_cursor_result root i n prel: forall c' c nd ndd, 
(c, (n, prel)) = update_partial_cursor_rel c' (root, prel) nd ->
map (fun x0 : node val * Z => Vint (Int.repr (snd x0)))
  ((nd, i) :: c') =
map (fun x0 : node val * Z => Vint (Int.repr (snd x0)))
  ((ndd,i) :: c).
Proof. induction c'; simpl; intros.
+ inv H; trivial.
+ destruct a. f_equal. remember (update_partial_cursor_rel c' (root, prel)(update_node_nth_child z n0 nd)).
  destruct p; inv H; simpl. f_equal. eapply (IHc' c0 (update_node_nth_child z n0 nd) nd) in Heqp; clear IHc'.
  simpl in Heqp. inv Heqp. trivial.
Qed.

Lemma update_partial_cursor_result' root i n prel: forall c' c nd ndd, 
(c, (n, prel)) = update_partial_cursor_rel c' (root, prel) nd ->
map (fun x0 : node val * Z => Vint (Int.repr (snd x0)))
  ((ndd, i) :: c') =
map (fun x0 : node val * Z => Vint (Int.repr (snd x0)))
  ((nd,i) :: c).
Proof. induction c'; simpl; intros.
+ inv H; trivial.
+ destruct a. f_equal. remember (update_partial_cursor_rel c' (root, prel)(update_node_nth_child z n0 nd)).
  destruct p; inv H; simpl. f_equal. eapply (IHc' c0 (update_node_nth_child z n0 nd) nd) in Heqp; clear IHc'.
  simpl in Heqp. inv Heqp. trivial.
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
                                    (cons e (nil))
                                    false       (* new root can't be leaf *)
                                    true
                                    true
                                    (hd d newx)), prel) in
           let cursor := moveToKey X (get_root relation) oldk [] in
           (cursor, relation)
    | (n,i)::c' =>
      match n with
        btnode ptr0 le isLeaf First Last x =>
        if isLeaf
        then
          if key_in_le (entry_key e) le
          then              (* the key is already in the tree, we only update the listentry *)
            let newle := update_le e le in
            let newn := btnode X ptr0 newle isLeaf First Last x in
            update_currnode_cursor_rel c r newn
          else
            if fullnode n
            then
              let newn := splitnode_left n e in
              let newe := splitnode_right n e (hd d newx) in
              let (newc,newr) := update_currnode_cursor_rel c r newn in
              putEntry (tl newc) newr newe oldk (tl newx) d (* recursive call on previous level *)
            else          (* we insert e in le, because the node isn't full *)
              let newle := insert_le le e in
              let newn := btnode X ptr0 newle isLeaf First Last x in
              update_currnode_cursor_rel c r newn
        else
          if fullnode n
          then
            let newn := splitnode_left n e in
            let newe := splitnode_right n e (hd d newx) in
            let (newc,newr) := update_currnode_cursor_rel c r newn in
            putEntry (tl newc) newr newe oldk (tl newx) d (* recusive call on previous level *)
          else
            let newle := insert_le le e in
            let newn := btnode X ptr0 newle isLeaf First Last x in
            let (newc,newr) := update_currnode_cursor_rel c r newn in
            let movec := moveToKey X newn oldk (tl newc) in
            (movec,newr)
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
    + simpl. lia.
  - intros.
    pose (c'':=((btnode X ptr0 le false First Last x, i) :: c')). fold c''. fold c'' in teq5.
    assert (length c'' = length(fst(newc,newr))).
    rewrite <- teq5. apply update_currnode_same_length. rewrite H. simpl.
    destruct newc eqn:HC.
    + simpl in H. inv H.
    + simpl. lia.
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

Lemma FCI_increase: forall X (le:list (entry X)) key i,
    i <= findChildIndex' le key i.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. lia.
  - destruct a; simpl.
    * destruct (Ptrofs.ltu key0 k). lia.
      eapply Z.le_trans with (m:= Z.succ i). lia.
      apply IHle.
    * destruct (Ptrofs.ltu key0 k). lia.
      eapply Z.le_trans with (m:=Z.succ i). lia.
      apply IHle.
Qed.

Lemma FCI'_next_index {X: Type} (le: list (entry X)) key i:
  findChildIndex' le key (Z.succ i) = Z.succ (findChildIndex' le key i).
Proof.
  revert i.
  induction le as [|[k v x|k n] le]; simpl; try easy;
    destruct (Ptrofs.ltu key k); easy.
Qed.  

Lemma FRI'_next_index {X: Type} (le: list (entry X)) key i:
  findRecordIndex' le key (Z.succ i) = Z.succ (findRecordIndex' le key i).
Proof.
  revert i.
  induction le as [|[k v x|k n] le]; simpl; try easy;
    destruct (Ptrofs.ltu k key); simpl; easy.
Qed.

Lemma FCI_inrange: forall X (n:node X) key,
    -1 <= findChildIndex n key < Zlength (node_le n).
Proof.
  intros X n key.
  destruct n as [ptr0 le isLeaf F L x]; simpl.
  induction le. easy. simpl.
  autorewrite with sublist.
  destruct a as [k v x'|k n]; destruct (Ptrofs.ltu key k);
  replace (findChildIndex' le key 0) with (Z.succ (findChildIndex' le key (-1))) by now rewrite <- FCI'_next_index.
  all: destruct (findChildIndex' le key (-1)); unfold  findChildIndex' in IHle |- *; lia.
Qed.

Lemma FCI_inrange'': forall X (le:list (entry X)) key j i,
    findChildIndex' le key j = i ->
    j <= i.
Proof.
  intros.
  revert j H; induction le; simpl; intros. lia.
  destruct a as [k v x'|k n]; destruct (Ptrofs.ltu key0 k); simpl in *; try lia.
  1,2: apply IHle in H; lia.
Qed.

Lemma FRI_increase: forall X (le:list (entry X)) key i,
    i <= findRecordIndex' le key i.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. lia.
  - destruct a; simpl.
    * destruct (Ptrofs.ltu k key0); simpl; try lia.
      eapply Z.le_trans with (m:= Z.succ i). lia.
      apply IHle.
    * destruct (Ptrofs.ltu k key0); simpl; try lia.
      eapply Z.le_trans with (m:= Z.succ i). lia.
      apply IHle.
Qed.

Lemma FRI_inrange: forall X (n:node X) key,
    0 <= findRecordIndex n key <= Zlength (node_le n).
Proof.
  intros X n key.
   destruct n as [ptr0 le isLeaf F L x]; simpl.
  rewrite <- (Z.add_0_r (Zlength le)).
  forget 0 as i.
  revert i; induction le; intros. easy.
  simpl. autorewrite with sublist.
  pose proof (Zlength_nonneg le).
  destruct (Ptrofs.ltu (entry_key a) key); simpl; try easy; try lia.
  specialize (IHle (Z.succ i));   lia.
Qed.


