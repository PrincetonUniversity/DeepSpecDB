(** * btrees.v : Formal Model of BTrees  *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.

Require Import index.

(**
    BTREES FORMAL MODEL
 **)

Definition Fanout := 15%nat.
Lemma Fanout_eq : Fanout = 15%nat.
Proof. reflexivity. Qed.
Definition MaxTreeDepth := 20%nat.
Lemma MTD_eq : MaxTreeDepth = 20%nat.
Proof. reflexivity. Qed.

Hint Rewrite Fanout_eq : rep_omega.
Hint Rewrite MTD_eq : rep_omega.
Global Opaque Fanout.
Global Opaque MaxTreeDepth.

Definition key := Z.            (* unsigned long in C *)
Definition V:Type := Z.         (* I need some type for value_rep *)
Variable b : nat.
Variable X:Type.                (* val or unit *)

Inductive entry (X:Type): Type :=
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: option (node X) -> listentry X -> bool -> bool -> bool -> X -> node X
with listentry (X:Type): Type :=
     | nil: listentry X
     | cons: entry X -> listentry X -> listentry X.

Definition cursor (X:Type): Type := list (node X * index). (* ancestors and index *)
Definition relation (X:Type): Type := node X * nat * nat * X.  (* root, numRecords and depth *)

Definition entryIndex {X:Type} (c:cursor X) : index :=
  match c with
  | [] => ip 0
  | (n,i)::c' => i
  end.

Definition currNode {X:Type} (c:cursor X) : option (node X) :=
  match c with
  | [] => None
  | (n,i)::c' => Some n
  end.

Fixpoint numKeys_le {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => 0%nat
  | cons e le' => S (numKeys_le le')
  end.

Definition numKeys {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ _ _ x => numKeys_le le end.

Definition isValid {X:Type} (c:cursor X) : bool :=
  match c with
  | [] => false
  | (n,i)::c' =>
    match n with btnode ptr0 le isLeaf First Last x =>
                 Last && (index_eqb i (ip (numKeys_le le)))
    end
  end.                      

Definition isFirst {X:Type} (c:cursor X) : bool :=
  match c with
  | [] => false
  | (n,i)::c' =>
    match n with btnode ptr0 le isLeaf First Last x =>
                 First && (index_eqb i (ip 0))
    end
  end.

Fixpoint node_depth {X:Type} (n:node X) : nat :=
  match n with
    btnode ptr0 le _ _ _ _ => max_nat (listentry_depth le)
                                (match ptr0 with
                                 | None => O
                                 | Some n' => S (node_depth n') end)
  end
with listentry_depth {X:Type} (le:listentry X) : nat :=
       match le with
       | nil => O
       | cons e le' => max_nat (entry_depth e) (listentry_depth le')
       end
with entry_depth {X:Type} (e:entry X) : nat :=
       match e with
       | keyval _ _ _ => S O
       | keychild _ n => S (node_depth n)
       end.                                                 

Fixpoint nth_entry_le {X:Type} (i:nat) (le:listentry X): option (entry X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => Some e
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_entry_le i' le'
            end
  end.

Fixpoint le_length {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => O
  | cons _ le' => S (le_length le')
  end.

Definition node_length {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ _ _ _ => le_length le end.

Fixpoint nth_node_le {X:Type} (i:nat) (le:listentry X): option (node X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => match e with
                       | keychild _ n => Some n
                       | keyval _ _ _ => None
                       end
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_node_le i' le'
            end
  end.

Lemma nth_node_le_decrease: forall X (le:listentry X) (n:node X) i,
    nth_node_le i le = Some n ->
    (node_depth n < listentry_depth le)%nat.
Proof.
  induction le; intros.
  - unfold nth_node_le in H.
    destruct i; inversion H.
  - simpl.
    destruct i.
    + apply le_max_split_l. simpl in H. destruct e; try inv H. simpl. auto.
    + apply le_max_split_r. apply IHle with (i:=i). simpl in H. auto.
Qed.
      
Definition nth_node {X:Type} (i:index) (n:node X): option (node X) :=
  match n with btnode ptr0 le _ _ _ _ =>
               match i with
               | im => ptr0
               | ip na => nth_node_le na le
               end
  end.

Lemma nth_node_decrease: forall X (n:node X) (n':node X) i,
    nth_node i n = Some n' ->
    (node_depth n' < node_depth n)%nat.
Proof.
  intros. unfold nth_node in H.
  destruct n. destruct i.
  - simpl. destruct o. inversion H. subst.
    apply le_max_split_r. auto. inversion H.
  - simpl. apply le_max_split_l. apply nth_node_le_decrease with (i:=n). auto.
Qed.

Definition getRecord (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,i)::c' =>
    match n with
      btnode ptr0 le b _ _ x =>
      match i with
      | im => nullval              (* no -1 at leaf nodes *)
      | ip ii =>
        match (nth_entry_le ii le) with
        | None => nullval
        | Some e =>
          match e with
          | keychild _ _ => nullval
          | keyval k v x => x
          end
        end
      end
    end
  end.

Definition getKey {X:Type} (c:cursor X): option key :=
  match c with
  | [] => None
  | (n,i)::c' =>
    match n with
      btnode ptr0 le b _ _ x =>
      match i with
      | im => None            (* ptr0 has no key *)
      | ip ii => 
        match (nth_entry_le ii le) with
        | None => None
        | Some e =>
          match e with
          | keychild k _ => Some k
          | keyval k _ _ => Some k
          end
        end
      end
    end
  end.

Fixpoint findChildIndex' {X:Type} (le:listentry X) (key:key) (i:index): index :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (key <? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    | keychild k c =>
      match (key <? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    end
  end.

Definition findChildIndex {X:Type} (le:listentry X) (key:key): index :=
  findChildIndex' le key im.

Fixpoint findRecordIndex' {X:Type} (le:listentry X) (key:key) (i:index): index :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (key <=? k) with
      | true => i
      | false => findRecordIndex' le' key (next_index i)
      end
    | keychild k c =>
      match (key <=? k) with
      | true => i
      | false => findRecordIndex' le' key (next_index i)
      end
    end
  end.

Definition findRecordIndex {X:Type} (le:listentry X) (key:key) : index :=
  findRecordIndex' le key (ip O).

Fixpoint update_le_nth_child {X:Type} (i:nat) (le:listentry X) (n:node X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' => match i with
                  | O => match e with
                         | keychild k c => cons X (keychild X k n) le'
                         | keyval k v x => cons X (keychild X k n) le' (* shouldnt happen *)
                         end
                  | S i' => update_le_nth_child i' le' n
                  end
  end.  

Fixpoint update_le_nth_val {X:Type} (i:nat) (le:listentry X) (newv:V) (newx:X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' => match i with
                  | O => match e with
                         | keychild k c => cons X (keyval X k newv newx) le' (* shouldnt happen *)
                         | keyval k v x => cons X (keyval X k newv newx) le'
                         end
                  | S i' => update_le_nth_val i' le' newv newx
                  end
  end.

Definition update_node_nth_child {X:Type} (i:index) (oldn:node X) (n:node X) : node X :=
  match oldn with btnode ptr0 le isLeaf First Last x =>
  match i with
  | im => btnode X (Some n) le isLeaf First Last x
  | ip ii => btnode X ptr0 (update_le_nth_child ii le n) isLeaf First Last x
  end
  end.

Fixpoint update_cursor {X:Type} (c:cursor X) (n:node X) : cursor X :=
  match c with
  | [] => []
  | (oldn,i)::c' =>
    let newn := update_node_nth_child i oldn n in
    (newn,i)::(update_cursor c' newn)
  end.

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