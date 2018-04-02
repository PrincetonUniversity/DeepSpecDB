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
     | btnode: option (node X) -> listentry X -> bool -> X -> node X
with listentry (X:Type): Type :=
     | nil: listentry X
     | cons: entry X -> listentry X -> listentry X.

Inductive index: Type :=
| im: index
| ip: nat -> index.

Definition nat_to_index (n:nat) := ip n.

Definition cursor (X:Type): Type := list (node X * index). (* ancestors and index *)
Definition full_cursor (X:Type) : Type := bool * cursor X.
Definition relation (X:Type): Type := node X * nat * X.  (* root and numRecords *)

Definition next_index (i:index) : index :=
  match i with
  | im => ip (O%nat)
  | ip n => ip (S n)
  end.

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Lemma max_0: forall a, max_nat a 0 = a.
Proof. induction a. auto. simpl. auto. Qed.

Theorem le_max_split_l: forall n a b,
    (n < a)%nat -> (n< max_nat a b)%nat.
Proof.
  intros.
  generalize dependent n.
  generalize dependent b0.
  generalize dependent a.
  induction a; intros.
  - inversion H.
  - destruct b0.
    + rewrite max_0. auto.
    + simpl. destruct n. omega.
      assert (n<a)%nat by omega. apply IHa with (b0:=b0) in H0. omega.
Qed.      

Theorem max_flip: forall a b, max_nat a b = max_nat b a.
Proof.
  induction a; intros.
  - simpl. rewrite max_0. auto.
  - simpl. destruct b0.
    + simpl. auto.
    + simpl. rewrite IHa. auto.
Qed.    

Theorem le_max_split_r: forall n a b,
    (n < b)%nat -> (n< max_nat a b)%nat.
Proof.
  intros. rewrite max_flip. apply le_max_split_l. auto.
Qed.
  
Definition max_index (i1:index) (i2:index): index :=
  match i1 with
  | im => i2
  | ip n1 => match i2 with
            | im => i1
            | ip n2 => ip (max_nat n1 n2)
             end
  end.

Fixpoint node_depth {X:Type} (n:node X) : nat :=
  match n with
    btnode ptr0 le _ _ => max_nat (listentry_depth le)
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
  end.                          (* USEFUL? *)

Fixpoint numKeys_le {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => 0%nat
  | cons e le' => S (numKeys_le le')
  end.

Definition numKeys {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ x => numKeys_le le end.

  
Fixpoint move_to_first {X:Type} (c:cursor X) (curr:node X): cursor X:=
  match curr with btnode ptr0 le _ _ =>
                  match ptr0 with
                  | Some n => move_to_first ((curr,im)::c) n
                  | None => match le with
                            | nil => c (* possible? *)
                            | cons e le' => match e with
                                            | keyval _ _ _ => ((curr,ip (0%nat))::c)
                                            | keychild _ _ => c (* not possible, we would have a ptr0 otherwise *)
                                            end
                            end
                  end
  end.

Fixpoint full_move_to_first {X:Type} (csr:full_cursor X) (curr:node X): full_cursor X:=
  match csr with (b,c) =>
                 match numKeys curr with
                                    | O => (false, move_to_first c curr)
                                    | _ => (true, move_to_first c curr)
                 end
  end.

Fixpoint le_length {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => O
  | cons _ le' => S (le_length le')
  end.

Definition node_length {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ _ => le_length le end.

Definition index_leb_nat (i:index) (n:nat) : bool :=
  match i with
  | im => true
  | ip n' => (n' <=? n)%nat
  end.

Fixpoint move_to_next_partial {X:Type} (c:cursor X) : cursor X :=
  match c with
  | [] => []
  | (n,i)::c' =>
    match (index_leb_nat i (node_length n -2)) with 
    | true => (n,next_index i)::c'
    | false => move_to_next_partial c'
    end
  end.

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
  match n with btnode ptr0 le _ _ =>
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

Definition move_to_next {X:Type} (c:cursor X): cursor X * bool :=
  match (move_to_next_partial c) with
  | [] => (c,false)                     (* C program returns false here *)
  | (n,i)::c' => match nth_node i n with
                 | Some n' => (move_to_first c n',true)
                 | None => (c,true)    (* possible at leaf nodes *)
                 end
  end.

Definition getRecord (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,i)::c' =>
    match n with
      btnode ptr0 le b x =>
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
      btnode ptr0 le b x =>
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
      match (key <=? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    | keychild k c =>
      match (key <=? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    end
  end.

Definition findChildIndex {X:Type} (le:listentry X) (key:key): index :=
  findChildIndex' le key im.

(* n should be the current node pointed to, so if c=(m,i)::c', it should be m(i) *)
Function moveToRecord {X:Type} (c:cursor X) (key:key) (n:node X) {measure node_depth n}: cursor X * bool :=
  match n with btnode ptr0 le isLeaf x =>
               match isLeaf with
               | true =>
                 match findChildIndex le key with
                 | im => ((n,ip 0)::c, false)
                 | ip ii =>
                   match getKey ((n,ip ii)::c) with
                   | None => (c,false)  (* shouldnt happen, findChildIndex return valid indexes *)
                   | Some k => ((n,ip ii)::c, key =? k)
                   end
                 end
               | false =>
                 match nth_node (findChildIndex le key) n with
                 | None => (c,false)    (* should not happen: we should have ptr0 and findChildIndex should not overflow *)
                 | Some n' =>
                   moveToRecord ((n,findChildIndex le key)::c) key n'
                 end
               end
  end.
Proof.
  intros.
  apply nth_node_decrease with (i:= findChildIndex le key0). auto.
Qed.

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
  match oldn with btnode ptr0 le isLeaf x =>
  match i with
  | im => btnode X (Some n) le isLeaf x
  | ip ii => btnode X ptr0 (update_le_nth_child ii le n) isLeaf x
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
  
(* c should not be complete, and points to n *)
(* nEFC is newEntryFromChild pointer *)
Fixpoint insertKeyRecord' {X:Type} (key:key) (value:V) (nEFC:X) (n:node X) (c:cursor X): node X * cursor X * bool :=
  match n with btnode ptr0 le isLeaf x =>
  match isLeaf with
  | true =>
    match le with
    | nil =>               (* first key *)
      let newn:= btnode X ptr0 (cons X (keyval X key value nEFC) (nil X)) isLeaf x in
      (newn,update_cursor c newn,true)
    | _ =>
      match (findChildIndex le key) with
      | im => (n,c,false) (* TODO: THIS IS NOT ADDRESSED IN THE C CODE!!! *)
      | ip ii =>
        match (nth_key ii le) with
        | None => (n,c,false)   (* impossible, findChildIndex returns an index in range ? *)
        | Some k =>
          match (k =? key) with
          | true =>             (* update *)
            let newn:= btnode X ptr0 (update_le_nth_val ii le value nEFC) isLeaf x in
            (newn,update_cursor c newn,true) (* I don't think we should use nEFC. wich val? *)
          | false => (n,c,false)          (* new node, TODO *)
          end
        end
      end
    end
  | false => (n,c,false) (* TODO *)
  end
  end.
