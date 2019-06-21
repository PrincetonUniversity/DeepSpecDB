(** * btrees.v : Formal Model of BTrees  *)

Require Import VST.floyd.functional_base.
Require Import Sorting.Sorted.
Require Import Program.Basics.
Require Import Program.Combinators.

Import ListNotations.
(* Maximum number of entries in a node *)
Definition Fanout := 15%nat.
(* Middle = (Fanout+1)/2, for splitting nodes *)
Definition Middle := 8%nat.
(* Maximum tree depth *)
Definition MaxTreeDepth := 20%nat.

Definition K := Z. Definition V := ptrofs.
Context {X: Type}.

(* B+tree abtract model *)
Inductive node: Type :=
| leaf: forall (records: list (K * V * X)) (isFirst: bool) (isLast: bool) (val: X), node
| internal: forall (ptr0: node) (children: list (K * node)) (isFirst: bool) (isLast: bool) (val: X), node.

Definition isLeaf (n: node): bool := 
  match n with | leaf _ _ _ _ => true | internal _ _ _ _ _ => false end.

Definition keys (n: node): list K := 
  match n with | leaf recs _ _ _ => map (fst ∘ fst) recs | internal _ children _ _ _ => map fst children end.

Definition F (n: node): bool := 
  match n with | leaf _ F _ _ => F | internal _ _ F _ _ => F end.

Definition L (n: node): bool := 
  match n with | leaf _ _ L _ => L | internal _ _ _ L _ => L end.

Definition val (n: node): X := 
  match n with | leaf _ _ _ x => x | internal _ _ _ _ x => x end.

(* number of keys in a node *)
Definition numKeys (n:node) : nat := length (keys n).

Section correct_node_ind.
  Variables (P : node -> Prop) (Q : list (K * node)-> Prop).

  Hypotheses
    (hleaf: forall l F L v, P (leaf l F L v))
    (hinternal : forall ptr0 (entries:list (K * node)) F L v,
        P ptr0 -> Q entries -> P (internal ptr0 entries F L v))
    (hnil : Q [])
    (hcons : forall (k: K) (n: node), P n -> forall l: list (K * node), Q l -> Q (cons (k,n) l)).

  Fixpoint node_ind2 (n: node): P n :=
    match n as x return P x with
    | leaf l F L v => hleaf l F L v
    | internal ptr0 l F L v =>
      hinternal ptr0 l F L v (node_ind2 ptr0)
                (((fix l_ind (l':list (K * node)) : Q l' :=
                     match l' as x return Q x with
                     | nil => hnil
                     | cons (k1, n1) tl => hcons k1 n1 (node_ind2 n1) tl (l_ind tl)
                     end)) l)
    end.
End correct_node_ind.

Lemma node_induction (P: node -> Prop)
        (hleaf: forall entries isFirst isLast val, P (leaf entries isFirst isLast val))
        (hinternal : forall ptr0 (entries:list (K * node)) isFirst isLast val,
            P ptr0 -> Forall (P ∘ snd) entries -> P (internal ptr0 entries isFirst isLast val)):
  forall n: node, P n.
Proof.
  refine (node_ind2 P (Forall (P ∘ snd)) hleaf hinternal _ _).
  easy. now constructor.
Qed.

(* Abstracting a B+tree to an ordered list of (key,value) pairs *)
Fixpoint abs_node (n: node) : list (K * V) :=
  match n with
  | leaf le _ _ _ => map fst le
  | internal ptr0 le _ _ _ => abs_node ptr0 ++ flat_map (abs_node ∘ snd) le
  end.

(* Number of records the B+tree is holding *)
Fixpoint node_numrec (n:node): nat :=
  match n with
  | leaf le _ _ _ => length le
  | internal ptr0 le _ _ _ => node_numrec ptr0 + fold_right Nat.add 0%nat (map (node_numrec ∘ snd) le)
  end.

Lemma numrec_abs_node_length (n: node): length (abs_node n) = node_numrec n.
Proof.
  apply (node_induction (fun n => Datatypes.length (abs_node n) = node_numrec n)).
  + intros. simpl. now rewrite map_length.
  + intros * hlength hforall.
    simpl. rewrite app_length, hlength.
    replace (Datatypes.length (flat_map (abs_node ∘ snd) entries))%nat with
        (fold_right Nat.add 0 (map (node_numrec ∘ snd) entries))%nat.
    reflexivity.
    induction entries. reflexivity.
    simpl. rewrite app_length. inversion hforall. simpl in H1. rewrite H1.
    rewrite IHentries. reflexivity. assumption.
Qed.

Fixpoint nth_key (i:nat) (n: node): option K := nth_error (keys n) i.

Inductive balanced: forall (depth: nat) (n: node), Prop :=
| leaf_balanced: forall le F L v, balanced 0 (leaf le F L v)
| internal_balanced: forall d ptr0 hd tl F L v,
    let l := hd :: tl in
    balanced d ptr0 -> Forall (balanced d ∘ snd) l -> balanced (S d) (internal ptr0 l F L v).

Definition relation: Type := {rootd : node * nat | balanced (snd rootd) (fst rootd)} * X.

Coercion relation_as_btree := fun (r : relation) => fst (proj1_sig (fst r)).

Definition root (r: relation): node := fst (proj1_sig (fst r)).
Definition depth (r: relation): nat := snd (proj1_sig (fst r)).

(* numRecords of the relation *)
Definition get_numrec (rel: relation) : nat := node_numrec (root rel).

Definition index (n: node): Type :=
  if isLeaf n then {k: nat | (k <= numKeys n)%nat}
  else unit + {k: nat | (k < numKeys n)%nat}.

Definition ptr0_index {ptr0 l F L v} : index (internal ptr0 l F L v) := inl tt.

Definition internal_le_index {ptr0 l F L v}:
  forall (k: nat) (h: (k < length l)%nat), index (internal ptr0 l F L v).
refine (fun k h => inr (exist _ k _)).
cbn. now rewrite map_length.
Defined.

Definition leaf_le_index {l F L v}:
  forall (k: nat) (h: (k <= length l)%nat), index (leaf l F L v).
refine (fun k h => exist _ k _).
cbn. now rewrite map_length.
Defined.

Definition next_index {n: node} {d: nat} (hbal: balanced d n): index n -> index n.
refine
  ((match n as m return n = m -> index m -> index m with
  | leaf l _ _ _ =>
    fun heq i => match i with exist k hk => exist _ (min (k + 1) (numKeys n)) _ end
  | internal _ l _ _ _ =>
    fun heq i => match i with
             | inl tt => inr (exist _ 0%nat _)
             | inr (exist k hk) => inr (exist _ (min (k + 1) (pred (numKeys n))) _) end
  end) eq_refl).
+ subst. apply Nat.le_min_r.
+ subst. inversion hbal. cbn. omega.
+ subst. rewrite Nat.min_lt_iff. right. omega.
Defined.

Definition prev_index {n: node} {d: nat} (hbal: balanced d n): index n -> index n.
refine
  (match n as m return n = m -> index m -> index m with
  | leaf l _ _ _ =>
    fun heq i => match i with exist k hk => exist _ (pred k) _ end
  | internal _ l _ _ _ =>
    fun heq i => match i with
                 | inl tt => inl tt
                 | inr (exist 0%nat hk) => inl tt
                 | inr (exist k hk) => inr (exist _ (pred k) _) end
    end eq_refl); omega.
Defined.

Definition findChildIndex (n: node) {d} (key:K): balanced d n -> option (index n) :=
  match n as m return balanced d m -> option (index m) with
  | leaf _ _ _ _ => fun _ => None
  | internal _ _ _ _ _ => fun hbal =>
    Some (fold_left (fun acc k => if key <? k then acc else next_index hbal acc) (keys n) ptr0_index)
  end.

Definition findRecordIndex (n: node) {d} (key:K): balanced d n -> option (index n).
  refine (
  match n as m return n = m -> balanced d m -> option (index m) with
  | leaf _ _ _ _ => fun heq hbal =>
                      Some (fold_right (fun k acc => if key <=? k then prev_index hbal acc else acc)
                                       (leaf_le_index (numKeys n) _) (keys n))
  | internal _ _ _ _ _ => fun _ => fun _ => None
  end eq_refl).
  subst. cbn. rewrite map_length. constructor.
Defined.

Inductive isParent: {parent: node & index parent} -> node -> Prop :=
| is_ptr0: forall ptr0 le F L v,
    isParent (existT _ (internal ptr0 le F L v) (inl tt)) ptr0
| in_le: forall ptr0 le F L v n i hi,
    nth_error (map snd le) i = Some n ->
    isParent (existT (fun n => index n) (internal ptr0 le F L v) (inr (exist _ i hi))) n.

Definition cursorEntry: Type := {n: node & index n}.

Definition cursor (r: relation) :=
  { c: list cursorEntry |
    Sorted (fun e1 e2 => isParent e1 (projT1 e2)) c /\ option_map (@projT1 _ (fun n => index n)) (hd_error c) = Some (root r) }.

Definition cursor_in_lists: forall r, cursor r -> list cursorEntry := fun r c => proj1_sig c.
Coercion cursor_in_lists: cursor >-> list.

Section Cursors.
  Context {r: relation}.

  Lemma cursor_neq_nil (c: cursor r): (c: list _) <> [].
  Proof.
    now destruct c as [[|ni c] [hsorted hhd]].
  Qed.

  Definition lastPair (c: cursor r): cursorEntry := proj1_sig (projT2 (exists_last (cursor_neq_nil c))).

  Definition currNode (c: cursor r): node := projT1 (lastPair c).
  Definition entryIndex (c: cursor r): index (currNode c):= projT2 (lastPair c).

  Definition isComplete (c: cursor r): bool :=
    isLeaf (currNode c).

  Lemma cursor_relation_depth (c: cursor r): (length c <= S (depth r))%nat.
  Proof.  
    destruct r as [[[root depth] hbalanced] v], c as [[|ni c] [hsorted hhd]]; cbn.
    easy. apply le_n_S.
    cbn in hhd, hbalanced. destruct ni. inversion hhd.
    subst. clear hhd v.
    revert root depth i c hbalanced hsorted.
    apply (node_induction (fun root => forall (depth0 : nat) (i : index root) (c : list cursorEntry),
                               balanced depth0 root ->
                               Sorted (fun e1 e2 : {parent : node & index parent} => isParent e1 (projT1 e2)) (existT (fun n : node => index n) root i :: c) -> (Datatypes.length c <= depth0)%nat)).
    + intros * hbalanced hsorted. inversion hbalanced. inversion hsorted. inversion H7. easy. inversion H8.
    + intros * hptr0 hchildren depth i c hbalanced hsorted.
      destruct c as [|[newroot newindex] c]. cbn. omega. cbn.
      inversion hbalanced. apply le_n_S. inversion hsorted.
      inversion_clear H10. rewrite Forall_forall in hchildren, H6. unfold compose in hchildren.
      inversion H11; cbn in H11; subst.
    - now apply (hptr0 _ newindex).
    - apply nth_error_In, list_in_map_inv in H17.
      destruct H17 as [x [hnsndx hIn]]. cbn in hnsndx. subst.
      apply (hchildren x hIn _ newindex). now apply H6. easy.
  Qed.

  Lemma Lsorted_app1 {A: Type} (R: A -> A -> Prop):
    forall (l: list A) (hlnil: l <> []) (a: A) (hsorted: Sorted R l) (hR: R (proj1_sig (projT2 (exists_last hlnil))) a),
      Sorted R (l ++ [a]).
  Proof.
    intros.
    destruct (exists_last hlnil) as [l' [last h]]. cbn in hR.
    rewrite h in hsorted |- *. rewrite <- app_assoc. cbn. clear hlnil h.
    induction l'. now repeat constructor.
    destruct l'. inversion hsorted. inversion H2. repeat constructor. assumption. assumption.
    cbn in hsorted, IHl' |- *. inversion hsorted. constructor. apply IHl'. assumption. constructor.
    inversion H2. assumption.
  Qed.

  Definition cursor_cons (c: cursor r) (n: node) (i: index n)
             (h : isParent (lastPair c) n): cursor r.
  Proof.
    refine (exist _ (c ++ [existT _ n i]) _).
    destruct c as [[|[n' i'] c] [hsorted hrel]]. easy.
    cbn in hrel |- *.
    split.
    + rewrite app_comm_cons. eapply Lsorted_app1. assumption.
      exact h.
    + assumption.
  Defined.
  
  Lemma lastPair_cursor_cons (c: cursor r) (n: node) (i: index n)
        (h : isParent (lastPair c) n):
    lastPair (cursor_cons c n i h) = existT _ n i.
  Proof.
    unfold lastPair.
    destruct (exists_last (cursor_neq_nil (cursor_cons c n i h))) as [l' [[n' i'] happ]].
    cbn.
    unfold cursor_cons in happ. cbn in happ. now apply app_inj_tail in happ.
  Qed.
  
  (* is a cursor valid? invalid if the cursor is past the very last key *)
  Definition isValid (c: cursor r): bool :=
    match lastPair c with
    | existT (leaf l F L v) (exist i _) =>
      negb (andb L (nat_eq_dec i (length l)))
    | _ => false
    end.

  (* does the cursor point to the very first key? *)
  Definition isFirst (c: cursor r): bool :=
    match lastPair c with
    | existT (leaf _ F _ _) (exist i _) => F && (i =? 0)%nat
    | _ => false end.

  (* get record pointed to by cursor *)
  Definition getCEntry (c:cursor r) : option (K * V * X) :=
    match lastPair c with
    | existT (leaf l F L v) (exist i _) => nth_error l i
    | _ => None
    end.
  (* Warning: the .c moveToFirst accepts an empty cursor (and the relation root as n) as input. *)
  (* Goes down to first key *)
  Program Fixpoint moveToFirst (c: cursor r) (n: node)
          {measure (length c) (fun x y: nat => (y < x <= depth r + 2)%nat)}:
    isParent (lastPair c) n -> cursor r :=
    match n as m return isParent (lastPair c) m -> cursor r with
    | leaf le F L v as m => fun hpar => cursor_cons c m (leaf_le_index 0%nat (Nat.le_0_l _)) _
    | internal ptr0 le F L v as m => fun hpar => moveToFirst (cursor_cons c m ptr0_index _) ptr0 _
    end.
  Next Obligation.
    rewrite app_length.
    pose proof (cursor_relation_depth c). cbn. omega.
  Qed.
  Next Obligation.
    rewrite lastPair_cursor_cons. constructor.
  Qed.
  Next Obligation.
    apply Wf.measure_wf, Nat.gt_wf.
  Defined.

 Lemma  moveToFirst_eq (c: cursor r) le F L v
             (h : pairwiseCursorIntegrity (lastPair c) (leaf le F L v, ip 0)):
   moveToFirst c (leaf le F L v) h = cursor_cons c (leaf le F L v) (ip 0) h.
 Proof.
   unfold moveToFirst. unfold moveToFirst_func. cbn.
  
End Cursors.
  
Lemma moveToFirst_complete {r: relation} (c: cursor r) (n: node)
      (h: pairwiseCursorIntegrity (lastPair c) (n, if isLeaf n then ip 0 else im)):
  isComplete (moveToFirst c n h) = true.
Proof.
  
  destruct n as [|ptr0 le F L v].
  
  cbn.
  revert dependent c.
  apply (Fix (Wf.measure_wf (Nat.gt_wf (depth r)) (fun (c: cursor r) => length c))
             (fun c => forall (h : pairwiseCursorIntegrity (lastPair c) (n, if isLeaf n then ip 0 else im)),
                  isComplete (moveToFirst c n h) = true)).
  intros c hind hint.
  unfold Wf.MR in hind.
  destruct n as [|ptr0 le F L v].
  
  replace (moveToFirst c (leaf records isFirst0 isLast val0) hint) with (cursor_cons c (leaf records isFirst0 isLast val0) (ip 0) hint). cbn.
  unfold moveToFirst, moveToFirst_func. 
  unfold moveToFirst.
  unfold isComplete. unfold moveToFirst. 
  
  
(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to last key *)
Program Fixpoint moveToLast (c:cursor r) (n: node)
        (h : pairwiseCursorIntegrity (lastPair c) (n, if isLeaf n then ip (numKeys n) else ip (numKeys n - 1)))
        {measure (length c) (fun n m: nat => (m < n <= depth r + 2)%nat)}: cursor r :=
  match n with
  | leaf le F L v => cursor_cons c n (ip (numKeys n)) _
  | internal ptr0 le F L v => moveToFirst (cursor_cons c n (ip (numKeys n - 1)) _)
                                          (nth (numKeys n - 1) (map snd le) ptr0) _
  end.
Next Obligation.
  cbn.
  
  destruct ptr0; cbn in h |- *;
    rewrite lastPair_cursor_cons; constructor. omega.
  
Next Obligation.
  apply Wf.measure_wf, Nat.gt_wf.
Qed.                       


Function moveToLast {X:Type} (n:node X) (c:cursor X) (level:nat) {measure node_depth n}: cursor X :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => (n,ip (numKeys n))::c
    | false => match (nth_node (ip(numKeys n -1)) n)  with
               | None => c      (* not possible, isLeaf is false *)
               | Some n' => moveToLast n' ((n,ip (numKeys n -1))::c) (level+1)
               end
    end
  end.
Proof.
  intros. apply nth_node_decrease in teq1. auto.
Qed.

(* takes a PARTIAL cursor, n next node (pointed to by the cursor) and goes down to the key, or where it should be inserted *)
Function moveToKey {X:Type} (n:node X) (key:key) (c:cursor X) {measure node_depth n} : cursor X :=
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
  intros. apply nth_node_decrease in teq1. auto.
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
  match isLeaf with
  | true =>
    let numkeys := numKeys_le le in
    match numkeys with
    | O => true
    | S numm =>
      match nth_entry_le O le with
      | None => false                 (* impossible *)
      | Some e0 =>
        let lowest := entry_key e0 in
        match nth_entry_le numm le with
        | None => false         (* impossible *)
        | Some el =>
          let highest := entry_key el in
          andb ( orb (key.(k_) >=? lowest.(k_)) (First))
               ( orb (key.(k_) <=? highest.(k_)) (Last))
        end
      end
    end
  | false =>
    match findChildIndex n key with
    | im => false
    | ip ii => negb (Nat.eqb (S ii) (numKeys n))
    end
  end
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
Definition lastpointer {X:Type} (n:node X): index :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               match isLeaf with
               | true => ip (numKeys_le le)
               | false => match numKeys_le le with
                          | O => im
                          | S ii => ip ii
                          end
               end
  end.

(* Returns the index of the first pointer of a node *)
Definition firstpointer {X:Type} (n:node X): index :=
  match n with btnode ptr0 le isLeaf First Last pn =>
               match isLeaf with
               | true => ip O
               | false => im
               end
  end.

(* Goes up in the cursor as long as the index is the last possible one for the current node *)
Fixpoint up_at_last {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | [(n,i)] => [(n,i)]
  | (n,i)::c' => match index_eqb i (lastpointer n) with
                 | false => c
                 | true => up_at_last c'
                 end
  end.

(* Increments current index of the cursor. The current index should not be the last possible one *)
Definition next_cursor {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,next_index i)::c'
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
  | (n,i)::c' => match index_eqb i (firstpointer n) with
                 | false => c
                 | true => up_at_first c'
                 end
  end.

(* Decrements current index of the cursor. The current index should not be the first possible one *)
Definition prev_cursor {X:Type} (c:cursor X): cursor X :=
  match c with
  | [] => []
  | (n,i)::c' => (n,prev_index i)::c'
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
          moveToLast X n' cdecr (length cdecr) (* going down on the left if we had to go up *)
        end
      end
    end
  end.

Definition normalize {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c
  | (n,i)::c' => match (index_eqb i (ip (numKeys n))) with
                 | true => moveToNext c r
                 | false => c
                 end
  end.

(* moves the cursor to the next non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToNext {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c' => match (index_eqb i (ip (numKeys n))) with
                 | true => moveToNext (moveToNext c r) r (* at last position, move twice *)
                 | false => moveToNext c r
                 end
  end.

(* move the cursor to the previous non-equivalent position 
 takes a FULL cursor as input *)
Definition RL_MoveToPrevious {X:Type} (c:cursor X) (r:relation X) : cursor X :=
  match c with
  | [] => c                     (* not possible *)
  | (n,i)::c => match (index_eqb i (ip O)) with
                | true => moveToPrev (moveToPrev c r) r (* at first position, move twice *)
                | false => moveToPrev c r
                end
  end.

(* the nth first entries of a listentry *)
Fixpoint nth_first_le {X:Type} (le:listentry X) (i:nat) {struct i}: listentry X :=
  match i with
  | O => nil X
  | S ii => match le with
           | cons e le' => cons X e (nth_first_le le' ii)
           | nil => nil X
           end
  end.

(* number of first keys *)
Lemma numKeys_nth_first: forall (X:Type) (le:listentry X) i,
    (i <= numKeys_le le)%nat ->
    numKeys_le (nth_first_le le i) = i.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - destruct i; simpl. auto. simpl in H. omega.
  - destruct i.
    + simpl. auto.
    + simpl. apply f_equal. apply IHle. simpl in H. omega.
Qed.

(* selecting all keys of a listentry *)
Lemma nth_first_same: forall X (l:listentry X) m,
    m = numKeys_le l ->
    nth_first_le l m = l.
Proof.
  intros. generalize dependent m.
  induction l; intros.
  - destruct m; simpl; auto.
  - destruct m. simpl in H. inv H. simpl. rewrite IHl. auto. simpl in H. inv H. auto.
Qed.

(* skips the nth first entries of a listentry *)
Fixpoint skipn_le {X:Type} (le:listentry X) (i:nat) : listentry X :=
  match i with
  | O => le
  | S ii => match le with
           | nil => nil X
           | cons e le' => skipn_le le' ii
           end
  end.

(* number of keys when skipping *)
Lemma numKeys_le_skipn: forall X (l:listentry X) m,
    numKeys_le (skipn_le l m) = (numKeys_le l - m)%nat.
Proof.
  intros. generalize dependent m.
  induction l; intros.
  - simpl. destruct m; simpl; auto.
  - simpl. destruct m; simpl. auto. apply IHl.
Qed.

(* nth_entry when skipping entries *)
Lemma nth_entry_skipn: forall X i le (e:entry X),
    nth_entry_le i le = Some e ->
    nth_entry_le 0 (skipn_le le i) = Some e.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - destruct i; simpl in H; inversion H.
  - simpl. destruct i.
    + simpl in H. auto.
    + simpl in H. apply IHle in H.
      destruct (skipn_le le i).
      simpl in H. inv H.
      simpl in H. auto.
Qed.

Lemma nth_entry_skipn': forall X m n le (e:entry X),
    nth_entry_le m le = Some e ->
    (n <= m)%nat ->
    nth_entry_le (m-n) (skipn_le le n) = Some e.
Proof.
  intros. generalize dependent m. generalize dependent n.
  induction le; intros.
  - destruct m; simpl in H; inv H.
  - destruct n.
    + simpl. replace (m-0)%nat with m by omega. auto.
    + simpl. destruct m.
      * inv H0.
      * simpl. apply IHle. simpl in H. auto. omega.
Qed.

(* tl of a listentry *)
Definition tl_le {X:Type} (le:listentry X): listentry X :=
  match le with
  | nil => nil X
  | cons _ le' => le'
  end.

(* skipping 0 entries *)
Lemma skipn_0: forall X (le:listentry X),
    skipn_le le 0 = le.
Proof.
  destruct le.
  - simpl. auto.
  - simpl. auto.
Qed.

(* skipping all entries *)
Lemma skipn_full: forall X (le:listentry X),
    skipn_le le (numKeys_le le) = nil X.
Proof.
  intros. induction le.
  - simpl. auto.
  - simpl. auto.
Qed.

(* skipping one more entry *)
Lemma skip_S: forall X (le:listentry X) i,
    skipn_le le (S i) = tl_le (skipn_le le i).
Proof.
  intros. generalize dependent le.
  induction i; intros.
  - destruct le; simpl; auto. apply skipn_0.
  - destruct le; simpl; auto.
Qed.

(* sublist of a listentry *)
Definition suble {X:Type} (lo hi: nat) (le:listentry X) : listentry X :=
  nth_first_le (skipn_le le lo) (hi-lo).

Lemma suble_nil: forall X (le:listentry X) lo,
    suble lo lo le = nil X.
Proof.
  intros. unfold suble. replace ((lo - lo)%nat) with O by omega. simpl. auto.
Qed.

Lemma suble_nil': forall X (le:listentry X) m n,
    (m <= n)%nat ->
    suble n m le = nil X.
Proof.
  intros. unfold suble.
  replace (m-n)%nat with O by omega. simpl. auto.
Qed.

Lemma suble_skip: forall A m f (l:listentry A),
    f = numKeys_le l -> 
    suble m f l = skipn_le l m.
Proof.
  intros. unfold suble. apply nth_first_same.
  rewrite numKeys_le_skipn. rewrite H. auto.
Qed.

Lemma numKeys_suble: forall A m f (l:listentry A),
    (m <= f <= numKeys_le l)%nat ->
    numKeys_le (suble m f l) = (f - m)%nat.
Proof.
  intros. destruct H.
  unfold suble.
  rewrite numKeys_nth_first. auto.
  rewrite numKeys_le_skipn. omega.
Qed.  

(* appending two listentries *)
Fixpoint le_app {X:Type} (l1:listentry X) (l2:listentry X) :=
  match l1 with
  | nil => l2
  | cons e le => cons X e (le_app le l2)
  end.

Lemma nth_first_increase: forall X n (le:listentry X) e,
    (n < numKeys_le le)%nat ->
    nth_entry_le n le = Some e ->
    nth_first_le le (S n) = le_app (nth_first_le le n) (cons X e (nil X)).
Proof.
  intros. generalize dependent le.
  induction n; intros.
  - destruct le; simpl in H0; inv H0.
    simpl. auto.
  - destruct le.
    + simpl in H0. inv H0.
    + replace (nth_first_le (cons X0 e0 le) (S (S n))) with (cons X0 e0 (nth_first_le le (S n))).
      rewrite IHn. simpl. auto. simpl in H. omega.
      simpl in H0. auto.
      simpl. auto.
Qed.

Lemma skipn_increase: forall X n (le:listentry X) e,
    (S n < numKeys_le le)%nat ->
    nth_entry_le n le = Some e ->
    skipn_le le n = cons X e (skipn_le le (S n)).
Proof.
  intros. generalize dependent le.
  induction n; intros.
  - destruct le; simpl in H0; inv H0.
    simpl. rewrite skipn_0. auto.
  - simpl. destruct le.
    + simpl. simpl in H0. inv H0.
    + simpl. rewrite IHn. auto.
      simpl in H. omega. simpl in H0. auto.
Qed.

Lemma suble_increase: forall X n m (le:listentry X) e,
    (n <= m < numKeys_le le)%nat ->
    nth_entry_le m le = Some e ->
    suble n (S m) le = le_app (suble n m le) (cons X e (nil X)).
Proof.
  intros. unfold suble. replace (S m - n)%nat with (S (m - n)) by omega.
  rewrite nth_first_increase with (e:=e).
  auto.
  rewrite numKeys_le_skipn. omega.
  apply nth_entry_skipn'. auto. omega.
Qed.  

(* Inserts an entry in a list of entries (that doesnt already has the key) *)
Fixpoint insert_le {X:Type} (le:listentry X) (e:entry X) : listentry X :=
  match le with
  | nil => cons X e (nil X)
  | cons e' le' => match ((entry_key e).(k_) <=? (entry_key e').(k_)) with
                  | true => cons X e le
                  | false => cons X e' (insert_le le' e)
                  end
  end.

(* inserting adds one entry *)
Lemma numKeys_le_insert: forall X (l:listentry X) e,
    numKeys_le (insert_le l e) = S (numKeys_le l).
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
          (skipn_le (insert_le le e) (S Middle)) (* the middle entry isn't copied *)
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
    | None => Int.repr 0     (* splitnode should be full *)
    | Some e' =>
      match e' with
      | keyval k _ _ => k
      | keychild k _ => k
      end
    end
  end.
  
(* returns true if the node is full and should be split on insertion *)
Definition fullnode {X:Type} (n:node X) : bool :=
  (Fanout <=? numKeys n)%nat.

(* Is a key already in a listentry? *)
Fixpoint key_in_le {X:Type} (key:key) (le:listentry X) : bool :=
  match le with
  | nil => false
  | cons e le' => match ((entry_key e).(k_) =? key.(k_)) with
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
  | cons e' le' => match ((entry_key e).(k_) =? (entry_key e').(k_)) with
                  | true => cons X e le'
                  | false => cons X e' (update_le e le')
                  end
  end.

(* updates a child in a listentry *)
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

(* updates value in a listentry *)
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

(* updates nth child of a node *)
Definition update_node_nth_child {X:Type} (i:index) (oldn:node X) (n:node X) : node X :=
  match oldn with btnode ptr0 le isLeaf First Last x =>
  match i with
  | im => btnode X (Some n) le isLeaf First Last x
  | ip ii => btnode X ptr0 (update_le_nth_child ii le n) isLeaf First Last x
  end
  end.

(* recursivey updates a cursor with a new leaf node *)
(* DEPRECATED *)
Fixpoint update_cursor {X:Type} (c:cursor X) (n:node X) : cursor X :=
  match c with
  | [] => []
  | (oldn,i)::c' =>
    let newn := update_node_nth_child i oldn n in
    (newn,i)::(update_cursor c' newn)
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
  - pose (c'':=((btnode X0 ptr0 le true First Last x, i) :: c')). fold c''. fold c'' in teq6.
    assert (length c'' = length(fst(newc,newr))).
    rewrite <- teq6. apply update_currnode_same_length. rewrite H. simpl.
    destruct newc eqn:HC.
    + simpl in H. inv H.
    + simpl. omega.
  - intros.
    pose (c'':=((btnode X0 ptr0 le false First Last x, i) :: c')). fold c''. fold c'' in teq5.
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
