(** * btrees.v : Formal Model of BTrees  *)

Require Import VST.floyd.functional_base.
Require Import Sorting.Sorted.
Require Import Program.Basics.
Require Import Program.Combinators.
From Equations Require Import Equations.
Set Equations Transparent.
Import ListNotations.

(* For computations *)
Fixpoint wf_guard {A} {R : A -> A -> Prop}
         (n : nat) (wfR : well_founded R) : well_founded R :=
  match n with
  | 0%nat => wfR
  | S n => fun x =>
            Acc_intro x (fun y _ => wf_guard n (wf_guard n wfR) y)
  end.
Strategy 100 [wf_guard].


(* Maximum number of entries in a node *)
Definition Fanout := 15%nat.
(* Middle = (Fanout+1)/2, for splitting nodes *)
Definition Middle := 8%nat.
(* Maximum tree depth *)
Definition MaxTreeDepth := 20%nat.

Definition K: Type := Z. Definition V: Type := ptrofs.

Section BTrees.
Context {X: Type}.
Context {X_eq_dec: EqDec X}.

(* B+tree abtract model *)
Inductive node: Type :=
| leaf: forall (records: list (K * V * X)) (isFirst: bool) (isLast: bool) (val: X), node
| internal: forall (ptr0: node) (children: list (K * node)) (isFirst: bool) (isLast: bool) (val: X), node.

Fixpoint node_eq_dec (n1 n2: node): {n1 = n2} + {n1 <> n2}.
  unfold EqDec.
  pose proof X_eq_dec. pose proof bool_dec. pose proof Z.eq_dec.
  pose proof Ptrofs.eq_dec. pose proof list_eq_dec.
  repeat decide equality.
Defined.

Definition isLeaf (n: node): Prop :=
  match n with
  | leaf _ _ _ _ => True
  | _ => False
end.

Definition leaf_dec n: {isLeaf n} + {not (isLeaf n)} :=
match n as m return {isLeaf m} + {not(isLeaf m)} with
| leaf _ _ _ _ => left I
| internal _ _ _ _ _ => right (fun hcontr => hcontr)
end.
  
Definition keys (n: node): list K := 
  match n with
  | leaf recs _ _ _ => map (fst ∘ fst) recs
  | internal _ children _ _ _ => map fst children
  end.

Definition F (n: node): bool := 
  match n with | leaf _ F _ _ | internal _ _ F _ _ => F end.

Definition L (n: node): bool := 
  match n with | leaf _ _ L _ | internal _ _ _ L _ => L end.

Definition FL (n: node): bool * bool := (F n, L n).

Definition val (n: node): X := 
  match n with | leaf _ _ _ x => x | internal _ _ _ _ x => x end.

(* number of keys in a node *)
Definition numKeys (n:node) : nat :=
match n with leaf l _ _ _ => length l | internal _ l _ _ _ => length l end.

Section node_ind.
  Variables (P : node -> Prop) (Q : list (K * node)-> Prop).

  Hypotheses
    (hleaf: forall l F L v, P (leaf l F L v))
    (hinternal : forall ptr0 (entries:list (K * node)) F L v,
        P ptr0 -> Q entries -> P (internal ptr0 entries F L v))
    (hnil : Q [])
    (hcons : forall (k: K) (n: node), P n -> forall l: list (K * node), Q l -> Q (cons (k,n) l)).

  Fixpoint general_node_ind (n: node): P n :=
    match n as x return P x with
    | leaf l F L v => hleaf l F L v
    | internal ptr0 l F L v =>
      hinternal ptr0 l F L v (general_node_ind ptr0)
                (((fix l_ind (l':list (K * node)) : Q l' :=
                     match l' as x return Q x with
                     | nil => hnil
                     | cons (k1, n1) tl => hcons k1 n1 (general_node_ind n1) tl (l_ind tl)
                     end)) l)
    end.
End node_ind.

Section node_rect.
  Variables (P : node -> Type) (Q : list (K * node)-> Type).

  Hypotheses
    (hleaf: forall l F L v, P (leaf l F L v))
    (hinternal : forall ptr0 (entries:list (K * node)) F L v,
        P ptr0 -> Q entries -> P (internal ptr0 entries F L v))
    (hnil : Q [])
    (hcons : forall (k: K) (n: node), P n -> forall l: list (K * node), Q l -> Q (cons (k,n) l)).

  Fixpoint general_node_rect (n: node): P n :=
    match n as x return P x with
    | leaf l F L v => hleaf l F L v
    | internal ptr0 l F L v =>
      hinternal ptr0 l F L v (general_node_rect ptr0)
                (((fix l_ind (l':list (K * node)) : Q l' :=
                     match l' as x return Q x with
                     | nil => hnil
                     | cons (k1, n1) tl => hcons k1 n1 (general_node_rect n1) tl (l_ind tl)
                     end)) l)
    end.
End node_rect.

Lemma node_ind2 (P: node -> Prop)
        (hleaf: forall entries isFirst isLast val, P (leaf entries isFirst isLast val))
        (hinternal : forall ptr0 (entries:list (K * node)) isFirst isLast val,
            P ptr0 -> Forall (P ∘ snd) entries -> P (internal ptr0 entries isFirst isLast val)):
  forall n: node, P n.
Proof.
  refine (general_node_ind P (Forall (P ∘ snd)) hleaf hinternal _ _).
  easy. now constructor.
Defined.

Definition node_rect2 (P: node -> Type)
        (hleaf: forall entries isFirst isLast val, P (leaf entries isFirst isLast val))
        (hinternal : forall ptr0 (entries:list (K * node)) isFirst isLast val,
            P ptr0 -> (forall e, In e entries -> P (snd e)) -> P (internal ptr0 entries isFirst isLast val)):
  forall n: node, P n.
Proof.
  refine (general_node_rect P (fun entries => forall e, In e entries -> P (snd e)) hleaf hinternal _ _).
  easy.
  intros.
  destruct (in_dec (prod_eqdec Z.eq_dec node_eq_dec) e l). apply (X1 _ i).
  destruct (prod_eqdec Z.eq_dec node_eq_dec e (k, n)). subst. easy.
  pose proof (proj2 (not_in_cons e (k, n) l) (conj n1 n0)). contradiction.
Defined.

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
  apply (node_ind2 (fun n => Datatypes.length (abs_node n) = node_numrec n)).
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

Definition nth_key (i:nat) (n: node): option K := nth_error (keys n) i.

Inductive balanced: forall (depth: nat) (n: node), Prop :=
| leaf_balanced: forall le F L v, balanced 0 (leaf le F L v)
| internal_balanced: forall d ptr0 l last v,
    L ptr0 = false ->
    balanced d ptr0 -> Forall (fun n => FL n = (false, false) /\ balanced d n) (map snd l) -> F (snd last) = false -> balanced d (snd last) -> balanced (S d) (internal ptr0 (l ++ [last]) (F ptr0) (L (snd last)) v).

Definition relation: Type := {rootd : node * nat |
                              let (root, depth) := rootd in
                              FL root = (true, true) /\
                              balanced depth root} * X.

Coercion relation_as_btree := fun (r : relation) => fst (proj1_sig (fst r)).

Definition root (r: relation): node := fst (proj1_sig (fst r)).
Definition depth (r: relation): nat := snd (proj1_sig (fst r)).

(* numRecords of the relation *)
Definition get_numrec (rel: relation) : nat := node_numrec (root rel).

Definition index (n: node): Type :=
  if leaf_dec n then {k: nat | (k <= numKeys n)%nat}
  else unit + {k: nat | (k < numKeys n)%nat}.

Definition ptr0_index {ptr0 l F L v} : index (internal ptr0 l F L v) := inl tt.

Definition internal_le_index {ptr0 l F L v} (k: nat) (h: (k < length l)%nat): index (internal ptr0 l F L v) :=
  inr (exist _ k h).

Definition leaf_index {l F L v} (k: nat) (h: (k <= length l)%nat): index (leaf l F L v) :=
  exist _ k h.

Definition leaf_0_index {l F L v}: index (leaf l F L v) :=
  leaf_index 0%nat (Nat.le_0_l _).

Lemma internal_pred_length {d ptr0 l F L v} (h: balanced d (internal ptr0 l F L v)):
  (pred (length l) < length l)%nat.
Proof.
  inversion h. rewrite app_length. cbn. omega.
Qed.

Definition index_eq_dec: forall n, EqDec (index n).
  intros [] [] [].
  + destruct (Nat.eq_dec x x0).
    left. now apply exist_ext.
    right. now injection.
  + left. now destruct u, u0.
  + right. discriminate.
  + right. discriminate.
  + destruct s, s0. destruct (Nat.eq_dec x x0).
    left. f_equal. subst. now apply exist_ext.
    right. now injection.
Defined.

Definition child_at (n: node) (i: index n): not (isLeaf n) -> node := 
match n as m, i return not (isLeaf m) -> node with
| leaf l _ _ _, exist k hk => fun h => match h I with end
| internal ptr0 l _ _ _, inl tt => fun _ => ptr0
| internal ptr0 l _ _ _, inr (exist k hk) => fun _ => nth k (map snd l) ptr0
end.

Definition record_at (n: node) (i: index n): isLeaf n -> V :=
match n as m, i return isLeaf m -> V with
| leaf l _ _ _, exist k hk => fun _ => nth k (map (snd ∘ fst) l) Ptrofs.zero
| internal ptr0 l _ _ _, _ => fun h => match h with end
end.

Definition at_index (n: node) (i: index n): if leaf_dec n then V else node :=
match n as m, i return if leaf_dec m then V else node with
| leaf l _ _ _, exist k hk => nth k (map (snd ∘ fst) l) Ptrofs.zero
| internal ptr0 l _ _ _, inl tt => ptr0
| internal ptr0 l _ _ _, inr (exist k hk) => nth k (map snd l) ptr0
end.

Notation "n @ i" := (at_index n i) (at level 0).

(*
Equations next_index {n: node} {d: nat} (hbal: balanced d n) (i: index n): index n :=
  next_index (n := ?(leaf _ _ _ _)) hbal (exist hk) := exist _ (min (k + 1) (length l)) _ ;
  next_index (n := ?(internal _ _ _ _ _)) hbal (inl tt) := inr (exist _ 0%nat _) ;
  next_index (n := ?(internal _ _ _ _ _)) hbal (inr (exist hk)) := inr (exist _ (min (k + 1) (length l - 1)) _).
*)

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
+ subst. inversion hbal. cbn. rewrite app_length. cbn. omega.
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

Definition findChildIndex {d} (n: node) (key:K): not (isLeaf n) -> balanced d n -> index n :=
  match n as m return not (isLeaf m) -> balanced d m -> index m with
  | leaf _ _ _ _ => fun hleaf _ => match hleaf I with end
  | internal _ _ _ _ _ => fun hleaf hbal =>
    fold_left (fun acc k => if key <? k then acc else next_index hbal acc) (keys n) ptr0_index
  end.

Definition findRecordIndex {d} (n: node) (key:K): isLeaf n -> balanced d n -> index n :=
  match n as m return isLeaf m -> balanced d m -> index m with
  | leaf l _ _ _ => fun _ hbal =>
                      fold_right (fun k acc => if key <=? k then prev_index hbal acc else acc)
                                       (leaf_index (length l) (le_n _)) (keys n)
  | internal _ _ _ _ _ => fun hleaf _ => match hleaf with end
  end.

Inductive isChild: forall (child: node) (parent: {n: node & index n}), Prop :=
| is_ptr0: forall ptr0 le F L v,
    isChild ptr0 (existT _ (internal ptr0 le F L v) (inl tt))
| in_le: forall ptr0 le F L v n i hi,
    nth_error (map snd le) i = Some n ->
    isChild n (existT (fun n => index n) (internal ptr0 le F L v) (inr (exist _ i hi))).

Definition cursorEntry: Type := {n: node & index n}.

Definition cursorEntry_eq_dec: EqDec cursorEntry.
  intros c1 c2. destruct c1 as [n1 i1], c2 as [n2 i2].
  destruct (node_eq_dec n1 n2).
  + subst. destruct (index_eq_dec n2 i1 i2). subst. now left.
    right. now intros h%inj_pair2.
  + right. now injection.
Defined.

(* a 'cursor r' can be empty, but when it is not, its last element is the root of r. *)
Definition cursor (r: relation) :=
  { c: list cursorEntry |
    Sorted (fun e1 e2 => isChild (projT1 e1) e2) c /\
    last (map (@projT1 _ _) c) (root r) = root r }.

Definition list_of_cursor: forall {r}, cursor r -> list cursorEntry := fun r c => proj1_sig c.
Coercion list_of_cursor: cursor >-> list.
Add Printing Coercion list_of_cursor.

Definition cursor_eq_dec: EqDec (list cursorEntry) :=
  list_eq_dec cursorEntry_eq_dec.

Notation "[| c |]" := (list_of_cursor c).

Definition nontrivial_cursor (r: relation): Type := {c: cursor r | [| c |] <> []}.
Coercion cursor_of_nontrivial_cursor :=
  fun {r: relation} (c: nontrivial_cursor r) => proj1_sig c.

Section Cursors.
  Context {r: relation}.
  
  Lemma cursor_coercion (c: nontrivial_cursor r) (c': cursor r):
    proj1_sig c = c' -> [|c|] = [|c'|].
  Proof.
    intro h. destruct c as [[]], c'. cbn in h. now inversion h.
  Qed.

  Definition firstPair (c: nontrivial_cursor r): cursorEntry :=
    let l := proj1_sig (proj1_sig c) in
    (match l as l' return l = l' -> cursorEntry with
    | hd :: _ => fun _ => hd
    | [] => fun heq => match (proj2_sig c) heq with end
     end) eq_refl.
  
  Definition currNode (c: nontrivial_cursor r): node := projT1 (firstPair c).
  Definition entryIndex (c: nontrivial_cursor r): index (currNode c):= projT2 (firstPair c).

  Definition isComplete (c: nontrivial_cursor r): Prop :=
    isLeaf (currNode c).

  Definition complete_dec (c: nontrivial_cursor r): {isComplete c} + {not (isComplete c)} :=
    leaf_dec (currNode c).

  Definition isNextNode (c: cursor r) (n: node): Prop :=
    match cursor_eq_dec [| c |] [] with
    | left _ => n = root r
    | right hneqnil => isChild n (firstPair (exist _ c hneqnil))
    end.
    
  Inductive subnode: nat -> node -> node -> Prop :=
  | subnode_refl: forall n, subnode 0 n n
  | subnode_step: forall child_node parent_node parent_index n k,
      isChild child_node (existT _ parent_node parent_index) -> subnode k parent_node n -> subnode (S k) child_node n.

  Definition path_length {d n1 n2} (h: subnode d n1 n2): nat := d.

  Lemma subnode_leaf: forall k n l F L v, subnode k n (leaf l F L v) -> n = leaf l F L v /\ (k = 0)%nat.
  Proof.
    induction k.
    + intros. now inversion H.
    + intros. inversion H. apply IHk in H2. destruct H2. subst. inversion H1.
  Qed.

  Lemma subnode_trans: forall {nkm nmp} n m p, subnode nkm n m -> subnode nmp m p -> subnode (nkm + nmp) n p.
  Proof.
    induction nkm.
    + intros * hsubnm hsubmp. inversion hsubnm. subst. cbn. assumption.
    + intros * hsubnm hsubmp.
      inversion hsubnm.
      subst. rewrite Nat.add_succ_l.
      eapply subnode_step. apply H0.
      eapply IHnkm. apply H1. assumption.
  Qed.

  Theorem cursor_subnode: forall (c: cursor r) (k: nat) (e: cursorEntry),
      nth_error [|c|] k = Some e -> subnode (length [|c|] - k - 1) (projT1 e) (root r).
  Proof.
    intros * hnth.
    destruct c as [[ |hd c] [hsorted hlast]]; cbn in hnth; simpl length.
    rewrite nth_error_nil in hnth. discriminate.
    rewrite <- Nat.sub_add_distr, Nat.add_1_r, Nat.sub_succ.
    revert e hd k hsorted hlast hnth.
    induction c.
    + intros.
      unshelve epose proof (proj1 (nth_error_Some [hd] k) _).
      { intro hcontr. rewrite hnth in hcontr. discriminate. }
      cbn in H. replace k with 0%nat in hnth |- * by omega.
      cbn in hlast, hnth |- *. inversion hnth. subst.
      rewrite hlast. constructor.
    + intros.
      destruct k.
      - cbn in hnth |- *. destruct a as [n i].
        apply (subnode_step _ n i).
        inversion hsorted. inversion H2.
        inversion hnth. subst. assumption.
        specialize (IHc (existT _ n i) (existT _ n i) 0%nat). cbn in IHc, hlast. rewrite Nat.sub_0_r in IHc.
        eapply IHc. inversion hsorted. assumption.
        assumption. reflexivity.
      - cbn in hnth. simpl length. rewrite Nat.sub_succ.
        eapply IHc. inversion hsorted. exact H1.
        cbn in hlast |- *. assumption.
        assumption.
  Qed.

  Corollary isNextNode_subnode: forall c n, isNextNode c n -> subnode (length [|c|]) n (root r).
  Proof.
    intros * h. remember c as cur.
    destruct c as [[ | [n' i] c] [hsorted hlast]]; cbn in Heqcur.
    + rewrite Heqcur in h |- *. cbn in h |- *. subst. constructor.
    + rewrite Heqcur in h |- *. cbn. apply (subnode_step n n' i). exact h.
      assert (hnth: nth_error [|cur|] 0 = Some (existT _ n' i)) by now subst cur.
      apply cursor_subnode in hnth.
      subst cur. cbn in hnth. rewrite Nat.sub_0_r in hnth. assumption.
  Qed.

  Theorem subnode_balanced: forall {k d child parent},
      balanced d parent -> 
      subnode k child parent ->
      balanced (d - k) child /\ (k <= d)%nat.
  Proof.
    induction k.
    + intros * hbal hsub. inversion hsub. subst.
      rewrite Nat.sub_0_r. split. assumption. omega.
    + intros * hbal hsub.
      inversion hsub. subst.
      specialize (IHk d parent_node parent hbal H1). destruct IHk as [hbal_rec le_rec].
      inversion hbal_rec; subst. inversion H0.
      assert (d0 = d - S k)%nat by omega.
      inversion H0. subst. split. assumption. omega.
      subst. apply nth_error_in in H10. rewrite Forall_forall in H4.
      rewrite map_app, in_app_iff in H10. destruct H10 as [h|h].
      specialize (H4 child h); split; [easy|omega].
      destruct h. subst. split; [easy | omega].
      contradiction.
  Qed.

  Corollary subnode_root: forall {k n}, subnode k n (root r) -> balanced (depth r - k) n.
  Proof.
    intros * h.
    destruct r as [[[rootnode rootdepth] [hFL hbalanced]] relval].
    cbn in h, hbalanced |- *. exact (proj1 (subnode_balanced hbalanced h)).
  Qed.
  
  Corollary currNode_balanced: forall {c: nontrivial_cursor r}, balanced (depth r - pred (length [|c|])) (currNode c).
  Proof.
    intro c. remember c as cur.
    destruct c as [[[ |hd tl]]]; cbn in *. contradiction.
    unshelve epose proof (cursor_subnode cur 0 hd _) as h.
    now subst. apply @subnode_balanced with (d := depth r) in h.
    destruct h as [h hle].
    rewrite Heqcur in h |- *. unfold currNode, firstPair. cbn in h |- *.
    now rewrite Nat.sub_0_r in h.
    now destruct r as [[[] []]].
  Qed.
  
  Corollary isNextNode_balanced: forall {c n}, isNextNode c n -> balanced (depth r - length [|c|]) n.
  Proof.
    intros * h. apply isNextNode_subnode, subnode_root in h. assumption.
  Qed.
  
  Corollary isNextNode_length: forall c ptr0 l F L v,
      isNextNode c (internal ptr0 l F L v) -> (length l > 0)%nat.
  Proof.
    intros * h. apply isNextNode_subnode, subnode_root in h.
    inversion h. rewrite app_length. cbn. omega.
  Qed.

  Theorem cursor_relation_depth (c: cursor r): (length [| c |] <= S (depth r))%nat.
  Proof.
    remember c as cur. destruct c as [[ | hd c] [hsorted hhd]]; cbn.
    subst. cbn. omega.
    assert (h: nth_error [|cur|] 0 = Some hd). now subst.
    pose proof (cursor_subnode _ _ _ h).
    destruct r as [[[root rel_depth] hbal] relval].
    cbn in *.
    apply (subnode_balanced (proj2 hbal)) in H.
    rewrite Nat.sub_0_r in H.
    destruct H. omega.
  Qed.
  
  Definition cursor_cons (c: cursor r) (n: node) (i: index n)
    (h: isNextNode c n): nontrivial_cursor r.
    simple refine (exist _ (exist _ (existT _ n i :: list_of_cursor c) _) _); cbn.
    destruct c as [[ |[n' i'] c] [hsorted hrel]];
    cbn in h |- *. split. repeat constructor. assumption.
    split.
    + constructor. assumption. constructor. easy.
    + assumption.
    + discriminate.
  Defined.
  
  Lemma lastPair_cursor_cons (c: cursor r) (n: node) (i: index n)
        (h : isNextNode c n):
    firstPair (cursor_cons c n i h) = existT _ n i.
  Proof.
    reflexivity.
  Qed.

  Lemma isNextNode_cursor_cons {ptr0 l F L v} (c: cursor r) (n: node := internal ptr0 l F L v)
        (hleaf: not (isLeaf n)) (h: isNextNode c n) (i: index n):
    isNextNode (cursor_cons c n i h) n@i.
  Proof.
    cbn. destruct i. destruct u. constructor.
    destruct s. constructor. apply nth_error_nth. rewrite map_length. assumption.
  Qed.
  
  Equations? cursor_tail (c: nontrivial_cursor r): cursor r :=
    cursor_tail (@exist (@exist [] _) hneqnil) := False_rect _ _ ;
    cursor_tail (@exist (@exist (_ :: tl) _) _) := exist _ tl _.
  split. now apply Sorted_inv in s. now destruct tl.
  Defined.

  Lemma isNextNode_cursor_tail {c: nontrivial_cursor r}:
    isNextNode (cursor_tail c) (currNode c).
  Proof.
    destruct c as [[[ | hd tl] [hsorted hlast]] hnil]. contradiction.
    rewrite cursor_tail_equation_2.
    unfold isNextNode, currNode, firstPair. simpl.
    destruct tl. assumption. 
    cbn. inversion hsorted. inversion H2. 
    assumption.
  Qed.
  
  Inductive cursor_subterm: cursor r -> cursor r -> Prop :=
  | cursor_tail_subterm: forall c: nontrivial_cursor r, cursor_subterm (cursor_tail c) c.
  
  Lemma cursor_subterm_wf_qed: WellFounded cursor_subterm.
  Proof.
    intros [le]. induction le. 
    + constructor. intros tl htl. inversion htl.
      apply cursor_coercion in H1. now destruct c.
    + constructor. intros tl htl.
      inversion htl.
      destruct c as [[[]]]. contradiction.
      rewrite cursor_tail_equation_2.
      unfold cursor_of_nontrivial_cursor in H1.
      apply cursor_coercion in H1. cbn in H1.
      inversion H1. subst. apply IHle.
  Qed.

  Instance cursor_subterm_wf: WellFounded cursor_subterm := wf_guard 32 cursor_subterm_wf_qed.
  
  Definition isValid (c: nontrivial_cursor r): Prop :=
    match firstPair c with
    | existT (leaf l F L v) (exist i _) =>
      not (L = true /\ i = length l)
    | _ => False
    end.

  Definition valid_dec c: {isValid c} + {not(isValid c)}.
  destruct c as [[[ | [[l F [] | ]] tl]]]; cbn in *.
  + contradiction.
  + destruct i as [i], (Nat.eq_dec i (length l)).
    right. subst. intro h. now apply h.
    left. intro h. destruct h as [_ h]. apply n0. exact h.
  + destruct i as [i]. now left.
  + right. easy.
  Defined.

  (* does the cursor point to the very first key? *)
  Definition isFirst (c: nontrivial_cursor r): bool :=
    match firstPair c with
    | existT (leaf _ F _ _) (exist i _) => F && (i =? 0)%nat
    | _ => false end.

  (* get record pointed to by cursor *)
  Definition getCEntry (c: nontrivial_cursor r) : option (K * V * X) :=
    match firstPair c with
    | existT (leaf l F L v) (exist i _) => nth_error l i
    | _ => None
    end.

  Lemma inj_exist {A: Type} (P: A -> Prop):
    forall a a' ha ha', exist P a ha = exist P a' ha' -> a = a'.
  Proof.
    intros * h. now injection h.
  Qed.
  
  Equations moveToFirst (c: cursor r) (n: node) (hpar: isNextNode c n): nontrivial_cursor r :=
    moveToFirst c (leaf l F L v) hpar := cursor_cons c (leaf l F L v) leaf_0_index hpar;
    moveToFirst c (internal ptr0 l F L v) hpar :=
            moveToFirst (cursor_cons c (internal ptr0 l F L v) ptr0_index hpar) ptr0 (is_ptr0 _ _ _ _ _).

  Definition node_subterm: node -> node -> Prop :=
    fun child parent => exists (i: index parent), isChild child (existT _ parent i).
  
  Theorem node_subterm_wf: well_founded node_subterm.
  Proof.
    intro n.
    apply (node_ind2 (fun n => Acc node_subterm n));
    intros; constructor; intros n' hn'; unfold node_subterm in hn';
    destruct hn' as [i hi]; inversion hi.
    + assumption.
    + apply nth_error_in in H3. rewrite Forall_forall in H0.
      apply list_in_map_inv in H3. destruct H3 as [x [heq hin]].
      unfold compose in H0.
      specialize (H0 x hin). rewrite <- heq in H0. assumption.
  Qed.

  Instance node_subterm_wf_instance: WellFounded node_subterm := wf_guard 32 node_subterm_wf.

  Equations moveToLast (c: cursor r) (n: node) (h: isNextNode c n):
    nontrivial_cursor r by wf n node_subterm :=
    moveToLast c (leaf l F L v) h := cursor_cons c (leaf l F L v) (exist _ (length l) _) h;
    moveToLast c (internal ptr0 l F L v) h :=
            moveToLast (cursor_cons c (internal ptr0 l F L v) (inr (exist _ (pred (length l))%nat (internal_pred_length (isNextNode_balanced h)))) h)
                       (nth (pred (length l)) (map snd l) ptr0) _.
  Next Obligation.
    cbn. constructor. apply nth_error_nth. rewrite map_length.
    eapply internal_pred_length, isNextNode_balanced. exact h.
  Qed.
  Next Obligation.
    unfold node_subterm.
    apply isNextNode_length in h.
    unshelve eexists (inr (exist _ (pred (length l))%nat _)).
    cbn. omega.
    constructor. rewrite (nth_error_nth _ ptr0). reflexivity.
    rewrite map_length. omega.
  Qed.  

  Lemma moveToFirst_complete (c: cursor r) (n: node)
        (h: isNextNode c n):
    isComplete (moveToFirst c n h).
  Proof.
    revert dependent c.
    apply (node_ind2 (fun n => forall (c: cursor r) (h : isNextNode c n), isComplete (moveToFirst c n h))).
    + intros. rewrite moveToFirst_equation_1. unfold isComplete, currNode. now rewrite lastPair_cursor_cons.
    + intros. rewrite moveToFirst_equation_2. 
      apply H.
  Qed.

  Lemma moveToLast_complete (c: cursor r) (n: node)
        (h: isNextNode c n):
    isComplete (moveToLast c n h).
  Proof.
    revert dependent c.
    apply (node_ind2 (fun n => forall (c: cursor r) (h : isNextNode c n), isComplete (moveToLast c n h))).
    + intros. rewrite moveToLast_equation_1. unfold isComplete, currNode. now rewrite lastPair_cursor_cons.
    + intros. rewrite moveToLast_equation_2.
      rewrite <- Forall_map, Forall_forall in H0.
      apply H0.
      apply nth_In. rewrite map_length.
      apply isNextNode_length in h. omega.
  Qed.

  Equations(noind) moveToKey (c: cursor r) (n: node) (h: isNextNode c n) (k: K):
    nontrivial_cursor r by wf n node_subterm :=
    moveToKey c (leaf l F L v) h k => cursor_cons c (leaf l F L v) (findRecordIndex (leaf l F L v) k _ (isNextNode_balanced h)) h;
                                     moveToKey c (internal ptr0 l F L v) h k =>
    let m := internal ptr0 l F L v in
    let childIndex: index m := findChildIndex m k _ (isNextNode_balanced h) in
    moveToKey (cursor_cons c m childIndex h) m@childIndex (isNextNode_cursor_cons _ _ _ _) k.
  Next Obligation.
    destruct fold_left.
    + destruct u. exists ptr0_index. constructor.
    + destruct s as [k0 hk]. exists (internal_le_index k0 hk).
      constructor. apply nth_error_nth. rewrite map_length. assumption.
  Qed.

  Definition isNodeParent {d} (n: node) (k: K): balanced d n -> Prop :=
    match n as m return balanced d m -> Prop with
    | leaf [] _ _ _ => fun hbal => True
    | leaf ((lowest_key, _, _) as hd::tl) F L _ as n => fun _ =>
        let '(highest_key, _, _) := proj1_sig (projT2 (exists_last (fun h => @nil_cons _ hd tl (eq_sym h)))) in
        ((k >= lowest_key) \/ F = true) /\ ((k <= highest_key) \/ L = true)
    | internal _ l _ _ _ as n => fun hbal => 
                                  match findChildIndex n k (fun h => match h with end) hbal with
                                  | inl tt => False
                                  | inr (exist k hk) => not (S k = length l)
                                  end
    end.

  Lemma isNodeParent_dec {d} n k (hbal: balanced d n):
    {isNodeParent n k hbal} + {not (isNodeParent n k hbal)}.
  Proof.
    destruct n as [[ | []] | ]; cbn.
    + left. trivial.
    + destruct p as [lk v].
      destruct exists_last as [? [[[hk]] ]]. cbn.
      destruct (Z_ge_lt_dec k lk), (Z_le_gt_dec k hk), isFirst0, isLast; (* intuition *) admit.
    (* Could find a better way for this, intuition works but takes 20 seconds. *)
    + destruct fold_left.
    - destruct u. now right.
    - destruct s as [k0 hchildren].
      destruct (Nat.eq_dec (S k0) (length children)).
      now right. now left.
  (* Qed. *) Admitted.

  Equations AscendToParent (c: cursor r) (k: K): cursor r by wf (length [|c|]) lt :=
    AscendToParent (@exist [] _) k := exist _ [] (conj _ eq_refl) ;
    AscendToParent (@exist [e] _) k := exist _ [e] _ ;
    AscendToParent (@exist (hd::tl) _) k := let c: nontrivial_cursor r := exist _ (exist _ (hd::tl) _) _ in
            if isNodeParent_dec (currNode c) k currNode_balanced then c else AscendToParent (cursor_tail c) k.

  Equations goToKey (c: cursor r) (k: K): cursor r :=
    goToKey c k with AscendToParent c k :=
      {
      | @exist [] _ => moveToKey (exist _ [] _) (root r) eq_refl k ;
      | @exist (hd :: tl) _ =>
        let c': nontrivial_cursor r := exist _ (exist _ (hd::tl) _) _ in
        moveToKey (cursor_tail c') (currNode c') isNextNode_cursor_tail k
      }.

  Definition lastpointer {d} (n: node): balanced d n -> index n :=
    match n as m return balanced d m -> index m with
    | leaf l _ _ _ => fun _ => exist _ (length l) (le_n _)
    | internal _ l _ _ _ => fun h => inr (exist _ (pred (length l)) (internal_pred_length h))
    end.

  (* The following shouldn't be necessary... *)
  Instance this_measure_wf: WellFounded (Telescopes.tele_measure (Telescopes.tip (nontrivial_cursor r))
                                                                 (nontrivial_cursor r) (fun c => c) (Wf.MR cursor_subterm cursor_of_nontrivial_cursor)).
  typeclasses eauto.
  Qed.

  Equations(noind) up_at_last (c: nontrivial_cursor r):
    nontrivial_cursor r by wf (cursor_of_nontrivial_cursor c) cursor_subterm :=
    up_at_last c := if cursor_eq_dec (cursor_tail c) [] then c else
                      if index_eq_dec _ (entryIndex c) (lastpointer (currNode c) currNode_balanced)
                      then up_at_last (exist _ (cursor_tail c) _) else c.
  Solve Obligations with constructor.

  Definition next_cursor (c: nontrivial_cursor r): nontrivial_cursor r :=
    cursor_cons (cursor_tail c) (currNode c) (next_index currNode_balanced (entryIndex c)) isNextNode_cursor_tail.

  Definition moveToNext (c: nontrivial_cursor r): nontrivial_cursor r.
    simple refine (let cincr: nontrivial_cursor r := next_cursor (up_at_last c) in
                   if valid_dec c then (if complete_dec cincr then cincr
                                        else moveToFirst cincr (child_at (currNode cincr) (entryIndex cincr) _) _) else c).
    exact n.
    remember cincr as cincr'.
    destruct cincr' as [[[ | [[] index] ]]]. contradiction.
    now cbn in n.
    cbn in *. destruct index.
    + destruct u. constructor.
    + destruct s. constructor. apply nth_error_nth.
      now rewrite map_length.
  Defined.

  Definition firstpointer {d} (n: node): balanced d n -> index n :=
    match n as m return balanced d m -> index m with
    | leaf l _ _ _ => fun _ => exist _ 0%nat (Nat.le_0_l _)
    | internal _ l _ _ _ => fun h => inl tt
    end.

  Equations(noind) up_at_first (c: nontrivial_cursor r):
    nontrivial_cursor r by wf (cursor_of_nontrivial_cursor c) cursor_subterm :=
    up_at_first c := if cursor_eq_dec (cursor_tail c) [] then c else
                       if index_eq_dec _ (entryIndex c) (firstpointer (currNode c) currNode_balanced)
                       then up_at_first (exist _ (cursor_tail c) _) else c.
  Solve Obligations with constructor.

  Definition prev_cursor (c: nontrivial_cursor r): nontrivial_cursor r :=
    cursor_cons (cursor_tail c) (currNode c) (prev_index currNode_balanced (entryIndex c)) isNextNode_cursor_tail.

  Definition moveToPrev (c: nontrivial_cursor r): nontrivial_cursor r.
    simple refine (let cdecr: nontrivial_cursor r := prev_cursor (up_at_last c) in
                   if valid_dec c then (if complete_dec cdecr then cdecr
                                        else moveToFirst cdecr (child_at (currNode cdecr) (entryIndex cdecr) _) _) else c).
    exact n.
    remember cdecr as cdecr'.
    destruct cdecr' as [[[ | [[] index] ]]]. contradiction.
    now cbn in n.
    cbn in *. destruct index.
    + destruct u. constructor.
    + destruct s. constructor. apply nth_error_nth.
      now rewrite map_length.
  Defined.

  Definition normalize (c: nontrivial_cursor r): isComplete c -> nontrivial_cursor r :=
    match firstPair c as p return isLeaf (projT1 p) -> nontrivial_cursor r  with
    | existT (leaf l _ _ _ as currNode) (exist k hk) => fun _ => if Nat.eq_dec k (length l) then moveToNext c else c                                                    
    | existT (internal _ _ _ _ _ as currNode) _ => fun hcomplete => match hcomplete with end
    end.

  Definition RL_MoveToNext (c: nontrivial_cursor r): isComplete c -> nontrivial_cursor r :=
    match firstPair c as p return isLeaf (projT1 p) -> nontrivial_cursor r with
    | existT (leaf l _ _ _ as currNode) (exist k hk) => fun _ => if Nat.eq_dec k (length l) then moveToNext (moveToNext c) else moveToNext c                                                    
    | existT (internal _ _ _ _ _ as currNode) _ => fun hcomplete => match hcomplete with end
    end.

  Definition RL_MoveToPrevious (c: nontrivial_cursor r): isComplete c -> nontrivial_cursor r :=
    match firstPair c as p return isLeaf (projT1 p) -> nontrivial_cursor r with
    | existT (leaf l _ _ _ as currNode) (exist k hk) => fun _ => if Nat.eq_dec k O%nat then moveToPrev (moveToPrev c) else moveToPrev c                                                    
    | existT (internal _ _ _ _ _ as currNode) _ => fun hcomplete => match hcomplete with end
    end.

  Definition RL_GetRecord (c: nontrivial_cursor r): isComplete c -> V :=
    record_at (currNode c) (entryIndex c).

End Cursors.

End BTrees.

(* Some execution tests *)

Definition ptr0: node := leaf (map (fun x => (x, Ptrofs.zero, tt)) [1; 2; 3]) true false tt.
Definition three: node := leaf (map (fun x => (x, Ptrofs.zero, tt)) [4; 5; 6]) false false tt.
Definition thirty: node := leaf (map (fun x => (x, Ptrofs.zero, tt)) [40; 50]) false false tt.
Definition sixty: node := leaf (map (fun x => (x, Ptrofs.zero, tt)) [70; 80; 82; 84; 86]) false true tt.

Definition test_btree: node :=
  internal ptr0 ([(3, three); (30, thirty)] ++ [(60, sixty)]) true true tt.

Arguments relation (X) : clear implicits.

Definition r: relation unit.
  refine (exist _ (test_btree, 1%nat) _, tt).
  repeat constructor.
Defined.

Definition c: cursor r. refine (exist _ [] _). repeat constructor. Defined.

Require Import Ascii.

Definition format_ce (ce: @cursorEntry unit): string :=
match ce with
| existT (leaf _ _ _ _) (exist k hk) => String (ascii_of_N (N.of_nat (k+48))) EmptyString
| existT (internal _ _ _ _ _) (inl tt) => "ptr0"%string
| existT (internal _ _ _ _ _) (inr (exist k hk)) => String (ascii_of_N (N.of_nat (k+48))) EmptyString
end.

Definition format_index {X} {n: @node X}: @index X n -> string :=
match n as m return index m -> string with
| leaf _ _ _ _ => fun '(exist k hk) => String (ascii_of_N (N.of_nat (k+48))) EmptyString
| internal _ _ _ _ _ => fun i => match i with
                             | inl tt => "ptr0"%string
                             | inr (exist k hk) => String (ascii_of_N (N.of_nat (k+48))) EmptyString
                             end
end.

Definition first_cursor: nontrivial_cursor r.
  refine (moveToFirst c (root r) _).
  constructor.
Defined.

Definition last_cursor: nontrivial_cursor r.
  refine (moveToLast c (root r) _).
  constructor.
Defined.

(* reste à faire attention: Admitted et instance cheloue?
 utiliser un max de abstract tactic et Qed *)

Compute (map format_ce (proj1_sig last_cursor)).

Compute (format_index (findRecordIndex three 5 _ _)).

Compute (map format_ce (proj1_sig (moveToNext first_cursor))).

Compute (map format_ce (proj1_sig last_cursor)).

Compute (format_index (findChildIndex (fst (proj1_sig (fst r))) 61 (fun h => match h with end) (proj2 (proj2_sig (fst r))))).
Eval vm_compute in (map format_ce (proj1_sig first_cursor)).



(*

Fixpoint insert_child (l: list (K * node)) (k: K) (child: node) (hbal: balanced d child): list (K * node) :=
match l with [] => [(k, child)] | (hdk, hdn) as hd :: tl => if k <=? hdk then (k, child) :: l else hd :: (insert_child l k child hbal).


(* Inserts an entry in a list of entries (that doesnt already has the key) *)
Fixpoint insert_le {X:Type} (le:listentry X) (e:entry X) : listentry X :=
  match le with
  | nil => cons X e (nil X)
  | cons e' le' => match ((entry_key e).(k_) <=? (entry_key e').(k_)) with
                  | true => cons X e le
                  | false => cons X e' (insert_le le' e)
                  end
  end.

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
 *)
