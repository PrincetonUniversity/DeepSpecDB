(** * btrees_sep.v : Representation of btrees in Separation Logic *)

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
Require Import btrees.

Open Scope logic.
(**
    REPRESENTATIONS IN SEPARATION LOGIC
 **)

Definition tbtnode:=      Tstruct _BtNode noattr.
Definition tentry:=       Tstruct _Entry noattr.
Definition tchildrecord:= Tunion _Child_or_Record noattr.
Definition trelation:=    Tstruct _Relation noattr.
Definition tcursor:=      Tstruct _Cursor noattr.

Definition value_repr (v:V) : val := Vptrofs v.
  
Definition value_rep (v:V) (p:val) : mpred := (* this should change if we change the type of Values? *)
  data_at Ews (tptr tvoid) (value_repr v) p.

Lemma value_rep_local_prop: forall v p,
    value_rep v p |-- !!(isptr p).
Proof.
  intros. unfold value_rep. entailer!.
Qed.

Hint Resolve value_rep_local_prop: saturate_local.

Lemma value_valid_pointer: forall v p,
    value_rep v p |-- valid_pointer p.
Proof.
  intros. unfold value_rep. entailer!.
Qed.

Hint Resolve value_valid_pointer: valid_pointer.

Definition getval (n:node val): val :=
  match n with btnode _ _ _ _ _ x => x end.

Definition getvalr (r:relation val): val := snd r.

Definition entry_val_rep (e:entry val) :=
  match e with
  | keychild k c => (Vptrofs k,  inl (getval c))
  | keyval k v x => (Vptrofs k,  inr x)
  end.

Instance Inhabitant_entry_val_rep: Inhabitant (val * (val + val)) :=
    (Vundef, inl Vundef).
  

Lemma Znth_to_list:forall {X}{Inh: Inhabitant X}  i le e endle,
    Znth_option i le = Some e ->
    Znth i (le ++ endle) = e.
Proof.
  intros.
  rewrite Znth_option_e in H.
  repeat if_tac in H; inv H.
  autorewrite with sublist in *.
  rewrite Znth_map in H3 by list_solve. inv H3.
  autorewrite with sublist. auto.
Qed.

Lemma Znth_to_list': forall i le e endle,
    Znth_option i le = Some e ->
    Znth i (map entry_val_rep le ++ endle) = entry_val_rep e.
Proof.
  intros.
  rewrite Znth_option_e in H.
  repeat if_tac in H; inv H.
  autorewrite with sublist in *.
  rewrite Znth_map in H3 by list_solve. inv H3.
  autorewrite with sublist.
  rewrite Znth_map by list_solve. auto.
Qed.

Definition optionally {A}{B} (f: A -> B) (base: B) (o: option A) : B :=
  match o with Some x => f x | None => base end.

Fixpoint entry_rep (e:entry val): mpred:=
  match e with
  | keychild _ n => btnode_rep n
  | keyval _ v x => value_rep v x
  end
with btnode_rep (n:node val):mpred :=
  match n with btnode ptr0 le b First Last pn =>
  EX ent_end:list(val * (val + val)),
  malloc_token Ews tbtnode pn *
  data_at Ews tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Zlength (node_le n))),(
                       optionally getval nullval ptr0,(
                       map entry_val_rep le ++ ent_end)))))) pn *
  optionally btnode_rep emp ptr0 *
  iter_sepcon entry_rep le
  end.


Lemma btnode_rep_local_prop: forall n,
    btnode_rep n |-- !!(isptr (getval n)).
Proof.
  intros. destruct n. unfold btnode_rep. Intros ent_end. entailer!.
Qed.
  
Hint Resolve btnode_rep_local_prop: saturate_local.

Lemma btnode_valid_pointer: forall n,
    btnode_rep n |-- valid_pointer (getval n).
Proof.
  intros. destruct n. unfold btnode_rep. Intros ent_end. entailer!.
Qed.

Hint Resolve btnode_valid_pointer: valid_pointer.

Lemma unfold_btnode_rep: forall n,
    btnode_rep n =
  match n with btnode ptr0 le b First Last pn =>
  EX ent_end:list (val * (val+val)),
  malloc_token Ews tbtnode pn *
  data_at Ews tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Zlength (node_le n))),(
                       optionally getval nullval ptr0,(
                       map entry_val_rep le ++ ent_end)))))) pn *
  optionally btnode_rep emp ptr0 *
  iter_sepcon entry_rep le
  end.
Proof.
  intros. destruct n as [ptr0 le b First Last x].
  apply pred_ext; simpl; Intros ent_end; Exists ent_end; entailer!.
Qed.

Arguments btnode_rep n : simpl never.


Lemma fold_btnode_rep:
  forall ptr0 le b First Last pn (ent_end: list (val * (val+val)))
    nk,
  nk = Zlength (node_le (btnode val ptr0 le b First Last pn)) ->
  malloc_token Ews tbtnode pn *
  data_at Ews tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr nk),(
                       optionally getval nullval ptr0,(
                       map entry_val_rep le ++ ent_end)))))) pn *
  optionally btnode_rep emp ptr0 *
  iter_sepcon entry_rep le
 |-- btnode_rep (btnode val ptr0 le b First Last pn).
Proof.
 intros. subst.
 rewrite unfold_btnode_rep.
 Exists ent_end. cancel.
Qed.

Lemma cons_le_iter_sepcon:
  forall e le, entry_rep e * iter_sepcon entry_rep le |-- iter_sepcon entry_rep (e :: le).
Proof. intros. simpl. auto. Qed.

Lemma le_iter_sepcon_split: forall i le e,
    Znth_option i le = Some e ->
    iter_sepcon entry_rep le = entry_rep e * (entry_rep e -* iter_sepcon entry_rep le).
Proof.
  intros.
  rewrite Znth_option_e in H.
  repeat if_tac in H; inv H.
  autorewrite with sublist in *. rewrite Znth_map in H3 by list_solve. inv H3.
  generalize dependent i.
  induction le as [|e' le']; intros.
  - autorewrite with sublist in *. lia.
  - simpl. destruct (zeq i 0).
    + subst i. autorewrite with sublist in *. 
      apply pred_ext.
      * cancel. rewrite <- wand_sepcon_adjoint. cancel.
      * sep_apply wand_frame_elim. cancel.
    + simpl in H0. apply pred_ext.
      * autorewrite with sublist in *.
         rewrite (IHle' (i-1)) at 1. cancel.
        rewrite <- wand_sepcon_adjoint. cancel. rewrite sepcon_comm. apply wand_frame_elim.
        eauto. lia. lia.
      * eapply derives_trans. apply wand_frame_elim. cancel.
Qed.

Definition relation_rep (r:relation val) :mpred :=
  match r with
  (n,prel) =>
    malloc_token Ews trelation prel *
    data_at Ews trelation (getval n, (Vptrofs(Ptrofs.repr(get_numrec r)), (Vint (Int.repr (get_depth r))))) prel *
    btnode_rep n
  end.

Lemma relation_rep_local_prop: forall r,
    relation_rep r |-- !!(isptr (getvalr r)).
Proof. 
  intros. destruct r. unfold relation_rep. entailer!.
Qed.

Hint Resolve relation_rep_local_prop: saturate_local.

Lemma relation_rep_valid_pointer: forall r,
    relation_rep r |-- valid_pointer (getvalr r).
Proof.
  intros. destruct r. unfold relation_rep. entailer!.
Qed.

Hint Resolve relation_rep_valid_pointer: valid_pointer.
  
Lemma fold_relation_rep:
  forall prel n d,
   d = Int.repr (get_depth (n, prel)) ->
  malloc_token Ews trelation prel * 
  data_at Ews trelation
           (getval n, (Vptrofs (Ptrofs.repr (get_numrec (n,prel))), Vint d)) prel *
  btnode_rep n 
  |-- relation_rep (n,prel).
Proof. intros. subst. unfold relation_rep.  apply derives_refl. Qed.

Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => getval n
  end.

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Ews tcursor p *
  match r with (_,prel) =>
               data_at Ews tcursor (prel,(
                                    Vint(Int.repr((Zlength c) - 1)),(
                                    List.rev (map (fun x => (Vint(Int.repr(snd x))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.

Definition subcursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val, EX length:Z, 
  malloc_token Ews tcursor p *
  match r with (_,prel) =>
               data_at Ews tcursor (prel,(
                                    Vint(Int.repr(length )),(
                                    List.rev (map (fun x => (Vint(Int.repr(snd x))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.
(* same as cursor_rep, but _length can contain anything *)

Lemma value_fits_tcursor_props u v idxlst anclst: 
      value_fits tcursor (u, (v, (idxlst, anclst))) -> Zlength idxlst = MaxTreeDepth /\ Zlength anclst = MaxTreeDepth.
Proof. 
 simpl in *. 
 rewrite value_fits_eq. simpl. rewrite !value_fits_eq. simpl. 
 unfold unfold_reptype. simpl. intuition.
Qed.

Lemma cursor_rep_local_prop: forall c r p,
    cursor_rep c r p |-- !!(isptr p).
Proof. 
  intros. unfold cursor_rep. Intros a. Intros i. destruct r. entailer!.
Qed.

Hint Resolve cursor_rep_local_prop: saturate_local.

Lemma cursor_rep_valid_pointer: forall c r p,
    cursor_rep c r p |-- valid_pointer p.
Proof.
  intros. unfold cursor_rep. Intros a. Intros i. destruct r. entailer!.
Qed.    

Hint Resolve cursor_rep_valid_pointer: valid_pointer.

Lemma subcursor_rep_local_prop: forall c r p,
    subcursor_rep c r p |-- !!(isptr p).
Proof. 
  intros. unfold subcursor_rep. Intros a. Intros i. Intros l. destruct r. entailer!.
Qed.

Hint Resolve subcursor_rep_local_prop: saturate_local.

Lemma subcursor_rep_valid_pointer: forall c r p,
    subcursor_rep c r p |-- valid_pointer p.
Proof.
  intros. unfold subcursor_rep. Intros a. Intros i. Intros l. destruct r. entailer!.
Qed.

Hint Resolve subcursor_rep_valid_pointer: valid_pointer.

Lemma cursor_subcursor_rep: forall c r pc,
    cursor_rep c r pc |-- subcursor_rep c r pc.
Proof.
  intros. unfold cursor_rep, subcursor_rep. Intros anc_end. Intros idx_end.
  Exists anc_end. Exists idx_end. Exists (Zlength c -1). cancel.
Qed.

Inductive subchild {X:Type} : node X ->  list (entry X) -> Prop :=
| sc_eq: forall k n le, subchild n (keychild X k n :: le)
| sc_cons: forall e n le, subchild n le -> subchild n (e :: le).


Lemma subchild_nth {X}: forall (n: node X) le, subchild n le -> exists i, nth_node_le i le = Some n.
Proof.
  induction le.
  easy.
  intro h. inv h.
 - exists 0. unfold nth_node_le. autorewrite with sublist; auto. 
 -
  specialize (IHle H1). destruct IHle.
  exists (Z.succ x).
  pose proof (nth_node_le_some _ _ _ H).
  unfold nth_node_le in *.
  unfold Z.succ. 
  autorewrite with sublist. auto. 
Qed.

Lemma nth_subchild: forall {X:Type} i le (child:node X),
    nth_node_le i le = Some child -> subchild child le.
Proof.
  intros.
  unfold nth_node_le in H.
  destruct (Znth_option i le) as [[|]|] eqn:H0; inv H. rename H0 into H.
  rewrite Znth_option_e in H.
  repeat if_tac in H; inv H. autorewrite with sublist in *.
  generalize dependent i.
  induction le; intros.
  - autorewrite with sublist in H1; lia.
  - destruct (zeq i 0); subst; autorewrite with sublist in H3.
    + inv H3. apply sc_eq.
    + apply sc_cons. autorewrite with sublist in H1. apply (IHle(i-1)); try list_solve.
        simpl in H3. rewrite Znth_pos_cons in H3 by list_solve. auto.
Qed.

Inductive subnode {X : Type}: node X -> node X -> Prop :=
  sub_refl : forall n : node X, subnode n n
| sub_ptr0 : forall (n m : node X) (le : list (entry X)) (First Last : bool) (x : X),
    subnode n m -> subnode n (btnode X (Some m) le false First Last x)
| sub_child : forall (n m : node X) (le : list (entry X)) (ptr0 : node X) (First Last : bool) (x : X),
    subnode n m -> subchild m le -> subnode n (btnode X (Some ptr0) le false First Last x).

Lemma sub_trans {X: Type}: forall n m p: node X,
    subnode n m -> subnode m p -> subnode n p.
Proof.
  intros n m.
  apply (Fix (well_founded_ltof (node X) (fun n => Z.to_nat (node_depth n))) (fun p => subnode n m -> subnode m p -> subnode n p)).
  unfold ltof.
  intros p hind hnm hmp.
  inversion hmp.
  - now subst.
  - apply sub_ptr0.
    refine (hind m0 _ _ _); auto.
    rewrite <- H1. simpl.
    subst.
    pose proof (node_depth_nonneg m0).
    pose proof (Zlength_nonneg le).
    zify. subst. 
    rewrite ?Z2Nat.id by lia.  (* this line not needed in Coq 8.11 or after *)
    lia.
  - subst. apply (sub_child _ m0); auto. apply hind; auto.
    pose proof (node_depth_nonneg m0).
    pose proof (node_depth_nonneg (btnode X (Some ptr0) le false First Last x)).

    apply subchild_nth in H0. destruct H0.
    pose proof (nth_node_le_decrease le _ _ H0).
    apply Z2Nat.inj_lt; auto.
    simpl. rewrite Z.max_lt_iff. auto.
Defined.

Theorem subchild_rep: forall n le,
    subchild n le ->
    iter_sepcon entry_rep le |-- btnode_rep n * (btnode_rep n -* iter_sepcon entry_rep le).
Proof.
  intros.
  induction le. inv H.
  inversion H.
  - simpl. destruct n as [ptr0 nle isLeaf First Last x].
    cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - apply IHle in H2. simpl. eapply derives_trans.
    apply cancel_left. apply H2. cancel.
    rewrite <- wand_sepcon_adjoint. cancel. rewrite sepcon_comm.
    apply wand_frame_elim.
Qed.

Theorem subnode_rep: forall n root,
    subnode n root ->
    btnode_rep root = btnode_rep n * (btnode_rep n -* btnode_rep root).
Proof.
  intros. apply pred_ext.
  induction H; intros.
  - cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - destruct m.
     forget (btnode_rep n) as A. 
     rewrite unfold_btnode_rep.
     Intros ee. simpl optionally.
    sep_apply IHsubnode. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists ee. entailer!.
    sep_apply (modus_ponens_wand A). auto.
  - apply subchild_rep in H0. rewrite unfold_btnode_rep at 1.
    Intros ent_end. eapply derives_trans. apply cancel_left. apply H0.
    sep_apply IHsubnode. cancel. rewrite <- wand_sepcon_adjoint.
    autorewrite with norm. rewrite unfold_btnode_rep with (n:=btnode val (Some ptr0) le false First Last x).
    Exists ent_end. cancel. rewrite wand_sepcon_adjoint. apply wand_frame_ver.
  - apply wand_frame_elim.
Qed.

(* Partial cursor c is correct and points to n *)
Fixpoint partial_cursor_correct {X:Type} (c:cursor X) (n:node X) (root:node X): Prop :=
  match c with
  | [] => n = root
  | (n',i)::c' => (partial_cursor_correct c' n' root) /\ (nth_node i n' = Some n)
  end.

Lemma partial_correct_index : forall {X:Type}  (c:cursor X) n i n' root,
    partial_cursor_correct ((n,i)::c) n' root -> -1 <= i < Zlength (node_le n).
Proof.
  intros. destruct H.
  apply nth_node_some in H0. auto.
Qed.


Lemma partial_correct_indexes : forall {X:Type}  (c:cursor X) n' root,
    partial_cursor_correct c n' root ->
    Forall (fun ni => -1 <= snd ni < Zlength (node_le (fst ni))) c.
Proof.
  intros.
  revert n' H; induction c as [|[??]]; intros; constructor.
  apply partial_correct_index in H. auto.
  destruct H.
  apply (IHc _ H).
Qed.

Lemma Znth_option_cases {X : Type} (a : X) (l : list X) (i : Z): Znth_option i l = None ->
      i<0 \/ i >= Zlength l.
Proof. unfold Znth_option, Znth; intros. destruct (zlt i 0). left; trivial.
  right. unfold Inhabitant_option in H.
  remember (Z.to_nat i) as j. generalize dependent i. generalize dependent l. clear.
  induction j; simpl; intros.
+ symmetry in Heqj. apply Z2Nat_inj_0 in Heqj; trivial. subst i.
  destruct l; simpl in *. rewrite Zlength_nil. lia. congruence.
+ destruct l; simpl in *. rewrite Zlength_nil; trivial. rewrite Zlength_cons.
  assert (Y: Z.pred i >= 0).
  1: apply Z.le_ge; apply Zgt_0_le_0_pred; lia.
  specialize (IHj l H (Z.pred i) Y); clear H. lia.
Qed.

(* Complete cursor is correct and points to (keyval k v x) *)
Definition complete_cursor_correct {X:Type} (c:cursor X) k v x (root:node X): Prop :=
  match c with
  | [] => False
  | (n,i)::c' => partial_cursor_correct c' n root /\ Znth_option i (node_le n) = Some (keyval X k v x)
  end.

Lemma complete_correct_index : forall {X:Type} (c:cursor X) n i k v x root ,
    complete_cursor_correct ((n,i)::c) k v x root -> 0 <= i < Zlength (node_le n).
Proof.
  intros. unfold complete_cursor_correct in H.
  destruct H. apply Znth_option_some in H0. auto.
Qed.

Lemma complete_correct_indexes : forall {X:Type}  (c:cursor X) k v x root,
    complete_cursor_correct c k v x root ->
    Forall (fun ni => -1 <= snd ni < Zlength (node_le (fst ni))) c.
Proof.
  intros.
  destruct c as [|[??]]. constructor.
  destruct H.
  constructor.
  apply Znth_option_some in H0. simpl; lia. trivial.
  eapply partial_correct_indexes; eauto.
Qed.

(* Cursor is complete and correct for relation *)
Definition complete_cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X): Prop :=
  match getCEntry c with
  | None => False
  | Some (keychild _ _) => False
  | Some (keyval k v x) => complete_cursor_correct c k v x (get_root rel)
  end.

Lemma complete_correct_rel_index : forall  {X:Type} (c:cursor X) n i r,
    complete_cursor_correct_rel ((n,i)::c) r -> 0 <= i < Zlength (node_le n).
Proof.
  intros.
  unfold complete_cursor_correct_rel in H. destruct (getCEntry ((n,i)::c)); try contradiction.
  destruct e; try contradiction. eapply complete_correct_index. eauto.
Qed.

(* Cursor is partial but correct for the relation *)
Definition partial_cursor_correct_rel  {X:Type}  (c:cursor X) (rel:relation X) : Prop :=
  match c with
  | [] => True
  | (n,i)::c' =>
    match nth_node i n with
    | None => False
    | Some n' => partial_cursor_correct c n' (get_root rel)
    end
  end.

Lemma partial_correct_rel_index: forall  {X:Type}  (c:cursor X) n i r,
    partial_cursor_correct_rel ((n,i)::c) r -> i < Zlength (node_le n).
Proof.
  intros. unfold partial_cursor_correct_rel in H. destruct (nth_node i n); try contradiction.
  eapply partial_correct_index. eauto.
Qed.

(* Cursor is correct for relation. Either partial or complete *)
Definition cursor_correct_rel  {X:Type}  (c:cursor X) (rel:relation X) : Prop :=
  complete_cursor_correct_rel c rel \/ partial_cursor_correct_rel c rel.

Lemma nth_subnode: forall  {X:Type}  i (n n':node X),
    nth_node i n' = Some n -> subnode n n'.
Proof.
  intros.
  destruct n' as [ptr0 le isLeaf x].
  destruct isLeaf, ptr0; try easy.
  simpl in H.
  if_tac in H.
  - subst. inv H.
    constructor. constructor.
  - unfold nth_node_le in H.
     destruct (Znth_option i le) as [[|]|] eqn:?H; inv H. rename H1 into H.
     rewrite Znth_option_e in H.
     repeat if_tac in H ;inv H. rename H4 into H.
     destruct le; simpl in *.
     + autorewrite with sublist in H2; lia.
     + autorewrite with sublist in H2.
         destruct (zeq i 0). 
         * subst. autorewrite with sublist in H. inv H. 
         apply (sub_child _ n). constructor. apply sc_eq.
         *  autorewrite with sublist in H.
         eapply (sub_child _ n). constructor.
      apply sc_cons.
      apply nth_subchild with (i-1). unfold nth_node_le, Znth_option.
      fold (@Inhabitant_option (entry X)) in H.
      rewrite H. auto.
Qed.
    
(* if n is pointed to by a partial cursor, then it is a subnode of the root *)
Theorem partial_cursor_subnode': forall  {X:Type} (c:cursor X) root n,
    partial_cursor_correct c n root ->
    subnode n root.
Proof.
  intros. generalize dependent n.
  induction c.
  - intros. simpl in H. subst. apply sub_refl.
  - intros. destruct a as [n' i]. simpl in H.
    destruct H. apply IHc in H. apply nth_subnode in H0.
    eapply sub_trans; eauto.
Qed.

(* The current node of a complete cursor is a subnode of the root *)
Theorem complete_cursor_subnode: forall  {X:Type}  (c:cursor X) r,
    complete_cursor_correct_rel c r ->
    subnode (currNode c r) (get_root r).
Proof.
  destruct r as [root prel].
  pose (r:=(root,prel)). intros. unfold get_root. simpl.
  destruct c as [|[n i] c']. inv H.
  unfold complete_cursor_correct_rel in H.
  destruct (getCEntry ((n,i)::c')); try inv H.
  destruct e; try contradiction. unfold complete_cursor_correct in H.
  destruct H. apply partial_cursor_subnode' in H. unfold get_root in H. simpl in H.
  simpl. auto.
Qed.

(* Current node of a partial cursor is a subnode of the root *)
Theorem partial_cursor_subnode: forall  {X:Type}  (c:cursor X) r,
    partial_cursor_correct_rel c r ->
    subnode (currNode c r) (get_root r).
Proof. 
  intros. unfold partial_cursor_correct_rel in H.
  destruct c as [|[n i] c']. simpl. apply sub_refl.
  simpl. simpl in H. destruct (nth_node i n).
  destruct H. apply partial_cursor_subnode' in H. auto. inv H.
Qed.

(* The currnode of a correct cursor is a subnode of the root *)
Theorem cursor_subnode: forall  {X:Type}  (c:cursor X) r,
    cursor_correct_rel c r -> subnode (currNode c r) (get_root r).
Proof.
  intros. unfold cursor_correct_rel in H.
  destruct H. apply complete_cursor_subnode. auto.
  apply partial_cursor_subnode. auto.
Qed.

(* This is modified to include the balancing property. *)
Inductive intern_le {X:Type}: list (entry X) -> Z -> Prop :=
| ileo: forall k n, intern_le (keychild X k n :: nil) (node_depth n)
| iles: forall k n le d, intern_le le d -> node_depth n = d -> intern_le (keychild X k n :: le) d.

Inductive leaf_le {X:Type}: list (entry X) -> Prop :=
| llen: leaf_le nil
| llec: forall k v x le, leaf_le le -> leaf_le (keyval X k v x :: le).  

Lemma intern_no_keyval: forall {X:Type} i le d k v x,
    intern_le le d -> Znth_option i le = Some (keyval X k v x) -> False.
Proof.
  intros. rewrite Znth_option_e in H0.
  repeat if_tac in H0; inv H0.
 generalize dependent i.
  induction H; simpl; intros.
  - autorewrite with sublist in H2. assert (i=0) by lia. subst. inv H4. 
  - destruct (zeq i 0). subst. inv H4.
     autorewrite with sublist in H2.
     autorewrite with sublist in H4.
     apply (IHintern_le (i-1)). lia. list_solve. auto.
Qed.

(* An intern node should have a defined ptr0, and leaf nodes should not *)
Definition node_integrity {X:Type} (n:node X) : Prop :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => ptr0 = None /\ leaf_le le
    | false => match ptr0 with
               | None => False
               | Some ptr0 => intern_le le (node_depth ptr0)
              end
    end
  end.

(* node integrity of every subnode *)
Definition root_integrity {X:Type} (root:node X) : Prop :=
  forall n, subnode n root -> node_integrity n.

Lemma node_of_root_integrity {X} (root: node X):
  root_integrity root -> node_integrity root.
Proof.
  unfold root_integrity. intro H. 
  apply H. constructor.
Qed.

Lemma entry_subnode: forall  {X:Type}  i (n:node X) n' k,
    node_integrity n ->
    Znth_option i (node_le n) = Some (keychild X k n') ->
    subnode n' n.
Proof.
  intros X i n n' k hint h.
 destruct n. simpl in h, hint.
  destruct isLeaf, entryzero; try easy.
  - destruct hint as [_ hleaf].
    exfalso.
    clear - hleaf h.
    generalize dependent i; induction le; simpl; intros.
    rewrite Znth_option_nil in h; inv h.
    destruct (zeq i 0).
    subst. rewrite Znth_option_e in h. simpl in h. rewrite zlt_true in h by list_solve.
    autorewrite with sublist in h. 
    inv h. inv hleaf. inv hleaf. apply IHle with (i-1); auto.
    rewrite <- h. clear - n. autorewrite with sublist. auto. 
  - apply (sub_child _ n'); [constructor | ].
     generalize dependent i; induction le; intros.
    easy.
    destruct (zeq i 0).
    +
    subst i. autorewrite with sublist in h. inv h.
    constructor.
    +
    autorewrite with sublist in h.
   apply IHle in h. constructor; auto.
    inv hint. autorewrite with sublist in h. inv h. auto.
Qed.

(* integrity of every child of an entry *)
Definition entry_integrity {X:Type} (e:entry X) : Prop :=
  match e with
  | keyval k v x => True
  | keychild k child => root_integrity child
  end.

(* Intern nodes have non-empty le *)
Lemma intern_le_cons: forall {X:Type} ptr0 le b F L pn,
    node_integrity (btnode X ptr0 le b F L pn) ->
    is_true (negb (node_isLeaf (btnode X ptr0 le b F L pn))) ->
    exists e le', le = e :: le'.
Proof.
  intros. simpl in H. simpl in H0. destruct b. inv H0.
  destruct le. destruct ptr0; inv H. exists e. exists le. auto.
Qed.

Lemma integrity_nth: forall {X:Type}  (n:node X) e i,
    node_integrity n ->
    is_true (negb (node_isLeaf  n)) ->
    Znth_option i (node_le n) = Some e ->
    exists k c, e = keychild X k c.
Proof.
  intros. destruct n. generalize dependent i.
  destruct isLeaf; simpl in H0. contradiction. simpl.
  induction le; intros.
  - apply Znth_option_some in H1. autorewrite with sublist in H1; lia.
  - rewrite Znth_option_e in H1. repeat if_tac in H1; try discriminate.
      inv H1. simpl in H. destruct entryzero; try contradiction. inv H.
       autorewrite with sublist in *.
      assert (i=0) by lia. subst i. inv H5.
       exists k. exists n0. auto.
      destruct (zeq i 0). subst. autorewrite with sublist in H5. inv H5.
      exists k. exists n0. auto.
      autorewrite with sublist in H5.
      apply IHle with (i-1); auto.
Qed.

Lemma integrity_nth_leaf: forall  {X:Type} (n:node X) e i,
    node_integrity n ->
    is_true (node_isLeaf n) ->
    Znth_option i (node_le n) = Some e ->
    exists k v x, e = keyval X k v x.
Proof.
  intros. destruct n. generalize dependent i.
  destruct isLeaf; simpl in H0; try contradiction. simpl.
  induction le; intros.
  - autorewrite with sublist in H1. inv H1.
  - destruct (zeq i 0).
     autorewrite with sublist in H1. inv H1. destruct H. subst. inv H1. eauto.
     autorewrite with sublist in H1. apply IHle with  (i-1); auto.
     inv H. inv H3. constructor; auto.
Qed.
  
Lemma Zsuccminusone: forall x,
    (Z.succ x) -1 = x.
Proof. intros. rep_lia. Qed.

Definition node_wf (n:node val) : Prop := (Zlength (node_le n) <= Fanout).
Definition root_wf (root:node val) : Prop := forall n, subnode n root -> node_wf n.
Definition entry_wf (e:entry val) : Prop :=
  match e with
  | keyval _ _ _ => True
  | keychild _ c => root_wf c
  end. 

Lemma node_wf_numKeys:
   forall n,  node_wf n -> 0 <= Zlength (node_le n) <= Fanout.
Proof.
intros.
red in H.
destruct n; simpl in *. rep_lia.
Qed.
  
Lemma subchild_depth X (n ptr0: node X) le isLeaf First Last (x: X)
      (h: subchild n le):
  (node_depth n < node_depth (btnode X (Some ptr0) le isLeaf First Last x)).
Proof.
  induction le; inversion h; simpl.
  + subst. rewrite Z.max_lt_iff; left. rewrite Z.max_lt_iff; left. lia.
  + subst.
     apply IHle in H1. clear IHle. simpl in H1.
     apply Z.max_lt_iff in H1. destruct H1.
     apply Z.max_lt_iff; left.
     apply Z.max_lt_iff; right.
     auto.
     apply Z.max_lt_iff; right.
     auto.
Qed.

Lemma subnode_depth X: forall (n n': node X) (h: subnode n' n),
  (node_depth n' <= node_depth n).
Proof.
  induction 1.
 - lia.
 - transitivity (node_depth m); auto.
    simpl.
    apply Z.max_le_iff; right. lia.
 - transitivity (node_depth m). auto.
    apply Z.lt_le_incl, subchild_depth. assumption.
Qed.

Lemma subnode_equal_depth X (n root: node X) (hsub: subnode n root) (hdepth: node_depth n = node_depth root):
  n = root.
Proof.
  inversion hsub.
  - reflexivity.
  - apply subnode_depth in H.
    subst. simpl in hdepth.
    pose proof (Z.le_max_r (listentry_depth le) (Z.succ (node_depth m))).
    fold  (listentry_depth le) in hdepth.
    lia.
  - apply (subchild_depth X _ ptr0 le false First Last x) in H0.
    rewrite H2 in H0. apply subnode_depth in H. lia.
Qed.

(* With the new intern_le predicate, this <= can actually be =. TODO *)
Lemma partial_length': forall {X:Type} (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> (Zlength c <= node_depth root - node_depth n).
Proof.
  intros X c root n h.
  generalize dependent n.
  induction c.
  + intros n h. rewrite Zlength_nil.
    simpl in h. subst. lia.
  + intros n h. simpl. destruct a as [n' i]. simpl in h.
    specialize (IHc n' (proj1 h)).
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ (proj1 h))).
    pose proof (nth_node_decrease _ _ _ (proj2 h)).
   rewrite Zlength_cons. 
    lia.
Qed.
(*
(* With the new intern_le predicate, this <= can actually be =. TODO *)
Lemma partial_length_eq: forall {X:Type} (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> (Zlength c = node_depth root - node_depth n).
Proof.
  intros X c root n h.
  generalize dependent n.
  induction c.
  + intros n h. rewrite Zlength_nil.
    simpl in h. subst. lia.
  + intros n h. simpl. destruct a as [n' i]. simpl in h.
    specialize (IHc n' (proj1 h)). destruct h. 
(*    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ (proj1 h))).
    pose proof (nth_node_decrease _ _ _ (proj2 h)).*)
   rewrite Zlength_cons, IHc; clear IHc.
    generalize dependent n. generalize dependent n'. induction c; simpl; intros.
    -  subst n'. rewrite Zminus_diag. destruct root; simpl in *. destruct entryzero; try discriminate.
       destruct isLeaf; try discriminate. destruct (zeq i (-1)); try discriminate.
       * inv H0. unfold nth_node in H0. red in H0. red in H.  Search nth_node. 
    lia.
Qed.*)
Lemma integrity_depth X (ptr0: node X) le F L x:
  let n := btnode X (Some ptr0) le false F L x in
  node_integrity n ->
  node_depth n = Z.succ (node_depth ptr0).
Proof.
  simpl.
  intro h.
  induction le. inversion h.
  inversion h.
  + subst. simpl. rewrite Z.max_r; auto. rewrite Z.max_l; auto. lia.
      pose proof (node_depth_nonneg n); lia.
  + subst. specialize (IHle H1).
    simpl. rewrite H3.
    pose proof (Zlength_nonneg le).
    pose proof (node_depth_nonneg ptr0).
    rewrite Z.max_r; try  lia. (*rewrite Z.max_comm; lia. *)
Qed.

Lemma node_depth_succ {X:Type} (n n': node X) i (nint: node_integrity n) (n'int: node_integrity n') (h: nth_node i n' = Some n):
  node_depth n' = Z.succ (node_depth n).
Proof.
  pose proof (nth_subnode _ _ _ h) as nn'sub.
  pose proof (nth_node_decrease _ _ _ h) as nn'depth.
  (* n' is an internal node. *) 
  destruct n' as [[ptr0|] le [] F L x]; try easy.
  rewrite integrity_depth. f_equal.
  simpl in h.
  if_tac in h. now inv h.
  simpl in n'int.
  { clear -n'int h.
    unfold nth_node_le in h.
    destruct (Znth_option i le) as [[|]|] eqn:?H; inv h.
    rewrite Znth_option_e in H.
    repeat if_tac in H; inv H. rename H3 into H.
    generalize dependent i; induction le; simpl; intros;
    autorewrite with sublist in H1; try lia.
    destruct (zeq i 0); subst; autorewrite with sublist in H.
    inv H. inv n'int; auto.
    apply IHle in H; auto; try lia.
    inv n'int; auto. simpl in H. rewrite Znth_nil in H. inv H.
    autorewrite with sublist. lia.
  }
  assumption.
Qed.

Lemma partial_length'': forall {X:Type} (c:cursor X) (root:node X) (n:node X),
    root_integrity root ->
    partial_cursor_correct c n root -> Zlength c = node_depth root - node_depth n.
Proof.
  intros X c root n rint h.
  generalize dependent c. revert n.
  apply (Fix (well_founded_ltof (node X) (fun n => Z.to_nat (node_depth root - node_depth n)))
       (fun n => 
       forall c,
         partial_cursor_correct c n root -> Zlength c = (node_depth root - node_depth n))).
  unfold ltof.
  intros n hind c hc.
  destruct c as [|[n' i'] c].
  - simpl in hc |-*. subst. rewrite Zlength_nil; lia.
  - pose proof (partial_cursor_subnode' _ _ _ hc) as hsub.
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ hc)).
    pose proof (nth_node_decrease _ _ _ (proj2 hc)).
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ (proj1 hc))).
   rewrite Zlength_cons.
    unshelve epose proof (hind n' _ c (proj1 hc)).
    zify.
    rewrite ?Z2Nat.id by lia.  (* this line not needed in Coq 8.11 or after *)
    lia.
    replace (node_depth n) with (node_depth n' - 1).
    lia. simpl in hc.
    rewrite (node_depth_succ n n' i').
    + lia.
    + now apply rint.
    + pose proof (partial_cursor_subnode' _ _ _ (proj1 hc)). now apply rint.
    + easy.
Qed.

Lemma partial_length: forall {X:Type} (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> Zlength c <= node_depth root.
Proof.
  intros X c root n h.
  pose proof (partial_length' _ _ _ h).
  pose proof (node_depth_nonneg n); 
  lia.
Qed.

Lemma get_depth_nonneg: forall {X} (r: relation X), 0 <= get_depth r.
Proof.
intros.
unfold get_depth.
apply node_depth_nonneg.
Qed.

Lemma partial_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    partial_cursor_correct_rel c r -> (0 <= Zlength c <= get_depth r).
Proof.
  intros.
  pose proof (get_depth_nonneg r).
  unfold partial_cursor_correct_rel in H.
  destruct c as [|[n i] c']. simpl. rewrite Zlength_nil. 
  lia.
  destruct (nth_node i n); try contradiction.
  apply partial_length in H.
  rewrite Zlength_cons in *.
   unfold get_depth in *. split. list_solve. lia.
Qed.

Lemma leaf_depth X (n: node X) (hintegrity: node_integrity n) (hleaf: is_true (node_isLeaf n)): node_depth n = 0.
Proof.
  destruct n as [[ptr0|] le [] F L x]; try easy.
  now simpl in hintegrity.
  simpl.
  fold (listentry_depth le).
  replace (listentry_depth le) with 0. easy.
  induction le. easy.
  simpl in hintegrity |-*. destruct hintegrity as [_ hintegrity].
  inv hintegrity. unfold listentry_depth; simpl. fold (listentry_depth le).
  rewrite Z.max_r by apply listentry_depth_nonneg.
  now apply IHle.
Qed.

Lemma nth_entry_keyval_leaf X i (n: node X) k v x:
  node_integrity n -> Znth_option i (node_le n) = Some (keyval X k v x) -> is_true (node_isLeaf n).
Proof.
  intros hint hentry.
  destruct n as [[ptr0|] le [] F L x']; try easy.
  exfalso. simpl in hint.
  generalize dependent i. induction le; simpl in *; intros.
  autorewrite with sublist in hentry. inv hentry.
  destruct (zeq i 0).
  subst. 
  autorewrite with sublist in hentry. inv hentry.
  inv hint.
  autorewrite with sublist in hentry.
  apply IHle in hentry; auto.
  inv hint; auto.
  autorewrite with sublist in hentry. inv hentry.
Qed.

Lemma complete_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    root_integrity (get_root r) -> complete_cursor_correct_rel c r -> Zlength c = Z.succ (get_depth r).
Proof.
  intros X c [rootnode prel] hint h.
  pose proof (hint _ (complete_cursor_subnode _ _ h)).
  unfold complete_cursor_correct_rel in h.
  remember (getCEntry c) as d; destruct d; try contradiction.
  destruct e; try contradiction.
  destruct c as [|[n i] c]; try easy.
  simpl in H, h |-*.
  rewrite Zlength_cons.
  rewrite (partial_length'' c rootnode n); try easy.
  rewrite (leaf_depth _ n). unfold get_depth. simpl. lia. assumption.
  apply (nth_entry_keyval_leaf X i n k  v x H). rewrite Heqd. trivial.
Qed.

Definition complete_cursor (c:cursor val) (r:relation val) : Prop :=
  complete_cursor_correct_rel c r /\ root_integrity (get_root r).
Definition partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor_correct_rel c r /\ root_integrity (get_root r).
(* non-empty partial cursor: the level 0 has to be set *)
Definition ne_partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor_correct_rel c r /\ (0 < Zlength c).

Definition correct_depth (r:relation val) : Prop :=
  get_depth r < MaxTreeDepth.

Lemma partial_complete_length: forall (c:cursor val) (r:relation val),
    ne_partial_cursor c r \/ complete_cursor c r ->
    correct_depth r ->
    (0 <= Zlength c - 1 < MaxTreeDepth).
Proof.
  intros. destruct H.
  - unfold ne_partial_cursor in H. destruct H.
    split. destruct c. inv H1. rewrite Zlength_cons.
    rewrite Zsuccminusone. apply Zlength_nonneg.
    unfold correct_depth in H0.
    assert (Zlength c < MaxTreeDepth). apply partial_rel_length in H. lia. lia.
  - unfold complete_cursor in H. destruct H. apply complete_rel_length in H; trivial.
    rewrite H.
    pose proof (get_depth_nonneg r).
    red in H0. lia.
Qed.

Lemma partial_complete_length': forall (c:cursor val) (r:relation val),
    complete_cursor c r \/ partial_cursor c r->
    correct_depth r ->
    (0 <= Zlength c <= MaxTreeDepth).
Proof.
  intros. destruct H.
  - destruct H. unfold complete_cursor in H. apply complete_rel_length in H; trivial.
    rewrite H. red in H0. pose proof (get_depth_nonneg r). lia.
  - unfold partial_cursor in H. destruct H.
    split. destruct c. apply Zlength_nonneg. rewrite Zlength_cons. rep_lia.
    unfold correct_depth in H0.
    apply partial_rel_length in H.  lia.
Qed.

Lemma complete_leaf: forall n i c r,
    complete_cursor ((n,i)::c) r ->
(*    root_integrity (get_root r) -> *)
    is_true (node_isLeaf n).
Proof.
  intros n i c r hcomplete.
  assert (hintegrity: root_integrity (get_root r)) by (destruct hcomplete; auto).
  destruct r as [rootnode prel], hcomplete as [hcomplete _].
  unshelve eassert (nintegrity := hintegrity n _). 
  replace n with (currNode ((n, i) :: c) (rootnode, prel)) by reflexivity. now apply complete_cursor_subnode.
  unfold complete_cursor_correct_rel in hcomplete.
  case_eq (getCEntry ((n, i) :: c)).
  + intros e he. rewrite he in hcomplete.
    destruct e; try contradiction.
    simpl in hcomplete.
    destruct n as [[ptr0|] le [] First Last x]; try easy. exfalso.
    simpl in nintegrity, he.
    apply (intern_no_keyval _ _ _ _ _ _ nintegrity he).
  + intro hnone.
    now rewrite hnone in hcomplete.
Qed.

(* This lemma shows that either isValid is to blame, or complete_cursor_correct_rel, not the root_integrity *)
Lemma complete_cursor_correct_rel_isValid {X} (r: relation X) (c: cursor X)
  (CCCR: complete_cursor_correct_rel c r): isValid c r = true.
Proof. red in CCCR.
  destruct r as [rootnode prel], c as [|[[ptr0 le [] First [] x] i] c]; try easy;
    unfold isValid; simpl; remember (Z.eqb i (Zlength le)) as b; symmetry in Heqb; 
    destruct b; trivial; apply Z.eqb_eq in Heqb; subst.  (*; rewrite negb_true_iff; apply Z.eqb_neq*)
  + apply complete_correct_rel_index in CCCR; simpl in CCCR. lia.
  + apply complete_correct_rel_index in CCCR; simpl in CCCR. lia.
Qed.

(* This lemma shows that the isValid predicate is not what it should be: all complete cursors are valid. *)
Lemma complete_valid r c
  (hcomplete: complete_cursor c r): isValid c r = true.
Proof. apply complete_cursor_correct_rel_isValid. apply hcomplete. Qed.

Lemma complete_partial_leaf: forall n i c r,
    complete_cursor ((n,i)::c) r \/
    partial_cursor ((n,i)::c) r ->
    is_true (node_isLeaf n) ->
    complete_cursor ((n,i)::c) r.
Proof.
  intros n i c r h hleaf.
  destruct h as [h | h]. assumption. exfalso.
  unfold partial_cursor, partial_cursor_correct_rel in h.
  case_eq (nth_node i n).
  - now destruct n as [[ptr0|] le [] F L x].
  - intro hnone. now rewrite hnone in h.
Qed.

Lemma int_unsigned_ptrofs_toint: (* move these two into Floyd? *)
  Archi.ptr64 = false ->
  forall n : ptrofs,
  Int.unsigned (Ptrofs.to_int n) = Ptrofs.unsigned n.
Proof.
intros.
unfold Ptrofs.to_int.
rewrite Int.unsigned_repr; auto.
pose proof (Ptrofs.unsigned_range n).
rewrite Ptrofs.modulus_eq32 in H0 by auto.
rep_lia.
Qed.

Lemma int64_unsigned_ptrofs_toint:
  Archi.ptr64 = true ->
  forall n : ptrofs,
  Int64.unsigned (Ptrofs.to_int64 n) = Ptrofs.unsigned n.
Proof.
intros.
unfold Ptrofs.to_int64.
rewrite Int64.unsigned_repr; auto.
pose proof (Ptrofs.unsigned_range n).
rewrite Ptrofs.modulus_eq64 in H0 by auto.
rep_lia.
Qed.

Lemma Vptrofs_repr_Vlong_repr:
     Archi.ptr64=true ->
   forall z, Vptrofs (Ptrofs.repr z) = Vlong (Int64.repr z).
Proof.
intros.
unfold Vptrofs. rewrite H. normalize.
Qed.


Lemma partial_cursor_correct_cnil {X} c n root: 
      @partial_cursor_correct X c n root -> 
      match c with nil => n=root | _ => True end.
Proof. intros. destruct c; simpl; trivial. Qed.

Lemma ne_partial_cursor_ne {c r}: 
      ne_partial_cursor c r -> c <> [].
Proof. intros ? ?; subst. destruct H. rewrite Zlength_nil in H0; lia. Qed.

Lemma complete_cursor_correct_ne {X} c k v (x:X) root: 
      complete_cursor_correct c k v x root -> c <> [].
Proof. intros ? ?; subst. apply H. Qed.

Lemma complete_cursor_correct_rel_ne {X} c r: @complete_cursor_correct_rel X c r -> c <> [].
Proof. intros ? ?; subst c. unfold complete_cursor_correct_rel in H. simpl in H; trivial. Qed.

Lemma complete_cursor_ne c r: complete_cursor c r -> c <> [].
Proof. intros. eapply complete_cursor_correct_rel_ne. apply H. Qed.

Lemma partial_cursor_correct_isValid {X}: forall c root n,
      @partial_cursor_correct X c root n -> c=[] \/ isValid' c root=true.
Proof.
  induction c; simpl; intros; unfold isValid'; subst; simpl. left; trivial. right.
  destruct a. destruct H. destruct (IHc _ _ H); clear IHc; subst.
+ specialize (partial_cursor_correct_cnil _ _ _ H); simpl; intros. subst n0.
  unfold nth_node in H0. destruct n; simpl in *.
  destruct entryzero; try discriminate. 
  destruct isLeaf; try discriminate. rewrite negb_true_iff.
  specialize (Zlength_nonneg le); intros. rewrite andb_false_iff. right. apply Z.eqb_neq.
  destruct (zeq z (-1)); [| apply nth_node_le_some in H0]; lia.
+ destruct n0. rewrite negb_true_iff.
  specialize (Zlength_nonneg le); intros. rewrite andb_false_iff. right. apply Z.eqb_neq.
  apply nth_node_some in H0. simpl in H0. lia. 
Qed.

Lemma partial_cursor_correct_rel_isValid {X} c r
      (R: @partial_cursor_correct_rel X c r): c=[] \/ isValid c r=true.
Proof.
  destruct c; simpl in R. left; trivial.
  destruct p; right. remember (nth_node z n). destruct o; try contradiction.
  symmetry in Heqo. clear R.
  unfold isValid; simpl. destruct n.
  apply nth_node_some in Heqo. simpl in Heqo. destruct Last; trivial.
  remember (z =? Zlength le) as b; destruct b; trivial.
  symmetry in Heqb. apply Z.eqb_eq in Heqb; lia.
Qed.

Lemma partial_cursor_isValid c r
      (R: partial_cursor c r): c=[] \/ isValid c r=true.
Proof. apply partial_cursor_correct_rel_isValid; apply R. Qed. 

Lemma ne_partial_cursor_isValid c r
      (R: ne_partial_cursor c r): isValid c r=true.
Proof. specialize (ne_partial_cursor_ne R); intros. 
  destruct R. destruct (partial_cursor_correct_rel_isValid _ _ H0). auto. trivial. 
Qed.

Lemma cursor_correct_rel_isValid {X} c r
      (R: @cursor_correct_rel X c r): c=[] \/ isValid c r =true.
Proof. destruct R as [R | R]. 
  right; apply (complete_cursor_correct_rel_isValid _ _ R).
  apply (partial_cursor_correct_rel_isValid _ _ R).
Qed.

Lemma complete_cursor_correct_isValid {X} c k v (x:X) root: 
      complete_cursor_correct c k v x root -> isValid' c root=true.
Proof. intros. destruct c; try contradiction. destruct p. destruct H.
  unfold isValid'. simpl. specialize (Znth_option_some _ _ _ _ H0); intros.
  destruct n. simpl in *. destruct Last; simpl; trivial.
  rewrite negb_true_iff. apply Z.eqb_neq. lia.
Qed.

Lemma isValid_nil {X} root (R:@isValid' X [] root = true):
   node_Last root = true -> node_le root <> nil.
Proof. unfold isValid' in R. simpl in R. destruct root; simpl; intros ? ?; subst.
  rewrite Zlength_nil in R. simpl in R. congruence.
Qed. 
Lemma isValid_nil' {X} root (R:@isValid' X [] root = true):
   node_Last root = false \/ node_le root <> nil.
Proof. unfold isValid' in R. simpl in R. destruct root; simpl in *.
  destruct Last; simpl in *; [ right | left; trivial].
  intros ?; subst. rewrite Zlength_nil in R. inv R.
Qed.

Lemma isValid_nil'' {X} root (R:node_Last root = false \/ node_le root <> nil):
      @isValid' X [] root = true.
Proof. unfold isValid'; simpl. destruct root; simpl in *.
  destruct R; subst; simpl; trivial. rewrite negb_true_iff.
  remember (@Zlength (entry X) le) as z. destruct z.
+ symmetry in Heqz. apply Zlength_nil_inv in Heqz; contradiction.
+ apply andb_false_r. 
+ apply andb_false_r.
Qed. 

Lemma update_partial_cursor_rel_getval: forall c' root prel n c r, 
      (c, r) = update_partial_cursor_rel c' (root, prel) n ->
      map getval (map fst c') = map getval (map fst c).
Proof. induction c'; simpl; intros. inv H; simpl; trivial.
destruct a.
remember (update_partial_cursor_rel c' (root, prel)
         (update_node_nth_child z n0 n)) as p; destruct p.
apply IHc' in Heqp; clear IHc'. inv H. rewrite Heqp. simpl. f_equal.
unfold update_node_nth_child. destruct n0; simpl.
if_tac; simpl; trivial.
Qed. 

Lemma LeafEntry_entry_numrec_one {X e} (E: @LeafEntry X e): entry_numrec e =1.
Proof. destruct e; [ trivial | simpl in E; contradiction]. Qed.

Lemma entry_numrec_update_le_Leaf k: forall le (K : key_in_le k le = true)
      (HLeaf : forall e : entry val, In e le -> LeafEntry e) v w,
      map entry_numrec(update_le (keyval val k v w) le) = map entry_numrec le.
Proof. induction le; simpl in *; intros; trivial.
  rewrite Ptrofs.eq_sym. destruct (Ptrofs.eq (entry_key a) k); simpl in *.
+ f_equal. rewrite LeafEntry_entry_numrec_one; auto.
+ f_equal. eapply IHle; auto.
Qed.

Lemma get_numrec_update_le_Leaf k b First Last prel ptr: forall le (K : key_in_le k le = true)
      (HLeaf : forall e : entry val, In e le -> LeafEntry e) v w x,
get_numrec (btnode val ptr (update_le (keyval val k v w) le) b First Last x, prel) =
get_numrec (btnode val ptr le b First Last x, prel).
Proof. induction le; simpl in *; intros. inv K.
 rewrite Ptrofs.eq_sym. destruct (Ptrofs.eq (entry_key a) k); simpl.
 + unfold get_numrec; simpl. rewrite LeafEntry_entry_numrec_one; auto.
 + unfold get_numrec; simpl in *. rewrite entry_numrec_update_le_Leaf; auto.
Qed.

Lemma LeafEntry_entry_depth_zero X e: @LeafEntry X e -> 0 = entry_depth e.
Proof. destruct e; simpl; intros; trivial. contradiction. Qed.

Lemma entry_depth_update_le_Leaf k: forall le (K : key_in_le k le = true)
      (HLeaf : forall e : entry val, In e le -> LeafEntry e) v w,
map entry_depth (update_le (keyval val k v w) le) = map entry_depth le.
Proof. induction le; simpl in *; intros; trivial.
  rewrite Ptrofs.eq_sym. destruct (Ptrofs.eq (entry_key a) k); simpl in *.
+ f_equal. apply LeafEntry_entry_depth_zero; eauto.
+ f_equal. apply IHle; auto.
Qed.
Lemma get_depth_update_le_Leaf k ptr b First Last x prel le (K : key_in_le k le = true)
      (HLeaf : forall e : entry val, In e le -> LeafEntry e) v w:
get_depth (btnode val ptr (update_le (keyval val k v w) le) b First Last x, prel) =
get_depth (btnode val ptr le b First Last x, prel).
Proof. unfold get_depth; simpl. rewrite entry_depth_update_le_Leaf; trivial. Qed.
(*
Lemma update_partial_cursor_root: forall nd root (SUBNODE: subnode nd root) 
      c prel newc n prel1 ptr le First Last k v w x
      (K:key_in_le k le = true)
      (HLeaf: forall e, In e le -> LeafEntry e)
      (ND: nd=btnode val ptr le true First Last x),
        (newc, (n, prel1)) =
           update_partial_cursor_rel c (root, prel)
             (btnode val ptr (update_le (keyval val k v w) le) true First Last x) ->
        (getval n = getval root /\ 
         get_numrec (n, prel1) = get_numrec (root, prel) /\ 
         get_depth (n, prel1) = get_depth (root, prel)) .
Proof. intros ? ? ?. induction SUBNODE; intros; subst; simpl in *.
 induction c; simpl; intros.
+ inv H. inv SUBNODE; simpl.
  - split3; trivial.
    * apply get_numrec_update_le_Leaf; trivial.
    * apply get_depth_update_le_Leaf; trivial.
  - inv H. red in H.  rewrite entry_depth_update_le_Leaf; trivial. unfold get_depth. simpl. f_equal. f_equal.  induction le; simpl in *; intros; trivial.
         rewrite Ptrofs.eq_sym. destruct (Ptrofs.eq (entry_key a0) k); simpl in *. f_equal. rewrite LeafEntry_entry_numrec_one; auto.
         rewrite IHle; trivial. Search entry_numrec.  if_tac.
           unfold update_le. f_equal. f_equal. admit.
      ++ 
    * unfold update_le. simpl. admit.
  destruct a. remember (update_node_nth_child z n0 n) as n1.H8 : key_in_le k le = true
Lemma update_partial_cursor_root: forall c root prel newc n prel1 ptr le First Last k v w x
      (K:key_in_le k le = true)
      (HLeaf: forall e, In e le -> LeafEntry e)
      (SUBNODE: subnode (btnode val ptr le true First Last x) root),
        (newc, (n, prel1)) =
           update_partial_cursor_rel c (root, prel)
             (btnode val ptr (update_le (keyval val k v w) le) true First Last x) ->
        (getval n = getval root /\ 
         get_numrec (n, prel1) = get_numrec (root, prel) /\ 
         get_depth (n, prel1) = get_depth (root, prel)) .
Proof. induction c; simpl; intros.
+ inv H. inv SUBNODE; simpl.
  - split3; trivial.
    * apply get_numrec_update_le_Leaf; trivial.
    * apply get_depth_update_le_Leaf; trivial.
  - inv H. red in H.  rewrite entry_depth_update_le_Leaf; trivial. unfold get_depth. simpl. f_equal. f_equal.  induction le; simpl in *; intros; trivial.
         rewrite Ptrofs.eq_sym. destruct (Ptrofs.eq (entry_key a0) k); simpl in *. f_equal. rewrite LeafEntry_entry_numrec_one; auto.
         rewrite IHle; trivial. Search entry_numrec.  if_tac.
           unfold update_le. f_equal. f_equal. admit.
      ++ 
    * unfold update_le. simpl. admit.*)

(*
Lemma update_partial_cursor_rel_props: forall c root prel newc n prel1 nn,
        (newc, (n, prel1)) = update_partial_cursor_rel c (root, prel) nn ->
        (getval n = getval root /\ 
         get_numrec (n, prel1) = get_numrec (root, prel) /\ 
         get_depth (n, prel1) = get_depth (root, prel)) .
Proof. induction c; simpl; intros. inv H. admit.
  destruct a. remember (update_node_nth_child z n0 nn) as n1.
  remember (update_partial_cursor_rel c (root, prel) n1) as p. destruct p as [nv [xx yy]]. inv H. 
  specialize (IHc _ _ _ _ _ _ Heqp). trivial. simpl in IHc. destruct n0; simpl in *.
  destruct (zeq z (-1)); simpl in *.   Print update_node_nth_child. 


Lemma update_partial_cursor_rel_props: forall c root prel newc n prel1 ptr le First Last k v v0 x,
        (newc, (n, prel1)) =
           update_partial_cursor_rel c (root, prel)
             (btnode val ptr (update_le (keyval val k v v0) le) true First Last x) ->
        (getval n = getval root /\ get_numrec (n, prel1) = get_numrec (root, prel) /\ get_depth (n, prel1) = get_depth (root, prel)) .
Proof. induction c; simpl; intros.
+ inv H. simpl. admit.
  destruct a. remember (update_node_nth_child z n0 n) as n1.
  remember (update_partial_cursor_rel c (root, prel) n1) as p. destruct p as [nv [xx yy]]. inv H. 
  specialize (IHc _ _ _ _ _ _ Heqp). simpl in IHc. destruct n0; simpl in *.
  destruct (zeq z (-1)); simpl in *.   Print update_node_nth_child. 
*)