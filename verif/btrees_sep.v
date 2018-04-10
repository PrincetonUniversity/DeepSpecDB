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
Require Import index.

(**
    REPRESENTATIONS IN SEPARATION LOGIC
 **)

Definition tbtnode:=      Tstruct _BtNode noattr.
Definition tentry:=       Tstruct _Entry noattr.
Definition tchildrecord:= Tunion _Child_or_Record noattr.
Definition trelation:=    Tstruct _Relation noattr.
Definition tcursor:=      Tstruct _Cursor noattr.

Definition value_rep (v:V) (p:val):= (* this should change if we change the type of Values? *)
  data_at Tsh tint (Vint (Int.repr v)) p.

Definition isLeaf {X:Type} (n:node X) : bool :=
  match n with btnode ptr0 le b First Last w => b end.

Definition getval (n:node val): val :=
  match n with btnode _ _ _ _ _ x => x end.

Fixpoint le_to_list (le:listentry val) : list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' =>
    (match e with
     | keychild k c => ((Vlong(Int64.repr k)),  inl (getval c))
     | keyval k v x => ((Vlong(Int64.repr k)),  inr x) (* ptr to the record?? *)
     end) :: le_to_list le'
  end.

Definition le_to_list_complete (le:listentry val):=
  le_to_list le ++ list_repeat (Fanout - numKeys_le le) (Vundef, inl Vundef).
                        
Fixpoint entry_rep (e:entry val):=
  match e with
  | keychild _ n => match n with btnode _ _ _ _ _ x => btnode_rep n x end
  | keyval _ v x => value_rep v x
  end
with btnode_rep (n:node val) (p:val):mpred :=
  match n with btnode ptr0 le b First Last x =>
  !!(x=p) &&
  malloc_token Tsh tbtnode p *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) p *
  field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool b) p *
  field_at Tsh tbtnode (DOT _FirstLeaf) (Val.of_bool First) p *
  field_at Tsh tbtnode (DOT _LastLeaf) (Val.of_bool Last) p *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _ptr0) nullval p
  | Some n' => match n' with btnode _ _ _ _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' p * btnode_rep n' p' end
  end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) p *
  le_iter_sepcon le
  end
with le_iter_sepcon (le:listentry val):mpred :=
  match le with
  | nil => emp
  | cons e le' => entry_rep e * le_iter_sepcon le'
  end.

Lemma btnode_rep_local_prop: forall n p,
    btnode_rep n p |-- !!(isptr p).
Proof.
  intros. destruct n. unfold btnode_rep. Intros. subst. entailer!.
Qed.

Lemma btnode_rep_local_prop2: forall n p,
    btnode_rep n p |-- !!(p = getval n).
Proof.
  intros. destruct n. unfold btnode_rep. Intros. subst. entailer!.
Qed.
  
Hint Resolve btnode_rep_local_prop: saturate_local.
Hint Resolve btnode_rep_local_prop2: saturate_local.

Lemma btnode_valid_pointer: forall n p,
    btnode_rep n p |-- valid_pointer p.
Proof.
  intros. destruct n. unfold btnode_rep. entailer!.
Qed.

Hint Resolve btnode_valid_pointer: valid_pointer.

Lemma btnode_rep_getval: forall n pn,
    btnode_rep n pn = !!(pn = getval n) && btnode_rep n pn.
Proof.
  intros. apply pred_ext; unfold btnode_rep; entailer!.
Qed.

Lemma unfold_btnode_rep: forall n p,
    btnode_rep n p =
  match n with btnode ptr0 le b First Last x =>
  !!(x=p) &&
  malloc_token Tsh tbtnode p *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) p *
  field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool b) p *
  field_at Tsh tbtnode (DOT _FirstLeaf) (Val.of_bool First) p *
  field_at Tsh tbtnode (DOT _LastLeaf) (Val.of_bool Last) p *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _ptr0) nullval p
  | Some n' => match n' with btnode _ _ _ _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' p * btnode_rep n' p' end
  end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) p *
  le_iter_sepcon le
  end.
Proof.
  intros. destruct n as [ptr0 le b First Last x]. apply pred_ext; simpl; entailer!.
Qed.

Definition relation_rep (r:relation val) (p:val):mpred :=
  match r with
  | (n,c,d,x) => !!(x=p) &&
    EX p':val,
          field_at Tsh trelation (DOT _root) p' p *
          btnode_rep n p' *
          field_at Tsh trelation (DOT _numRecords) (Vint(Int.repr(Z.of_nat c))) p *
          field_at Tsh trelation (DOT _depth) (Vint (Int.repr (Z.of_nat d))) p *
          malloc_token Tsh trelation p
  end.

Lemma relation_rep_local_prop: forall r p,
    relation_rep r p |-- !!(isptr p).
Proof. 
  intros. destruct r. unfold relation_rep. destruct p0. destruct p0. Intros p'. entailer!.
Qed.

Lemma relation_rep_local_prop2: forall r p,
    relation_rep r p |-- !!(p = snd r).
Proof. 
  intros. destruct r. unfold relation_rep. destruct p0. destruct p0. Intros p'. entailer!.
Qed.

Hint Resolve relation_rep_local_prop: saturate_local.
Hint Resolve relation_rep_local_prop2: saturate_local.

Lemma relation_rep_valid_pointer: forall r p,
    relation_rep r p |-- valid_pointer p.
Proof.
  intros. destruct r. unfold relation_rep. destruct p0. destruct p0. Intros p'. entailer!.
Qed.

Hint Resolve relation_rep_valid_pointer: valid_pointer.
  
Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => getval n
  end.

Fixpoint cursor_valid_bool {X:Type} (c:cursor X): bool :=
  match c with
  | [] => true
  | (b,i)::c' => match b with btnode ptr0 le _ _ _ x => (index_leb_nat i (numKeys_le le -1)) && cursor_valid_bool c' end
  end.                          (* might be incomplete *)

Definition rep_index (i:index):=
  match i with
  | im => Vint(Int.repr(-1))
  | ip n => Vint(Int.repr(Z.of_nat n))
  end.

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  match r with (n,c,x) => field_at Tsh tcursor (DOT _relation) x p end *
  field_at Tsh tcursor (DOT _level) (Vint(Int.repr(Zlength c - 1))) p *
  field_at Tsh tcursor (DOT _ancestorsIdx) ( List.rev (map (fun x => (rep_index (snd x)))  c) ++ idx_end) p *
  field_at Tsh tcursor (DOT _ancestors) (List.rev (map getval (map fst c)) ++ anc_end) p.

Lemma cursor_rep_local_prop: forall c r p,
    cursor_rep c r p |-- !!(isptr p).
Proof. 
  intros. unfold cursor_rep. Intros a. Intros i. entailer!.
Qed.

Hint Resolve cursor_rep_local_prop: saturate_local.

Lemma cursor_rep_valid_pointer: forall c r p,
    cursor_rep c r p |-- valid_pointer p.
Proof.
  intros. unfold cursor_rep. Intros a. Intros i. entailer!.
Qed.    

Hint Resolve cursor_rep_valid_pointer: valid_pointer.

Inductive subchild {X:Type} : node X -> listentry X -> Prop :=
| sc_eq: forall k n le, subchild n (cons X (keychild X k n) le)
| sc_cons: forall e n le, subchild n le -> subchild n (cons X e le).

Inductive subnode {X:Type} : node X -> node X -> Prop :=
| sub_refl: forall n, subnode n n
| sub_ptr0: forall n le b First Last x, subnode n (btnode X (Some n) le b First Last x)
| sub_child: forall n le ptr0 b First Last x, subchild n le -> subnode n (btnode X ptr0 le b First Last x)
| sub_trans: forall n n1 n2, subnode n n1 -> subnode n1 n2 -> subnode n n2.

Lemma btnode_rep_simpl_ptr0: forall le b x (p0:option (node val)) le0 b0 x0 proot p0 First Last F L,
    btnode_rep (btnode val (Some (btnode val p0 le0 b0 F L x0)) le b First Last x) proot =
    !!(x=proot) &&
      malloc_token Tsh tbtnode proot *
    field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys_le le)))) proot *
    field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool b) proot *
    field_at Tsh tbtnode (DOT _ptr0) x0 proot *
    field_at Tsh tbtnode (DOT _FirstLeaf) (Val.of_bool First) proot *
    field_at Tsh tbtnode (DOT _LastLeaf) (Val.of_bool Last) proot *
    btnode_rep (btnode val p0 le0 b0 F L x0) x0 *
    field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) proot *
    le_iter_sepcon le.
Proof.
  intros. apply pred_ext; entailer!; simpl; entailer!.
Qed.

Theorem subchild_rep: forall n le,
    subchild n le ->
    le_iter_sepcon le |-- EX pn:val, btnode_rep n pn * (btnode_rep n pn -* le_iter_sepcon le).
Proof.
  intros.
  induction le. inv H.
  inversion H.
  - simpl. destruct n as [ptr0 nle isLeaf First Last x].
    Exists x. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - apply IHle in H2. simpl. eapply derives_trans.
    apply cancel_left. apply H2. Intros pn. Exists pn. cancel.
    rewrite <- wand_sepcon_adjoint. cancel. rewrite sepcon_comm.
    apply wand_frame_elim.
Qed.

Theorem subnode_rep: forall n root proot,
    subnode n root ->
    btnode_rep root proot = EX pn:val, btnode_rep n pn * (* pn is getval of n *)
                              (btnode_rep n pn -* btnode_rep root proot).
Proof.
  intros. apply pred_ext.
  generalize dependent proot.
  induction H; intros.
  - Exists proot. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - destruct n. Exists v. rewrite btnode_rep_simpl_ptr0 by auto.
    entailer!. rewrite <- wand_sepcon_adjoint. entailer!.
  - apply subchild_rep in H.
    simpl. eapply derives_trans. apply cancel_left. apply H.
    Intros pn. Exists pn. cancel. rewrite <- wand_sepcon_adjoint.
    autorewrite with norm. cancel. rewrite wand_sepcon_adjoint. cancel.
  - eapply derives_trans. apply IHsubnode2.
    Intros p1. rewrite sepcon_comm.
    eapply derives_trans. apply cancel_left.
    apply IHsubnode1. normalize. Exists pn. entailer!. rewrite sepcon_comm.
    apply wand_frame_ver.
  - Intros pn. apply wand_frame_elim.
Qed.

Fixpoint cursor_correct {X:Type} (c:cursor X) (n:node X) (root:node X): Prop :=
  match c with
  | [] => n = root
  | (n',i)::c' => (cursor_correct c' n' root) /\ (nth_node i n' = Some n)
  end.

Definition get_root {X:Type} (rel:relation X) : node X := fst(fst (fst rel)).

Definition cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X): Prop :=
  cursor_correct c (currNode c rel) (get_root rel).

Lemma nth_le_subchild: forall X i (n:node X) le,
    nth_node_le i le = Some n -> subchild n le.
Proof.
  intros. generalize dependent le. induction i.
  - intros. simpl in H. destruct le; try inv H. destruct e; try inv H1.
    apply sc_eq.
  - intros. simpl in H. destruct le; try inv H. apply IHi in H1.
    apply sc_cons. auto.
Qed.

Lemma nth_subnode: forall X i (n:node X) n',
    nth_node i n' = Some n -> subnode n n'.
Proof.
  intros.
  induction i.
  - unfold nth_node in H. destruct n'. subst. apply sub_ptr0.
  - destruct n' as [ptr0 le isLeaf x]. simpl in H.
    generalize dependent n. generalize dependent le. induction n0.
    + intros. destruct le; simpl in H. inv H. destruct e; inv H.
      apply sub_child. apply sc_eq.
    + intros. simpl in H. destruct le. inv H.
      apply nth_le_subchild in H.
      apply sub_child. apply sc_cons. auto.
Qed.

Theorem cursor_subnode: forall X (c:cursor X) root n,
    cursor_correct c n root ->
    subnode n root.
Proof.
  intros. generalize dependent n.
  induction c.
  - intros. simpl in H. subst. apply sub_refl.
  - intros. destruct a as [n' i]. simpl in H.
    destruct H. apply IHc in H. apply nth_subnode in H0.
    eapply sub_trans; eauto.
Qed.