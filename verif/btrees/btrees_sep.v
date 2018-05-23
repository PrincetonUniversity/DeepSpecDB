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

Definition value_repr (v:V) : val := Vint(Int.repr v.(v_)).
  
Definition value_rep (v:V) (p:val) : mpred := (* this should change if we change the type of Values? *)
  data_at Tsh (tptr tvoid) (value_repr v) p.

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

Definition key_repr (key:key) : val := Vint(Int.repr key.(k_)).

Definition isLeaf {X:Type} (n:anode X) : bool :=
  match n with btnode ptr0 le b First Last w => b end.

Definition getval (n:anode val): val :=
  match n with btnode _ _ _ _ _ x => x end.

Definition getvalr (r:arelation val): val := snd r.

Definition entry_val_rep (e:aentry val) :=
  match e with
  | keychild k c => (key_repr k,  inl (getval c))
  | keyval k v x => (key_repr k,  inr x)
  end.
    
Fixpoint le_to_list (le:alistentry val) : list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' => entry_val_rep e :: le_to_list le'
  end.

Lemma le_to_list_length: forall (le:alistentry val),
    Zlength (le_to_list le) =
    Z.of_nat (numKeys_le le).
Proof.
  intros.
  induction le.
  - simpl. auto.
  - simpl. rewrite Zlength_cons. rewrite IHle.
    rewrite Zpos_P_of_succ_nat. auto.
Qed.

Lemma le_to_list_Znth0: forall e le,
    Znth 0 (d:=(Vundef,inl Vundef)) (le_to_list (cons val e le)) = entry_val_rep e.
Proof.
  intros. simpl. rewrite Znth_0_cons. auto.
Qed.

Lemma Znth_Zsucc: forall (X:Type) (i:Z) (e:X) (le:list X) d,
    i >= 0 -> Znth (d:=d) (Z.succ i) (e::le) = Znth i le.
Proof.
  intros. unfold Znth. rewrite if_false. rewrite if_false.
  simpl. rewrite Z2Nat.inj_succ. auto.
  omega. omega. omega.
Qed.
  
Lemma Znth_to_list: forall i le e endle d,
    nth_entry_le i le = Some e ->
    Znth (d:=d) (Z.of_nat i) (le_to_list le ++ endle) = entry_val_rep e.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - destruct i; inv H.
  - destruct i as [|ii].
    + simpl. rewrite Znth_0_cons. simpl in H. inv H. auto.
    + simpl. simpl in H. apply IHle in H.
      rewrite Zpos_P_of_succ_nat.
      rewrite Znth_Zsucc with (i:=Z.of_nat ii) (e:=entry_val_rep a) (le:=le_to_list le ++ endle).
      auto. omega.
Qed.

Fixpoint aentry_rep (e:aentry val): mpred:=
  match e with
  | keychild _ n => abtnode_rep n
  | keyval _ v x => value_rep v x
  end
with abtnode_rep (n:anode val):mpred :=
  match n with btnode ptr0 le b First Last pn =>
  EX ent_end:list(val * (val + val)),
  malloc_token Tsh tbtnode pn *
  data_at Tsh tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Z.of_nat (numKeys n))),(
                       match ptr0 with
                       | None => nullval
                       | Some n' => getval n'
                       end,(
                       le_to_list le ++ ent_end)))))) pn *
  match ptr0 with
  | None => emp
  | Some n' => abtnode_rep n'
  end *
  ale_iter_sepcon le
  end
with ale_iter_sepcon (le:alistentry val):mpred :=
  match le with
  | nil => emp
  | cons e le' => aentry_rep e * ale_iter_sepcon le'
  end.

Definition entry_val_rep' (e:entry) (p:val) :=
  match e with
  | keychild k c => (key_repr k,  inl p)
  | keyval k v _ => (key_repr k,  inr p)
  end.

Fixpoint le_to_list' (le:listentry) (lv: list val): list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' => match lv with
                 | [] => []
                 | p::lv' => entry_val_rep' e p :: le_to_list' le' lv'
                 end
  end.

Fixpoint entry_rep (e:entry) (p:val):mpred:=
  match e with
  | keychild _ n => btnode_rep n p
  | keyval _ v _ => value_rep v p
  end
with btnode_rep (n:node) (pn:val):mpred :=
  match n with btnode ptr0 le b First Last u =>
  EX ent_end:list(val * (val + val)), EX lv:list val, EX ptr0val:val,
  malloc_token Tsh tbtnode pn *
  data_at Tsh tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Z.of_nat (numKeys n))),(
                       match ptr0 with
                       | None => nullval
                       | Some n' => ptr0val
                       end,(
                       le_to_list' le lv ++ ent_end)))))) pn *
  match ptr0 with
  | None => emp
  | Some n' => btnode_rep n' ptr0val
  end *
  le_iter_sepcon le lv
  end
with le_iter_sepcon (le:listentry) (lv:list val):mpred :=
  match le with
  | nil => emp
  | cons e le' => match lv with
                 | [] => emp
                 | p::lv' => entry_rep e p * le_iter_sepcon le' lv'
                 end
  end.

Fixpoint get_list_val (le:alistentry val) : list val :=
  match le with
  | nil => []
  | cons e le' => (get_entry_val e) :: (get_list_val le')
  end
with get_entry_val (e:aentry val) : val :=
       match e with
       | keychild _ n => getval n
       | keyval _ _ x => x
       end.

Lemma numKeys_le_formalize: forall X (le:alistentry X),
    numKeys_le (formalize_le X le) = numKeys_le le.
Proof.
  intros. induction le.
  - simpl. auto.
  - simpl. rewrite IHle. auto.
Qed.

Lemma entry_val_rep_formalize: forall (e:aentry val),
    entry_val_rep e = entry_val_rep' (formalize_entry val e) (get_entry_val e).
Proof.
  intros. destruct e.
  - simpl. auto.
  - simpl. auto.
Qed.

Lemma le_to_list_formalize: forall (le:alistentry val),
    le_to_list le = le_to_list' (formalize_le val le) (get_list_val le).
Proof.
  intros. induction le.
  - simpl. auto.
  - simpl. rewrite entry_val_rep_formalize. rewrite IHle. auto.
Qed.

Lemma entry_rep_formalize: forall (e:aentry val),
    aentry_rep e = entry_rep (formalize_entry val e) (get_entry_val e).
Proof.
  intros. destruct e.
  - simpl. auto.
  - simpl. auto. Admitted.

Lemma iter_sepcon_formalize: forall (le:alistentry val),
    ale_iter_sepcon le = le_iter_sepcon (formalize_le val le) (get_list_val le).
Proof. 
  intros. induction le.
  - simpl. auto.
  - simpl. Admitted.
  
Lemma btnode_rep_formalize: forall an,
    abtnode_rep an |-- btnode_rep (formalize val an) (getval an).
Proof.
  intros.
  destruct an as [ptr0 le isLeaf first last pn].
  simpl. Admitted.

Lemma formalize_btnode_rep: forall n pn,
    btnode_rep n pn |-- EX an: anode val, !!(formalize val an = n) && abtnode_rep an.
Proof.
Admitted.

Lemma btnode_rep_local_prop: forall n,
    abtnode_rep n |-- !!(isptr (getval n)).
Proof.
  intros. destruct n. unfold abtnode_rep. Intros ent_end. entailer!.
Qed.
  
Hint Resolve btnode_rep_local_prop: saturate_local.

Lemma btnode_valid_pointer: forall n,
    abtnode_rep n |-- valid_pointer (getval n).
Proof.
  intros. destruct n. unfold abtnode_rep. Intros ent_end. entailer!.
Qed.

Hint Resolve btnode_valid_pointer: valid_pointer.

Lemma unfold_btnode_rep: forall n,
    abtnode_rep n =
  match n with btnode ptr0 le b First Last pn =>
  EX ent_end:list (val * (val+val)),
  malloc_token Tsh tbtnode pn *
  data_at Tsh tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Z.of_nat (numKeys n))),(
                       match ptr0 with
                       | None => nullval
                       | Some n' => getval n'
                       end,(
                       le_to_list le ++ ent_end)))))) pn *
  match ptr0 with
  | None => emp
  | Some n' => abtnode_rep n'
  end *
  ale_iter_sepcon le
  end.
Proof.
  intros. destruct n as [ptr0 le b First Last x].
  apply pred_ext; simpl; Intros ent_end; Exists ent_end; entailer!.
Qed.

Arguments btnode_rep n : simpl never.

Lemma le_iter_sepcon_split: forall i le e,
    nth_entry_le i le = Some e ->
    ale_iter_sepcon le = aentry_rep e * (aentry_rep e -* ale_iter_sepcon le).
Proof.
  intros. assert(i < numKeys_le le)%nat by (apply nth_entry_le_some with (e:=e); auto).
  generalize dependent i.
  induction le as [|e' le']; intros.
  - simpl in H0. inv H0.
  - simpl. destruct i as [|ii].
    + simpl in H. inv H. apply pred_ext.
      * cancel. rewrite <- wand_sepcon_adjoint. cancel.
      * eapply derives_trans. apply wand_frame_elim. cancel.
    + simpl in H. simpl in H0. apply pred_ext.
      * rewrite IHle' at 1. cancel.
        rewrite <- wand_sepcon_adjoint. cancel. rewrite sepcon_comm. apply wand_frame_elim.
        eauto. omega.
      * eapply derives_trans. apply wand_frame_elim. cancel.
Qed.

Definition arelation_rep (r:arelation val) (numrec:nat) :mpred :=
  match r with
  (n,prel) =>
    malloc_token Tsh trelation prel *
    data_at Tsh trelation (getval n, (Vint(Int.repr(Z.of_nat(numrec))), (Vint (Int.repr (Z.of_nat(get_depth r)))))) prel *
    abtnode_rep n
  end.

Definition relation_rep (r:relation) (numrec:nat) (prel:val) : mpred :=
  match r with
    (n,u) => EX pn:val,
    malloc_token Tsh trelation prel *
    data_at Tsh trelation (pn, (Vint(Int.repr(Z.of_nat(numrec))), (Vint (Int.repr (Z.of_nat(get_depth r)))))) prel *
    btnode_rep n pn
  end.

Lemma node_depth_formalize: forall X (n:anode X),
    node_depth n = node_depth (formalize X n).
Proof. Admitted.

Lemma relation_rep_formalize: forall r numrec,
    arelation_rep r numrec |-- relation_rep (formalize_rel val r) numrec (snd(r)).
Proof.
  intros.
  unfold arelation_rep, relation_rep. destruct r as [n prel].
  simpl. Exists (getval n). cancel. unfold get_depth. unfold get_root. simpl.
  rewrite node_depth_formalize. cancel. apply btnode_rep_formalize.
Qed.

Lemma formalize_relation_rep: forall r numrec prel,
    relation_rep r numrec prel |--
                 EX ar:arelation val, !!(formalize_rel val ar = r) && arelation_rep ar numrec.
Proof.
Admitted.

Lemma relation_rep_local_prop: forall r n,
    relation_rep r n |-- !!(isptr (getvalr r)).
Proof. 
  intros. destruct r. unfold relation_rep. entailer!.
Qed.

Hint Resolve relation_rep_local_prop: saturate_local.

Lemma relation_rep_valid_pointer: forall r n,
    relation_rep r n |-- valid_pointer (getvalr r).
Proof.
  intros. destruct r. unfold relation_rep. entailer!.
Qed.

Hint Resolve relation_rep_valid_pointer: valid_pointer.
  
Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => getval n
  end.

Definition rep_index (i:index): Z :=
  match i with
  | im => -1
  | ip n => Z.of_nat n
  end.

Lemma next_rep: forall i,
    (rep_index i) + 1 = rep_index (next_index i).
Proof.
  intros. destruct i.
  - simpl. auto.
  - simpl. rewrite Zpos_P_of_succ_nat. omega.
Qed.

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  match r with (_,prel) =>
               data_at Tsh tcursor (prel,(
                                    Vint(Int.repr((Zlength c) - 1)),(
                                    List.rev (map (fun x => (Vint(Int.repr(rep_index (snd x)))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.

Definition subcursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val, EX length:Z,
  malloc_token Tsh tcursor p *
  match r with (_,prel) =>
               data_at Tsh tcursor (prel,(
                                    Vint(Int.repr(length )),(
                                    List.rev (map (fun x => (Vint(Int.repr(rep_index (snd x)))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.
(* same as cursor_rep, but _length can contain anything *)

Lemma cursor_rep_local_prop: forall c r p,
    cursor_rep c r p |-- !!(isptr p).
Proof. 
  intros. unfold cursor_rep. Intros a. Intros i. destruct r. entailer!.
Qed.

Hint Resolve cursor_rep_local_prop: saturate_local.

Lemma cursor_rep_valid_pointer: forall c r p,
    cursor_rep c r p |-- valid_pointer p.
Proof.
  intros. unfold cursor_rep. Intros a. Intros i. entailer!.
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
  intros. unfold subcursor_rep. Intros a. Intros i. Intros l. entailer!.
Qed.

Hint Resolve subcursor_rep_valid_pointer: valid_pointer.

Lemma cursor_subcursor_rep: forall c r pc,
    cursor_rep c r pc |-- subcursor_rep c r pc.
Proof.
  intros. unfold cursor_rep, subcursor_rep. Intros anc_end. Intros idx_end.
  Exists anc_end. Exists idx_end. Exists (Zlength c -1). cancel.
Qed.

Inductive subchild {X:Type} : node X -> listentry X -> Prop :=
| sc_eq: forall k n le, subchild n (cons X (keychild X k n) le)
| sc_cons: forall e n le, subchild n le -> subchild n (cons X e le).

Inductive subnode {X:Type} : node X -> node X -> Prop :=
| sub_refl: forall n, subnode n n
| sub_ptr0: forall n le b First Last x, subnode n (btnode X (Some n) le b First Last x)
| sub_child: forall n le ptr0 b First Last x, subchild n le -> subnode n (btnode X ptr0 le b First Last x)
| sub_trans: forall n n1 n2, subnode n n1 -> subnode n1 n2 -> subnode n n2.

Lemma nth_subchild: forall (X:Type) i le (child:node X),
    nth_node_le i le = Some child -> subchild child le.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - destruct i; inv H.
  - destruct i as [|ii].
    + simpl in H. destruct e; inv H. apply sc_eq.
    + simpl in H. apply IHle in H. apply sc_cons. auto.
Qed.

Lemma btnode_rep_simpl_ptr0: forall le b pn (p0:option (node val)) le0 b0 pn0 p0 First Last F L,
    btnode_rep (btnode val (Some (btnode val p0 le0 b0 F L pn0)) le b First Last pn) =
    EX ent_end:list (val * (val+val)),
    malloc_token Tsh tbtnode pn *
    data_at Tsh tbtnode (Val.of_bool b,(
                       Val.of_bool First,(
                       Val.of_bool Last,(
                       Vint(Int.repr (Z.of_nat (numKeys_le le))),(
                       pn0,(
                       le_to_list le ++ ent_end)))))) pn *
  btnode_rep (btnode val p0 le0 b0 F L pn0) *
  le_iter_sepcon le.
Proof.
  intros. rewrite unfold_btnode_rep. apply pred_ext; Intros ent_end; Exists ent_end; entailer!.
Qed.

Theorem subchild_rep: forall n le,
    subchild n le ->
    le_iter_sepcon le |-- btnode_rep n * (btnode_rep n -* le_iter_sepcon le).
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
  - destruct n. rewrite btnode_rep_simpl_ptr0 by auto.
    entailer!. rewrite <- wand_sepcon_adjoint. Exists ent_end. entailer!.
  - apply subchild_rep in H. rewrite unfold_btnode_rep at 1.
    Intros ent_end. eapply derives_trans. apply cancel_left. apply H.
    cancel. rewrite <- wand_sepcon_adjoint.
    autorewrite with norm. rewrite unfold_btnode_rep with (n:=btnode val ptr0 le b First Last x).
    Exists ent_end. cancel. rewrite wand_sepcon_adjoint. cancel.
  - eapply derives_trans. apply IHsubnode2. rewrite sepcon_comm.
    eapply derives_trans. apply cancel_left.
    apply IHsubnode1. normalize. entailer!. rewrite sepcon_comm.
    apply wand_frame_ver.
  - apply wand_frame_elim.
Qed.

(* Partial cursor c is correct and points to n *)
Fixpoint partial_cursor_correct {X:Type} (c:cursor X) (n:node X) (root:node X): Prop :=
  match c with
  | [] => n = root
  | (n',i)::c' => (partial_cursor_correct c' n' root) /\ (nth_node i n' = Some n)
  end.

Lemma partial_correct_index : forall (X:Type) (c:cursor X) n i n' root,
    partial_cursor_correct ((n,i)::c) n' root -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold partial_cursor_correct in H. destruct H.
  apply nth_node_some in H0. auto.
Qed.

(* Complete cursor is correct and points to (keyval k v x) *)
Definition complete_cursor_correct {X:Type} (c:cursor X) k v x (root:node X): Prop :=
  match c with
  | [] => False
  | (n,i)::c' => match i with
                 | im => False
                 | ip ii => partial_cursor_correct c' n root /\ nth_entry ii n = Some (keyval X k v x)
                 end
  end.

Lemma complete_correct_index : forall {X:Type} (c:cursor X) n i k v x root,
    complete_cursor_correct ((n,i)::c) k v x root -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold complete_cursor_correct in H. destruct i.
  omega. destruct H. apply nth_entry_some in H0. simpl. omega.
Qed.

(* Cursor is complete and correct for relation *)
Definition complete_cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X): Prop :=
  match getCEntry c with
  | None => False
  | Some e => match e with
              | keychild _ _ => False
              | keyval k v x => complete_cursor_correct c k v x (get_root rel)
              end
  end.

Lemma complete_correct_rel_index : forall (X:Type) (c:cursor X) n i r,
    complete_cursor_correct_rel ((n,i)::c) r -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold complete_cursor_correct_rel in H. destruct (getCEntry ((n,i)::c)); try contradiction.
  destruct e; try contradiction. eapply complete_correct_index. eauto.
Qed.

(* Cursor is partial but correct for the relation *)
Definition partial_cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X) : Prop :=
  match c with
  | [] => True
  | (n,i)::c' =>
    match nth_node i n with
    | None => False
    | Some n' => partial_cursor_correct c n' (get_root rel)
    end
  end.

Lemma partial_correct_rel_index: forall (X:Type) (c:cursor X) n i r,
    partial_cursor_correct_rel ((n,i)::c) r -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold partial_cursor_correct_rel in H. destruct (nth_node i n); try contradiction.
  eapply partial_correct_index. eauto.
Qed.

(* Cursor is correct for relation. Either partial or complete *)
Definition cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X) : Prop :=
  complete_cursor_correct_rel c rel \/ partial_cursor_correct_rel c rel.

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

Lemma entry_subnode: forall X i (n:node X) n' k,
    nth_entry i n = Some (keychild X k n') ->
    subnode n' n.
Proof.
  intros. destruct n. simpl in H. apply sub_child. generalize dependent l. 
  induction i; intros.
  - destruct l. inv H.
    inv H. apply sc_eq.
  - destruct l. simpl in H. inv H. simpl in H. apply IHi in H.
    apply sc_cons. auto.
Qed.    
    
(* if n is pointed to by a partial cursor, then it is a subnode of the root *)
Theorem partial_cursor_subnode': forall X (c:cursor X) root n,
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
Theorem complete_cursor_subnode: forall X (c:cursor X) r,
    complete_cursor_correct_rel c r ->
    subnode (currNode c r) (get_root r).
Proof.
  destruct r as [root prel].
  pose (r:=(root,prel)). intros. unfold get_root. simpl.
  destruct c as [|[n i] c']. inv H.
  unfold complete_cursor_correct_rel in H.
  destruct (getCEntry ((n,i)::c')); try inv H.
  destruct e; try inv H. unfold complete_cursor_correct in H.
  destruct i. inv H. destruct H. apply partial_cursor_subnode' in H. unfold get_root in H. simpl in H.
  simpl. auto.
Qed.

(* Current node of a partial cursor is a subnode of the root *)
Theorem partial_cursor_subnode: forall X (c:cursor X) r,
    partial_cursor_correct_rel c r ->
    subnode (currNode c r) (get_root r).
Proof. 
  intros. unfold partial_cursor_correct_rel in H.
  destruct c as [|[n i] c']. simpl. apply sub_refl.
  simpl. simpl in H. destruct (nth_node i n).
  destruct H. apply partial_cursor_subnode' in H. auto. inv H.
Qed.

(* The currnode of a correct cursor is a subnode of the root *)
Theorem cursor_subnode: forall X (c:cursor X) r,
    cursor_correct_rel c r -> subnode (currNode c r) (get_root r).
Proof.
  intros. unfold cursor_correct_rel in H.
  destruct H. apply complete_cursor_subnode. auto.
  apply partial_cursor_subnode. auto.
Qed.
  
Inductive intern_le {X:Type}: listentry X -> Prop :=
| ileo: forall k n, intern_le (cons X (keychild X k n) (nil X))
| iles: forall k n le, intern_le le -> intern_le (cons X (keychild X k n) le).

Inductive leaf_le {X:Type}: listentry X -> Prop :=
| llen: leaf_le (nil X)
| llec: forall k v x le, leaf_le le -> leaf_le (cons X (keyval X k v x) le).  

Lemma intern_no_keyval: forall X i le k v x,
    intern_le le -> nth_entry_le i le = Some (keyval X k v x) -> False.
Proof.
  intros. generalize dependent i.
  induction H.
  - intros. destruct i as [|ii].
    + simpl in H0. inv H0.
    + simpl in H0. destruct ii; inv H0.
  - intros. destruct i as [|ii].
    + simpl in H0. inv H0.
    + simpl in H0. eapply IHintern_le. eauto.
Qed.

(* An intern node should have a defined ptr0, and leaf nodes should not *)
Definition node_integrity {X:Type} (n:node X) : Prop :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => ptr0 = None /\ leaf_le le
    | false => match ptr0 with
               | None => False
               | Some _ => intern_le le
              end
    end
  end.

(* node integrity of every subnode *)
Definition root_integrity {X:Type} (root:node X) : Prop :=
  forall n, subnode n root -> node_integrity n.

(* integrity of every child of an entry *)
Definition entry_integrity {X:Type} (e:entry X) : Prop :=
  match e with
  | keyval k v x => True
  | keychild k child => root_integrity child
  end.

(* leaf nodes have None ptr0 *)
Lemma leaf_ptr0: forall {X:Type} ptr0 le b F L pn,
    node_integrity (btnode X ptr0 le b F L pn) ->
    LeafNode (btnode X ptr0 le b F L pn) ->
    ptr0 = None.
Proof.
  intros. simpl in H. simpl in H0. destruct b; try inv H0. destruct H. auto.
Qed.

(* Intern nodes have Some ptr0 *)
Lemma intern_ptr0: forall {X:Type} ptr0 le b F L pn,
    node_integrity (btnode X ptr0 le b F L pn) ->
    InternNode (btnode X ptr0 le b F L pn) ->
    exists n, ptr0 = Some n.
Proof.
  intros. simpl in H. simpl in H0. destruct b. inv H0.
  destruct ptr0. exists n. auto. inv H.
Qed.

(* Intern nodes have non-empty le *)
Lemma intern_le_cons: forall {X:Type} ptr0 le b F L pn,
    node_integrity (btnode X ptr0 le b F L pn) ->
    InternNode (btnode X ptr0 le b F L pn) ->
    exists e le', le = cons X e le'.
Proof.
  intros. simpl in H. simpl in H0. destruct b. inv H0.
  destruct le. destruct ptr0; inv H. exists e. exists le. auto.
Qed.

Lemma integrity_nth: forall (X:Type) (n:node X) e i,
    node_integrity n ->
    InternNode n ->
    nth_entry i n = Some e ->
    exists k c, e = keychild X k c.
Proof.
  intros. destruct n. generalize dependent i.
  destruct b; simpl in H0. contradiction. simpl.
  induction l; intros.
  - simpl in H1. destruct i; simpl in H1; inv H1.
  - destruct i.
    + simpl in H. destruct o; try contradiction. inv H.
      simpl in H1. inv H1. exists k. exists n0. auto. simpl in H1.
      exists k. exists n0. inv H1. auto.
    + simpl in H1. apply IHl in H1. auto. simpl in H. simpl.
      destruct o; try contradiction. inv H. destruct i; inv H1. auto.
Qed.

Lemma integrity_nth_leaf: forall (X:Type) (n:node X) e i,
    node_integrity n ->
    LeafNode n ->
    nth_entry i n = Some e ->
    exists k v x, e = keyval X k v x.
Proof.
  intros. destruct n. generalize dependent i.
  destruct b; simpl in H0; try contradiction. simpl.
  induction l; intros.
  - destruct i; simpl in H1; inv H1.
  - destruct i.
    + simpl in H. destruct H. inv H2. simpl in H1. inv H1.
      exists k. exists v. exists x0. auto.
    + simpl in H1. apply IHl in H1. auto. simpl in H.
      simpl. destruct H. split; auto. inv H2. auto.
Qed.
  
Lemma Zsuccminusone: forall x,
    (Z.succ x) -1 = x.
Proof. intros. rep_omega. Qed.

Definition node_wf (n:node val) : Prop := (numKeys n <= Fanout)%nat.
Definition root_wf (root:node val) : Prop := forall n, subnode n root -> node_wf n.
Definition entry_wf (e:entry val) : Prop :=
  match e with
  | keyval _ _ _ => True
  | keychild _ c => root_wf c
  end. 

Lemma partial_length: forall (X:Type) (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> (length c <= node_depth root)%nat.
Proof.
Admitted.

Lemma partial_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    partial_cursor_correct_rel c r -> (0 <= length c <= get_depth r)%nat.
Proof.
  intros. unfold partial_cursor_correct_rel in H.
  destruct c as [|[n i] c']. simpl. omega.
  destruct (nth_node i n); try contradiction.
  apply partial_length in H. unfold get_depth. split. omega. auto.
Qed.

Definition balanced {X:Type} (root:node X) : Prop := True.
(* this should also include root integrity *)

Lemma complete_length: forall (X:Type) (c:cursor X) k v x root,
    balanced root ->
    complete_cursor_correct c k v x root ->
    length c = S(node_depth root).
Proof.
Admitted.

Lemma complete_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    balanced (get_root r) -> complete_cursor_correct_rel c r -> length c = S (get_depth r).
Proof.
  intros. unfold complete_cursor_correct_rel in H0.
  destruct (getCEntry c); try contradiction.
  destruct e; try contradiction.
  eapply complete_length; eauto.
Qed.    

Definition complete_cursor (c:cursor val) (r:relation val) : Prop :=
  complete_cursor_correct_rel c r /\ balanced (get_root r).
Definition partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor_correct_rel c r /\ balanced (get_root r).
(* non-empty partial cursor: the level 0 has to be set *)
Definition ne_partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor_correct_rel c r /\ (O < length c)%nat /\ balanced (get_root r).

Definition correct_depth (r:relation val) : Prop :=
  (get_depth r < MaxTreeDepth)%nat.

Lemma partial_complete_length: forall (c:cursor val) (r:relation val),
    ne_partial_cursor c r \/ complete_cursor c r ->
    correct_depth r ->
    (0 <= Zlength c - 1 < 20).
Proof.
  intros. destruct H.
  - unfold ne_partial_cursor in H. destruct H. destruct H1.
    split. destruct c. inv H1. rewrite Zlength_cons.
    rewrite Zsuccminusone. apply Zlength_nonneg.
    unfold correct_depth in H0.
    assert (length c < 20)%nat. rewrite MTD_eq in H0. apply partial_rel_length in H. omega.
    rewrite Zlength_correct. omega.
  - unfold complete_cursor in H. destruct H. rewrite Zlength_correct. apply complete_rel_length in H.
    rewrite H.
    split; rewrite Nat2Z.inj_succ; rewrite Zsuccminusone. omega.
    unfold correct_depth in H0. rep_omega. auto.
Qed.

Lemma partial_complete_length': forall (c:cursor val) (r:relation val),
    complete_cursor c r \/ partial_cursor c r->
    correct_depth r ->
    (0 <= Zlength c <= 20).
Proof.
  intros. destruct H.
  - unfold complete_cursor in H. destruct H. rewrite Zlength_correct. apply complete_rel_length in H.
    rewrite H.
    split; rewrite Nat2Z.inj_succ. omega.
    unfold correct_depth in H0. rep_omega. auto.
  - unfold partial_cursor in H. destruct H. destruct H1.
    split. destruct c. apply Zlength_nonneg. rewrite Zlength_cons. rep_omega.
    unfold correct_depth in H0.
    assert (length c < 20)%nat. rewrite MTD_eq in H0. apply partial_rel_length in H. omega.
    rewrite Zlength_correct. omega.
Qed.

Lemma complete_leaf: forall n i c r,
    complete_cursor ((n,i)::c) r ->
    root_integrity (get_root r) ->
    LeafNode n.
Proof.
  intros.
  destruct r as [root prel].
  simpl in H0.
  assert(subnode n root).
  unfold complete_cursor in H. destruct H.
  apply complete_cursor_subnode in H. simpl in H. auto.
  unfold root_integrity in H0. apply H0 in H1. unfold node_integrity in H1.
  destruct n. destruct b. simpl. auto.
  exfalso. destruct o; try contradiction.
  unfold complete_cursor in H. destruct H.
  unfold complete_cursor_correct_rel in H.
Admitted.