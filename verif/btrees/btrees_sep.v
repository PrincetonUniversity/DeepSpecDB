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
Require Import btrees.

(**
    REPRESENTATIONS IN SEPARATION LOGIC
 **)

Definition tbtnode:=      Tstruct _BtNode noattr.
Definition tentry:=       Tstruct _Entry noattr.
Definition tchildrecord:= Tunion _Child_or_Record noattr.
Definition trelation:=    Tstruct _Relation noattr.
Definition tcursor:=      Tstruct _Cursor noattr.

Definition rec_repr (rec: V): val :=
  Vint (Ptrofs.to_int rec).

Definition rec_rep (rec: V) (p: val): mpred :=
  data_at Ews (tptr tvoid) (rec_repr rec) p.

Lemma rec_rep_local_prop: forall v p,
    rec_rep v p |-- !!(isptr p).
Proof.
  intros. unfold rec_rep. entailer!.
Qed.

Hint Resolve rec_rep_local_prop: saturate_local.

Lemma rec_valid_pointer: forall v p,
    rec_rep v p |-- valid_pointer p.
Proof.
  intros. unfold rec_rep. entailer!.
Qed.

Hint Resolve rec_valid_pointer: valid_pointer.

Definition key_repr (key:K) : val := Vint (Int.repr key).

Fixpoint remember_In {A: Type} (l: list A): list {a: A | In a l} :=
match l with
| [] => []
| hd::tl => exist _ hd (in_eq _ _) :: map (fun '(exist x hx) => exist _ x (in_cons _ _ _ hx)) (remember_In tl)
end.

Lemma remember_In_spec {A: Type} (l: list A):
  map (@proj1_sig _ _) (remember_In l) = l.
Proof.
  induction l as [| x hx].
  reflexivity.
  cbn. rewrite map_map.
  f_equal.
  rewrite <- IHhx at 2. 
  apply map_ext.
  intros []. reflexivity.
Qed.

Existing Instance node_subterm_wf_instance. (* doesn't seem to work *)

Require Import Equations.Equations.

(* add ent_end *)
Equations(noind) btnode_rep (n: @node val): mpred by wf n node_subterm :=
  btnode_rep (leaf l F L v) => malloc_token Ews tbtnode v *
       data_at Ews tbtnode
               (Val.of_bool true,
               (Val.of_bool F,
               (Val.of_bool L,
               (Vint (Int.repr (Z.of_nat (length l))),
               (nullval,
               (map (fun '(k, rec, v) => (Vint (Int.repr k), inr (rec_repr rec))) l)))))) v
                * iter_sepcon (fun '(_, rec, p) => rec_rep rec p) l;
  btnode_rep (internal ptr0 l F L v) => malloc_token Ews tbtnode v *
       data_at Ews tbtnode
               (Val.of_bool false,
               (Val.of_bool F,
               (Val.of_bool L,
               (Vint (Int.repr (Z.of_nat (length l))),
               (getval ptr0,
               (map (fun '(k, n) => (Vint (Int.repr k), inl (getval n))) l)))))) v
                * btnode_rep ptr0 * (@iter_sepcon mpred _ _ _ (fun x => btnode_rep (snd (proj1_sig x))) (remember_In l): mpred).
Next Obligation.
  unfold node_subterm. intros. exists ptr0_index. constructor.
Qed.
Next Obligation.
  intros.
  unfold node_subterm.
  apply In_nth_error in H. destruct H as [i hi].
  unshelve eexists (inr (exist _ i _)).
  cbn. eapply nth_error_Some. rewrite hi. discriminate.
  constructor. eapply map_nth_error in hi. exact hi.
Qed.

(*
Program Fixpoint node_rep (n: node) {wf node_subterm n}: mpred :=
  match n with
  | leaf l F L v => malloc_token Ews tbtnode v *
       data_at Ews tbtnode
               (Val.of_bool true,
               (Val.of_bool F,
               (Val.of_bool L,
               (Vint (Int.repr (Z.of_nat (length l))),
               (nullval,
               (map (fun t: K*V*val => match t with (k, rec, v) => (Vint (Int.repr k), inr (rec_repr rec)) end) l)))))) v
                * iter_sepcon (fun t => match t: K*V*val with (_, rec, p) => rec_rep rec p end) l
  | internal ptr0 l F L v as m => malloc_token Ews tbtnode v *
       data_at Ews tbtnode
               (Val.of_bool false,
               (Val.of_bool F,
               (Val.of_bool L,
               (Vint (Int.repr (Z.of_nat (length l))),
               (getval ptr0,
               (map (fun '(k, n) => (Vint (Int.repr k), inl (getval n))) l)))))) v
                * node_rep ptr0 * iter_sepcon (fun x: {a: K*node | In a l} => match x with (_, n) => node_rep n end) (remember_In l)
   end.
Next Obligation.
  unfold node_subterm. exists ptr0_index. constructor.
Qed.
Next Obligation.
  unfold node_subterm.
  apply In_nth_error in H. destruct H as [n hn].
  unshelve eexists (inr (exist _ n _)).
  cbn. eapply nth_error_Some. rewrite hn. discriminate.
  constructor. eapply map_nth_error in hn. exact hn.
Qed.
Next Obligation.
  apply Wf.measure_wf, node_subterm_wf.
Qed. *)

Lemma btnode_rep_local_prop: forall n,
    btnode_rep n |-- !!(isptr (getval n)).
Proof.
  intros. destruct n; simp btnode_rep; entailer.
Qed.
  
Hint Resolve btnode_rep_local_prop: saturate_local.

Lemma btnode_valid_pointer: forall n,
    btnode_rep n |-- valid_pointer (getval n).
Proof.
  intros. destruct n; simp btnode_rep; entailer.
Qed.

Hint Resolve btnode_valid_pointer: valid_pointer.

Lemma iter_sepcon_nth {A: Type} (i: nat) (l: list A) (e: A) (f: A -> mpred):
  nth_error l i = Some e -> iter_sepcon f l = f e * (f e -* iter_sepcon f l).
Proof.
  intro h.
  apply nth_error_split in h. destruct h as [l1 [l2 [hl12 hlen]]].
  rewrite hl12. rewrite iter_sepcon_app. cbn.
  rewrite (sepcon_comm (f e) (iter_sepcon f l2)), <- (sepcon_assoc _ _ (f e)),
       wand_sepcon', (sepcon_comm (f e)). reflexivity.
Qed.

Definition relation_rep: relation val -> mpred :=
  fun '(exist (root, depth) (conj hFL hbalanced), prel) => 
    malloc_token Ews trelation prel *
    data_at Ews trelation
            (getval root,
            (Vint (Int.repr (Z.of_nat (node_numrec root))),
             Vint (Int.repr (Z.of_nat depth)))) prel *
    btnode_rep root.


Lemma relation_rep_local_prop: forall r,
    relation_rep r |-- !!(isptr (snd r)).
Proof. 
  intros [[[] []]]. unfold relation_rep. entailer.
Qed.

Hint Resolve relation_rep_local_prop: saturate_local.

Lemma relation_rep_valid_pointer: forall r,
    relation_rep r |-- valid_pointer (snd r).
Proof.
  intros [[[] []]]. unfold relation_rep. entailer.
Qed.

Hint Resolve relation_rep_valid_pointer: valid_pointer.
  
Definition currVal {r: relation val} (c: nontrivial_cursor r): val :=
  getval (currNode c).

Definition rep_index {X: Type} {n: @node X} (i: index n): Z :=
  match n, i with
  | leaf _ _ _ _, exist k hk => Z.of_nat k
  | internal _ _ _ _ _, inl tt => -1
  | internal _ _ _ _ _, inr (exist k hk) => Z.of_nat k
end.

Lemma next_rep {X: Type} {n: @node X} {d: nat} (i: index n) (h: balanced d n):
    rep_index i + 1 = rep_index (next_index h i).
Proof.
  destruct n, i. cbn.
Abort. (* This is no longer provable. *)

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Ews tcursor p *
  match r with (_,prel) =>
               data_at Ews tcursor (prel,(
                                    Vint(Int.repr((Zlength c) - 1)),(
                                    List.rev (map (fun x => (Vint(Int.repr(rep_index (snd x)))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.

Definition subcursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val, EX length:Z,
  malloc_token Ews tcursor p *
  match r with (_,prel) =>
               data_at Ews tcursor (prel,(
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


Lemma subchild_nth {X}: forall (n: node X) le, subchild n le -> exists i, nth_node_le i le = Some n.
Proof.
  induction le.
  easy.
  intro h. inversion h. exists 0%nat. easy.
  specialize (IHle H1). destruct IHle.
  exists (S x)%nat.
  easy.
Qed.

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

Inductive subnode {X : Type} : node X -> node X -> Prop :=
  sub_refl : forall n : node X, subnode n n
| sub_ptr0 : forall (n m : node X) (le : listentry X) (First Last : bool) (x : X),
    subnode n m -> subnode n (btnode X (Some m) le false First Last x)
| sub_child : forall (n m : node X) (le : listentry X) (ptr0 : node X) (First Last : bool) (x : X),
    subnode n m -> subchild m le -> subnode n (btnode X (Some ptr0) le false First Last x).

Lemma sub_trans {X: Type}: forall n m p: node X,
    subnode n m -> subnode m p -> subnode n p.
Proof.
  intros n m.
  apply (Fix (well_founded_ltof (node X) (fun n => node_depth n)) (fun p => subnode n m -> subnode m p -> subnode n p)).
  unfold ltof.
  intros p hind hnm hmp.
  inversion hmp.
  - now subst.
  - apply sub_ptr0.
    refine (hind m0 _ _ _).
    rewrite <- H1. simpl.
    apply index.lt_max_split_r. omega.
    assumption.
    assumption.
  - apply (sub_child _ m0). apply hind.
    rewrite <- H2. apply subchild_nth in H0. destruct H0.
    simpl.
    apply (Nat.lt_le_trans _ (listentry_depth le)).
    apply (nth_node_le_decrease _ le _ _ H0).
    apply index.le_l. 
    assumption.
    assumption.
    assumption.
Defined.

Lemma btnode_rep_simpl_ptr0: forall le b pn (p0:option (node val)) le0 b0 pn0 p0 First Last F L,
    btnode_rep (btnode val (Some (btnode val p0 le0 b0 F L pn0)) le b First Last pn) =
    EX ent_end:list (val * (val+val)),
  malloc_token Ews tbtnode pn *
  data_at Ews tbtnode (Val.of_bool b,(
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
  - destruct m. rewrite btnode_rep_simpl_ptr0 by auto. entailer.
    sep_apply IHsubnode. entailer!.
    rewrite <- wand_sepcon_adjoint. Exists ent_end. entailer!.
    rewrite sepcon_comm. apply modus_ponens_wand.
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

Lemma partial_correct_index : forall (X:Type) (c:cursor X) n i n' root,
    partial_cursor_correct ((n,i)::c) n' root -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold partial_cursor_correct in H. destruct H.
  apply nth_node_some in H0. auto.
Qed.

(* Complete cursor is correct and points to (keyval k v x) *)
Definition keyval_cursor_correct {X:Type} (c:cursor X) k v x (root:node X): Prop :=
  match c with
  | [] => False
  | (n,i)::c' => match i with
                 | im => False
                 | ip ii => partial_cursor_correct c' n root /\ nth_entry ii n = Some (keyval X k v x)
                 end
  end.

(* Complete cursor is correct and points after the last keyval *)
Definition lastpointer_cursor_correct {X:Type} (c:cursor X) (root:node X): Prop :=
  match c with
  | [] => False
  | (n,i)::c' => match i with
                 | im => False
                 | ip ii => partial_cursor_correct c' n root /\ LeafNode n /\ ii = numKeys n
                 end
  end.

Lemma keyval_correct_index : forall {X:Type} (c:cursor X) n i k v x root,
    keyval_cursor_correct ((n,i)::c) k v x root -> idx_to_Z i < Z.of_nat (numKeys n).
Proof.
  intros. unfold keyval_cursor_correct in H. destruct i.
  omega. destruct H. apply nth_entry_some in H0. simpl. omega.
Qed.

(* Cursor is complete and correct for relation *)
Definition complete_cursor_correct_rel {X:Type} (c:cursor X) (rel:relation X): Prop :=
  match getCEntry c with
  | None => lastpointer_cursor_correct c (get_root rel)
  | Some e => match e with
              | keychild _ _ => False
              | keyval k v x => keyval_cursor_correct c k v x (get_root rel)
              end
  end.

Lemma complete_correct_rel_index : forall (X:Type) (c:cursor X) n i r,
    complete_cursor_correct_rel ((n,i)::c) r -> idx_to_Z i <= Z.of_nat (numKeys n).
Proof.
  intros. unfold complete_cursor_correct_rel in H. destruct (getCEntry ((n,i)::c)).
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

Lemma nth_le_subchild: forall X i (n:node X) le,
    nth_node_le i le = Some n -> subchild n le.
Proof.
  intros. generalize dependent le. induction i.
  - intros. simpl in H. destruct le; try inv H. destruct e; try inv H1.
    apply sc_eq.
  - intros. simpl in H. destruct le; try inv H. apply IHi in H1.
    apply sc_cons. auto.
Qed.

Lemma nth_subnode: forall X i (n n':node X),
    nth_node i n' = Some n -> subnode n n'.
Proof.
  intros.
  destruct n' as [ptr0 le isLeaf x].
  destruct isLeaf, ptr0; try easy.
  induction i.
  - unfold nth_node in H. destruct n. subst. inversion H.
    constructor. constructor.
  - simpl in H.
    generalize dependent n. generalize dependent le. destruct n1.
    + intros. destruct le; simpl in H. inv H.
      apply (sub_child _ n). constructor.
      destruct e. easy. inv H. apply sc_eq.
    + intros. simpl in H. destruct le. inv H.
      apply nth_le_subchild in H.
      apply (sub_child _ n). constructor. apply sc_cons. auto.
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

(* This is modified to include the balancing property, as well as First/Last coherence. *)
Inductive intern_le {X:Type}: bool -> bool -> listentry X -> nat -> Prop :=
| ileo: forall k ptr0 le isLeaf First Last x,
    let n := btnode X ptr0 le isLeaf First Last x in
    intern_le First Last (cons X (keychild X k n) (nil X)) (node_depth n)
| iles: forall k le ptr0 le' isLeaf First Last x,
    let n := btnode X ptr0 le' isLeaf First false x in
    let d := node_depth n in
    intern_le false Last le d ->
    intern_le First Last (cons X (keychild X k n) le) d.

Inductive leaf_le {X:Type}: listentry X -> Prop :=
| llen: leaf_le (nil X)
| llec: forall k v x le, leaf_le le -> leaf_le (cons X (keyval X k v x) le).  

Lemma intern_no_keyval X i le d k v x F L:
    intern_le F L le d -> nth_entry_le i le = Some (keyval X k v x) -> False.
Proof.
  intros H Heq. generalize dependent i.
  induction H.
  - intros. destruct i as [|ii].
    + simpl in Heq. inv Heq.
    + simpl in Heq. destruct ii; inv Heq.
  - intros. destruct i as [|ii].
    + simpl in Heq. inv Heq.
    + simpl in Heq. eapply IHintern_le. eauto.
Qed.

(* An intern node should have a defined ptr0, and leaf nodes should not *)
Definition node_integrity {X:Type} (n:node X) : Prop :=
  match n with
    btnode ptr0 le isLeaf First Last x =>
    match isLeaf with
    | true => ptr0 = None /\ leaf_le le
    | false => match ptr0 with
               | None => False
               | Some ptr0 => intern_le First Last le (node_depth ptr0)
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

Lemma entry_subnode: forall X i (n:node X) n' k,
    node_integrity n ->
    nth_entry i n = Some (keychild X k n') ->
    subnode n' n.
Proof.
  intros X i n n' k hint h. destruct n. simpl in h, hint.
  destruct b, o; try easy.
  - destruct hint as [_ hleaf].
    exfalso. generalize dependent l; induction i; destruct l; try easy; intros.
    inversion h. subst e. inversion hleaf.
    simpl in h. inversion hleaf. apply (IHi l); easy.
  - apply (sub_child _ n'). constructor.
    generalize dependent i. generalize dependent b0. induction l; intros.
    easy.
    destruct i. inversion h. constructor.
    constructor. simpl in h.
    inversion hint. subst l. destruct i; easy.
    refine (IHl false _ i h). rewrite H4 in H2. assumption.
Qed.

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
  generalize dependent b0.
  induction l; intros.
  - simpl in H1. destruct i; simpl in H1; inv H1.
  - destruct i.
    + simpl in H. destruct o; try contradiction. inv H.
      simpl in H1. inv H1. exists k. exists n0. auto. simpl in H1.
      exists k. exists n0. inv H1. auto.
    + simpl in H1. apply (IHl false) in H1. auto. simpl in H. simpl.
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

Lemma subchild_depth X (n ptr0: node X) le isLeaf First Last (x: X)
      (h: subchild n le):
  (node_depth n < node_depth (btnode X (Some ptr0) le isLeaf First Last x))%nat.
Proof.
  induction le; inversion h; simpl.
  + apply index.lt_max_split_l. destruct (listentry_depth). omega.
    apply lt_le_trans with (m := S (node_depth n)). omega.
    apply le_n_S, index.le_max_split_l. omega.
  + rewrite <- index.max_nat_assoc.
    apply index.lt_max_split_r.
    simpl in IHle.
    apply IHle. assumption.
Qed.

Lemma subnode_depth X: forall (n n': node X) (h: subnode n' n),
  (node_depth n' <= node_depth n)%nat.
Proof.
  apply (Fix (well_founded_ltof _ node_depth) (fun n => forall n', subnode n' n -> (node_depth n' <= node_depth n)%nat)).
  intros n hind n' h.
  inversion h.
  + omega.
  + transitivity (node_depth m).
  apply hind. unfold ltof. subst n. simpl.
  apply index.lt_max_split_r. omega. assumption.
  simpl. apply index.le_max_split_r. omega.
  + transitivity (node_depth m).
    apply hind. unfold ltof. subst n. apply subchild_depth. assumption.
    assumption. apply Nat.lt_le_incl, subchild_depth. assumption.
Qed.

Lemma subnode_equal_depth X (n root: node X) (hsub: subnode n root) (hdepth: node_depth n = node_depth root):
  n = root.
Proof.
  inversion hsub.
  - reflexivity.
  - apply subnode_depth in H.
    subst. simpl in hdepth.
    assert (h := index.le_r (listentry_depth le) (S (node_depth m))).
    rewrite <- hdepth in h. omega.
  - apply (subchild_depth X _ ptr0 le false First Last x) in H0.
    rewrite H2 in H0. apply subnode_depth in H. omega.
Qed.

Lemma partial_length': forall (X:Type) (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> (length c <= node_depth root - node_depth n)%nat.
Proof.
  intros X c root n h.
  generalize dependent n.
  induction c.
  + intros n h.
    simpl in h. subst. simpl. omega.
  + intros n h. simpl. destruct a as [n' i]. simpl in h.
    specialize (IHc n' (proj1 h)).
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ _ (proj1 h))).
    pose proof (nth_node_decrease _ _ _ _ (proj2 h)). 
    omega.
Qed.

Lemma integrity_depth X (ptr0: node X) le F L x:
  let n := btnode X (Some ptr0) le false F L x in
  node_integrity n ->
  node_depth n = S (node_depth ptr0).
Proof.
  simpl.
  intro h.
  generalize dependent F.
  induction le; intros F h; inversion h.
  + subst. simpl. now rewrite max_refl.
  + replace n0 with n. rewrite <- H4 in IHle. specialize (IHle false H2).
    unfold listentry_depth; fold (@listentry_depth X) (@node_depth X).
    rewrite <- max_nat_assoc. rewrite IHle. now rewrite max_refl.
    unfold n, n0. now subst.
Qed.

Lemma node_depth_succ X (n n': node X) i (nint: node_integrity n) (n'int: node_integrity n') (h: nth_node i n' = Some n):
  node_depth n' = S (node_depth n).
Proof.
  pose proof (nth_subnode _ _ _ _ h) as nn'sub.
  pose proof (nth_node_decrease _ _ _ _ h) as nn'depth.
  (* n' is an internal node. *) 
  destruct n' as [[ptr0|] le [] F L x]; try easy.
  rewrite integrity_depth. f_equal.
  simpl in h.
  destruct i as [|i]. now inversion h.
  simpl in n'int.
  { clear -n'int h.
    generalize dependent le. revert F.
    induction i; destruct le; try easy; intros.
    inv n'int; now inv h.
    simpl in h. apply (IHi false le).
    inv n'int. now destruct i. assumption. assumption. }
  assumption.
Qed.

Lemma partial_length'': forall (X:Type) (c:cursor X) (root:node X) (n:node X),
    root_integrity root ->
    partial_cursor_correct c n root -> (length c = node_depth root - node_depth n)%nat.
Proof.
  intros X c root n rint h.
  generalize dependent c. revert n.
  apply (Fix (well_founded_ltof (node X) (fun n => (node_depth root - node_depth n)%nat))
       (fun n => 
       forall c,
         partial_cursor_correct c n root -> Datatypes.length c = (node_depth root - node_depth n)%nat)).
  unfold ltof.
  intros n hind c hc.
  destruct c as [|[n' i'] c].
  - simpl in hc |-*. subst. omega.
  - pose proof (partial_cursor_subnode' _ _ _ _ hc) as hsub.
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ _ hc)).
    pose proof (nth_node_decrease _ _ _ _ (proj2 hc)).
    pose proof (subnode_depth _ _ _ (partial_cursor_subnode' _ _ _ _ (proj1 hc))).
    unshelve epose proof (hind n' _ c (proj1 hc)).
    omega.
    simpl. replace (node_depth n) with (node_depth n' - 1)%nat.
    omega. simpl in hc.
    rewrite (node_depth_succ _ n n' i').
    + omega.
    + now apply rint.
    + pose proof (partial_cursor_subnode' _ _ _ _ (proj1 hc)). now apply rint.
    + easy.
Qed.

Lemma partial_length: forall (X:Type) (c:cursor X) (root:node X) (n:node X),
    partial_cursor_correct c n root -> (length c <= node_depth root)%nat.
Proof.
  intros X c root n h.
  pose proof (partial_length' _ _ _ _ h).
  omega.
Qed.

Lemma partial_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    partial_cursor_correct_rel c r -> (0 <= length c <= get_depth r)%nat.
Proof.
  intros. unfold partial_cursor_correct_rel in H.
  destruct c as [|[n i] c']. simpl. omega.
  destruct (nth_node i n); try contradiction.
  apply partial_length in H. unfold get_depth. split. omega. auto.
Qed.

Lemma leaf_depth X (n: node X) (hintegrity: node_integrity n) (hleaf: LeafNode n): node_depth n = 0%nat.
Proof.
  destruct n as [[ptr0|] le [] F L x]; try easy.
  now simpl in hintegrity.
  simpl.
  replace (listentry_depth le) with 0%nat. easy.
  induction le. easy.
  simpl in hintegrity |-*. destruct hintegrity as [_ hintegrity].
  inversion hintegrity. simpl.
  now apply IHle.
Qed.

Lemma nth_entry_keyval_leaf X i (n: node X) k v x:
  node_integrity n -> nth_entry i n = Some (keyval X k v x) -> LeafNode n.
Proof.
  intros hint hentry.
  destruct n as [[ptr0|] le [] F L x']; try easy.
  exfalso. simpl in hint.
  generalize dependent le. revert F. induction i; destruct le; try easy.
  intro h. now inversion h.
  intros h hentry.
  simpl in hentry. inv h. now destruct i. rewrite H4 in H2.
  now apply (IHi false le). 
Qed.

Lemma complete_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    root_integrity (get_root r) -> complete_cursor_correct_rel c r -> length c = S (get_depth r).
Proof.
  intros X c [rootnode prel] hint h.
  pose proof (hint _ (complete_cursor_subnode _ _ _ h)).
  unfold complete_cursor_correct_rel in h.
  destruct (getCEntry c); try contradiction.
  destruct e; try contradiction.
  destruct c as [|[n [|i]] c]; try easy.
  simpl in H, h |-*. f_equal.
  rewrite (partial_length'' _ c rootnode n); try easy.
  rewrite (leaf_depth _ n). unfold get_depth. simpl. omega. assumption.
  apply (nth_entry_keyval_leaf _ _ _ _ _ _ H (proj2 h)).
Qed.    

Lemma lastpointer_rel_length: forall (X:Type) (c:cursor X) (r:relation X),
    root_integrity (get_root r) -> lastpointer_cursor_correct_rel c r -> length c = S (get_depth r).
Proof.
  intros X c [rootnode prel] hint h.
  unfold lastpointer_cursor_correct_rel in h.
  destruct c as [|[n [|ii]] c]; try contradiction.
  destruct h as [partial [leaf _]].
  pose proof (partial_length'' _ _ _ _ hint partial) as length.
  simpl. rewrite length. unfold get_depth.
  replace (node_depth n) with 0%nat. omega.
  symmetry. apply leaf_depth.
  apply hint. apply (partial_cursor_subnode' _ c).
  assumption. assumption.
Qed.    


Definition complete_cursor (c:cursor val) (r:relation val) : Prop :=
  complete_cursor_correct_rel c r /\ root_integrity (get_root r).
Definition partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor_correct_rel c r /\ root_integrity (get_root r).
(* non-empty partial cursor: the level 0 has to be set *)
Definition ne_partial_cursor (c:cursor val) (r:relation val) : Prop :=
  partial_cursor c r /\ c <> [].
Definition lastpointer_cursor (c: cursor val) (r: relation val) : Prop :=
  lastpointer_cursor_correct_rel c r /\ root_integrity (get_root r).

Definition correct_depth (r:relation val) : Prop :=
  (get_depth r < MaxTreeDepth)%nat.

Lemma partial_complete_length: forall (c:cursor val) (r:relation val),
    ne_partial_cursor c r \/ complete_cursor c r \/ lastpointer_cursor c r ->
    correct_depth r ->
    (0 <= Zlength c - 1 < 20).
Proof.
  intros. destruct H as [H | [H | H]].
  - unfold ne_partial_cursor in H. destruct H.
    split. destruct c. contradiction. rewrite Zlength_cons.
    rewrite Zsuccminusone. apply Zlength_nonneg.
    unfold correct_depth in H0.
    assert (length c < 20)%nat. rewrite MTD_eq in H0.
    destruct H as [hpartial hint].
    apply partial_rel_length in hpartial. omega.
    rewrite Zlength_correct. omega.
  - destruct H. rewrite Zlength_correct. apply complete_rel_length in H.
    rewrite H.
    split; rewrite Nat2Z.inj_succ; rewrite Zsuccminusone. omega.
    unfold correct_depth in H0. rep_omega. auto.
  - destruct H as [hlastp hint].
    destruct c as [|[n [|ii]] c]; try contradiction.
    rewrite Zlength_cons, Zsuccminusone.
    simpl in hlastp. split. apply Zlength_nonneg.
    eapply (Z.le_lt_trans _ (Z.of_nat (get_depth r))).
    unfold get_depth. rewrite Zlength_correct. 
    apply Nat2Z.inj_le, (partial_length _ _ (get_root r) n). easy.
    unfold correct_depth in H0. rewrite MTD_eq in H0. omega.
Qed.

Lemma partial_complete_length': forall (c:cursor val) (r:relation val),
    complete_cursor c r \/ partial_cursor c r ->
    correct_depth r ->
    (0 <= Zlength c <= 20).
Proof.
  intros. destruct H.
  - unfold complete_cursor in H. destruct H. rewrite Zlength_correct. apply complete_rel_length in H.
    rewrite H.
    split; rewrite Nat2Z.inj_succ. omega.
    unfold correct_depth in H0. rep_omega. auto.
  - unfold partial_cursor in H. destruct H.
    split. destruct c. apply Zlength_nonneg. rewrite Zlength_cons. rep_omega.
    unfold correct_depth in H0.
    assert (length c < 20)%nat. rewrite MTD_eq in H0. apply partial_rel_length in H. omega.
    rewrite Zlength_correct. omega.
Qed.

Lemma complete_leaf: forall n i c r,
    complete_cursor ((n,i)::c) r ->
    LeafNode n.
Proof.
  intros n i c r hcomplete.
  destruct r as [rootnode prel], hcomplete as [hcomplete hintegrity].
  unshelve eassert (nintegrity := hintegrity n _). 
  replace n with (currNode ((n, i) :: c) (rootnode, prel)) by reflexivity. now apply complete_cursor_subnode.
  unfold complete_cursor_correct_rel in hcomplete.
  case_eq (getCEntry ((n, i) :: c)).
  + intros e he. rewrite he in hcomplete.
    destruct e; try contradiction.
    destruct i as [|i]; try contradiction.
    simpl in hcomplete.
    destruct n as [[ptr0|] le [] First Last x]; try easy. exfalso.
    simpl in nintegrity, he.
    apply (intern_no_keyval _ _ _ _ _ _ _ _ _ nintegrity he).
  + intro hnone.
    now rewrite hnone in hcomplete.
Qed.

(* All complete cursors are valid. *)
Lemma complete_valid (r: relation val) (c: cursor val)
  (hcomplete: complete_cursor c r): isValid c r = true.
Proof.
  destruct r as [rootnode prel], c as [|[[ptr0 le [] First [] x] [|i]] c]; try easy;
    unfold isValid; simpl.
  + now compute in hcomplete.
  + replace (i =? numKeys_le le)%nat with false. reflexivity.
    symmetry. rewrite Nat.eqb_neq.
    pose proof (complete_correct_rel_index _ _ _ _ _ (proj1 hcomplete)) as h.
    simpl in h. rewrite <- Nat2Z.inj_lt in h. omega.
  + pose proof (complete_leaf _ _ _ _ hcomplete). easy.
Qed.
  
Lemma complete_partial_leaf: forall n i c r,
    complete_cursor ((n,i)::c) r \/
    partial_cursor ((n,i)::c) r ->
    LeafNode n ->
    complete_cursor ((n,i)::c) r.
Proof.
  intros n i c r h hleaf.
  destruct h as [h | h]. assumption. exfalso.
  unfold partial_cursor, partial_cursor_correct_rel in h.
  case_eq (nth_node i n).
  - now destruct n as [[ptr0|] le [] F L x].
  - intro hnone. now rewrite hnone in h.
Qed.
