Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Signatures.
Require btrees.btrees.
Require btrees.btrees_sep. Require btrees.btrees_spec.
Require FiniteSet FlatData SortedTuples SortedAttributes Values Plans.
Require SeqScan.
Require db_operations.

Section Tuple.
  Import Values SortedAttributes FiniteSet FlatData Plans.
  Fixpoint string_to_list_byte (s: string) : list byte :=
    match s with
    | EmptyString => nil
    | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
    end.

  Definition stringpool : Type := (* This is only temporary. *)
    { v | (type_of_value v) = type_string } -> val.

  Program Definition val_of_value (sp : stringpool) (v : value) : val :=
    match v with
    | Value_string s => sp (exist _ v _)
    | Value_ptrofs x => Vint (Ptrofs.to_int x) end.

  (* This need to be implemented. *)
  Definition stringpool_rep (sp : stringpool) : mpred := emp.

  Definition tuple := Tuple.tuple TPL.T.
  Definition support : tuple -> setA := Tuple.support TPL.T.
  Definition attribute := Tuple.attribute TPL.T.
  Definition dot : tuple -> attribute -> value := Tuple.dot TPL.T. Check dot.
  Definition Otuple : OrderedSet.Oeset.Rcd tuple := Tuple.OTuple TPL.T.
  Global Opaque tuple support attribute dot Otuple.

  Definition tuple_rep (sh : share) (t : tuple) (p : val) : mpred :=
    EX sp : stringpool,
            data_at sh (tarray size_t (Z.of_nat (Fset.cardinal FAN (support t))))
                    (map (val_of_value sp oo dot t) ({{{support t}}})) p * stringpool_rep sp.
End Tuple. 

Section CompSpecs.
  
  Definition db_operations_CompSpecs : compspecs. make_compspecs db_operations.prog. Defined.
  Definition db_operations_Vprog : varspecs. mk_varspecs db_operations.prog. Defined.

  Definition relation_mem_CompSpecs : compspecs. make_compspecs relation_mem.prog. Defined.
  Definition relation_mem_Vprog : varspecs. mk_varspecs relation_mem.prog. Defined.
  
End CompSpecs.

Section AttrList.
  Import db_operations SortedAttributes FiniteSet.

  Existing Instance db_operations_CompSpecs.
  
  Definition t_attr_list_t := Tstruct _attribute_list_t noattr.
  
  Definition id_of_attribute (a : attribute) : list byte :=
    match a with
    | Attr_string _ s => string_to_list_byte s
    | Attr_ptrofs _ s => string_to_list_byte s end.

  Definition domain_of_attribute (a : attribute) : val :=
    match a with
    | Attr_ptrofs _ _ => Vint (Int.repr 0)
    | Attr_string _ _ => Vint (Int.repr 1) end.

  Definition attribute_string_rep sh (a : attribute) (p : val) : mpred :=
    match a with
    | Attr_ptrofs _ _ => emp
    | Attr_string _ s => cstring sh (string_to_list_byte s) p end.

  Fixpoint attribute_lseg_rep (sh : share) (l : list attribute) (p q : val) : mpred :=
    match l with
    | [] => !! (p = q /\ is_pointer_or_null p) && emp
    | a :: tl =>
      EX r : val, EX sptr : val, data_at sh t_attr_list_t (sptr, (domain_of_attribute a, r)) p * attribute_lseg_rep sh tl r q * attribute_string_rep sh a sptr end.

  Lemma attribute_lseg_nil sh l : attribute_lseg_rep sh l nullval nullval |-- !! (l = []).
  Proof.
    destruct l; simpl; entailer.
    saturate_local. apply field_compatible_nullval with (P := False) in H.
    contradiction.
  Qed.
  
  Definition attribute_list_rep sh l p := attribute_lseg_rep sh l p nullval.

  Lemma attribute_lseg_rep_local_facts:
    forall sh l p q,
      attribute_lseg_rep sh l p q |--
                         !! (is_pointer_or_null p /\ is_pointer_or_null q).
  Proof.
    induction l; intros; unfold attribute_lseg_rep; entailer.
    fold attribute_lseg_rep. sep_apply IHl. entailer.
  Qed.

  Hint Resolve attribute_lseg_rep_local_facts : saturate_local.

  Lemma attribute_list_rep_local_facts:
    forall sh l p,
      attribute_list_rep sh l p |--
                         !! (is_pointer_or_null p /\ (p=nullval <-> l=nil)).
  Proof.
    unfold attribute_list_rep, attribute_lseg_rep. induction l; intros; entailer.
    entailer!. easy.
    fold attribute_lseg_rep in IHl |- *.
    sep_apply (IHl r). entailer!. apply field_compatible_nullval1 in H0.
    easy.
  Qed.

  Hint Resolve attribute_list_rep_local_facts : saturate_local.

  Lemma attribute_list_rep_valid_pointer:
    forall sh l p, readable_share sh ->
                   attribute_list_rep sh l p |-- valid_pointer p.
  Proof.
    intros.
    unfold attribute_list_rep; destruct l; simpl. entailer.
    Intros r sptr. sep_apply data_at_valid_ptr.
    apply readable_nonidentity. assumption.
    entailer.
  Qed.

  Hint Resolve attribute_list_rep_valid_pointer : valid_pointer.

  Definition attributes_rep (sh : share) (attrs : Fset.set FAN) (p : val) : mpred :=
    attribute_list_rep sh ({{{attrs}}}) p.

  Definition attribute_list_length_spec :=
    DECLARE _attribute_list_length
            WITH sh: share, l: val, attrs: Fset.set FAN
                                                    PRE [ _l OF (tptr t_attr_list_t)]
                                                    PROP(readable_share sh)
                                                    LOCAL (temp _l l; temp _x l)
                                                    SEP (attributes_rep sh attrs l)
                                                    POST [ size_t ]
                                                    PROP()
                                                    LOCAL(temp ret_temp (Vint (Int.repr (Z.of_nat (Fset.cardinal _ attrs)))))
                                                    SEP (attributes_rep sh attrs l).


End AttrList.

Section Iterator.
  Import db_operations FlatData Plans Signatures.
  
  Existing Instance db_operations_CompSpecs.
  
  Definition t_iterator_t := Tstruct _iterator_t noattr.
  Definition t_methods := Tstruct _methods noattr.
  Definition t_seq_scan_env := Tstruct _seq_scan_env noattr.
  Definition t_index_join_env := Tstruct _index_join_env noattr.

  Record iterator_class (c: Cursor.Rcd Otuple) :=
    {
      env: Type;
      env_assert: env -> Cursor.cursor c -> val -> mpred;
      env_init: env -> env;
      env_next: env -> env;
      (* +axioms *)
      env_close: env -> env;
    }.
  Arguments env {c}.
  Arguments env_assert {c}.
  Arguments env_init {c}.
  Arguments env_next {c}.
  Arguments env_close {c}.

  Definition result_rep sh (r : result tuple) (p: val) : mpred :=
    match r with
    | Result t => tuple_rep sh t p
    | No_Result => emp (* ??? *)
    | Empty_Cursor => !! (p = nullval) end.

  Definition next_spec {c: Cursor.Rcd Otuple} (cl : iterator_class c) :=
    WITH p: val, e: env cl, it: Cursor.cursor c, sh: share, gv: globals
  PRE [ _env OF (tptr tvoid) ]
  PROP(Cursor.coherent it)
  LOCAL(gvars gv; temp _env p)
  SEP(mem_mgr gv; env_assert cl e it p)
  POST [ tptr tvoid ]
  EX t: val,
  PROP()
  LOCAL(temp ret_temp t)
  SEP(mem_mgr gv; result_rep sh (fst (Cursor.next it)) t; cl.(env_assert) (cl.(env_next) e) (snd (Cursor.next it)) p).
  
  Import btrees_sep btrees.

  Lemma node_dec_eq {X:Type} {h: EqDec X}: forall n1 n2: node X,
      {n1 = n2} + {n1 <> n2}.
  Proof.
    fix hrec 1.
    intros. decide equality. 
    apply bool_dec. apply bool_dec. apply bool_dec.
    decide equality. decide equality.
    apply Int.eq_dec. apply Int.eq_dec.
    apply Int.eq_dec. decide equality.
  Qed.
  
  Lemma subchild_nth {X}: forall (n: node X) le, subchild n le -> exists i, nth_node_le i le = Some n.
  Proof.
    induction le.
    easy.
    intro h. inversion h. exists 0%nat. easy.
    specialize (IHle H1). destruct IHle.
    exists (S x)%nat.
    easy.
  Qed.
  Open Scope nat_scope.
  Lemma index_le_split_l': forall m n p, n <= m -> n <= index.max_nat m p.
  Proof.
    induction m; intros n p h. omega.
    simpl. destruct p. assumption.
    transitivity (S m). assumption.
    apply le_n_S. apply IHm.
    omega.
  Qed.

  Lemma index_le_r: forall n m, m <= index.max_nat n m.
  Proof.
    induction n.
    simpl. easy.
    destruct m.
    omega.
    simpl. apply le_n_S. apply IHn.
  Qed.
    
  
  Inductive subnode' {X : Type} : node X -> node X -> Prop :=
    sub_refl' : forall n : node X, subnode' n n
  | sub_ptr0' : forall (n m : node X) (le : listentry X) (First Last : bool) (x : X),
               subnode' n m -> subnode' n (btnode X (Some m) le false First Last x)
  | sub_child' : forall (n m : node X) (le : listentry X) (ptr0 : option (node X)) (First Last : bool) (x : X),
      subnode' n m -> subchild m le -> subnode' n (btnode X ptr0 le false First Last x).

  Definition nodeDepthOrder X (n1 n2: node X) : Prop:= (node_depth n1 < node_depth n2)%nat.
  
  Lemma nodeDepthOrder_wf' {X} : forall depth, forall n, (node_depth n <= depth)%nat -> Acc (nodeDepthOrder X) n.
  Proof.
    unfold nodeDepthOrder.
    induction depth; intros.
    inversion H.
    constructor. intros. omega.
    constructor. intros.
    inversion H.
    + constructor. intros. apply IHdepth. omega.
    + apply IHdepth. omega.
  Defined.

  Theorem nodeDepthOrder_wf (X: Type) : well_founded (nodeDepthOrder X).
    red; intro; eapply nodeDepthOrder_wf'; eauto.
  Defined.
  
  Program Definition sub_trans' {X: Type}: forall n m p: node X,
      subnode' n m -> subnode' m p -> subnode' n p := fun n m =>
    Fix (nodeDepthOrder_wf X) (fun p => subnode' n m -> subnode' m p -> subnode' n p) _.
  Next Obligation.
    inversion H1.
    rewrite H3 in H0. assumption.
    apply sub_ptr0'.
    refine (H m0 _ _ _).
    unfold nodeDepthOrder.
    rewrite <- H4. simpl.
    apply index.le_max_split_r. omega.
    assumption.
    assumption.
    apply (sub_child' _ m0). apply H.
    unfold nodeDepthOrder.
    rewrite <- H5. apply subchild_nth in H3. destruct H3.
    simpl.
    apply (Nat.lt_le_trans _ (listentry_depth le)).
    apply (nth_node_le_decrease _ le _ x1 H3).
    apply index_le_split_l'. omega.
    assumption.
    assumption.
    assumption.
 Defined.
  
  Lemma subnode_cons {X: Type} {heqdec: EqDec X} {n0} {ptr0} {k k'} {n n'} {le} {First Last} {x}
        (h: subnode' n0 (btnode X (Some ptr0) (cons X (keychild X k' n') le) false First Last x)):
 n0 <> (btnode X (Some ptr0) (cons X (keychild X k' n') le) false First Last x) ->
 subnode' n0 (btnode X (Some ptr0) (cons X (keychild X k n) (cons X (keychild X k' n') le)) false First Last x).
  Proof.
    revert n0 h. fix hrec 1.
    intros n0 hsubn0 hneq.
    inversion hsubn0.
    + easy.
    + constructor. assumption.
    + apply (sub_child' _ m). assumption.
      apply sc_cons. assumption.
  Qed.
  
  Lemma root_integrity_cons {X} {ptr0} {k k'} {n n'} {le} {First Last} {x}
   (hint: root_integrity (btnode X (Some ptr0) (cons X (keychild X k n) (cons X (keychild X k' n') le)) false First Last x)):
    root_integrity (btnode X (Some ptr0) (cons X (keychild X k' n') le) false First Last x).
  Proof.
    unfold root_integrity in hint |- *.
    fix hrec 1.
    intros n0 hn0.
    inversion hn0.
    ++ unfold node_integrity.
       specialize (hint (btnode X (Some ptr0) (cons X (keychild X k n) (cons X (keychild X k' n') le)) false First Last x) (sub_refl _)).
       inversion hint. assumption.
    ++ apply hint.
       constructor.
    ++ apply hint.
       apply sub_child.
       apply sc_cons. assumption.
    ++ apply hint.
      admit. 
Admitted.

Definition btnode_induction {X} (P: node X -> Prop)
           (hleaf: forall n, LeafNode n -> P n)
           (hintern: forall (children: list (key * node X)) (h : children <> []) n First Last x,
               Forall (P oo snd) children -> P n ->
               P (btnode X (Some n)
                         (fold_right (fun (kn : key * node X) le => let (k, n) := kn in cons X (keychild X k n) le) (nil X) children) false First Last x)) : forall n, root_integrity n -> P n.
Proof.
  fix hrec 1.
  intros n rint. unfold root_integrity in rint.
  destruct n as [[n0 |] le [] ].
  + specialize (rint (btnode _ (Some n0) le true b b0 x) (sub_refl _)).
    simpl in rint. easy.
  + pose (children := listentry_rect X (fun _ => list (key * node X)) []
                                     (fun e l acc => match e with
                                                     | keychild k n' => (k, n') :: acc
                                                     | _ => [] (* doesn't happen *) end) le).
    simpl in children.
    assert (le_not_nil: le <> nil X).
    { intro. subst le. specialize (rint (btnode X (Some n0) (nil X) false b b0 x) (sub_refl _)).
      easy. }
    assert (children_not_nil: children <> []).
    { destruct le. easy. simpl in children.
      destruct e. specialize (rint (btnode X (Some n0) (cons X (keyval X k v x0) le) false b b0 x) (sub_refl _)). simpl in rint. inversion rint.
      easy. }
    replace le with (fold_right
                       (fun (kn : key * node X) (le : listentry X) => let (k, n) := kn in cons X (keychild X k n) le)
                       (nil X) children).
  - apply (hintern children children_not_nil n0 b b0 x). clear le_not_nil children_not_nil.
    rewrite Forall_forall. intros [childk childnode] hkn. simpl.
    apply hrec. 
    unfold root_integrity. intros subn hsubn.
    apply rint.
    apply sub_trans with (n1 := childnode). assumption.
    apply sub_child.
    apply In_nth with (d := (childk, childnode)) in hkn.
    destruct hkn as [i [hi hnth]].
    apply nth_subchild with (i := i).
    subst children.
    clear rint.
    revert le hi hnth.
    induction i ; destruct le.
    ++ easy.
    ++ destruct e. easy.
       intros _ hnth. simpl in hnth. inversion hnth. easy.
    ++ easy.
    ++ simpl. destruct e. easy.
       intros. simpl in *. apply IHi.
       omega. easy.
    ++ apply hrec. unfold root_integrity.
       intros n hsn. apply rint.
       apply sub_trans with (n2 := n0). assumption.
       constructor.
  - subst children. clear children_not_nil. destruct le.
    easy. clear le_not_nil. simpl.
    destruct e. specialize (rint _ (sub_refl _)). inversion rint.
    revert k n rint.
    induction le; simpl.
    reflexivity.
    intros k n rint.
    destruct e. specialize (rint _ (sub_refl _)). inversion rint. inversion H0.
    simpl in IHle. simpl. f_equal.
    apply IHle.
    intros n2 hn2.
    inversion hn2.
    ++ unfold node_integrity.
       specialize (rint (btnode X (Some n0) (cons X (keychild X k n) (cons X (keychild X k0 n1) le)) false b b0 x) (sub_refl _)).
       inversion rint. assumption.
    ++ apply rint.
       constructor.
    ++ apply rint.
       apply sub_child.
       apply sc_cons. assumption.
    ++ (* hn2 is obtained by transitivity. *)
      
      admit. 
    + apply hleaf. easy.
    + specialize (rint (btnode X None le false b b0 x) (sub_refl _)).
      easy.
Defined.

    
    intros n1 hn1.
    inversion hn1.
    simpl. specialize (rint (btnode X (Some n0) (cons X (keychild X k n) le) false b b0 x) (sub_refl _)) as rint1.
    simpl in rint1. inversion rint1. 

        
      assert (hlenil : le <> nil X).
      { intro hfalse. subst le. simpl in children. subst children. easy. }
      
      induction le.
      ++ easy. 
      ++ destruct e.
         
         pose proof (rint (btnode X (Some n0) (cons X (keyval X k0 v x0) le) false b b0 x) (sub_refl _)).
         simpl in H0.
         inversion H0.
         Print sc_eq.
         apply sc_eq.
         simpl in hkn. destruct hkn.
         
         apply rint.
      Print intern_le.
      induction le. easy.
      simpl in nint. inversion nint.
      subst le. inversion H.
      subst e. unfold In in hkn.
      subst children. simpl in hkn.
      


  Lemma cursor_iter_next_abs_node {X} (r: relation X):
    (get_numrec r > O)%nat ->
    root_integrity (get_root r) ->
    let c := moveToFirst (get_root r) [] 0 in
    let l := abs_node (get_root r) in
    forall n: nat,
      getCKey (Nat.iter n (fun c' => RL_MoveToNext c' r) c) = option_map fst (nth_error l n).
  Proof.
    destruct r as [root proot]. case_eq root. intros o le isLeaf First Last x hroot. simpl.
    intros hnempty rint.
    assert (H : (exists n, o = Some n) \/ le <> nil X).
    {
      destruct o.
      { left. exists n. reflexivity. }
      { right. intro. subst le. unfold get_numrec in hnempty. simpl in hnempty. omega. }
    }
    induction n; simpl; intros; destruct isLeaf.
    + assert (o = None /\ leaf_le le).
      { unfold root_integrity, node_integrity in rint. specialize rint with root.
        rewrite hroot in rint. apply rint. constructor. }
      destruct H0. subst o. destruct H as [[] | ]. discriminate.
      destruct le. contradiction.
      simpl. inversion H1. subst e. simpl.
      reflexivity.
    + unfold root_integrity, node_integrity in rint. 
      specialize (rint root). rewrite hroot in rint. specialize (rint (sub_refl _)).
      destruct o; [ | easy].
      inversion rint; subst le; clear H.
    - simpl. Print moveToFirst.


      
      case_eq le; intro hle. simpl. rewrite hle in H.
      unfold get_numrec, node_numrec in H. simpl in H. destruct o; try easy.
      

    
  (* This predicate states that the btree and cursor physically represent
     the abstract sequential scan iterator. *) (*
  Definition seqscan_env_assert (bt: relation val) (c: cursor val)
             (it: Cursor.cursor (SeqScan.SeqScan.build Otuple)) : mpred :=
    (* The root node of the btree and its address. *)
    let (root, pbt) := bt in
    let l : list (tuple * val) :=
        List.combine (Cursor.collection it) (List.map Vint (snd (List.split (abs_node relnode)))) in
*)
  Definition seqscan_iterator : iterator_class (SeqScan.SeqScan.build Otuple) :=
    {|
      env := btrees.relation val * btrees.cursor val;
      env_assert := fun e it p =>
                   let (rel, cur) := e in
                   let (relnode, qrel) := rel in
                   let l : list (tuple * val) :=
                       List.combine (Cursor.collection it) (List.map Vint (snd (List.split (abs_node relnode)))) in
                   EX qcur: val,
                            !! (Forall (fun x: tuple * val => option_map Vint (getCRecord cur) = Some (snd x) ->
                                                 fst (Cursor.next it) = Result (fst x)) l /\
                            complete_cursor (snd e) (relnode, qrel) /\
                                correct_depth (relnode, qrel) /\ root_wf (get_root (relnode, qrel)) /\
                                root_wf relnode) &&
                               iter_sepcon (fun x : tuple * val => let (t, p) := x in tuple_rep Tsh t p) l *
                                        data_at Tsh t_seq_scan_env (qrel, qcur) p *
                                        relation_rep (fst e) (btrees.get_numrec (fst e)) *
                                        cursor_rep (snd e) (fst e) qcur;
      env_init := fun e => (fst e, btrees.moveToFirst (fst (fst e)) (snd e) 0);
      env_next := fun e => (fst e, btrees.moveToNext (snd e) (fst e));
                             env_close := fun e => e; (* FreeRecord? *)
       (* +axioms *)
    |}.
  
  Definition seqscan_next_spec := (DECLARE _seq_scan_next (next_spec seqscan_iterator)).
End Iterator.


(* MATERIALIZE: WORK IN PROGRESS
Definition materialize_spec :=
  DECLARE _materialize
    WITH sh: share, a: val, it: val, c: cursor
    PRE [ _it OF (tptr t_iterator_t) ]
    PROP()
    LOCAL(temp _it it; temp _a a)
    SEP(iterator_rep sh c it)
    POST [  *)


Section Verif.
  Import db_operations btrees_spec FiniteSet SortedAttributes.
  Existing Instance db_operations_CompSpecs.
  Let Gprog := ltac:(with_library prog [attribute_list_length_spec; RL_IsEmpty_spec; RL_CursorIsValid_spec]).
  Hint Resolve attribute_list_rep_local_facts : saturate_local.
  Hint Resolve attribute_lseg_rep_local_facts : saturate_local.
  Hint Resolve attribute_list_rep_valid_pointer : valid_pointer.
 (*
  Lemma body_attribute_list_length: semax_body db_operations_Vprog Gprog f_attribute_list_length attribute_list_length_spec.
  Proof.
    start_function.
    forward. forward.
    forward_loop
      (EX x : val, EX l1 : list attribute, EX l2 : list attribute,
                                                   PROP ( {{{attrs}}} = l1 ++ l2 )
                                                        LOCAL (temp _n (Vint (Int.repr (Zlength l1))); temp _x x; temp _l l)
                                                        SEP (attribute_lseg_rep sh l1 l x; attribute_list_rep sh l2 x ))%assert.
    - Exists l (@nil attribute) (Fset.elements _ attrs).
      entailer!. unfold attributes_rep, attribute_list_rep. simpl. entailer!.
    - entailer!.
    - destruct l2. unfold attribute_list_rep, attribute_lseg_rep at 2. 
      Intros. rewrite H0 in HRE. contradiction.
      unfold attribute_list_rep; unfold attribute_lseg_rep at 2; fold attribute_lseg_rep. 
      Intros r sptr.
      forward.
      forward.
      Exists (r, l1 ++ [a], l2). entailer!.
      split. rewrite semax_lemmas.cons_app in H. rewrite app_assoc in H. auto.
      rewrite Zlength_app. rewrite Zlength_cons. simpl. reflexivity.
      unfold attribute_list_rep. cancel.
      revert l PNl. generalize l1. induction l0; intros. rewrite app_nil_l. simpl. Exists r sptr. entailer.
      simpl. Intros r0 sptr0. Exists r0 sptr0. entailer!.
      apply IHl0. auto.
    - forward. assert (h : l2 = []). rewrite <- H0; easy.
      subst l2. rewrite app_nil_r in H. subst l1.
      rewrite Fset.cardinal_spec. rewrite Zlength_correct; auto. entailer!.
      unfold attributes_rep, attribute_list_rep. sep_apply attribute_lseg_nil. simpl. entailer!.
  Qed.
  *)
  Import btrees btrees_sep Signatures.Cursor.
  Lemma body_seqscan_next: semax_body db_operations_Vprog Gprog f_seq_scan_next seqscan_next_spec.
  Proof.
    unfold seqscan_next_spec, next_spec.
    start_function.
    unfold seqscan_iterator, env_assert.
    destruct e as [rel c], rel as [relnode qrel].
    Intros qcur.
    forward.
    forward_call ((relnode, qrel), c, qcur, gv).
    entailer!.
    unfold fst.
    forward_if (PROP ( )
               LOCAL (temp _t'2 (if nat_eq_dec (numKeys relnode) 0%nat then Vint (Int.repr 1) else
                                       (Val.of_bool (negb (isValid c (relnode, qrel)))));
                temp _c qcur; gvars gv; temp _env p)
     SEP (mem_mgr gv; relation_rep (relnode, qrel) (get_numrec (relnode, qrel));
     cursor_rep c (relnode, qrel) qcur;
     iter_sepcon (fun x : tuple * val => let (t, p0) := x in tuple_rep Tsh t p0)
                 (combine (collection it) (map Vint (snd (split (abs_node relnode)))));
               data_at Tsh t_seq_scan_env (qrel, qcur) p)).
    forward. entailer!.
    destruct (nat_eq_dec (numKeys relnode) 0%nat). reflexivity.
    apply typed_true_tint_Vint in H5. contradiction.
    forward_call ((relnode, qrel), c, qcur, get_numrec (relnode, qrel)).
    forward. destruct (nat_eq_dec (numKeys relnode) 0%nat); apply typed_false_tint_Vint in H5.
    easy. entailer!. destruct btrees.isValid; easy.
    forward_if. 
    + forward. Exists (Vint (Int.repr 0)).
    unfold seqscan_iterator, env_next, env_assert, result_rep.
    entailer!. Exists qcur.
    entailer!.
    - split.
      * case_eq (next it); intros res next_c heq. unfold snd at 2 3.
        rewrite (next_collection _ _ H heq).
        rewrite Forall_forall. intros [t v] htv hc.
        unfold snd at 1 in hc. unfold fst at 2.
        Print Rcd.
        About Signatures.iter.
        apply Forall_impl with (P := fun x : tuple * val =>
          option_map Vint (getCRecord c) = Some (snd x) -> fst (next it) = Signatures.Result (fst x)).
        rewrite heq. destruct a. simpl.
        intros himpl hnextcur.
        Print moveToNext.
      * 
  Admitted.  
End Verif.
