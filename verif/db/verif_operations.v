Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Signatures.
Require FiniteSet FlatData SortedTuples SortedAttributes Values Plans.
Require SeqScan.
Require db_operations.
Require VST.progs.verif_queue2.
Require relation_mem.

Require Program.Basics. Require Program.Combinators.

Section Tuple.
  Import Values SortedAttributes FiniteSet FlatData Plans.
  Import Program.Basics Program.Combinators.
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

  Definition tuple : Type := Tuple.tuple TPL.T * val. (* Augmented type *)
  Definition support : tuple -> setA := Tuple.support TPL.T ∘ fst.
  Definition attribute := Tuple.attribute TPL.T.
  Definition dot : tuple -> attribute -> value := Tuple.dot TPL.T ∘ fst.
  Section Otuple.
    Import OrderedSet.Oeset.
    Definition Otuple' : OrderedSet.Oeset.Rcd (FlatData.Tuple.tuple TPL.T) := Tuple.OTuple TPL.T.
    Program Definition Otuple : OrderedSet.Oeset.Rcd tuple :=
      {|
        compare := fun '(t1, p1) '(t2, p2) => Otuple'.(compare) t1 t2 ;
        compare_eq_trans := fun '(t1, p1) '(t2, p2) '(t3, p3) h12 h23 => Otuple'.(compare_eq_trans) t1 t2 t3 h12 h23 ;
        compare_eq_lt_trans :=  fun '(t1, p1) '(t2, p2) '(t3, p3) h12 h23 => Otuple'.(compare_eq_lt_trans) t1 t2 t3 h12 h23 ;
        compare_lt_eq_trans :=  fun '(t1, p1) '(t2, p2) '(t3, p3) h12 h23 => Otuple'.(compare_lt_eq_trans) t1 t2 t3 h12 h23 ;
        compare_lt_trans :=  fun '(t1, p1) '(t2, p2) '(t3, p3) h12 h23 => Otuple'.(compare_lt_trans) t1 t2 t3 h12 h23 ;
        compare_lt_gt := fun '(t1, p1) '(t2, p2) => Otuple'.(compare_lt_gt) t1 t2
      |}.
  End Otuple.

  Global Opaque tuple support attribute dot Otuple.

  Definition tuple_rep (sh : share) (t : tuple) (p : val) : mpred :=
    EX sp : stringpool,
            data_at sh (tarray size_t (Z.of_nat (Fset.cardinal FAN (support t))))
                    (map (val_of_value sp oo dot t) ({{{support t}}})) p * stringpool_rep sp.
End Tuple. 

Instance CompSpecs : compspecs. make_compspecs db_operations.prog. Defined.
Definition Vprog : varspecs. mk_varspecs db_operations.prog. Defined.

Section AttrList.
  Import db_operations SortedAttributes FiniteSet.
  
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
  
  Definition t_iterator_t := Tstruct _iterator_t noattr.
  Definition t_methods := Tstruct _methods noattr.
  Definition t_seq_scan_env := Tstruct _seq_scan_env noattr.
  Definition t_index_join_env := Tstruct _index_join_env noattr.
  Definition t_fifo := Tstruct _fifo noattr.
  Import QEP.
  Definition iterator_invariant (c: cursor): Type := Cursor.cursor (type_cursor c) -> val -> mpred.
    
  Definition result_rep sh (r : result tuple) (p: val) : mpred :=
    match r with
    | Result t => tuple_rep sh t p
    | No_Result => emp (* ??? *)
    | Empty_Cursor => !! (p = nullval) end.
  
  Definition init_spec {c: cursor} (instance: iterator_invariant c) :=
    WITH sh: share, gv: globals, penv: val, c: Cursor.cursor (type_cursor c)
  PRE [ _env OF (tptr tvoid) ]
    PROP(Cursor.coherent c)
    LOCAL(gvars gv; temp _env penv)
    SEP(mem_mgr gv; instance c penv)
  POST [ tvoid ]
    PROP()
    LOCAL()
    SEP(mem_mgr gv; instance (Cursor.reset c) penv).

  Definition next_spec {c: cursor} (instance: iterator_invariant c) :=
    WITH sh: share, gv: globals, penv: val, c: Cursor.cursor (type_cursor c)
  PRE [ _env OF (tptr tvoid) ]
    PROP(Cursor.coherent c)
    LOCAL(gvars gv; temp _env penv)
    SEP(mem_mgr gv; instance c penv)
  POST [ tptr tvoid ]
  let '(res, next_c) := Cursor.next c in
  EX pres: val,
    PROP()
    LOCAL(temp ret_temp pres)
    SEP(mem_mgr gv; result_rep sh res pres; instance next_c penv).

  Definition close_spec {rcd: Cursor.Rcd Otuple} (instance: iterator_invariant rcd) :=
    WITH sh: share, gv: globals, penv: val, c: Cursor.cursor rcd
  PRE [ _env OF (tptr tvoid) ]
    PROP(Cursor.coherent c)
    LOCAL(gvars gv; temp _env penv)
    SEP(mem_mgr gv; instance c penv)
  POST [ tvoid ]
    PROP()
    LOCAL()
    SEP(mem_mgr gv). (* Something missing here. For now, the semantics of close are not well-defined. *)
  
  Definition iterator_methods {rcd: Cursor.Rcd Otuple}
             (instance: iterator_invariant rcd) (pmtable: val) : mpred :=
  EX sh: share, EX pinit: val, EX pnext: val, EX pclose: val,
  !! readable_share sh && 
  func_ptr' (init_spec instance) pinit *
  func_ptr' (next_spec instance) pnext *
  func_ptr' (close_spec instance) pclose *
  data_at sh t_methods (pinit, (pnext, pclose)) pmtable.

  Definition iterator_mpred {rcd: Cursor.Rcd Otuple} (c: Cursor.cursor rcd) (p: val) : mpred :=
  EX instance: iterator_invariant rcd, EX pmtable: val, EX penv: val, 
        data_at Ews t_iterator_t (pmtable, penv) p *
        iterator_methods instance pmtable *
        instance c penv.

  Print QEP.IndexJoin.
  Definition indexjoin_invariant (attrs: list attribute): iterator_invariant (QEP.IndexJoin attrs outer_cursor inner_index) :=
    fun 

End Iterator.

Section Materialize.
  Import db_operations FlatData Plans Signatures.
  Import verif_queue2.
  Import Cursor.
  Existing Instance CompSpecs.
  Definition abstract_cursor: Type  :=
    {
      rcd: Cursor.Rcd Otuple;
      rep: iterator_class rcd;
      concrete_env: rep.(env);
      cursor: Cursor.cursor rcd
    }.
  Set Printing Universes.
  Check val. Check abstract_cursor.
  Definition materialize_spec :=
    DECLARE _materialize
    WITH gv: globals,
             it: val, ac: abstract_cursor
    PRE [ _it OF (tptr t_iterator_t) ]
    PROP()
    LOCAL(gvars gv; temp _it it)
    SEP(mem_mgr gv; ac.(rep))
    POST [ tptr t_fifo ]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; fifo [] r).

  Definition materialize_spec :=
    DECLARE _materialize
    WITH gv: globals,
             it: val, ac: abstract_cursor
    PRE [ _it OF (tptr t_iterator_t) ]
    PROP()
    LOCAL(gvars gv; temp _it it)
    SEP(mem_mgr gv; ac.(rep).(env_assert) ac.(concrete_env) ac.(cursor) it)
    POST [ tptr t_fifo ]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; fifo (map snd (ac.(rcd).(collection))) r).

  Let Gprog := ltac:(with_library prog [materialize_spec]).
  
End Iterator.

Section Verif.
  Import db_operations FiniteSet SortedAttributes.
  Let Gprog := ltac:(with_library prog [attribute_list_length_spec]).
  Hint Resolve attribute_list_rep_local_facts : saturate_local.
  Hint Resolve attribute_lseg_rep_local_facts : saturate_local.
  Hint Resolve attribute_list_rep_valid_pointer : valid_pointer.
 
  Lemma body_attribute_list_length: semax_body Vprog Gprog f_attribute_list_length attribute_list_length_spec.
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
    - destruct l2; unfold attribute_list_rep, attribute_lseg_rep at 2. 
      Intros. subst x. contradiction.
      fold attribute_lseg_rep. 
      Intros r sptr.
      forward.
      forward.
      Exists (r, l1 ++ [a], l2). entailer!.
      split. rewrite <- app_assoc. simpl. auto.
      rewrite Zlength_app, Zlength_cons. reflexivity.
      unfold attribute_list_rep. cancel.
      revert l PNl. generalize l1. induction l0; intros. rewrite app_nil_l. simpl. Exists r sptr. entailer.
      simpl. Intros r0 sptr0. Exists r0 sptr0. entailer!.
      apply IHl0. auto.
    - forward. assert (h : l2 = []). rewrite <- H0; easy.
      subst l2. rewrite app_nil_r in H. subst l1.
      rewrite Fset.cardinal_spec. rewrite Zlength_correct; auto. entailer!.
      unfold attributes_rep, attribute_list_rep. sep_apply attribute_lseg_nil. simpl. entailer!.
  Qed.
  
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
