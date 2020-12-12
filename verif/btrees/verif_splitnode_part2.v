Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec. 
Require Import verif_splitnode_part0. 
Require Import verif_splitnode_part1. (*for Lemma splitnode_main_if_part2_proof*)

(* Could be useful in refactoring splitnode_main_if_then_proof *)
Definition splitnode_main_if_part1 : statement :=
 ltac:(let x := constr:(splitnode_main_if_then) in
         let x := eval hnf in x in
         match x with context C [Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr _) tint)) _] =>
           let y :=context C[Sskip]
            in exact y
         end).

Opaque Znth.

Lemma splitnode_main_if_then_proof:
 forall (Espec : OracleKind)
   (ptr0 : option (node val))  (le : list (entry val)) (isLeaf First Last : bool)
   (nval : val) (e : entry val) (pe : val) (gv : globals) (v_allEntries : val)
  (H : node_integrity (btnode val ptr0 le isLeaf First Last nval)),
  let n := btnode val ptr0 le isLeaf First Last nval : node val in
  forall (H0 : Zlength le = Fanout)
  (LEAFENTRY : LeafEntry e = is_true (node_isLeaf  (btnode val ptr0 le isLeaf First Last nval)))
  (k : key)(coprepr : val + val)
  (HEVR : entry_val_rep e = (Vptrofs k, coprepr))
  (INRANGE : 0 <= findRecordIndex n k <= Fanout)
  (vnewnode : val)
  (H1 : vnewnode <> nullval)
  (ent_end : list (val * (val + val)))
  (H2 : typed_true tint
       (force_val
          (both_int
             (fun n1 n2 : int => Some (Val.of_bool (Int.eq n1 n2)))
             (sem_cast_i2i I32 Signed) (sem_cast_i2i I32 Signed)
             (Val.of_bool isLeaf) (Vint (Int.repr 1))))),

semax (func_tycontext f_splitnode Vprog Gprog [])
  (PROP ( )(*
  LOCAL (temp _t'4 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
   temp _t'28 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr (findRecordIndex' le k 0)));
   temp _t'1 (Vint (Int.repr (findRecordIndex' le k 0))); temp _t'29 (Vptrofs k);
   lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries; temp _node nval;
   temp _entry pe; temp _isLeaf (Val.of_bool isLeaf))
*)
   LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode;
   temp _t'2 vnewnode; temp _t'27 (Val.of_bool Last);
   temp _tgtIdx
     (Vint (Int.repr (findRecordIndex' le k 0)));
   temp _t'1
     (Vint (Int.repr (findRecordIndex' le k 0)));
   temp _t'28 (Vptrofs k);
   lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   temp _node nval; temp _entry pe;
   temp _isLeaf (Val.of_bool isLeaf)) 

   SEP (mem_mgr gv; malloc_token Ews tbtnode nval;
   data_at Ews tbtnode
     (Val.of_bool isLeaf,
     (Val.of_bool First,
     (Vint (Int.repr 0),
     (Vint (Int.repr (Zlength (node_le (btnode val ptr0 le isLeaf First Last nval)))),
     (optionally getval nullval ptr0,
      map entry_val_rep le ++ ent_end))))) nval;
   optionally btnode_rep emp ptr0; iter_sepcon entry_rep le;
   btnode_rep (empty_node isLeaf false Last vnewnode);
   data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   entry_rep e; data_at Ews tentry ((Vptrofs k), coprepr) pe))
  splitnode_main_if_then
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX newx : val,
         PROP ( )
         LOCAL ()
         SEP (mem_mgr gv;
         btnode_rep
           (splitnode_left (btnode val ptr0 le isLeaf First Last nval)
              e);
         entry_rep
           (splitnode_right
              (btnode val ptr0 le isLeaf First Last nval) e newx);
         data_at Ews tentry
           (Vptrofs
              (splitnode_key
                 (btnode val ptr0 le isLeaf First Last nval) e),
           inl newx) pe))%assert) (stackframe_of f_splitnode)).
Proof.
 intros.
 abbreviate_semax.
    assert(LEAF: isLeaf=true).
    { destruct isLeaf; auto. simpl in H2. inv H2. }
   clear H2; pose (H2:=True).
    remember (findRecordIndex n k) as fri eqn:HFRI.
    replace (findRecordIndex' le k 0) with fri. simpl.
    change (Vint (Int.repr 0)) with (Val.of_bool false).
    sep_apply (fold_btnode_rep ptr0). 
     rewrite LEAF.
    set (nleft := btnode val ptr0 le true First false nval).
    clear ent_end. fold tentry.
    assert(ENTRY: exists ke ve xe, e = keyval val ke ve xe). (* the entry to be inserted at a leaf must be keyval *)
    { destruct e. eauto. simpl in LEAFENTRY.
      rewrite LEAF in LEAFENTRY. simpl in LEAFENTRY.
      elimtype False; rewrite LEAFENTRY; auto.  }
    destruct ENTRY as [ke [ve [xe ENTRY]]].
    assert_PROP(isptr xe).
    { rewrite ENTRY. unfold entry_rep. entailer!. }
    rename H3 into PTRXE.
    
    forward_for_simple_bound fri
    (EX i:Z, EX allent_end:list (val*(val+val)),
     (PROP (Zlength allent_end = Fanout + 1 - i)
      LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
      temp _t'27 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr fri));
      temp _t'1 (Vint (Int.repr fri)); temp _t'28 (Vptrofs k);
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Tsh (tarray tentry 16) (map entry_val_rep (sublist 0 i le)++ allent_end) v_allEntries;
           entry_rep e; data_at Ews tentry ((Vptrofs k), coprepr) pe)))%assert.
    { Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. unfold data_at_, field_at_. simpl. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Intros ent_end.
      assert(HENTRY: exists e, Znth_option i le = Some e).
      { apply Znth_option_in_range. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        unfold n in H0. simpl in H0. rewrite H0. rep_lia. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_nth_leaf. eauto. rewrite LEAF. simpl. auto. eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H5 into XIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep le ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. apply Znth_to_list'. auto. }
      assert(HIRANGE: (0 <= i < Fanout)).
      { clear -INRANGE H3. simpl in INRANGE. rep_lia. }  
      forward.                  (* t'26 = node->entries[i].key *) 
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                 (* allEntries[i].key = t'26 *)
      apply prop_right.  rep_lia.
      forward.                 (* t'25=node->entries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      entailer!.
      rename allent_end into x.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear - H4 HIRANGE. simpl in H4. rewrite Fanout_eq in H4.
        apply eq_sym in H4. rewrite Zlength_nil in H4.  rep_lia. list_solve.  }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4 H3 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. lia.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by lia. simpl in H4. rewrite Zlength_cons in *. rep_lia. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -INRANGE H3.
        simpl in INRANGE. change (findRecordIndex' le k 0) with (findRecordIndex n k) in *; rep_lia.  }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.      
      rewrite upd_Znth_twice.
      rewrite app_Znth2. rewrite !Zlength_map. autorewrite with sublist.
      rewrite upd_Znth_same.
      unfold upd_Znth. rewrite sublist_nil. simpl.
      (*NEW*)destruct (zlt 0 (Zlength x)); [ | lia].
      rewrite sublist_split with (lo:=0) (mid:=i) (hi:=i+1).
      erewrite sublist_len_1. rewrite <- app_nil_r with (l:=le).
      specialize (HZNTH List.nil).
      rewrite app_nil_r in HZNTH|-*.
      rewrite Znth_map in HZNTH.
      rewrite !map_app.
      simpl map.
      rewrite HZNTH. simpl.
      rewrite <- app_assoc. simpl. cancel.
      unfold n in H0. simpl in H0. rewrite H0. rep_lia.
      unfold n in H0. simpl in H0. rewrite H0. rep_lia.
      rep_lia.
      unfold n in H0. simpl in H0. rewrite H0. rep_lia. 
      simpl. lia. list_solve. list_solve. } 
    Intros allent_end. 
    forward.                    (* t'24=entry->key *)

    assert(FRIRANGE: 0 <= fri <= Fanout) by auto.
    rewrite ENTRY in HEVR. simpl in HEVR.
    assert (ke=k) by (apply Vptrofs_inj; congruence). subst ke.
    inv HEVR. assert (H5 := I).

    Opaque Znth.
    set (fri := findRecordIndex n k) in *.
    forward.                    (* allEntries[tgtIdx]->key = t'24 *)
    apply prop_right; rep_lia.
    forward.                    (* t'23=entry->ptr.record *)
    forward.                    (* allEntries[tgtIdx]->ptr.record = t'23 *)
    apply prop_right; rep_lia.
    assert(0 <= fri < Zlength (map entry_val_rep (sublist 0 fri le) ++ allent_end)).
    { split. lia. rewrite Zlength_app, Zlength_map.
      rewrite Zlength_sublist. rep_lia. rep_lia. lia. }
    rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.
    assert(FRILENGTH: Zlength (sublist 0 fri le) = fri).
    { rewrite Zlength_sublist. rep_lia. rep_lia.
      unfold n in H0. simpl in H0. rewrite H0. simpl in INRANGE. lia. }
    rewrite upd_Znth_app2 by list_solve.
    rewrite Zlength_map.
    rewrite FRILENGTH. rewrite Z.sub_diag.
    unfold upd_Znth. autorewrite with sublist. 

    forward_for_simple_bound Fanout
         ( EX i:Z, EX ent_end:list (val * (val+val)),
           PROP (fri <= i <= Fanout; Zlength ent_end = Fanout - i) 
           LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
                       lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
           SEP(mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node true false Last vnewnode);
                 data_at Ews tentry (Vptrofs k, inr xe) pe;
                 data_at Tsh (tarray tentry 16) 
                   (map entry_val_rep (sublist 0 fri le)
                     ++ (Vptrofs k, inr (force_val (sem_cast_pointer xe)))
                       :: map entry_val_rep (sublist fri i le)
                        ++ ent_end)
                  v_allEntries;
                  entry_rep(keyval val k ve xe)))%assert.

    abbreviate_semax.
    {                           (* second loop *)
      forward.                  (* i=tgtidx *)
      Exists fri. Exists ( sublist 1 (Zlength allent_end) allent_end).
      entailer!.
      simpl in INRANGE. list_solve. autorewrite with sublist. simpl.
      destruct (zlt 0 (Zlength allent_end)). cancel. lia. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      rename ent_end into x.
      Intros ent_end.
      assert(HENTRY: exists e, Znth_option i le = Some e).
      { apply Znth_option_in_range. simpl in H0. rewrite H0. lia. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_nth_leaf. eauto. simpl. auto. eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into XIPTR.
      rename H7 into IRANGE.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep le ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. apply Znth_to_list'. auto. }
      assert(HIRANGE: (0 <= i < Fanout)) by rep_lia.
      forward.                  (* t'22=node->entries[i].key *)
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                  (* allEntries[i+1].key=t'26 *)
      apply prop_right; rep_lia.
      forward.                  (* t'21=node->entries[i].ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i+1]->ptr.record=t'21 *)
      apply prop_right; rep_lia.
      Exists (sublist 1 (Zlength x) x).
      assert(XEMP: Zlength x > 0).
      { destruct x. clear -H8 HIRANGE. rep_lia. list_solve. }
      entailer!.
      { clear -IRANGE H8 XEMP. list_solve. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -HIRANGE. lia. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      rewrite upd_Znth_twice.
      (* rewrite upd_Znth_app2. *)
      rewrite upd_Znth_same.
      set (fri := findRecordIndex n k) in *.
      assert((upd_Znth (i + 1) (map entry_val_rep (sublist 0 fri le) 
                                             ++ (Vptrofs k, inr xe) 
                                              :: map entry_val_rep (sublist (fri) i le) ++ x) (Vptrofs ki, inr xi))
                                         = (map entry_val_rep (sublist 0 fri le)  ++ (Vptrofs k, inr xe) :: map entry_val_rep (sublist fri (i + 1) le) ++ sublist 1 (Zlength x) x)).
      { rewrite upd_Znth_app2. rewrite Zlength_map.
        autorewrite with sublist.
        change (?A::?B) with ([A]++B).
        rewrite upd_Znth_app2. simpl. rewrite Zlength_cons. simpl.
        rewrite upd_Znth_app2. rewrite Zlength_map.
        autorewrite with sublist.
        assert(i + 1 - fri - 1 - (i-fri) = 0) by (clear; lia).
        rewrite H17. f_equal. f_equal.
        rewrite upd_Znth0_old by trivial.
        assert(map entry_val_rep (sublist fri i le) ++ [(Vptrofs ki, (inr xi):(val+val))] = map entry_val_rep (sublist fri (i + 1) le)).
        { change (i+1) with (Z.succ i).
           rewrite Znth_option_e in HENTRY.
            repeat if_tac in HENTRY; inv HENTRY.
           autorewrite with sublist in H19.
           rewrite (sublist_split fri i (Z.succ i)) by list_solve. rewrite map_app.
           f_equal. rewrite sublist_one by list_solve.
           rewrite Znth_map in H21 by list_solve. inv H21.
           rewrite H22.  reflexivity.  }
        rewrite <- H18. rewrite <- app_assoc. simpl. auto.
        
        assert(i < Fanout) by (simpl in H0; rep_lia).
        rewrite !Zlength_map. autorewrite with sublist. rep_lia.
        autorewrite with sublist. rep_lia.
        list_solve.
      }
    rewrite <- ?Vptrofs_repr_Vlong_repr by reflexivity.
    change (Vlong (Ptrofs.to_int64 ki)) with (Vptrofs ki) in *.
    change (Vlong (Ptrofs.to_int64 k)) with (Vptrofs k) in *.
    simpl.  rewrite H17. cancel.
      rewrite Zlength_app. rewrite Zlength_cons. 
        rewrite !Zlength_map. list_solve.
         list_solve.
    } 
    Intros ent_end. autorewrite with sublist in H7. apply Zlength_nil_inv in H7.
    subst ent_end; clear H6.
    deadvars!.
   rewrite <- app_nil_end.

    match goal with |- semax _ _ ?c _ => change c with splitnode_main_if_part2 end.
    change Delta with (func_tycontext f_splitnode Vprog Gprog []).
    subst POSTCONDITION; unfold abbreviate.
    clear MORE_COMMANDS.
    clear - FRILENGTH H4 H5 FRIRANGE H3 PTRXE H1 INRANGE H H0 LEAFENTRY.
    eapply splitnode_main_if_part2_proof; try eassumption.
    reflexivity.
Qed.