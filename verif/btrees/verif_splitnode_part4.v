(** * verif_splitnode.v : Correctness proof of splitnode *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import btrees.relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec.
Require Import btrees.verif_splitnode_part0. (*For splitnode_main_if_else *)
Require Import btrees.verif_splitnode_part3.  (*For Lemma splitnode_main_ifelse_part2_proof*)

Opaque Znth.

Lemma splitnode_main_if_else_proof:
 forall (Espec : OracleKind)
   (ptr0 : option (node val))  (le : list (entry val)) (isLeaf First Last : bool)
   (nval : val) (e : entry val) (pe : val) (gv : globals) (v_allEntries : val)
  (H : node_integrity (btnode val ptr0 le isLeaf First Last nval)),
  let n := btnode val ptr0 le isLeaf First Last nval : node val in
  forall (H0 : Zlength le = Fanout)
  (LEAFENTRY : LeafEntry e = is_true (node_isLeaf (btnode val ptr0 le isLeaf First Last nval)))
  (k : key) (coprepr : val + val)
  (HEVR : entry_val_rep e = ((Vptrofs k), coprepr))
  (INRANGE : 0 <= findRecordIndex n k <= Fanout)
  (vnewnode : val)
  (H1 : vnewnode <> nullval)
  (ent_end : list (val * (val + val)))
  (H2 : typed_false tint
       (force_val
          (both_int
             (fun n1 n2 : int => Some (Val.of_bool (Int.eq n1 n2)))
             (sem_cast_i2i I32 Signed) (sem_cast_i2i I32 Signed)
             (Val.of_bool isLeaf) (Vint (Int.repr 1))))),

semax (func_tycontext f_splitnode Vprog Gprog [])
  (PROP ( )
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
     (Vint
        (Int.repr
           (Zlength (node_le (btnode val ptr0 le isLeaf First Last nval)))),
     (optionally getval nullval ptr0,
      map entry_val_rep le ++ ent_end))))) nval;
   optionally btnode_rep emp ptr0; iter_sepcon entry_rep le;
   btnode_rep (empty_node isLeaf false Last vnewnode);
   data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   entry_rep e; data_at Ews tentry ((Vptrofs k), coprepr) pe))
  splitnode_main_if_else
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
    assert(INTERN: isLeaf=false).
    { destruct isLeaf; auto. simpl in H2. inv H2. }
    remember (findRecordIndex n k) as fri eqn:HFRI.
    replace (findRecordIndex' le k 0) with fri. simpl.
    change (Vint (Int.repr 0)) with (Val.of_bool false).
    sep_apply (fold_btnode_rep ptr0). 
     rewrite INTERN.
    set (nleft := btnode val ptr0 le false First false nval).
    clear ent_end. fold tentry.
    assert(ENTRY: exists ke ce, e = keychild val ke ce). (* the entry to be inserted at an intern node must be keychild *)
    { destruct e. simpl in LEAFENTRY.
      rewrite INTERN in LEAFENTRY. simpl in LEAFENTRY.
      exfalso. rewrite <- LEAFENTRY. auto. eauto. }
    destruct ENTRY as [ke [ce ENTRY]].
    assert_PROP(isptr (getval ce)).
    { rewrite ENTRY. unfold entry_rep. entailer!. }
    rename H3 into PTRCE.
    
    forward_for_simple_bound fri
    (EX i:Z, EX allent_end:list (val*(val+val)),
     (PROP (Zlength allent_end = Fanout + 1 - i)
      LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
      temp _t'27 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr fri));
      temp _t'1 (Vint (Int.repr fri)); temp _t'28 (Vptrofs k);
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Tsh (tarray tentry 16) (map entry_val_rep (sublist 0 i le) ++ allent_end) v_allEntries;
           entry_rep e; data_at Ews tentry ((Vptrofs k), coprepr) pe)))%assert.
    { entailer!. 
      Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. simpl.
      unfold data_at_, field_at_. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Intros ent_end.
      assert(HENTRY: exists e, Znth_option i le = Some e).
      { apply Znth_option_in_range. simpl in INRANGE. 
        unfold n in H0. simpl in H0. rewrite H0. rep_lia. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { eapply integrity_nth. eauto. rewrite INTERN. simpl. auto. eauto. }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H5 into CIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep le ++ ent_end) = entry_val_rep (keychild val ki ci)).
      { intros. apply Znth_to_list'. auto. }
      assert(HIRANGE: (0 <= i < Fanout)).
      { clear -INRANGE H3. simpl in INRANGE. lia. }  
      forward.                  (* t'26 = node->entries[i].key *) 
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth. 
      forward.                 (* allEntries[i].key = t'26 *)
      apply prop_right; rep_lia.
      forward.                 (* t'25=node->entries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      apply prop_right; rep_lia.
      entailer!.
      rename allent_end into x.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear - H4 HIRANGE. rep_lia. 
        lia. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4 H3 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. lia.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by lia. simpl in H4.  rewrite Zlength_cons in H4; lia. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -INRANGE H3. simpl in *; rep_lia. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      apply derives_refl'; f_equal.
      autorewrite with sublist.
      pose proof (Znth_option_some _ _ _ _ HENTRY).
      rewrite (sublist_split 0 i (i+1)) by list_solve.  rewrite map_app, app_ass.
      f_equal.
      rewrite upd_Znth_twice by list_solve.
      rewrite upd_Znth_same by list_solve.       
      unfold upd_Znth. rewrite sublist_nil. simpl.
      destruct (zlt 0 (Zlength x)); [| lia].
      rewrite sublist_len_1 by list_solve. simpl. f_equal.
      specialize (HZNTH List.nil).
      rewrite app_nil_r in HZNTH.
      rewrite Znth_map in HZNTH by lia.
      rewrite HZNTH. simpl. auto. }
    Intros allent_end.
    forward.                    (* t'24=entry->key *)

    assert(FRIRANGE: 0 <= fri <= Fanout) by assumption.
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
    assert(0 <= fri < Zlength (map entry_val_rep (sublist 0 fri le)  ++ allent_end)).
    { unfold n in H0; simpl in H0. autorewrite with sublist.
      rep_lia. }      
    rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.
    deadvars!.
    assert(FRILENGTH: Zlength (sublist 0 fri le)  = fri).
    { unfold n in H0; simpl in H0.  autorewrite with sublist.
      rep_lia. } 
    unfold upd_Znth. rewrite sublist_app1 by (try list_solve; rewrite FRILENGTH; rep_lia).
    
    (*WAS: rewrite sublist_same by (try list_solve; rewrite FRILENGTH; rep_lia).*)
    (*NOW*) 
    destruct (Sumbool.sumbool_and (0 <= fri) (0 > fri)
         (fri <
          Zlength
            (map entry_val_rep (sublist 0 fri le) ++ allent_end))
         (fri >=
          Zlength
            (map entry_val_rep (sublist 0 fri le) ++ allent_end))
         (zle 0 fri)
         (zlt fri
            (Zlength
               (map entry_val_rep (sublist 0 fri le) ++ allent_end)))).
       2: solve [ destruct o; lia].
       simpl; rewrite sublist_same; [ | trivial | autorewrite with sublist in *; trivial].

    autorewrite with sublist.
    repeat rewrite FRILENGTH.
    replace (fri + 1 - fri) with 1 by rep_lia.
    replace (fri + Zlength allent_end - fri) with (Zlength allent_end) by rep_lia.

    forward_for_simple_bound Fanout
     ( EX i:Z, EX ent_end:list (val * (val+val)), 
      PROP(fri <= i <= Fanout; Zlength ent_end = Fanout - i)
      LOCAL(temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
                 lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP(mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node false false Last vnewnode);
           data_at Ews tentry (Vptrofs k, inl (getval ce)) pe;
           data_at Tsh (tarray tentry 16) (map entry_val_rep (sublist 0 fri le)  ++ (Vptrofs k, inl (getval ce)) :: map entry_val_rep (sublist fri i le) ++ ent_end) v_allEntries;
           entry_rep(keychild val k ce)))%assert.

    abbreviate_semax.
    {                           (* second loop *)
      forward.                  (* i=tgtidx *)
      Exists fri. Exists ( sublist 1 (Zlength allent_end) allent_end).
      entailer!.
      { clear -H3 INRANGE. simpl in INRANGE. change (findRecordIndex' le k 0) with (findRecordIndex n k) in *.
        autorewrite with sublist.  lia. }
       autorewrite with sublist. simpl. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      rename ent_end into x.
      Intros ent_end.
      assert(HENTRY: exists e, Znth_option i le = Some e).
      { apply Znth_option_in_range. simpl in H0. rewrite H0. lia. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { eapply integrity_nth. eauto. simpl. auto. eauto. }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into CIPTR.
      rename H7 into IRANGE.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep le ++ ent_end) = entry_val_rep (keychild val ki ci)).
      { intros. apply Znth_to_list'. auto. }
      forward.                  (* t'22=node->entries[i].key *)
       apply prop_right; rep_lia.
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                  (* allEntries[i+1].key=t'26 *)
       apply prop_right; rep_lia.
      forward.                  (* t'21=node->entries[i].ptr.record *)
       apply prop_right; rep_lia.
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i+1]->ptr.record=t'21 *)
       apply prop_right; rep_lia.
      entailer!.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear -H8 H6. rep_lia.
         simpl in *; rewrite Zlength_cons in *; rep_lia. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -IRANGE H8 XEMP. autorewrite with sublist. rep_lia. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear - H6. lia. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      rewrite upd_Znth_twice.
      (* rewrite upd_Znth_app2. *)
      rewrite upd_Znth_same.
    set (fri := findRecordIndex n k) in *.
      assert((upd_Znth (i + 1) (map entry_val_rep (sublist 0 fri le)  ++ (Vptrofs k, inl (getval ce)) :: map entry_val_rep (sublist fri i le) ++ x) (Vptrofs ki, inl (getval ci))) 
                 = (map entry_val_rep (sublist 0 fri le)  ++ (Vptrofs k, inl (getval ce)) :: map entry_val_rep (sublist fri (i + 1) le) ++ sublist 1 (Zlength x) x)).
      { autorewrite with sublist. f_equal.
        change (?A::?B) with ([A]++B).
        rewrite upd_Znth_app2 by list_solve. simpl. f_equal.
        autorewrite with sublist. rewrite (sublist_split fri i (i+1)) by (unfold n in H0; simpl in H0; list_solve).
        rewrite map_app, app_ass. f_equal.
        assert(i + 1 - fri - (Z.succ 0) - (i-fri) = 0) by (clear; lia).
        rewrite H18.
        rewrite upd_Znth0_old by trivial. rewrite (sublist_one i) by  (unfold n in H0; simpl in H0; list_solve).
        simpl; f_equal.
        clear - HENTRY. rewrite Znth_option_e in HENTRY.
        repeat if_tac in HENTRY; inv HENTRY. autorewrite with sublist in *.
        rewrite Znth_map in H2 by list_solve. inv H2. rewrite H3. reflexivity.
      }
      rewrite <- ?Vptrofs_repr_Vlong_repr by auto.
    change (Vlong (Ptrofs.to_int64 ki)) with (Vptrofs ki) in *.
    change (Vlong (Ptrofs.to_int64 k)) with (Vptrofs k) in *.
    simpl.  rewrite H18. simpl. cancel.
      list_solve.
      list_solve.
    }
    Intros ent_end. autorewrite with sublist in H7. apply Zlength_nil_inv in H7. subst ent_end.
    deadvars!.
    rewrite <- app_nil_end.
    eapply splitnode_main_ifelse_part2_proof; try eassumption; auto.
Qed.
