(** * verif_splitnode.v : Correctness proof of splitnode *)

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
Require Import verif_newnode.
Require Import verif_findindex.
Require Import verif_splitnode_part0.
Require Import verif_splitnode_part3.

Opaque Znth.

Lemma splitnode_main_if_else_proof:
 forall (Espec : OracleKind)
   (ptr0 : option (node val))  (le : list (entry val)) (isLeaf First Last : bool)
   (nval : val) (e : entry val) (pe : val) (gv : globals) (v_allEntries : val)
  (H : node_integrity (btnode val ptr0 le isLeaf First Last nval)),
  let n := btnode val ptr0 le isLeaf First Last nval : node val in
  forall (H0 : numKeys n = Fanout)
  (LEAFENTRY : LeafEntry e = LeafNode (btnode val ptr0 le isLeaf First Last nval))
  (keyrepr : val) (coprepr : val + val)
  (HEVR : entry_val_rep e = (keyrepr, coprepr))
  (k : key) (HK : keyrepr = key_repr k)
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
   temp _t'28 keyrepr;
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
           (numKeys (btnode val ptr0 le isLeaf First Last nval))),
     (optionally getval nullval ptr0,
      map entry_val_rep le ++ ent_end))))) nval;
   optionally btnode_rep emp ptr0; iter_sepcon entry_rep le;
   btnode_rep (empty_node isLeaf false Last vnewnode);
   data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   entry_rep e; data_at Ews tentry (keyrepr, coprepr) pe))
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
           (key_repr
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
      temp _t'1 (Vint (Int.repr fri)); temp _t'28 keyrepr;
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Tsh (tarray tentry 16) (map entry_val_rep (nth_first_le le i)++ allent_end) v_allEntries;
           entry_rep e; data_at Ews tentry (keyrepr, coprepr) pe)))%assert.
    { entailer!.
      Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. simpl.
      unfold data_at_, field_at_. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le i le = Some e).
      { apply nth_entry_le_in_range. simpl in INRANGE. 
        unfold n in H0. simpl in H0. rewrite H0. rep_omega. }
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
      { clear -INRANGE H3. simpl in INRANGE. omega. }  
      forward.                  (* t'26 = node->entries[i].key *) 
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                 (* allEntries[i].key = t'26 *)
      apply prop_right; rep_omega.
      forward.                 (* t'25=node->entries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      apply prop_right; rep_omega.
      entailer!.
      rename allent_end into x.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear - H4 HIRANGE. rep_omega. 
        omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4 H3 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by omega. simpl in H4.  rewrite Zlength_cons in H4; omega. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -INRANGE H3. simpl in *; rep_omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      apply derives_refl'; f_equal.
      unfold nth_first_le; autorewrite with sublist.
      pose proof (nth_entry_le_some _ _ _ HENTRY).
      rewrite (sublist_split 0 i (i+1)) by list_solve.  rewrite map_app, app_ass.
      f_equal.
      rewrite upd_Znth_twice by list_solve.
      rewrite upd_Znth_same by list_solve.       
      unfold upd_Znth. rewrite sublist_nil. simpl.
      rewrite sublist_len_1 by list_solve. simpl. f_equal.
      specialize (HZNTH List.nil).
      rewrite app_nil_r in HZNTH.
      rewrite Znth_map in HZNTH by omega.
      rewrite HZNTH. simpl. auto. }
    Intros allent_end.
    forward.                    (* t'24=entry->key *)
    rewrite HK. unfold key_repr.

    assert(FRIRANGE: 0 <= fri <= Fanout) by assumption.
    rewrite ENTRY in HEVR. simpl in HEVR. inv HEVR.

    Opaque Znth.
    set (fri := findRecordIndex n k) in *.
    forward.                    (* allEntries[tgtIdx]->key = t'24 *)
      apply prop_right; rep_omega.
    forward.                    (* t'23=entry->ptr.record *)
    forward.                    (* allEntries[tgtIdx]->ptr.record = t'23 *)
      apply prop_right; rep_omega.
    assert(0 <= fri < Zlength (map entry_val_rep (nth_first_le le fri) ++ allent_end)).
    { unfold n in H0; simpl in H0. unfold nth_first_le; autorewrite with sublist.
      rep_omega. }      
    rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.
    deadvars!.
    assert(FRILENGTH: Zlength (nth_first_le le fri) = fri).
    { unfold n in H0; simpl in H0.  unfold nth_first_le; autorewrite with sublist.
      rep_omega. } 
    unfold upd_Znth. rewrite sublist_app1 by (try list_solve; rewrite FRILENGTH; rep_omega).
    rewrite sublist_same by (try list_solve; rewrite FRILENGTH; rep_omega).
    autorewrite with sublist.
(*    rewrite sublist_app2 by (rewrite FRILENGTH; rep_omega). *)
    repeat rewrite FRILENGTH.
    replace (fri + 1 - fri) with 1 by rep_omega. (* rewrite Zlength_app. *)
(*    rewrite FRILENGTH. *)
    replace (fri + Zlength allent_end - fri) with (Zlength allent_end) by rep_omega.

    forward_for_simple_bound Fanout
     ( EX i:Z, EX ent_end:list (val * (val+val)), 
      PROP(fri <= i <= Fanout; Zlength ent_end = Fanout - i)
      LOCAL(temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
                 lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP(mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node false false Last vnewnode);
           data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) pe;
           data_at Tsh (tarray tentry 16) (map entry_val_rep (nth_first_le le fri) ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) :: map entry_val_rep (suble fri i le) ++ ent_end) v_allEntries;
           entry_rep(keychild val ke ce)))%assert.

    abbreviate_semax.
    {                           (* second loop *)
      forward.                  (* i=tgtidx *)
      Exists fri. Exists ( sublist 1 (Zlength allent_end) allent_end).
      entailer!.
      { clear -H3 INRANGE. simpl in INRANGE. change (findRecordIndex' le k 0) with (findRecordIndex n k) in *.
        autorewrite with sublist.  omega. }
      unfold suble. autorewrite with sublist. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      rename ent_end into x.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le i le = Some e).
      { apply nth_entry_le_in_range. simpl in H0. rewrite H0. omega. }
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
       apply prop_right; rep_omega.
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                  (* allEntries[i+1].key=t'26 *)
       apply prop_right; rep_omega.
      forward.                  (* t'21=node->entries[i].ptr.record *)
       apply prop_right; rep_omega.
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i+1]->ptr.record=t'21 *)
       apply prop_right; rep_omega.
      entailer!.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear -H8 H6. rep_omega.
         simpl in *; rewrite Zlength_cons in *; rep_omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -IRANGE H8 XEMP. autorewrite with sublist. rep_omega. }
      assert(INUM: i <= Zlength le).
      { unfold n  in H0. simpl in H0. rewrite H0. clear - H6. omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      rewrite upd_Znth_twice.
      (* rewrite upd_Znth_app2. *)
      rewrite upd_Znth_same.
    set (fri := findRecordIndex n k) in *.
      assert((upd_Znth (i + 1) (map entry_val_rep (nth_first_le le fri) ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) :: map entry_val_rep (suble fri i le) ++ x) (key_repr ki, inl (getval ci))) 
                 = (map entry_val_rep (nth_first_le le fri) ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) :: map entry_val_rep (suble fri (i + 1) le) ++ sublist 1 (Zlength x) x)).
      { unfold nth_first_le, suble; autorewrite with sublist. f_equal.
        change (?A::?B) with ([A]++B).
        rewrite upd_Znth_app2 by list_solve. simpl. f_equal.
        autorewrite with sublist. rewrite (sublist_split fri i (i+1)) by (unfold n in H0; simpl in H0; list_solve).
        rewrite map_app, app_ass. f_equal.
        assert(i + 1 - fri - (Z.succ 0) - (i-fri) = 0) by (clear; omega).
        rewrite H18.
        rewrite upd_Znth0. rewrite (sublist_one i) by  (unfold n in H0; simpl in H0; list_solve).
        simpl; f_equal.
        clear - HENTRY. unfold nth_entry_le, Znth_option in HENTRY.
        repeat if_tac in HENTRY; inv HENTRY. autorewrite with sublist in *.
        rewrite Znth_map in H2 by list_solve. inv H2. rewrite H3. reflexivity.
      }
      rewrite <- ?Vptrofs_repr_Vlong_repr by auto.
      rewrite H18. simpl. cancel.
      unfold nth_first_le, suble. list_solve.
      unfold nth_first_le, suble. list_solve.
    }
    eapply splitnode_main_ifelse_part2_proof; try eassumption.
    reflexivity.
    rewrite !Zlength_map; auto.
Qed.
