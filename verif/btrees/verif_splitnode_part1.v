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
Require Import verif_splitnode_part0.

Opaque Znth.

Lemma splitnode_main_if_part2_proof:
 forall (Espec : OracleKind) (ptr0 : option (node val)) (le : list (entry val))
          (First Last : bool) (nval pe : val) (gv : globals) (v_allEntries : val)
          (k : key) (ve : V) (xe : val) 
          (LEAFENTRY : LeafEntry (keyval val k ve xe) =
                  is_true (node_isLeaf (btnode val ptr0 le true First Last nval))),
          let n := btnode val ptr0 le true First Last nval : node val in
          forall (H0 : Zlength le = Fanout)
          (H : node_integrity (btnode val ptr0 le true First Last nval))
          (fri : Z)
          (HFRI : findRecordIndex n k = fri)
          (vnewnode : val)
         (H1 : vnewnode <> nullval),
         let nleft := btnode val ptr0 le true First false nval : node val in
         forall (PTRXE : isptr xe) (allent_end : list (val * (val + val)))
         (H3 : Zlength allent_end = Fanout + 1 - fri)
         (FRIRANGE : 0 <= fri <= Fanout)
(*         (H4 : 0 <= fri < Zlength (map entry_val_rep (sublist 0 fri le) ++ allent_end)) *),
semax (func_tycontext f_splitnode Vprog Gprog [])
  (PROP ()
   LOCAL (
   temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
   lvar _allEntries (tarray tentry 16) v_allEntries;
   temp _node nval; temp _entry pe)
   SEP (mem_mgr gv; btnode_rep nleft;
   btnode_rep (empty_node true false Last vnewnode);
   data_at Ews tentry (Vptrofs k, inr xe) pe;
   data_at Tsh (tarray tentry 16)
     (map entry_val_rep (sublist 0 fri le) ++
      (Vptrofs k, inr (force_val (sem_cast_pointer xe)))
      :: map entry_val_rep (sublist fri Fanout le)) v_allEntries;
   entry_rep (keyval val k ve xe))) splitnode_main_if_part2
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX newx : val,
         PROP ( )
         LOCAL ()
         SEP (mem_mgr gv;
         btnode_rep
           (splitnode_left
              (btnode val ptr0 le true First Last nval)
              (keyval val k ve xe));
         entry_rep
           (splitnode_right
              (btnode val ptr0 le true First Last nval)
              (keyval val k ve xe) newx);
         data_at Ews tentry
           (Vptrofs
              (splitnode_key
                 (btnode val ptr0 le true First Last nval)
                 (keyval val k ve xe)), inl newx) pe))%assert)
     (stackframe_of f_splitnode)).
Proof.
   intros. unfold splitnode_main_if_part2. abbreviate_semax.
   set (H4 := True).
   subst fri; set (fri := findRecordIndex n k) in *.
    pose (e:=keyval val k ve xe).
    rewrite unfold_btnode_rep with (n:=nleft).
    unfold nleft. Intros ent_end0.
    forward.                    (* node->numKeys=8 *)
    sep_apply insert_rep. fold e.
    replace (insert_le le e) with 
      (sublist 0 Middle (insert_le le e) 
      ++ sublist Middle (Zlength (insert_le le e)) (insert_le le e)).
    2:{ rewrite sublist_rejoin; try rep_lia.
         apply sublist_same; list_solve.
         clear - H0. simpl in H0.
         autorewrite with sublist. rep_lia. }
   rewrite iter_sepcon_app.
    
    forward_if (PROP ( )
    LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
           lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
    SEP (mem_mgr gv; btnode_rep (splitnode_left n e); btnode_rep (empty_node true false Last vnewnode);
         data_at Ews tentry (Vptrofs k, inr xe) pe;
         data_at Tsh (tarray tentry 16) 
            (map entry_val_rep (sublist 0 fri le)
             ++ (Vptrofs k, inr (force_val (sem_cast_pointer xe))) 
              :: map entry_val_rep (sublist fri Fanout le)) v_allEntries;
          iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e)))).
    {                           (* fri < 8 *)
      Intros.
      Intros. rewrite Int.signed_repr in H2. 
      2:{ subst fri; simpl in *. rewrite Fanout_eq in *. rep_lia. }
      unfold Sfor.              (* both forward_loop and forward_for_simple_bound fail here *)
      forward.                  (* i=tgtIdx *)
      forward_loop (EX i:Z, EX le_end:list(val*(val+val)), PROP(fri <= i <= Middle)
LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
       lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _i (Vint (Int.repr i)))
SEP (mem_mgr gv; iter_sepcon entry_rep (sublist 0 Middle (insert_le le e) );
          iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e)); malloc_token Ews tbtnode nval;
     data_at Ews tbtnode
       (Val.of_bool true,
       (Val.of_bool First,
       (Val.of_bool false,
       (Vint (Int.repr 8),
       (optionally getval nullval ptr0,
        map entry_val_rep ( (sublist 0 i (insert_le le e))) ++ le_end))))) nval;
     optionally btnode_rep emp ptr0; btnode_rep (empty_node true false Last vnewnode);
     data_at Ews tentry (Vptrofs k, inr xe) pe;
     data_at Tsh (tarray tentry 16)
       (map entry_val_rep ( (sublist 0 fri le)) ++
        (Vptrofs k, inr (force_val (sem_cast_pointer xe)))
        :: map entry_val_rep ( (sublist fri Fanout le))) v_allEntries))%assert.
      - Exists fri.
        Exists (map entry_val_rep ((sublist fri (Zlength le) le)) ++ ent_end0).
        entailer!.
        { clear - H2. subst fri. simpl. rewrite Middle_eq. lia. }
        apply derives_refl'. do 6 f_equal. rewrite <- app_ass. f_equal.
        rewrite <- map_app. f_equal.
        simpl in H0.
        replace (sublist 0 fri (insert_le le e)) with (sublist 0 fri le).
        rewrite sublist_rejoin; try list_solve.
        autorewrite with sublist. auto.
        rewrite insert_fri with (fri:=fri) (key0:=k); try auto with typeclass_instances.
        autorewrite with sublist. auto.
      -                         (* loop body *)
        Intros i.
        Intros le_end.             
        forward_if.
        + assert(HINSERT: (map entry_val_rep ( (sublist 0 fri le)) 
                                      ++ (Vptrofs k, inr (force_val (sem_cast_pointer xe)))
                                        :: map entry_val_rep ( (sublist fri Fanout le))) 
                       = map entry_val_rep ( (insert_le le e))).
          { rewrite insert_fri with (fri:=fri) (key0:=k); auto with typeclass_instances.
            rewrite map_app.
            simpl. f_equal.
            f_equal. f_equal.
            f_equal. f_equal. simpl in H0; lia.
          } 
          rewrite HINSERT.
          assert(HENTRY: exists ei, Znth_option i (insert_le le e) = Some ei).
          { apply Znth_option_in_range. simpl in H0. rewrite Zlength_insert_le. rewrite H0. rep_lia.  }
          destruct HENTRY as [ei HENTRY].  
          assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
          { eapply integrity_leaf_insert; auto with typeclass_instances.
             simpl in H. destruct H. eauto. unfold e in HENTRY.
            eauto. }
          destruct HEI as [ki [vi [xi HEI]]]. subst ei.
          assert_PROP(isptr xi).
          { apply le_iter_sepcon_split in HENTRY.
            gather_SEP (iter_sepcon entry_rep (sublist 0 Middle (insert_le le e)))
                       (iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e))).
            replace_SEP 0 ( iter_sepcon entry_rep (insert_le le e)).
            { entailer!. rewrite <- iter_sepcon_app. rewrite sublist_rejoin; try list_solve.
               rewrite sublist_same by list_solve. auto.
               autorewrite with sublist; auto.
               simpl in H0; rewrite H0.  rep_lia. }
            rewrite HENTRY. simpl entry_rep. entailer!. }
          rename H7 into XIPTR.
          assert(HZNTH: Znth i (map entry_val_rep ( (insert_le le e))) = entry_val_rep (keyval val ki vi xi)).
          { intros. rewrite Znth_map. apply Znth_option_e' in HENTRY. rewrite HENTRY. auto.
            apply Znth_option_some in HENTRY; rep_lia. }
          assert(0 <= i < 8) by lia.
          assert_PROP(Zlength le_end > 0).
          { entailer!.
            clear - H10 H7 H0. simplify_value_fits in H10.
            destruct H10, H1, H2, H3, H4.
            simplify_value_fits in H5. destruct H5.
            rewrite Zlength_app, Zlength_map in H5.
            pose proof (Zlength_sublist_hack 0 i (insert_le le e)).
            lia.  }            
          rename H8 into LEEND.
          forward.              (* t'20=allEntries[i]->key *)
          { unfold local, lift1. intro; apply prop_right. clear - HZNTH.
            fold Inhabitant_entry_val_rep;  rewrite HZNTH. hnf; auto. }
          fold Inhabitant_entry_val_rep; rewrite HZNTH.
          forward.              (* node->entries[i]->key=t'20 *)
          forward.              (* t'19=allEntries[i]->ptr.record *)
          { fold Inhabitant_entry_val_rep; rewrite HZNTH. entailer!. }
          fold Inhabitant_entry_val_rep; rewrite HZNTH.
          forward.              (* node->entries[i]->ptr.record = t'19 *)
          forward.              (* i=i+1 *)
          Exists (i+1).
          Exists (sublist 1 (Zlength le_end) le_end).
          assert (Hi:  i < Zlength (insert_le le e)). {
                      rewrite Zlength_insert_le. simpl in H0; rewrite H0. rep_lia.
         }
          entailer!. apply derives_refl'; repeat f_equal.
          autorewrite with sublist.
          rewrite upd_Znth_twice by list_solve.
          rewrite upd_Znth_same by list_solve.

          (*WAS:rewrite upd_Znth0. *)
          (*NOW:*)simpl; clear H11.
            rewrite upd_Znth_app2.
            2: rewrite Zlength_map, Zlength_sublist2, Z.min_l, Z.max_l by lia; simpl; lia.
            rewrite Zlength_map, Zlength_sublist2, Z.min_l, Z.max_l by lia; simpl. 
            rewrite Zminus_0_r, Zminus_diag.
            rewrite upd_Znth0_old by trivial. 

          fold (Z.succ i).
          rewrite (sublist_split 0 i (Z.succ i)) by lia.
          rewrite map_app, app_ass. f_equal.
          rewrite (sublist_one i) by lia. simpl. f_equal.
          clear - HENTRY. 
          apply Znth_to_list with (endle:=nil) in HENTRY.
          rewrite <- app_nil_end in HENTRY.
          rewrite HENTRY. reflexivity.
        + 
          assert(i=8) by rep_lia.
          forward.              (* break *)
          entailer!.
          unfold n, splitnode_left.
          rewrite unfold_btnode_rep 
          with (n:=btnode val ptr0 (sublist 0 Middle (insert_le le e)) true First false nval).
          Exists le_end.
          cancel.  simpl.
          apply derives_refl'; repeat f_equal.
          rewrite Zlength_sublist. rep_lia.
          rep_lia.  simpl in H0.  clear - H0. rewrite Zlength_insert_le. rep_lia.
    } 
    {                           (* fri >= 8 *)
      rewrite Int.signed_repr in H2. 
      2:{ subst fri; simpl in *. rewrite Fanout_eq in *. rep_lia. }
      forward.                  (* skip *)
      entailer!.
      assert((Middle <=? fri) = true).
      { clear -H2. rewrite Middle_eq. apply Z.leb_le. subst fri; simpl; lia.  }
      unfold splitnode_left, n.
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 (sublist 0 Middle (insert_le le e)) true First false nval).
      assert(SPLITLE:  le = (sublist 0 Middle le) ++ (sublist Middle (Zlength le) le)).
      {simpl in H0. rewrite sublist_rejoin; try rep_lia. autorewrite with sublist; auto. }
      rewrite SPLITLE.
      rewrite map_app, <- app_assoc.
      Exists (map entry_val_rep (sublist Middle (Zlength le) le) ++ ent_end0).
      simpl. cancel. 
      apply derives_refl'; do 5 f_equal.
     do 2 f_equal.
     rewrite <- SPLITLE.
     rewrite Zlength_sublist; auto. rep_lia.
      rewrite Zlength_insert_le. simpl in H0. rep_lia.
      do 3 f_equal.
      rewrite nth_first_insert with (k:=k); auto with typeclass_instances.
     rewrite <- SPLITLE. auto.
     rewrite <- SPLITLE.
     (*WAS: change (findRecordIndex' le k 0) with fri. rep_lia.*)
     (*NOW*) rewrite Middle_eq. lia.
    }
    rewrite unfold_btnode_rep with (n:=empty_node true false Last vnewnode).
    simpl. Intros ent_empty.
    assert(HINSERT: (map entry_val_rep ( (sublist 0 fri le))
                              ++ (Vptrofs k, inr xe)
                               :: map entry_val_rep ( (sublist fri Fanout le))) 
                            = map entry_val_rep ( (insert_le le e))).
    { rewrite insert_fri with (fri:=fri) (key0:=k); auto with typeclass_instances.
      rewrite map_app.
      simpl. f_equal.
      f_equal. 
      do 2 f_equal; simpl in H0; rep_lia.
    } 
    rewrite HINSERT.
    
    forward_for_simple_bound (Fanout + 1)
(EX i:Z, EX ent_right:list(val*(val+val)), (PROP (Zlength ent_right + i - 8 = Fanout)
     LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
     lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP (mem_mgr gv; btnode_rep (splitnode_left n e);
     malloc_token Ews tbtnode vnewnode;
     data_at Ews tbtnode
       (Vtrue, (Vfalse, (Val.of_bool Last, (Vint (Int.repr 0), (nullval,
        map entry_val_rep ((sublist Middle i (insert_le le e))) ++ ent_right)))))
       vnewnode;
     data_at Ews tentry (Vptrofs k, inr xe) pe;
     data_at Tsh (tarray tentry 16) (map entry_val_rep ( (insert_le le e))) v_allEntries;
     iter_sepcon entry_rep (sublist Middle (Zlength(insert_le le e)) (insert_le le e)))))%assert.
    
    { Exists ent_empty. entailer!.
      simplify_value_fits in H7. decompose [and] H7.  simplify_value_fits in H19.
         destruct H19. rewrite Z.add_simpl_r. rewrite Fanout_eq;  assumption.
        autorewrite with sublist; auto.  }
    {                           (* loop body *)
      assert(HENTRY: exists ei, Znth_option i (insert_le le e) = Some ei).
      { apply Znth_option_in_range. simpl in H0. rewrite Zlength_insert_le. rewrite H0.
        rep_lia. }
      destruct HENTRY as [ei HENTRY].  
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_leaf_insert; auto with typeclass_instances.
         simpl in H. destruct H. eauto. unfold e in HENTRY.
        eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY.
        rewrite unfold_btnode_rep with (n:=splitnode_left n e).
        unfold splitnode_left. unfold n. Intros ent_left.
        gather_SEP (iter_sepcon entry_rep (sublist 0 Middle (insert_le le e))) 
                          (iter_sepcon entry_rep (sublist Middle _ (insert_le le e))).
        replace_SEP 0 ( iter_sepcon entry_rep (insert_le le e)).
        { entailer!. rewrite <- iter_sepcon_app. rewrite sublist_rejoin; try rep_lia.
           rewrite sublist_same by list_solve; auto.
           autorewrite with sublist; auto.
          simpl in H0. rep_lia. }
        rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H5 into XIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep ( (insert_le le e)) ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. apply Znth_to_list'. auto. }

      forward.                  (* t'18=allEntries[i]->key *)
      apply prop_right; rep_lia.
      { specialize (HZNTH nil); rewrite <- app_nil_end in HZNTH; rewrite HZNTH. entailer!. }
      specialize (HZNTH nil); rewrite <- app_nil_end in HZNTH; rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->key=t'18 *)
      apply prop_right; rep_lia.
      forward.                  (* t'17=allEntries[i]->ptr.record *)
      apply prop_right; rep_lia.
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->ptr.record=t'17 *)
      entailer!.
      rename ent_right into x.
      Exists (sublist 1 (Zlength x) x). entailer!.
      list_solve.
      assert(8 <= i < 16) by rep_lia.
      (*NEW:*)clear H9; simpl. rewrite Middle_eq.

      rewrite upd_Znth_twice by list_solve.
      rewrite upd_Znth_same by list_solve.
      rewrite upd_Znth_app2.
      rewrite !Zlength_map.
      apply derives_refl'. do 6 f_equal.
      autorewrite with sublist.
      (*WAS: rewrite Zlength_sublist; try rep_lia.
        replace (i - 8 - (i - Middle)) with 0 by rep_lia.
        rewrite upd_Znth0.*)
      (*NOW:*)rewrite upd_Znth0_old.

      fold (Z.succ i).
      rewrite (sublist_split Middle i (Z.succ i)); try rep_lia.
      rewrite map_app, app_ass. f_equal.
      rewrite (sublist_one i); try lia. simpl; f_equal.
          clear - HENTRY.
          apply Znth_to_list with (endle:=nil) in HENTRY.
          rewrite <- app_nil_end in HENTRY.
          rewrite HENTRY. reflexivity.
      rewrite Zlength_insert_le. simpl in H0. rewrite H0. rep_lia.
      rewrite Zlength_insert_le. simpl in H0. rewrite H0. rep_lia.
      (*WAS: rewrite Zlength_insert_le. simpl in H0. rewrite H0. rep_lia.*)
      (*NOW:*) clear - H2 H5; rewrite Fanout_eq in *; lia. 
      pose proof (Zlength_insert_le _ le e). autorewrite with sublist.
      pose proof (Zlength_sublist_hack Middle i (insert_le le e)).
      spec (*H17*)H16; [rep_lia|].
      rep_lia.
    }
    Intros ent_right.
    forward.
    change Vtrue with (Val.of_bool true).
    change Vfalse with (Val.of_bool false).
    pose (ptr1 := @None (node val)).
    
    change nullval with (optionally getval nullval ptr1).
    rewrite <- (sepcon_emp (malloc_token _ _ _)). Intros.
    change emp with (optionally btnode_rep emp ptr1).
     rewrite add_repr, sub_repr.
    fold (Z.succ Fanout).
    replace (Z.succ Fanout) with (Zlength (insert_le le e))
      by (rewrite Zlength_insert_le; unfold n in H0; simpl in H0; rewrite H0; auto).
    rewrite Middle_eq.
    sep_apply (fold_btnode_rep ptr1).
    simpl.
    assert (Zlength le = Fanout) by (unfold n in H0; apply H0).
    rewrite Zlength_insert_le. rewrite Zlength_sublist; try rep_lia.
    rewrite Zlength_insert_le; rep_lia.
    assert(NTHENTRY: exists emid, Znth_option Middle (insert_le le e) = Some emid).
    { apply Znth_option_in_range. unfold n in H0. simpl in H0. rewrite Zlength_insert_le.
      rewrite H0. rep_lia. } 
    destruct NTHENTRY as [emid NTHENTRY].
    assert(HZNTH: Znth_option Middle (insert_le le e) = Some emid) by auto.
(*    apply Znth_to_list' with (endle:=nil) in HZNTH.*)
    rewrite Middle_eq in HZNTH. simpl in HZNTH.
      rewrite Znth_option_e in HZNTH. repeat if_tac in HZNTH; try discriminate.
      rewrite Znth_map in HZNTH.
     2:{ autorewrite with sublist in H6|-*; rep_lia. }
      apply Some_inj in HZNTH.

    forward.                    (* t'16=allEntries[8]->key *)
    { entailer!. fold Inhabitant_entry_val_rep. rewrite Znth_map.
      destruct (Znth 8 (insert_le le e)); simpl; auto.
      autorewrite with sublist in H11|-*. rep_lia. }
     fold Inhabitant_entry_val_rep.
    rewrite Znth_map by (autorewrite with sublist in H6|-*; rep_lia).
    rewrite HZNTH.
    forward.                    (* entry->key=t'16 *)
    forward.                    (* entry->ptr.child=newnode *)
    forward.                    (* return *)
    Exists vnewnode. fold e. simpl.
    rewrite NTHENTRY. simpl.
    cancel.
    apply sepcon_derives.
    simpl. unfold splitnode_leafnode.
    rewrite <- Middle_eq.
    subst ptr1. cancel.
    destruct (Znth 8 (insert_le le e)); apply derives_refl.
Qed.