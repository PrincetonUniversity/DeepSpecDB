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

Opaque Znth.

Lemma splitnode_main_if_part2_proof:
 forall (Espec : OracleKind) (ptr0 : option (node val)) (le : listentry val)
          (First Last : bool) (nval pe : val) (gv : globals) (v_allEntries : val)
          (ke : key) (ve : V) (xe : val) 
          (LEAFENTRY : LeafEntry (keyval val ke ve xe) =
                  LeafNode (btnode val ptr0 le true First Last nval)),
          let n := btnode val ptr0 le true First Last nval : node val in
          forall (H0 : numKeys n = Fanout)
          (H : node_integrity (btnode val ptr0 le true First Last nval))
          (k : key) (fri : Z)
          (HFRI : findRecordIndex n k = fri)
          (vnewnode : val)
         (H1 : vnewnode <> nullval),
         let nleft := btnode val ptr0 le true First false nval : node val in
         forall (PTRXE : isptr xe) (allent_end : list (val * (val + val)))
         (H3 : Zlength allent_end = Fanout + 1 - fri)
         (FRIRANGE : 0 <= fri <= Fanout)
         (H5 : key_repr ke = key_repr k)
         (H4 : 0 <= fri < Zlength (map entry_val_rep (le_to_list (nth_first_le le fri)) ++ allent_end))
         (FRILENGTH : Zlength (le_to_list (nth_first_le le fri)) = fri),
semax (func_tycontext f_splitnode Vprog Gprog [])
  (EX ent_end : list (val * (val + val)),
   PROP (fri <= Fanout <= Fanout;
   Zlength ent_end = Fanout - Fanout)
   LOCAL (temp _i (Vint (Int.repr Fanout));
   temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
   lvar _allEntries (tarray tentry 16) v_allEntries;
   temp _node nval; temp _entry pe)
   SEP (mem_mgr gv; btnode_rep nleft;
   btnode_rep (empty_node true false Last vnewnode);
   data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inr xe) pe;
   data_at Tsh (tarray tentry 16)
     (map entry_val_rep (le_to_list (nth_first_le le fri)) ++
      (Vptrofs (Ptrofs.repr (k_ k)), inr (force_val (sem_cast_pointer xe)))
      :: map entry_val_rep (le_to_list (suble fri Fanout le)) ++ ent_end) v_allEntries;
   entry_rep (keyval val ke ve xe))) splitnode_main_if_part2
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX newx : val,
         PROP ( )
         LOCAL ()
         SEP (mem_mgr gv;
         btnode_rep
           (splitnode_left
              (btnode val ptr0 le true First Last nval)
              (keyval val ke ve xe));
         entry_rep
           (splitnode_right
              (btnode val ptr0 le true First Last nval)
              (keyval val ke ve xe) newx);
         data_at Ews tentry
           (key_repr
              (splitnode_key
                 (btnode val ptr0 le true First Last nval)
                 (keyval val ke ve xe)), inl newx) pe))%assert)
     (stackframe_of f_splitnode)).
Proof.
   intros. unfold splitnode_main_if_part2. abbreviate_semax.
   subst fri; set (fri := findRecordIndex n k) in *.
    pose (H2:=True).
    Intros ent_end.
    deadvars!.
    pose (e:=keyval val ke ve xe).
    rewrite unfold_btnode_rep with (n:=nleft).
    unfold nleft. Intros ent_end0.
    forward.                    (* node->numKeys=8 *)
    sep_apply insert_rep. fold e.
    rewrite le_split with (le:=insert_le le e) (i:=Middle) by
        (simpl in H0; rewrite numKeys_le_insert; rewrite H0; rewrite Middle_eq; rewrite Fanout_eq; omega).
    rewrite le_iter_sepcon_app.
    
    forward_if (PROP ( )
    LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
           lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
    SEP (mem_mgr gv; btnode_rep (splitnode_left n e); btnode_rep (empty_node true false Last vnewnode);
         data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inr xe) pe;
         data_at Tsh (tarray tentry 16) 
            (map entry_val_rep (le_to_list (nth_first_le le fri)) 
             ++ (Vptrofs (Ptrofs.repr (k_ k)), inr (force_val (sem_cast_pointer xe))) 
              :: map entry_val_rep (le_to_list (suble fri Fanout le)) ++ ent_end) v_allEntries;
          le_iter_sepcon (skipn_le (insert_le le e) Middle))).
    {                           (* fri < 8 *)
      Intros.
      unfold Sfor.              (* both forward_loop and forward_for_simple_bound fail here *)
      forward.                  (* i=tgtIdx *)
      forward_loop (EX i:Z, EX le_end:list(val*(val+val)), PROP(fri <= i <= Middle)
LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
       lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _i (Vint (Int.repr i)))
SEP (mem_mgr gv; le_iter_sepcon (nth_first_le (insert_le le e) Middle);
          le_iter_sepcon (skipn_le (insert_le le e) Middle); malloc_token Ews tbtnode nval;
     data_at Ews tbtnode
       (Val.of_bool true,
       (Val.of_bool First,
       (Val.of_bool false,
       (Vint (Int.repr 8),
       (optionally getval nullval ptr0,
        map entry_val_rep (le_to_list (nth_first_le (insert_le le e) i)) ++ le_end))))) nval;
     optionally btnode_rep emp ptr0; btnode_rep (empty_node true false Last vnewnode);
     data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inr xe) pe;
     data_at Tsh (tarray tentry 16)
       (map entry_val_rep (le_to_list (nth_first_le le fri)) ++
        (Vptrofs (Ptrofs.repr (k_ k)), inr (force_val (sem_cast_pointer xe)))
        :: map entry_val_rep (le_to_list (suble fri Fanout le)) ++ ent_end) v_allEntries))%assert.
      - Exists fri.
        Exists (map entry_val_rep (le_to_list(skipn_le le fri)) ++ ent_end0).
        entailer!.
        set (fri := findRecordIndex n k) in *.
        rewrite le_split with (i:=fri) (le:=le) at 1.
        rewrite le_to_list_app.
        replace (nth_first_le (insert_le le e) fri) with (nth_first_le le fri).
        rewrite map_app.
        rewrite app_assoc. cancel.
        rewrite insert_fri with (fri:=fri) (key0:=ke).
        rewrite nth_first_app_same1. auto.
        rewrite numKeys_nth_first. auto.
        simpl in H0. rewrite H0. omega. unfold e. simpl. auto.
        apply FRI_repr. auto.
        simpl in H0. rewrite H0. omega.
      -                         (* loop body *)
        Intros i.
        Intros le_end.             
        forward_if.
        + assert(HINSERT: (map entry_val_rep (le_to_list (nth_first_le le fri)) 
                                      ++ (Vptrofs (Ptrofs.repr (k_ k)), inr (force_val (sem_cast_pointer xe)))
                                        :: map entry_val_rep (le_to_list (suble fri Fanout le)) ++ ent_end) 
                       = map entry_val_rep (le_to_list (insert_le le e)) ++ ent_end).
          { rewrite insert_fri with (fri:=fri) (key0:=ke).
            rewrite le_to_list_app, map_app.
            simpl. rewrite H5.
            rewrite suble_skip. unfold key_repr.
            rewrite <- app_assoc. simpl.
            unfold k_; rewrite Ptrofs.repr_unsigned; auto.
            unfold n in H0. simpl in H0. auto.      
            unfold e. simpl. auto. reflexivity.
            rewrite FRI_repr with (key2:=k) by auto. auto.
          } 
          rewrite HINSERT.
          assert(HENTRY: exists ei, nth_entry_le i (insert_le le e) = Some ei).
          { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0. rep_omega.  }
          destruct HENTRY as [ei HENTRY].  
          assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
          { eapply integrity_leaf_insert. simpl in H. destruct H. eauto. unfold e in HENTRY.
            eauto. }
          destruct HEI as [ki [vi [xi HEI]]]. subst ei.
          assert_PROP(isptr xi).
          { apply le_iter_sepcon_split in HENTRY.
            gather_SEP (le_iter_sepcon (nth_first_le (insert_le le e) Middle))
                       (le_iter_sepcon (skipn_le (insert_le le e) Middle)).
            replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
            { entailer!. rewrite le_split with (i:=Middle) (le:= (insert_le le e)) at 3.
              rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
              rewrite H0. rep_omega. }
            rewrite HENTRY. simpl entry_rep. entailer!. }
          rename H11 into XIPTR.
          assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep (le_to_list (insert_le le e)) ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
          { intros. apply Znth_to_list'. auto. }
          assert(0 <= i < 8) by omega.
          assert_PROP(Zlength le_end > 0).
          { entailer!.
            clear - H14 H11 H0. simplify_value_fits in H14.
            destruct H14, H1, H2, H3, H4.
            simplify_value_fits in H5. destruct H5.
            rewrite Zlength_app, Zlength_map in H5. rewrite le_to_list_length in H5.
            rewrite numKeys_nth_first in H5. omega.
            simpl in H0. rewrite numKeys_le_insert. rewrite H0. rep_omega.  }            
          rename H12 into LEEND.
          forward.              (* t'20=allEntries[i]->key *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->key=t'20 *)
          forward.              (* t'19=allEntries[i]->ptr.record *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->ptr.record = t'19 *)
          forward.              (* i=i+1 *)
          Exists (i+1).
          Exists (sublist 1 (Zlength le_end) le_end). entailer!.
          
          rewrite upd_Znth_twice.
          rewrite upd_Znth_same.
          rewrite upd_Znth_app2.
          rewrite !Zlength_map.
          rewrite le_to_list_length.
          rewrite numKeys_nth_first.
          replace(i-i) with 0 by omega.
          rewrite upd_Znth0. fold (Z.succ i).
          rewrite nth_first_increase with (e:=(keyval val ki vi xi)).
          rewrite le_to_list_app. simpl. rewrite map_app, <- app_assoc.
          cancel.
          auto.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
          rewrite !Zlength_map.
          rewrite le_to_list_length. rewrite numKeys_nth_first. rep_omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
          rewrite Zlength_app.
          rewrite !Zlength_map.
          rewrite le_to_list_length. rewrite numKeys_nth_first.
          omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
          rewrite Zlength_app.
          rewrite !Zlength_map.
          rewrite le_to_list_length. rewrite numKeys_nth_first.
          omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
        + 
          assert(i=8) by rep_omega.
          forward.              (* break *)
          entailer!.
          unfold n, splitnode_left.
          rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) true First false nval).
          Exists le_end.
          cancel. Opaque nth_first_le. simpl.
          rewrite numKeys_nth_first.  rewrite <- Middle_eq. simpl. cancel.
          simpl in H0. rewrite numKeys_le_insert. rewrite H0. rep_omega.
    } 
    {                           (* fri >= 8 *)
      forward.                  (* skip *)
      entailer!.
      set (fri := findRecordIndex n k) in *.
      assert((Middle <=? fri) = true).
      { clear -H8. rewrite Middle_eq. apply Z.leb_le. omega.  }
      unfold splitnode_left, n.
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) true First false nval).
      assert(SPLITLE: le_to_list le = le_to_list (nth_first_le le Middle) ++ le_to_list (skipn_le le Middle)).
      { rewrite le_split with (i:=Middle) at 1. rewrite le_to_list_app. auto.
        simpl in H0. rewrite H0. rewrite Middle_eq, Fanout_eq. omega. }
      rewrite SPLITLE.
      rewrite map_app, <- app_assoc.
      Exists (map entry_val_rep (le_to_list (skipn_le le Middle)) ++ ent_end0).
      simpl. rewrite numKeys_nth_first.
      rewrite nth_first_insert with (k:=ke). cancel.
      unfold e. simpl. auto.
      rewrite FRI_repr with (key2:=k). simpl. rewrite Middle_eq.
      change (findRecordIndex' le k 0) with fri.
      omega.
      auto. simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega.
    }
    rewrite unfold_btnode_rep with (n:=empty_node true false Last vnewnode).
    simpl. Intros ent_empty.
    assert(HINSERT: (map entry_val_rep (le_to_list (nth_first_le le fri))
                              ++ (Vptrofs (Ptrofs.repr (k_ k)), inr xe)
                               :: map entry_val_rep (le_to_list (suble fri Fanout le)) ++ ent_end) 
                            = map entry_val_rep (le_to_list (insert_le le e)) ++ ent_end).
    { rewrite insert_fri with (fri:=fri) (key0:=ke).
      rewrite le_to_list_app, map_app.
      simpl. rewrite H5.
      rewrite suble_skip. unfold key_repr.
      unfold n in H0. simpl in H0. rewrite <- app_assoc. simpl.
      unfold k_; rewrite Ptrofs.repr_unsigned;  reflexivity. rep_omega.
      simpl in H0. rewrite H0. auto.
      unfold e. simpl. auto.
      rewrite FRI_repr with (key2:=k) by auto. auto.
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
        map entry_val_rep (le_to_list(suble Middle i (insert_le le e))) ++ ent_right)))))
       vnewnode;
     data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inr xe) pe;
     data_at Tsh (tarray tentry 16) (map entry_val_rep (le_to_list (insert_le le e)) ++ ent_end) v_allEntries;
     le_iter_sepcon (skipn_le (insert_le le e) Middle))))%assert.                             
    
    { entailer!. rewrite suble_nil. Exists ent_empty. entailer!.
      simplify_value_fits in H11. decompose [and] H11.  simplify_value_fits in H23.
         destruct H23. rewrite Z.add_simpl_r.  assumption.  }
    {                           (* loop body *)
      assert(HENTRY: exists ei, nth_entry_le i (insert_le le e) = Some ei).
      { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0.
        rewrite Fanout_eq in H8. simpl in H8. rep_omega. }
      destruct HENTRY as [ei HENTRY].  
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_leaf_insert. simpl in H. destruct H. eauto. unfold e in HENTRY.
        eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY.
        rewrite unfold_btnode_rep with (n:=splitnode_left n e).
        unfold splitnode_left. unfold n. Intros ent_left.
        gather_SEP (le_iter_sepcon (nth_first_le (insert_le le e) Middle)) (le_iter_sepcon (skipn_le (insert_le le e) Middle)).
        replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
        { entailer!. rewrite le_split with (i:=Middle) (le:= (insert_le le e)) at 3.
          rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
          rewrite H0. rep_omega.  }
        rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into XIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep (le_to_list (insert_le le e)) ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. apply Znth_to_list'. auto. }

      forward.                  (* t'18=allEntries[i]->key *)
      apply prop_right; rep_omega.
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->key=t'18 *)
      apply prop_right; rep_omega.
      forward.                  (* t'17=allEntries[i]->ptr.record *)
      apply prop_right; rep_omega.
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->ptr.record=t'17 *)
      entailer!.
      rename ent_right into x.
(*      rewrite Fanout_eq in H9. simpl in H9. assert(Zlength x = 23 - i) by omega. *)
      Exists (sublist 1 (Zlength x) x). entailer!.
      { list_solve. }
      assert(8 <= i < 16).
      { clear - H8. rep_omega. } 
      
      rewrite upd_Znth_twice by list_solve.
      rewrite upd_Znth_same by list_solve.
      rewrite upd_Znth_app2.
      rewrite !Zlength_map.
      rewrite le_to_list_length.
      rewrite numKeys_suble.
      simpl. replace (i - 8 - (i - Middle)) with 0 by rep_omega.
      rewrite upd_Znth0. fold (Z.succ i).
      rewrite suble_increase with (e:=(keyval val ki vi xi)).
      rewrite le_to_list_app. simpl. rewrite map_app, <- app_assoc.
      cancel.

      rep_omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
      auto.
      rep_omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega.
      rewrite !Zlength_map.
      rewrite le_to_list_length. rewrite numKeys_suble. rep_omega.
      rep_omega. 
      rewrite numKeys_le_insert. simpl in H0. rewrite H0. rep_omega. 
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
     assert(HSUB: suble Middle (Z.succ Fanout) (insert_le le e) = skipn_le (insert_le le e) Middle).
      { apply suble_skip; [rep_omega|]. rewrite numKeys_le_insert. unfold n in H0. simpl in H0. rewrite H0.
        auto.  }
    rewrite HSUB.
    rewrite Middle_eq.
    sep_apply (fold_btnode_rep ptr1).
    simpl. rewrite numKeys_le_skipn. rewrite numKeys_le_insert.
    simpl in H0. rewrite H0. reflexivity.
    rewrite numKeys_le_insert. 
    simpl in H0. rewrite H0. rep_omega.
    clear HSUB. 
    assert(NTHENTRY: exists emid, nth_entry_le Middle (insert_le le e) = Some emid).
    { apply nth_entry_le_in_range. unfold n in H0. simpl in H0. rewrite numKeys_le_insert.
      rewrite H0. rep_omega. } 
    destruct NTHENTRY as [emid NTHENTRY].
    assert(HZNTH: nth_entry_le Middle (insert_le le e) = Some emid) by auto.
    apply Znth_to_list' with (endle:=ent_end) in HZNTH.
    rewrite Middle_eq in HZNTH. simpl in HZNTH.
    
    forward.                    (* t'16=allEntries[8]->key *)
    { entailer!. rewrite HZNTH.
      destruct emid; simpl; auto. }
    rewrite HZNTH.
    forward.                    (* entry->key=t'16 *)
    forward.                    (* entry->ptr.child=newnode *)
    forward.                    (* return *)
    Exists vnewnode. fold e. simpl.
    rewrite NTHENTRY. entailer!.
    simpl. unfold splitnode_leafnode. cancel.
    rewrite <- Middle_eq.
    subst ptr1.
    destruct emid; simpl; cancel.
Qed.

