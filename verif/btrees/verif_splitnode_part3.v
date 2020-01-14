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

Definition splitnode_main_if_else_part2 : statement :=
 ltac:(let x := constr:(splitnode_main_if_else) in
         let x := eval hnf in x in
         match x with context [Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr ?M) tint)) ?S] =>
          exact (Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr M) tint)) S)
         end).

Lemma splitnode_main_ifelse_part2_proof:
 forall (Espec : OracleKind) (ptr0 : option (node val))
     (le : list (entry val)) (First Last : bool) (nval pe : val) 
     (gv : globals) (v_allEntries : val) (ke : key) (ce : node val)
    (LEAFENTRY : LeafEntry (keychild val ke ce) =
            LeafNode (btnode val ptr0 le false First Last nval)),
   let n := btnode val ptr0 le false First Last nval : node val in 
   forall (H0 : numKeys n = Fanout)
      (H : node_integrity (btnode val ptr0 le false First Last nval)) 
      (k : key) (fri : Z) 
      (HFRI : findRecordIndex n k = fri)
      (vnewnode : val)
      (H1 : vnewnode <> nullval)
     (nleft := btnode val ptr0 le false First false nval : node val)
     (PTRCE : isptr (getval ce))
     (allent_end : list (val * (val + val)))
    (H3 : Zlength allent_end = Fanout + 1 - fri)
     (FRIRANGE : 0 <= fri <= Fanout)
     (H5 : key_repr ke = key_repr k)
     (H4 : 0 <= fri < Zlength (map entry_val_rep ( (sublist 0 fri le)) ++ allent_end))
     (FRILENGTH : Zlength (map entry_val_rep ( (sublist 0 fri le))) =fri),
semax (func_tycontext f_splitnode Vprog Gprog [])
  (EX ent_end : list (val * (val + val)),
   PROP (fri <= Fanout <= Fanout;
   Zlength ent_end = Fanout - Fanout)
   LOCAL (temp _i (Vint (Int.repr Fanout));
   temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
   lvar _allEntries (tarray tentry 16) v_allEntries;
   temp _node nval; temp _entry pe)
   SEP (mem_mgr gv; btnode_rep nleft;
   btnode_rep (empty_node false false Last vnewnode);
   data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce))
     pe;
   data_at Tsh (tarray tentry 16)
     (map entry_val_rep ( (sublist 0 fri le)) ++
      (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce))
      :: map entry_val_rep ( (sublist fri Fanout le)) ++ ent_end)
     v_allEntries; entry_rep (keychild val ke ce)))
   splitnode_main_if_else_part2
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX newx : val,
         PROP ( )
         LOCAL ()
         SEP (mem_mgr gv;
         btnode_rep
           (splitnode_left (btnode val ptr0 le false First Last nval)
              (keychild val ke ce));
         entry_rep
           (splitnode_right (btnode val ptr0 le false First Last nval)
              (keychild val ke ce) newx);
         data_at Ews tentry
           (key_repr
              (splitnode_key (btnode val ptr0 le false First Last nval)
                 (keychild val ke ce)), inl newx) pe))%assert)
     (stackframe_of f_splitnode)).
Proof.
    intros. pose proof I.
    assert (H0': Zlength le = Fanout) by apply H0.
    unfold splitnode_main_if_else_part2.
    abbreviate_semax.
    subst fri.
    set (fri := findRecordIndex n k) in *.
    Intros ent_end.
    deadvars!.
    pose (e:=keychild val ke ce).
    rewrite unfold_btnode_rep with (n:=nleft).
    unfold nleft. Intros ent_end0.
    forward.                    (* node->numKeys=8 *)
    sep_apply insert_rep. fold e.
    rewrite <- (sublist_same 0 (Zlength (insert_le le e)) (insert_le le e)) by auto.
    rewrite (sublist_split 0 Middle (Zlength (insert_le le e)))
       by (simpl in H0; rewrite ?Zlength_insert_le; rewrite ?H0; rep_omega).
    rewrite iter_sepcon_app.
    
    forward_if (PROP ( )
    LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
           lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
    SEP (mem_mgr gv; btnode_rep (splitnode_left n e); btnode_rep (empty_node false false Last vnewnode);
         data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) pe;
         data_at Tsh (tarray tentry 16)
           (map entry_val_rep ( (sublist 0 fri le))
            ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce))
            :: map entry_val_rep ( (sublist fri Fanout le)) ++ ent_end) v_allEntries;
             iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e)))).
    {                           (* fri < 8 *)
      Intros.
      unfold Sfor.              (* both forward_loop and forward_for_simple_bound fail here *)
      forward.                  (* i=tgtIdx *)
      forward_loop (EX i:Z, EX le_end:list(val*(val+val)), 
         PROP( fri <= i <= Middle)
         LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
                     lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval;
                     temp _entry pe; temp _i (Vint (Int.repr i)))
SEP (mem_mgr gv; iter_sepcon entry_rep (sublist 0 Middle (insert_le le e));
          iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e)); malloc_token Ews tbtnode nval;
     data_at Ews tbtnode
       (Val.of_bool false,
       (Val.of_bool First,
       (Val.of_bool false,
       (Vint (Int.repr 8),
       (optionally getval nullval ptr0,
        map entry_val_rep ( (sublist 0 i (insert_le le e))) ++ le_end))))) nval;
     optionally btnode_rep emp ptr0;
     btnode_rep (empty_node false false Last vnewnode);
     data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) pe;
     data_at Tsh (tarray tentry 16)
       (map entry_val_rep ( (sublist 0 fri le)) ++
        (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce))
        :: map entry_val_rep ( (sublist fri Fanout le)) ++ ent_end) v_allEntries))%assert.
      - Exists fri.
        Exists (map entry_val_rep ((sublist fri (Zlength le) le)) ++ ent_end0).
        entailer!.
        set (fri := findRecordIndex n k) in *.
        apply derives_refl'; do 6 f_equal. rewrite <- app_ass. f_equal.
        rewrite <- map_app; f_equal.
        rewrite insert_fri with (fri:=fri) (key0:=ke); auto with typeclass_instances.
        autorewrite with sublist. auto.
        apply FRI_repr. auto.
      -                         (* loop body *)
        Intros i.
        Intros le_end.             
        forward_if.
        + assert(HINSERT: (map entry_val_rep ( (sublist 0 fri le))
                                       ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce))
                                        :: map entry_val_rep ( (sublist fri Fanout le)) ++ ent_end)
                                   = map entry_val_rep ( (insert_le le e)) ++ ent_end).
          { rewrite insert_fri with (fri:=fri) (key0:=ke); auto with typeclass_instances.
            rewrite map_app.
            simpl. rewrite H5.
            rewrite app_ass; f_equal.
            change (?A::?B++?C) with ((A::B)++C); f_equal.
            unfold n in H0. simpl in H0. rewrite H0.
            f_equal.   
            unfold key_repr.
            unfold k_; rewrite ?Ptrofs.repr_unsigned. auto.
            rewrite FRI_repr with (key2:=k) by auto. auto.
          } 
          rewrite HINSERT.
          assert(HENTRY: exists ei, nth_entry_le i (insert_le le e) = Some ei).
          { apply nth_entry_le_in_range. simpl in H0. rewrite Zlength_insert_le. rewrite H0.
            rep_omega. }
          destruct HENTRY as [ei HENTRY].  
          assert (HEI: exists ki ci, ei = keychild val ki ci).
          {simpl in H. destruct ptr0; try contradiction.
           eapply integrity_intern_insert; eassumption. }
          destruct HEI as [ki [ci HEI]]. subst ei.
          assert_PROP(isptr (getval ci)).
          { apply le_iter_sepcon_split in HENTRY.
            gather_SEP (iter_sepcon entry_rep (sublist 0 Middle (insert_le le e)))
                       (iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e))).
            replace_SEP 0 (iter_sepcon entry_rep (insert_le le e)).
            { entailer!. apply derives_refl'. rewrite <- iter_sepcon_app. f_equal.
              rewrite sublist_rejoin; try rep_omega. autorewrite with sublist; auto.
              rewrite Zlength_insert_le; rep_omega. }
            rewrite HENTRY. simpl entry_rep. entailer!. }
          rename H11 into CIPTR.
          assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep ( (insert_le le e)) ++ ent_end) = entry_val_rep (keychild val ki ci)).
          { intros. apply Znth_to_list'. auto. }
(*
          assert(0 <= i < 8).
          { split. omega. rewrite Int.signed_repr in H10. auto.
            rewrite Middle_eq in H9. simpl in H9. rep_omega. }
*)
          assert_PROP(Zlength le_end > 0).
          { entailer!. 
            clear - FRIRANGE H13 H0 H0' H9 H10. simplify_value_fits in H13. decompose [and] H13.
            simplify_value_fits in H6; destruct H6. clear - FRIRANGE H5  H0 H0' H9 H10.
            rewrite Zlength_app, Zlength_map in H5. 
            rewrite Zlength_sublist in H5; try omega.
            rewrite Zlength_insert_le. rep_omega. }            
          rename H11 into LEEND.
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
          apply derives_refl'; do 6 f_equal.
          pose proof (Zlength_insert_le _ le e).
          rewrite upd_Znth_twice by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          autorewrite with sublist.
          rewrite upd_Znth_same by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          rewrite upd_Znth_app2 by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          rewrite !Zlength_map.
          rewrite (sublist_split 0 i (i+1))  by rep_omega.
          rewrite map_app, app_ass. 
          rewrite Zlength_sublist by rep_omega. f_equal.
          autorewrite with sublist.
          rewrite upd_Znth0. fold (Z.succ i).
          rewrite (sublist_one i) by rep_omega.
          simpl; f_equal.
          clear - HENTRY. unfold nth_entry_le in HENTRY.
          apply Znth_to_list with (endle:=nil) in HENTRY.
          rewrite <- app_nil_end in HENTRY.
          rewrite HENTRY. reflexivity.
        + 
          forward.              (* break *)
          assert (i=Middle) by rep_omega. subst i.
          entailer!. unfold n, splitnode_left.
          rewrite unfold_btnode_rep with (n:=btnode val ptr0 (sublist 0 Middle (insert_le le e)) false First false nval).
          Exists le_end.
          cancel. 
          apply derives_refl'; do 7 f_equal. simpl.
          pose proof (Zlength_insert_le _ le e).
           rewrite Zlength_sublist by rep_omega. rep_omega.
    } 
    {                           (* fri >= 8 *)
      forward.                  (* skip *)
      entailer!.
      set (fri := findRecordIndex n k) in *.
      assert((Middle <=? fri)= true).
      { clear -H8. rewrite Middle_eq. apply Z.leb_le. omega. }
      unfold splitnode_left, n.
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 (sublist 0 Middle (insert_le le e)) false First false nval).
      assert(SPLITLE:  le =  (sublist 0 Middle le) ++  (sublist Middle (Zlength le) le)).
      { simpl in H0. rewrite sublist_rejoin by rep_omega. autorewrite with sublist; auto.  }
      rewrite SPLITLE.
      rewrite !map_app, <- app_assoc.
      Exists (map entry_val_rep (sublist Middle (Zlength le) le) ++ ent_end0).
      simpl. cancel.
      rewrite <- SPLITLE.
      apply derives_refl'; do 7 f_equal.
          pose proof (Zlength_insert_le _ le e).
           rewrite Zlength_sublist by rep_omega. rep_omega.
      rewrite nth_first_insert with (k:=ke); auto with typeclass_instances.
      rewrite FRI_repr with (key2:=k). simpl. rewrite Middle_eq. simpl.
      change (findRecordIndex' le k 0) with fri.
      omega.
      auto.
    }
    rewrite unfold_btnode_rep with (n:=empty_node false false Last vnewnode).
    simpl. Intros ent_empty.
    assert(HINSERT: (map entry_val_rep ( (sublist 0 fri le)) ++ (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) :: map entry_val_rep ( (sublist fri Fanout le)) ++ ent_end) = map entry_val_rep ( (insert_le le e)) ++ ent_end).
    { rewrite insert_fri with (fri:=fri) (key0:=ke); auto with typeclass_instances.
      rewrite map_app.
      simpl. rewrite H5.
      rewrite app_ass; f_equal.
      change (?A::?B++?C) with ((A::B)++C); f_equal. f_equal.
      unfold key_repr.
            unfold k_; rewrite ?Ptrofs.repr_unsigned. auto.
      f_equal. f_equal. simpl in H0; auto.
      rewrite FRI_repr with (key2:=k) by auto. auto.
    } 
    rewrite HINSERT.
    
    forward_for_simple_bound (Fanout + 1)
(EX i:Z, EX ent_right:list(val*(val+val)),
(PROP (Zlength ent_right + i - 9 = Fanout; 9 <= i <= Fanout+1)
     LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr fri));
     lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP (mem_mgr gv; btnode_rep (splitnode_left n e);
     malloc_token Ews tbtnode vnewnode;
     data_at Ews tbtnode
       (Vfalse, (Vfalse, (Val.of_bool Last, (Vint (Int.repr 0), (nullval,
       map entry_val_rep ((sublist (Z.succ Middle) i (insert_le le e))) ++ ent_right)))))
       vnewnode;
     data_at Ews tentry (Vptrofs (Ptrofs.repr (k_ k)), inl (getval ce)) pe;
     data_at Tsh (tarray tentry 16) (map entry_val_rep ( (insert_le le e)) ++ ent_end) v_allEntries;
     iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e)))))%assert.                             
    
    { abbreviate_semax.
      forward.                  (* i=9 *)
      Exists (Z.succ Middle). Exists ent_empty. entailer!. 
      simplify_value_fits in H11. destruct H11, H17, H18, H19, H20.
      clear - H21. assert (value_fits (tarray tentry 15) ent_empty). auto.
      simplify_value_fits in H. destruct H. rewrite Z.add_simpl_r. assumption. }
    {                           (* loop body *)
      Intros.
      assert(HENTRY: exists ei, nth_entry_le i (insert_le le e) = Some ei).
      { apply nth_entry_le_in_range. simpl in H0. rewrite Zlength_insert_le. rewrite H0.
        rewrite Fanout_eq in H8. simpl in H8. rewrite Fanout_eq. destruct H8.
        simpl in H11. auto. rep_omega. }
      destruct HENTRY as [ei HENTRY].  
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { simpl in H; destruct ptr0; try contradiction.
        eapply integrity_intern_insert; eassumption.  }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY.
        rewrite unfold_btnode_rep with (n:=splitnode_left n e).
        unfold splitnode_left. unfold n. Intros ent_left.
        gather_SEP (iter_sepcon entry_rep (sublist 0 Middle (insert_le le e))) (iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e))).
        replace_SEP 0 ( iter_sepcon entry_rep (insert_le le e)).
        { entailer!. apply derives_refl'.
          rewrite <- iter_sepcon_app. f_equal. simpl in H0.
          rewrite sublist_rejoin by (rewrite ?Zlength_insert_le; rep_omega).
          autorewrite with sublist; auto. }
        rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into CIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (map entry_val_rep ( (insert_le le e)) ++ ent_end) = entry_val_rep (keychild val ki ci)).
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
      apply prop_right; rep_omega.
      entailer!.
      rename ent_right into x.
      rewrite Fanout_eq in CIPTR. simpl in CIPTR. assert(Zlength x = 24 - i) by omega.
      Exists (sublist 1 (Zlength x) x). entailer!.
      {rewrite Zlength_sublist. rep_omega. rep_omega. apply Z.le_refl. } 

    pose proof I.
(*
      assert(9 <= i < 16)%nat.
      { clear - H10 H8. assert(HH: 9 <= i <= 16) by auto.
        destruct H10. apply Z2Nat.inj_le in H0. apply Z2Nat.inj_le in H.
        destruct H8. apply Z2Nat.inj_lt in H2.
        simpl in H, H0, H1, H2. split. omega. omega. omega. omega. omega. omega. omega. omega. }
*) 
      apply derives_refl'; do 6 f_equal.
          pose proof (Zlength_insert_le _ le e).
      autorewrite with sublist.
          rewrite upd_Znth_twice by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          rewrite upd_Znth_same by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          rewrite upd_Znth_app2 by (autorewrite with sublist; rewrite Zlength_sublist; rep_omega).
          rewrite !Zlength_map.
      rewrite Zlength_sublist by rep_omega.
      replace (i - 9 - (i - Z.succ Middle)) with 0 by rep_omega.
      rewrite upd_Znth0. fold (Z.succ i).
      rewrite (sublist_split (Z.succ Middle) i (Z.succ i)) by rep_omega.
      rewrite map_app, app_ass. f_equal.
      rewrite (sublist_one i) by rep_omega. simpl.
      f_equal.
          clear - HENTRY. unfold nth_entry_le in HENTRY.
          apply Znth_to_list with (endle:=nil) in HENTRY.
          rewrite <- app_nil_end in HENTRY.
          rewrite HENTRY. reflexivity.
    }
    Intros ent_right.
    forward.                    (* newnode->numKeys=7 *)
    assert(NTHENTRY: exists emid, nth_entry_le Middle (insert_le le e) = Some emid).
    { apply nth_entry_le_in_range. unfold n in H0. simpl in H0. rewrite Zlength_insert_le.
      rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega. }
    destruct NTHENTRY as [emid NTHENTRY].
    assert (HEMID: exists ki ci, emid = keychild val ki ci).
    { simpl in H; destruct ptr0; try contradiction.
      eapply integrity_intern_insert; eassumption. }
    destruct HEMID as [ki [ci HEMID]].
    assert_PROP(isptr (getval ci)).
    { apply le_iter_sepcon_split in NTHENTRY.
      rewrite unfold_btnode_rep with (n:=splitnode_left n e).
      simpl (splitnode_left n e). destruct (btnode val ptr0 (sublist 0 Middle (insert_le le e)) false First false nval) eqn:HDES. Intros ent_end1. inv HDES.
      gather_SEP (iter_sepcon entry_rep (sublist 0 Middle (insert_le le e))) (iter_sepcon entry_rep (sublist Middle (Zlength (insert_le le e)) (insert_le le e))).
      replace_SEP 0 (iter_sepcon entry_rep (insert_le le e)).
      { entailer!. apply derives_refl'. rewrite <- iter_sepcon_app. f_equal.
        simpl in H0. rewrite sublist_rejoin by (rewrite ?Zlength_insert_le; rep_omega).
        autorewrite with sublist; auto. }
      rewrite NTHENTRY. simpl entry_rep. entailer!. }
    assert(HZNTH: nth_entry_le Middle (insert_le le e) = Some emid) by auto.
    apply Znth_to_list' with (endle:=ent_end) in HZNTH.
    rewrite Middle_eq in HZNTH. simpl in HZNTH.
    forward.                    (* t'5=allEntries[8]->ptr.child *)
     { entailer!. fold Inhabitant_entry_val_rep. rewrite HZNTH.
       simpl. apply isptr_is_pointer_or_null. auto. }
     fold Inhabitant_entry_val_rep. rewrite HZNTH. rewrite HEMID. simpl.
     forward.                   (* nenode->ptr0=t'5 *)
     replace  (sublist Middle (Zlength (insert_le le e))  (insert_le le e))
           with (emid :: sublist (Z.succ Middle) (Zlength (insert_le le e))   (insert_le le e)).
     2:{ simpl in H0.
          rewrite (sublist_split Middle (Z.succ Middle)); try rep_omega.
          rewrite (sublist_one Middle (Z.succ Middle)); try rep_omega.
         apply (Znth_to_list'' _ _ _ nil) in NTHENTRY. rewrite <- app_nil_end in NTHENTRY. rewrite NTHENTRY.
         simpl; auto. rewrite Zlength_insert_le; rep_omega.  rewrite Zlength_insert_le; rep_omega.
      }
    simpl iter_sepcon.
    change Vfalse with (Val.of_bool false).
    pose (ptr1 := Some ci).
    change (getval ci) with (optionally getval nullval ptr1).
    replace (entry_rep emid) with (optionally btnode_rep emp ptr1)
       by (rewrite HEMID; reflexivity).
    rewrite sub_repr. fold (Z.succ Fanout).
    rewrite <- H0' at 2.
    rewrite Zlength_insert_le.
    sep_apply (fold_btnode_rep ptr1).
    simpl.
    rewrite Zlength_sublist. rewrite H0'. rep_omega.
    rewrite H0'; rep_omega. rewrite Zlength_insert_le.
    rewrite H0'. rep_omega.
    subst ptr1. simpl. 
     
     forward.                    (* t'16=allEntries[8]->key *)
     { entailer!. fold Inhabitant_entry_val_rep. rewrite HZNTH. simpl. auto. }
     fold Inhabitant_entry_val_rep. rewrite HZNTH.
     forward.                    (* entry->key=t'16 *)
     forward.                    (* entry->ptr.child=newnode *)
     forward.                    (* return *)
     Exists vnewnode. fold e. simpl.
     unfold nth_entry_le in NTHENTRY; rewrite NTHENTRY. entailer!.
     simpl. rewrite <- (Zlength_insert_le _ le e); autorewrite with sublist; apply derives_refl.
Qed.


