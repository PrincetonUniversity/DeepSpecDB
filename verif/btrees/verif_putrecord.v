(** * verif_putrecord.v : Correctness proof of putEntry and RL_PutRecord *)

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
Require Import verif_movetokey.
Require Import verif_currnode.
Require Import verif_entryindex.
Require Import verif_splitnode_part0.

(* integrity of a new root *)
Lemma cons_integrity: forall r childe ke vnewnode,
    root_integrity r ->
    root_integrity childe ->
    node_depth childe = node_depth r ->
    root_integrity (btnode val (Some r) (cons val (keychild val ke childe) (nil val)) false true true vnewnode).
Proof.
  unfold root_integrity; intros.
  inv H2.
-
  simpl.
  rewrite <- H1.
  apply ileo.
-
  eauto.
-
  apply H0.
  eapply sub_trans. eassumption.
  inv H10.
  apply sub_refl.
  inv H4.
Qed.

(* well_formedness of a new root *)
Lemma cons_wf: forall r childe ke vnewnode,
    root_wf r ->
    root_wf childe ->
    root_wf (btnode val (Some r) (cons val (keychild val ke childe) (nil val)) false true true vnewnode).
Proof.
  intros.
  unfold root_wf. intros.
  inv H1.
-
  red. simpl. rep_omega.
-
  apply H; auto.
-
  apply H0. apply sub_trans with m; try assumption.
  inv H9. constructor. inv H3.
Qed.

Lemma body_putEntry: semax_body Vprog Gprog f_putEntry putEntry_spec.
Proof.
  start_function.
  rename H6 into EMPENTRY.
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  destruct r as [root prel]. pose (r:=(root,prel)).
  forward.                      (* t'44=cursor->level *)
  forward_if.                   (* if t'44=-1 *)
  (* split root case *)
  - assert(c=[]).
    { apply (f_equal Int.signed) in H6. apply partial_complete_length' in H.
      assert(Zlength c - 1 < MaxTreeDepth) by omega.
      autorewrite with norm in H6. destruct c. auto. rewrite Zlength_cons in H6.
      rewrite Zsuccminusone in H6. rep_omega. unfold correct_depth. omega. } subst c.
    destruct H. { exfalso. inv H. inv H7. }
    assert(HE: exists ke childe, e = keychild val ke childe).
    { simpl in H3. destruct e. simpl in H3. pose proof (node_depth_nonneg root); omega.
      exists k. exists n. auto. }
    destruct HE as [ke [childe HE]].
    assert_PROP(isptr (getval childe)).
    { rewrite HE. simpl entry_rep. entailer!. } rename H7 into ISPTRC.      
    forward_call(false,true,true, gv). (* t'1=createnewnode(false,true,true) *)
    Intros vnewnode.
    assert_PROP(isptr vnewnode).
    entailer!. rename H7 into ISPTRV.
    gather_SEP (malloc_token Ews tcursor pc)
               (data_at Ews tcursor _ pc). replace_SEP 0 (cursor_rep [] r pc).
    { entailer!. unfold cursor_rep. Exists anc_end. Exists idx_end. unfold r. cancel.
       } clear anc_end. clear idx_end.
    forward_if(PROP (vnewnode <> nullval) LOCAL (temp _currNode__1 vnewnode; 
                     temp _t'59 (Vint (Int.repr (-1))); gvars gv; temp _cursor pc; temp _newEntry pe; temp _key (key_repr oldk)) SEP (cursor_rep [] r pc; mem_mgr gv; btnode_rep (empty_node false true true vnewnode); relation_rep (root, prel) (get_numrec(root,prel) + entry_numrec e - 1); entry_rep e; data_at Tsh tentry (entry_val_rep e) pe)).
    + apply denote_tc_test_eq_split.
      replace (vnewnode) with (getval (empty_node false true true vnewnode)). entailer!.
      simpl. auto.
      entailer!.
    + forward.                  (* skip *)
      entailer!.
    + assert_PROP(False). unfold empty_node. entailer!. contradiction.
    + unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
      forward.                  (* t'52=cursor->relation *)
      unfold relation_rep. Intros.
      assert_PROP(isptr (getval root)). { entailer!. } rename H8 into ISPTRR.
      forward.                  (* t'53=t'52->root *)
      unfold empty_node.
      rewrite unfold_btnode_rep. Intros ent_end. simpl.
      assert_PROP(Zlength ent_end = Fanout).
      { entailer!. simplify_value_fits in H14.
        destruct H14, H20, H21, H22, H23.
        clear -H24.
        assert(value_fits (tarray tentry 15) ent_end). auto.
        simplify_value_fits in H. destruct H.
        simpl in H. rewrite Fanout_eq. simpl. auto. }
      rename H8 into HENTEND.
      forward.                  (* currnode1->ptr0=t'53 *)
      forward.                  (* currnode1->numKeys=1 *)
      subst e. simpl.
      forward.                  (* t'53=newEntry->key *)
      Opaque Znth.
      forward.                  (* currNode_1->entries[O] -> key = t'53 *)
      forward.                  (* t'52 = newEntry->ptr.child *)
      forward.                  (* currnode_1->entries[0].ptr.child = t'52 *)
      forward.                  (* t'51 = cursor->relation. *)
      forward.                  (* t'51->root=currnode_1 *)
      forward.                  (* t'48=cursor->relation *)
      forward.                  (* t'49=cursor->relation *)
      forward.                  (* t'50=t'49->depth *)
      forward.                  (* t'48->depth=t'50+1 *)
      entailer!. 
        pose proof (get_depth_nonneg (root,prel)).
        rewrite !Int.signed_repr by rep_omega.
        rep_omega.
      forward.                  (* t'45=cursor->relation *)
      forward.                  (* t'46=cursor->relation *)
      forward.                  (* t'47=t'46->numRecords *)
      forward.                  (* t'45->numRecords=t'47+1 *)
      forward.                  (* cursor->ancestors[0]=currnode_1 *)
      deadvars!.
      pose (newroot:= btnode val
                             (Some root)
                             (cons val (keychild val ke childe) (nil val))
                             false
                             true
                             true
                             vnewnode).
      forward_call(newroot,oldk,([]:cursor val),pc,(newroot,prel),
                      (get_numrec (root,prel) + node_numrec childe - 1 + 1)). (* movetoKey(currnode_1,key,cursor,0 *)
      unfold relation_rep. unfold newroot. simpl. fold newroot.
      * rewrite upd_Znth_same 
             by (rewrite HENTEND; rewrite Fanout_eq; simpl; omega).
        rewrite upd_Znth_twice
             by (rewrite HENTEND; rewrite Fanout_eq; simpl; omega).
        apply force_val_sem_cast_neutral_isptr in ISPTRV.
        assert(force_val(sem_cast_pointer vnewnode) = vnewnode).
        { apply Some_inj in ISPTRV. auto. }
        rewrite !add_repr.
        replace (get_depth (newroot, prel)) with (get_depth (root, prel)+1). 
          2:{ unfold newroot, get_depth. simpl get_root.
               simpl in H3. simpl. rewrite H3.
               pose proof (node_depth_nonneg root).
               rewrite (Z.max_l (Z.succ (node_depth root))) by omega.
               rewrite Z.max_l by omega. omega. 
           }
        cancel.
        unfold subcursor_rep.
        Exists (upd_Znth 0 anc_end vnewnode).
        Exists idx_end. Exists (-1).
        simpl. cancel. rewrite unfold_btnode_rep with (n:=newroot). unfold newroot.
        Exists (sublist 1 (Zlength ent_end) ent_end).
        simpl.
        assert(force_val(sem_cast_pointer(getval root)) = getval root).
        { apply force_val_sem_cast_neutral_isptr in ISPTRR. apply Some_inj in ISPTRR.
          auto. }
        assert(force_val(sem_cast_pointer(getval childe)) = getval childe).
        { apply force_val_sem_cast_neutral_isptr in ISPTRC. apply Some_inj in ISPTRC.
          auto. }
        rewrite upd_Znth0. cancel.
        normalize. cancel.
      * assert (Hri: root_integrity (get_root (newroot, prel))).
                  apply cons_integrity; auto. clear - H3. simpl in H3. omega.
        split. split. simpl; auto. auto. split; auto.
        split. 
        unfold correct_depth.
        assert(get_depth (newroot,prel)= node_depth newroot). unfold get_depth. simpl. auto. rewrite H8.
        assert(get_depth (root,prel) = node_depth root). unfold get_depth. simpl. auto.
        rewrite H9 in H0.
        simpl. simpl in H3. rewrite H3. 
               pose proof (node_depth_nonneg root).
               rewrite (Z.max_l (Z.succ (node_depth root))) by omega.
               rewrite Z.max_l by omega. omega. 
        simpl. split. auto. apply cons_wf. auto. simpl in H2. auto.
      * forward.                (* return *)
        Exists ([vnewnode]:list val). entailer!.
        destruct (putEntry val [] (root,prel) (keychild val ke childe) oldk [] nullval) as [newc newr] eqn:HNEW.
        unfold relation_rep.
        rewrite putEntry_equation. simpl. fold newroot.
        replace (Vptrofs (Ptrofs.repr (get_numrec (root, prel) + node_numrec childe - 1 + 1)))
                with
               (Vptrofs (Ptrofs.repr (get_numrec (newroot, prel)))). cancel.
        { repeat apply f_equal. unfold newroot. unfold get_numrec. simpl. omega. }
  - destruct c as [|[currnode entryidx] c'] eqn:HC.
    { exfalso. apply H6. normalize.  }
    forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)).       (* t'26=currnode(cursor) *)
    { unfold r. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. 
      rewrite HC. simpl. cancel. }
    { rewrite HC. unfold r. split.
      destruct H. right. auto. left. unfold ne_partial_cursor.
      destruct H. split; auto. simpl. rewrite Zlength_cons in *. rep_omega.
      unfold correct_depth. omega. }
    rewrite HC. simpl.
    assert(SUBNODE: subnode currnode root).
    { destruct H. destruct H. apply complete_cursor_subnode in H. simpl in H. auto.
      destruct H. apply partial_cursor_subnode in H. simpl in H. auto. }
    assert(SUBREP: subnode currnode root) by auto.
    apply subnode_rep in SUBREP.
    destruct currnode as [ptr0 le isLeaf First Last x].
    pose(currnode := btnode val ptr0 le isLeaf First Last x). simpl.
    rewrite SUBREP. fold currnode.
    rewrite unfold_btnode_rep with (n:=currnode) at 1. unfold currnode. Intros ent_end.
    forward.                    (* t'27=t'26->isLeaf *)
    { destruct isLeaf; entailer!. }
    forward_if.

    +                           (* leaf node *)
      apply complete_partial_leaf in H. 2:(rewrite H7; simpl; auto).
      sep_apply (fold_btnode_rep ptr0). fold currnode.
      sep_apply modus_ponens_wand. fold r. clear ent_end.
      forward_call(r,c,pc,(get_numrec r + entry_numrec e - 1)). (* t'12=entryindex(cursor) *)
      { unfold relation_rep. unfold r. cancel. rewrite HC. fold currnode. cancel. }
      { split. rewrite <- HC in H. unfold r.
      right. auto. 
      unfold correct_depth. unfold r. omega. }
      forward_call(r,c,pc,(get_numrec r + entry_numrec e - 1)). (* t'13=currnode(cursor) *)
      { split. rewrite <- HC in H. unfold r. right. auto.
        unfold correct_depth. unfold r. omega. }
      rewrite HC. simpl. rewrite SUBREP. fold currnode.
      rewrite unfold_btnode_rep with (n:=currnode) at 1. unfold currnode.
      Intros ent_end.
      forward.                  (* t'41=t'13->numKeys *)
      sep_apply (fold_btnode_rep ptr0). fold currnode.
      clear ent_end. deadvars!.
      assert (H99: 0 <= entryidx < numKeys_le le). {
          destruct H. red in H; simpl in H.
          destruct (nth_entry_le entryidx le) eqn:?H; try contradiction.
          destruct e0; try contradiction.
          apply nth_entry_le_some in H9. auto. }
      assert (H98: numKeys_le le <= Fanout). {apply H2 in SUBNODE.
          apply node_wf_numKeys in SUBNODE. simpl in SUBNODE. rep_omega. }
     forward_if(PROP ( )
     LOCAL (temp _t'56 (Vint (Int.repr (numKeys currnode)));
     temp _t'15 (Vint (Int.repr entryidx)); 
     temp _cursor pc; temp _newEntry pe; temp _key (key_repr oldk);
     temp _t'17 (Val.of_bool(key_in_le (entry_key e) le))) (* new local *)
     SEP (btnode_rep currnode; malloc_token Ews trelation prel;
     data_at Ews trelation
       (getval root,
       (Vptrofs (Ptrofs.repr (get_numrec (root, prel) + entry_numrec e - 1)),
       Vint (Int.repr (get_depth r)))) prel; btnode_rep currnode -* btnode_rep root;
     cursor_rep ((currnode, entryidx) :: c') r pc; entry_rep e;
     data_at Ews tentry (entry_val_rep e) pe)).
      {
        sep_apply modus_ponens_wand.
        forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)). (* t'15=currnode(cursor) *)
        { entailer!. unfold relation_rep. unfold r. cancel.
          fold currnode. rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel. }
        { split. rewrite <- HC in H. unfold r. right. auto.
        unfold correct_depth. unfold r. omega. }
        forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)). (* t'12=entryindex(cursor) *)
        { split. rewrite <- HC in H. unfold r.
          right. auto. 
          unfold correct_depth. unfold r. omega. }
        unfold relation_rep. unfold r. rewrite SUBREP. rewrite HC. simpl.
        rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last x) at 1.
        Intros currnode_end.
        forward.                (* t'42=t'15->entries[t'16]->key *)
        apply prop_right; rep_omega.
        (* we need to know in he leaf case that the cursor points to where the key should be if already in the relation *)
        admit.
        admit.        
      } {                       (* entryidx > numKeys isn't possible *)
        normalize in H8. omega.
      } {
        forward_if.
        - admit.
        (* we need have key_in_le precisely at entry_index *)
        -
          sep_apply modus_ponens_wand.
          forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)). (* t'11=currnode(cursor) *)
          { entailer!. unfold relation_rep. unfold r. cancel. fold currnode. 
             rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel. }
          { split. rewrite <- HC in H. unfold r.
            right. auto. 
            unfold correct_depth. unfold r. omega. }
          unfold relation_rep. unfold r. rewrite SUBREP. rewrite HC. simpl.
          rewrite unfold_btnode_rep with (n:= (btnode val ptr0 le isLeaf First Last x)) at 1.
          Intros ent_end.
          forward.              (* t'35=t'11->numKeys *)
          forward_if.
          +
            sep_apply (fold_btnode_rep ptr0).
            clear ent_end.
            sep_apply modus_ponens_wand.
            deadvars!.
            forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)). (* t'4=entryindex(cursor) *)
      { unfold relation_rep. unfold r. cancel. rewrite HC. cancel. }
      { split. right. rewrite HC. auto. unfold correct_depth. unfold r. omega. }
      forward_call(r,c,pc,(get_numrec (root, prel) + entry_numrec e - 1)). (* t'11=currnode(cursor) *)
      { split. rewrite <- HC in H. unfold r.
        right. auto. 
        unfold correct_depth. unfold r. omega. }
      unfold relation_rep. unfold r. rewrite SUBREP.
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last x) at 1.
      Intros ent_end.
      rewrite HC. simpl.
      forward.                  (* i=t'5->numKeys *)
      admit.                    (* for loop *)
      
          + admit.
      }      
    +                           (* intern node *)
      admit.
all:fail.
Admitted.

Lemma gotokey_complete: forall c r key,
    complete_cursor c r ->
    complete_cursor (goToKey c r key) r.
Proof.
intros.
destruct H.
split; auto.
Admitted.

Lemma putentry_complete: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    complete_cursor newc newr.
Proof.
Admitted.

Lemma putentry_depth: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    correct_depth r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    correct_depth newr.
Proof.
Admitted.

Lemma putentry_wf: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    root_wf (get_root r) ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    root_wf (get_root newr).
Proof.
Admitted.

Lemma putentry_integrity: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    root_integrity (get_root r) ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    root_integrity (get_root newr).
Proof.
Admitted.

Lemma putentry_numrec: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    get_numrec r < Int.max_signed - 1 ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    get_numrec newr < Int.max_signed.
Proof.
Admitted.

Lemma complete_depth: forall c r,
    complete_cursor c r ->
    root_integrity (get_root r) ->
    cursor_depth c r = 0.
Proof.
Admitted.

Lemma body_RL_PutRecord: semax_body Vprog Gprog f_RL_PutRecord RL_PutRecord_spec.
Proof.
  start_function.
  forward_if(PROP (pc<>nullval)
     LOCAL (gvars gv; lvar _newEntry (Tstruct _Entry noattr) v_newEntry; temp _cursor pc;
     temp _key (key_repr key); temp _record recordptr)
     SEP (data_at_ Tsh (Tstruct _Entry noattr) v_newEntry; mem_mgr gv; relation_rep r (get_numrec r);
     cursor_rep c r pc; value_rep record recordptr)).
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False). entailer!. contradiction.
  - fold tentry.
    forward.                    (* newentry.ptr.record=record *)
    forward.                    (* newentry.key=key *)
    assert_PROP(isptr recordptr).
    { entailer!. }
    forward_call(c,pc,r,key,get_numrec r).   (* gotokey(cursor,key) *)
    { split3; auto. unfold correct_depth. omega. }
    forward_call((goToKey c r key),pc,r,(keyval val key record recordptr), v_newEntry, key, gv). (* putEntry(cursor,newEntry,key *)
    + instantiate (Frame := []). apply force_val_sem_cast_neutral_isptr in H5. apply Some_inj in H5. rewrite <- H5.
      rewrite <- H5.
      simpl.
      simpl. replace((get_numrec r + 1 - 1)) with (get_numrec r) by omega. cancel.      
    + split3; auto. left. apply gotokey_complete. auto.
      split3; auto. simpl.
      split3; auto.
      assert(complete_cursor (goToKey c r key) r) by (apply gotokey_complete; auto).
      apply eq_sym.
      apply complete_depth. auto. auto. split; auto. omega.
    + Intros newx.
      destruct(putEntry val (goToKey c r key) r) as [newc newr] eqn:HPUTENTRY.
      forward_call(newc,pc,newr,get_numrec newr). (* RL_MoveToNext(cursor) *)
      * cancel.
      * apply gotokey_complete with (key:=key) in H.
        split3.
        eapply putentry_complete. eauto. eauto.
        eapply putentry_depth. eauto. unfold correct_depth. omega. eauto.
        split.
        eapply putentry_wf. eauto. auto. eauto.
        eapply putentry_integrity. eauto. auto. eauto.
      * forward.                (* return *)
        Exists newx.
        entailer!. unfold RL_PutRecord.
        rewrite HPUTENTRY.
        cancel.
Qed.
