(** * verif_putrecord.v : Correctness proof of putEntry and RL_PutRecord *)

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
Require Import btrees.btrees_spec. (*
Require Import verif_newnode.
Require Import verif_movetokey.
Require Import verif_currnode.
Require Import verif_entryindex.*)

Require Import btrees.verif_splitnode_part0. (*for Lemma upd_Znth_twice*)

(* integrity of a new root *)
Lemma cons_integrity: forall r childe ke vnewnode,
    root_integrity r ->
    root_integrity childe ->
    node_depth childe = node_depth r ->
    root_integrity (btnode val (Some r) (keychild val ke childe :: nil) false true true vnewnode).
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
    root_wf (btnode val (Some r) (keychild val ke childe :: nil) false true true vnewnode).
Proof.
  intros.
  unfold root_wf. intros.
  inv H1.
-
  red. simpl. autorewrite with sublist. rep_lia.
-
  apply H; auto.
-
  apply H0. apply sub_trans with m; try assumption.
  inv H9. constructor. inv H3.
Qed.

Lemma key_in_le_true {X} k: forall l, @key_in_le X k l = true ->
      exists front e tail, l=front++e::tail /\ Ptrofs.eq (entry_key e) k = true /\
                           forall ee, In ee front -> Ptrofs.eq (entry_key ee) k = false.
Proof. induction l; simpl; intros. inv H.
  remember (Ptrofs.eq (entry_key a) k); symmetry in Heqb; destruct b.
  + clear H. exists nil, a, l. split3; trivial.
    intros. inv H.
  + destruct (IHl H) as [front [e [tail [L [E F]]]]]; clear IHl; subst.
    exists (a::front), e, tail; split3; trivial.
    intros. inv H0; trivial; auto. 
Qed.

Lemma key_in_le_false {X} k: forall l, @key_in_le X k l = false ->
      forall e, In e l -> Ptrofs.eq (entry_key e) k = false.
Proof. induction l; simpl; intros. contradiction.
  destruct H0; subst.
  + destruct (Ptrofs.eq (entry_key e) k); trivial.
  + destruct (Ptrofs.eq (entry_key a) k). inv H. auto.
Qed.

Lemma Znth_option_key_in_le_true {X e}: forall l i, Znth_option i l = Some e ->
      @key_in_le X (entry_key e) l = true.
Proof.
  induction l; simpl; intros.
  rewrite Znth_option_nil in H; discriminate. 
  destruct (zeq 0 i). 
  + subst. rewrite Znth_option_0 in H; trivial. inv H; simpl. rewrite Ptrofs.eq_true; trivial.
  + rewrite Znth_option_cons in H; trivial. apply IHl in H. rewrite H.
    destruct (Ptrofs.eq (entry_key a) (entry_key e)); trivial.
Qed.


Lemma body_putEntry: semax_body Vprog Gprog f_putEntry putEntry_spec.
Proof.
  start_function. rename H7 into ENotVundef.
  rename H0 into Hleaf. assert (EN:= LeafEntry_entry_numrec_one Hleaf).
  rename H1 into H0; rename H2 into H1; rename H3 into H2; rename H4 into H3;
  rename H5 into H4; rename H6 into H5;
  rename H8 into EMPENTRY.
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  destruct r as [root prel]. pose (r:=(root,prel)).
  forward.                      (* t'44=cursor->level *)
  forward_if.                   (* if t'44=-1 *)
  (* split root case *)
  - assert(c=[]).
    { apply (f_equal Int.signed) in H6. apply partial_complete_length' in H.
      assert(Zlength c - 1 < MaxTreeDepth) by lia.
      autorewrite with norm in H6. destruct c. auto. rewrite Zlength_cons in H6.
      rewrite Zsuccminusone in H6. rep_lia. unfold correct_depth. lia. } subst c.
    destruct H. { exfalso. inv H. inv H7. }
    assert(HE: exists ke childe, e = keychild val ke childe).
    { simpl in H3. destruct e. simpl in H3. pose proof (node_depth_nonneg root); lia.
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
    { entailer!.  (*unfold cursor_rep. Exists anc_end. Exists idx_end. unfold r. cancel.*)
       } clear anc_end. clear idx_end.
    forward_if(PROP (vnewnode <> nullval)
                     LOCAL (temp _currNode__1 vnewnode; temp _t'59 (Vint (Int.repr (-1))); 
                                 gvars gv; temp _cursor pc; temp _newEntry pe; 
                                 temp _key (Vptrofs oldk)) 
                     SEP (cursor_rep [] r pc; mem_mgr gv; 
                            btnode_rep (empty_node false true true vnewnode); 
                            relation_rep (root, prel); (* entry_rep e; *) data_at (*Tsh*)sh tentry (entry_val_rep e) pe)).
(*    + apply denote_tc_test_eq_split.
      replace (vnewnode) with (getval (empty_node false true true vnewnode)). entailer!.
      simpl. auto.
      entailer!.
*)
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
      { entailer!.  (* simplify_value_fits in H14.
        destruct H14, H20, H21, H22, H23.
        clear -H24.
        assert(value_fits (tarray tentry 15) ent_end). auto.
        simplify_value_fits in H. destruct H.
        simpl in H. rewrite Fanout_eq. simpl. auto.*)  }
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
(*      entailer!. 
        pose proof (get_depth_nonneg (root,prel)).
        rewrite !Int.signed_repr by rep_lia.
        rep_lia.
*)
      forward.                  (* t'45=cursor->relation *)
      forward.                  (* t'46=cursor->relation *)
      forward.                  (* t'47=t'46->numRecords *)
      forward.                  (* t'45->numRecords=t'47+1 *)
      forward.                  (* cursor->ancestors[0]=currnode_1 *)
      deadvars!.
      pose (newroot:= btnode val
                             (Some root)
                             (keychild val ke childe :: nil)
                             false
                             true
                             true
                             vnewnode).
      forward_call(newroot,oldk,([]:cursor val),pc,(newroot,prel) (*,
                      (get_numrec (root,prel) + node_numrec childe - 1 + 1) *) ). (* movetoKey(currnode_1,key,cursor,0 *)
      unfold relation_rep. unfold newroot. simpl. fold newroot.
      * rewrite upd_Znth_same 
             by (rewrite HENTEND; rewrite Fanout_eq; simpl; lia).
        rewrite upd_Znth_twice
             by (rewrite HENTEND; rewrite Fanout_eq; simpl; lia).
        apply force_val_sem_cast_neutral_isptr in ISPTRV.
        assert(force_val(sem_cast_pointer vnewnode) = vnewnode).
        { apply Some_inj in ISPTRV. auto. }
        rewrite !add_repr.
        replace (get_depth (newroot, prel)) with (get_depth (root, prel)+1). 
          2:{ unfold newroot, get_depth. simpl get_root.
               simpl in H3. simpl. rewrite H3.
               pose proof (node_depth_nonneg root).
               rewrite (Z.max_l (Z.succ (node_depth root))) by lia.
               rewrite Z.max_l by lia. lia. 
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
        rewrite upd_Znth0_old. cancel.
        normalize. rewrite Fanout_eq in HENTEND; lia. (* cancel. *)
      * assert (Hri: root_integrity (get_root (newroot, prel))).
                  apply cons_integrity; auto. clear - H3. simpl in H3. lia.
        split. split. simpl; auto. auto. split; auto.
        split. 
        unfold correct_depth.
        assert(get_depth (newroot,prel)= node_depth newroot). unfold get_depth. simpl. auto. rewrite H8.
        assert(get_depth (root,prel) = node_depth root). unfold get_depth. simpl. auto.
        rewrite H9 in H0.
        simpl. simpl in H3. rewrite H3. 
               pose proof (node_depth_nonneg root).
               rewrite (Z.max_l (Z.succ (node_depth root))) by lia.
               rewrite Z.max_l by lia. lia. 
        simpl. split. auto. apply cons_wf. auto. simpl in H2. auto.
      * forward.                (* return *)
        (*Exists ([vnewnode]:list val). entailer!.*)
(*
        destruct (putEntry val [] (root,prel) (keychild val ke childe) oldk [] nullval) as [newc newr] eqn:HNEW.
        unfold relation_rep.
        rewrite putEntry_equation. simpl. fold newroot.
        replace (Vptrofs (Ptrofs.repr (get_numrec (root, prel) + node_numrec childe - 1 + 1)))
                with
               (Vptrofs (Ptrofs.repr (get_numrec (newroot, prel)))). cancel.
        { repeat apply f_equal. unfold newroot. unfold get_numrec. simpl. lia. }
*)
  - destruct c as [|[currnode entryidx] c'] eqn:HC.
    { exfalso. apply H6. normalize.  }
    forward_call(r,c,pc (*,(get_numrec (root, prel) + entry_numrec e - 1) *) ).       (* t'26=currnode(cursor) *)
    { unfold r. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. 
      rewrite HC. simpl. cancel. }
    { rewrite HC. unfold r. split.
      destruct H. right. auto. left. unfold ne_partial_cursor.
      destruct H. split; auto. simpl. rewrite Zlength_cons in *. rep_lia.
      unfold correct_depth. lia. }
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
      forward_call(r,c,pc (*,(get_numrec r + entry_numrec e - 1) *) ). (* t'12=entryindex(cursor) *)
      { unfold relation_rep. unfold r. cancel. rewrite HC. fold currnode. cancel. }
      { split. rewrite <- HC in H. unfold r.
      right. auto. 
      unfold correct_depth. unfold r. lia. }
      forward_call(r,c,pc (* ,(get_numrec r + entry_numrec e - 1) *) ). (* t'13=currnode(cursor) *)
      { split. rewrite <- HC in H. unfold r. right. auto.
        unfold correct_depth. unfold r. lia. }
      rewrite HC. simpl. rewrite SUBREP. fold currnode.
      rewrite unfold_btnode_rep with (n:=currnode) at 1. unfold currnode.
      Intros ent_end.
      forward.                  (* t'41=t'13->numKeys *)
      sep_apply (fold_btnode_rep ptr0). fold currnode.
      clear ent_end. deadvars!.
      assert (H99: 0 <= entryidx < Zlength le /\ partial_cursor_correct c' (btnode val ptr0 le isLeaf First Last x) root ). {
          destruct H. red in H; simpl in H.
          destruct (Znth_option entryidx le) eqn:?H; try contradiction.
          destruct e0; try contradiction.
          apply Znth_option_some in H9. split. auto. apply H. }
      destruct H99 as [H99 PCC].
      assert (H98: Zlength le <= Fanout). {apply H2 in SUBNODE.
          apply node_wf_numKeys in SUBNODE. simpl in SUBNODE. rep_lia. }

     forward_if(PROP ( )
     LOCAL (temp _t'56 (Vint (Int.repr (Zlength (node_le currnode))));
     temp _t'15 (Vint (Int.repr entryidx)); 
     temp _cursor pc; temp _newEntry pe; temp _key (Vptrofs oldk);
     temp _t'17 (Val.of_bool(key_in_le (entry_key e) le))) (* new local *)
     SEP (btnode_rep currnode; malloc_token Ews trelation prel;
     data_at Ews trelation
       (getval root,
       (Vptrofs (Ptrofs.repr (get_numrec (root, prel)(* + entry_numrec e - 1*))),
       Vint (Int.repr (get_depth r)))) prel; btnode_rep currnode -* btnode_rep root;
     cursor_rep ((currnode, entryidx) :: c') r pc; (*entry_rep e;*)
     data_at sh tentry (entry_val_rep e) pe; mem_mgr gv)).
      {
        sep_apply modus_ponens_wand.
        forward_call(r,c,pc (* ,(get_numrec (root, prel) + entry_numrec e - 1) *) ). (* t'15=currnode(cursor) *)
        { entailer!. unfold relation_rep. unfold r. cancel.
          fold currnode. rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel. }
        { split. rewrite <- HC in H. unfold r. right. auto.
        unfold correct_depth. unfold r. lia. }
        forward_call(r,c,pc (* ,(get_numrec (root, prel) + entry_numrec e - 1) *) ). (* t'12=entryindex(cursor) *)
        { split. rewrite <- HC in H. unfold r.
          right. auto. 
          unfold correct_depth. unfold r. lia. }
        unfold relation_rep. unfold r. rewrite SUBREP. rewrite HC. simpl.
        rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last x) at 1.
        Intros currnode_end. (*
        assert (IsLongEntry: is_long (let (x0, _) := entry_val_rep e in x0)).
        { clear - H5. destruct e; simpl; trivial. }*)
        forward.                (* t'42=t'15->entries[t'16]->key *)
        { rewrite Fanout_eq in H98. apply prop_right; rep_lia. }
        (* we need to know in he leaf case that the cursor points to where the key should be if already in the relation *)
        { entailer!. destruct (Znth_option_in_range entryidx le) as [entry E]. trivial. clear - E.
          erewrite (Znth_to_list' entryidx le entry); [| apply E].
          unfold entry_val_rep. destruct entry; simpl; trivial. }
        forward. 
        { clear - H5. entailer!. destruct e; simpl; trivial. }
        forward.
        fold r. fold currnode. entailer!. 
        + clear H9 Ppc SUBREP H12 H13 H14 H15 H16 H17 H18 H19 H6 H8 PNpe PNx PNpc SUBNODE.
          destruct (Znth_option_in_range entryidx le H99) as [en Hen].
          erewrite Znth_to_list' in * by (apply Hen).
          assert (EnLe: In en le). { apply Znth_option_e' in Hen; subst en. apply Znth_In. trivial. }
          remember (key_in_le (entry_key e) le) as KeyInLe; symmetry in HeqKeyInLe.
          unfold Val.of_bool.
          destruct e; simpl in H10; [ clear H10 | simpl in Hleaf; contradiction]. simpl in *. clear Hleaf.
          remember (entry_val_rep en) as ENVRe. destruct ENVRe as [vn sn]; simpl in *.

          (* destruct en; inversion HeqENVRe; subst vn sn; clear HeqENVRe; simpl in *.*
             Maybe it's enough to just remember that vn is a Vptrofs, rather than dsicriminating on sn, like this:*)
          assert (XX: exists kn, vn = Vptrofs kn /\ kn = entry_key en). { destruct en; simpl in HeqENVRe; inv HeqENVRe; eexists; split; reflexivity. }
          destruct XX as [kn [? KN]]; subst vn kn; simpl.
          unfold sem_cast_i2bool, Int64.eq. simpl. rewrite 2 int64_unsigned_ptrofs_toint by trivial. (*64bit*)
          specialize (Ptrofs.eq_spec (entry_key en) k). 
          specialize (Znth_option_key_in_le_true _ _ Hen); intros HH.
          destruct (Ptrofs.eq (entry_key en) k); intros X.
          * subst k. rewrite HH in HeqKeyInLe. subst KeyInLe. rewrite zeq_true; trivial.
         (* * destruct (zeq (Ptrofs.unsigned (entry_key en)) (Ptrofs.unsigned k)).
            - assert (Ptrofs.repr (Ptrofs.unsigned (entry_key en)) = Ptrofs.repr (Ptrofs.unsigned k)). rewrite e; trivial.
               rewrite 2 Ptrofs.repr_unsigned in H6. elim X; trivial. 
            - (*simpl. destruct KeyInLe; trivial.xx
              destruct (key_in_le_true _ _ HeqKeyInLe) as [HT [entryE [TL [EE1 [EE2 EE3]]]]]; clear HeqKeyInLe.
              apply Ptrofs.same_if_eq in EE2. subst k le. apply in_app_or in EnLe. destruct EnLe.
              ++ apply Ptrofs.same_if_eq. specialize (EE3 _ H6).  admit.
              ++  apply EE3 in H6.  specialize (key_in_le_false _ _ HeqKeyInLe _ EnLe); intros X; simpl in X.
             simpl. unfold Ptrofs.eq in X. rewrite Int64.eq_false; simpl; trivial.
             unfold Ptrofs.to_int64. if_tac in X. discriminate. intros N. clear - N H6.
             rewrite <- ! int64_unsigned_ptrofs_toint in N; trivial.
             rewrite <- ! int64_unsigned_ptrofs_toint in H6; trivial.
             rewrite ! Int64.repr_unsigned in N. rewrite N in H6. apply H6; trivial.*)
         (* lia.  
(*           Search key_in_le.
          destruct (zeq (Ptrofs.unsigned (entry_key en)) (Ptrofs.unsigned k)).*)
          destruct KeyInLe.
            * destruct (key_in_le_true _ _ HeqKeyInLe) as [HT [entryE [TL [EE1 [EE2 EE3]]]]]; clear HeqKeyInLe.
              (*Here is where we need to know in he leaf case that the cursor points to where the key should be if already,
               to deduce that k0=k *)
              destruct (). if_tac.
              unfold entry_key in EE2.  destruct entryE; simpl. 2:{ simpl in *. contradiction. simpl in Hleaf; contradiction.
              simpl in *. Print entry_depth.
              -- destruct entryE; simpl in H11; simpl.
                 ++ apply Ptrofs.same_if_eq in EE2; subst k0.
                    unfold entry_val_rep in H11. destruct en; simpl in H11; simpl in *. subst le.
         rewrite map_app in H3. simpl in H3. simpl in *.
                remember (entry_val_rep e) as EVRe. destruct EVRe as [v s]; simpl in *.
                remember (entry_val_rep en) as ENVRe. destruct ENVRe as [vn sn]; simpl in *.
                unfold force_val, both_long. simpl. unfold entry_val_rep in HeqENVRe, HeqEVRe.
                destruct e; destruct en; simpl in *.
              -- inversion HeqENVRe; subst vn sn; clear HeqENVRe.
                 inversion HeqEVRe; subst v s; clear HeqEVRe. simpl.
                 destruct (Int64.eq_dec (Ptrofs.to_int64 k0) (Ptrofs.to_int64 k)).
                 ++ rewrite e, Int64.eq_true; simpl; trivial.
                 ++ rewrite Int64.eq_false; trivial. simpl. subst.
                 remember (Int64.eq (Ptrofs.to_int64 k0) (Ptrofs.to_int64 k)) as b; symmetry in Heqb; destruct b; simpl; trivial.
                 ++  rewrite Int64.eq_spec.
                 destruct ().  ; inv HeqEVRe. simpl. 
                 Znth_to_list'Search Znth_option. subst k0.

                remember (Znth entryidx (map entry_val_rep le)) as e3. destruct e3; simpl in *.
                destruct v; try contradiction.
                destruct v0; try contradiction. clear - Heqee.  Print entry_val_rep. Print entry_key.*)
                admit. *)
           * destruct KeyInLe. 
             ++ destruct (key_in_le_true _ _ HeqKeyInLe) as [FRONT [E [TAIL [EE1 [EE2 EE3]]]]].
                destruct (zeq (Ptrofs.unsigned (entry_key en)) (Ptrofs.unsigned k)); simpl; trivial.
                admit.
             ++ specialize (key_in_le_false _ _ HeqKeyInLe _ EnLe); intros Y; simpl in Y.
                unfold Ptrofs.eq in Y. destruct (zeq (Ptrofs.unsigned (entry_key en)) (Ptrofs.unsigned k)). inv Y. simpl; trivial.

         + (*replace (get_numrec r + entry_numrec e - 1) with (get_numrec r) by lia.*)
           clear. cancel.
           subst currnode. Exists currnode_end. cancel. 
           fold btnode_rep. fold entry_rep. cancel.
      } {                       (* entryidx > numKeys isn't possible *)
        normalize in H8. lia.
      } {
        forward_if.
        - forward_call.
          { unfold relation_rep. subst r. simpl. 
            sep_apply modus_ponens_wand. cancel. }
          { split. 
            + right. subst currnode r; apply H.
            + unfold correct_depth; subst r. lia. }
          (*partial attemp by Lennart from here on*)
          forward_call.
          { split. 
            + right. subst currnode r; apply H.
            + unfold correct_depth; subst r. lia. }
          forward.
          { entailer!. clear - H13 ENotVundef Hleaf.
            destruct e; [ unfold tentry in * | simpl in Hleaf; contradiction].
            simpl. simpl in *.
            assert (TC: tc_val (Tpointer tvoid noattr) v0).
            { rewrite value_fits_eq in H13; simpl in H13.
              rewrite 2 value_fits_eq in H13; simpl in H13.
              rewrite value_fits_eq in H13; simpl in H13.
              apply H13; trivial. }
            clear - TC. destruct v0; simpl in *; trivial. }
          simpl. rewrite SUBREP; clear SUBREP; Intros.
          rewrite unfold_btnode_rep at 1; Intros ent_end.
          forward.
          { entailer!. }
          forward. (*simpl.
          destruct e ; simpl in Hleaf; [ simpl in *| contradiction]. clear H4 H5 H6 EN EMPENTRY.
Parameter listval:list val.
          Exists listval. rewrite putEntry_equation. simpl. rewrite H8.
          remember (update_partial_cursor_rel c' (root, prel) (btnode val ptr0 (update_le (keyval val k v v0) le) true First Last x)) as updPC.
          destruct updPC as [newc newr]. cancel.
          specialize (update_partial_snd_r _ (root, prel) c' (btnode val ptr0 (update_le (keyval val k v v0) le) true First Last x)); simpl; intros HPrel.
          destruct newr as [n prel0]; simpl; simpl in *.
          rewrite <- HequpdPC in HPrel; simpl in HPrel; subst prel0.
          assert (Lcc': Zlength newc = Zlength c').
            { rewrite 2 Zlength_correct.
              rewrite (update_partial_same_length _ c' (root, prel) (btnode val ptr0 (update_le (keyval val k v v0)le) true First Last x)).
              rewrite <- HequpdPC; trivial. }
          rewrite sepcon_comm. apply sepcon_derives.
          { subst currnode; unfold cursor_rep; rewrite ! Zlength_cons. subst r. simpl. 
            apply exp_derives. intros AE. apply exp_derives; intros IS. cancel.
            rewrite Lcc'.
            apply derives_refl'. f_equal. f_equal. f_equal. f_equal.
            + f_equal. f_equal.
              exploit (update_partial_cursor_result' root entryidx n prel c' newc (btnode val ptr0 (update_le (keyval val k v v0) le) true First Last x)).
              trivial. intros XX; inv XX; trivial. (*maybe we're leaving an item of type node val on the shelf here*)
            + apply update_partial_cursor_rel_getval in HequpdPC; rewrite HequpdPC; trivial. }
          { cancel. subst r. Search btnode_rep. Locate LeafEntry_entry_numrec_one.
            unfold complete_cursor, complete_cursor_correct_rel in H. simpl in H; destruct H.
             Search subnode. (newc, (n, prel)) =
           update_partial_cursor_rel c' (root, prel)
             (btnode val ptr0 (update_le (keyval val k v v0) le) true First Last x):
        (getval n = getval root /\ get_numrec (n, prel) = get_numrec (root, pefl) /\ get_depth (n, prel) = get_depth (root, prel))))) .


Search btnode_rep. destruct newr as [xx prel0 ]destruct r0; simpl; simpl in Heqp. cancel.
            subst r; simpl in *.
            assert (n=root) by admit. subst n.
            rewrite Vptrofs_repr_Vlong_repr; trivial. cancel.
            admit. (*LHS of magic wand is too specific?*) }
          
            rewrite Lcc'. 
            specialize update_partial_cursor_result'; intros XX.
            apply derives_refl'. f_equal. f_equal. f_equal. f_equal.
            + f_equal. f_equal.
              specialize (XX root entryidx xx prel c' c (btnode val ptr0 (update_le e le) true First Last x)).
              rewrite <- Heqp in XX. exploit XX; clear XX. trivial. intros XX; inv XX. rewrite H19; trivial.
            + apply update_partial_cursor_rel_getval in Heqp; rewrite Heqp; trivial. }

 (btnode val ptr0 (update_le e le) true First Last x)); rewrite <- Heqp; intros X; simpl in X; subst prel.
          

          remember (putEntry val ((btnode val ptr0 le true First Last x, entryidx) :: c') (root, prel) e oldk listval nullval )
            as put; destruct put as [put1 put2].
          cancel.
          rewrite putEntry_equation, H8 in Heqput.
          unfold update_currnode_cursor_rel in Heqput. simpl in Heqput.
          remember (update_partial_cursor_rel c' (root, prel) (btnode val ptr0 (update_le e le) true First Last x)) as p; destruct p; inv Heqput.
          specialize (update_partial_snd_r _ (root, prel) c' (btnode val ptr0 (update_le e le) true First Last x)); rewrite <- Heqp; intros X; simpl in X; subst prel.
          rewrite sepcon_comm. apply sepcon_derives.
          { subst currnode; unfold cursor_rep; rewrite ! Zlength_cons. subst r. simpl. destruct r0 as [xx prel]; simpl; simpl in Heqp.
            apply exp_derives. intros AE. apply exp_derives; intros IS. cancel.
            assert (Lcc': Zlength c = Zlength c').
            { rewrite 2 Zlength_correct.
              rewrite (update_partial_same_length _ c' (root, prel) (btnode val ptr0 (update_le e le) true First Last x)).
              rewrite <- Heqp; trivial. }
            rewrite Lcc'. 
            specialize update_partial_cursor_result'; intros XX.
            apply derives_refl'. f_equal. f_equal. f_equal. f_equal.
            + f_equal. f_equal.
              specialize (XX root entryidx xx prel c' c (btnode val ptr0 (update_le e le) true First Last x)).
              rewrite <- Heqp in XX. exploit XX; clear XX. trivial. intros XX; inv XX. rewrite H19; trivial.
            + apply update_partial_cursor_rel_getval in Heqp; rewrite Heqp; trivial. }

          { unfold relation_rep. destruct r0; simpl; simpl in Heqp. cancel.
            subst r; simpl in *.
            assert (n=root) by admit. subst n.
            rewrite Vptrofs_repr_Vlong_repr; trivial. cancel.
            admit. (*LHS of magic wand is too specific?*) }*) admit.
            

        (* we need have key_in_le precisely at entry_index *)
        -
          sep_apply modus_ponens_wand.
          forward_call(r,c,pc (* ,(get_numrec (root, prel) + entry_numrec e - 1) *) ). (* t'11=currnode(cursor) *)
          { entailer!. unfold relation_rep. unfold r. cancel. fold currnode. 
             rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel.  }
          { split. rewrite <- HC in H. unfold r.
            right. auto. 
            unfold correct_depth. unfold r. lia. }
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
            forward_call(r,c,pc (* ,(get_numrec (root, prel) + entry_numrec e - 1) *) ). (* t'4=entryindex(cursor) *)
      { unfold relation_rep. unfold r. cancel. rewrite HC. cancel. }
      { split. right. rewrite HC. auto. unfold correct_depth. unfold r. lia. }
      forward_call(r,c,pc (* ,(get_numrec (root, prel) + entry_numrec e - 1) *) ). (* t'11=currnode(cursor) *)
      { split. rewrite <- HC in H. unfold r.
        right. auto. 
        unfold correct_depth. unfold r. lia. }
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

Lemma AscendToParent_nil: forall c k, [] = @AscendToParent val c k -> c=[].
Proof. induction c; simpl; trivial.
intros. destruct a. destruct c. inv H. remember (@isNodeParent val n k). destruct b. inv H.
  apply IHc in H. inv H.
Qed.

Lemma gotokey_complete: forall c r key,
    complete_cursor c r ->
    complete_cursor (goToKey c r key) r.
Proof.
Admitted.

Lemma putentry_complete: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    complete_cursor newc newr.
Proof.
Admitted.

(*Lennart: here's a partial proof- perhaps this is not true...*)
Lemma putentry_depth: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    correct_depth r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    correct_depth newr.
Proof.
Admitted.
(*Lennart: here's a partial proof- perhaps this is not true...
unfold correct_depth. induction c; simpl; intros.
+ rewrite putEntry_equation in H1. destruct r as [root prel].
  inv H1. simpl. unfold get_depth in *. simpl in *.
  rewrite (Z.max_l _ 0). 2: apply entry_depth_nonneg.
  admit.
+ rewrite putEntry_equation in H1. destruct r as [root prel]. destruct a as [n z].
  destruct n. 
  - remember (key_in_le (entry_key e) le) as b; destruct b.
    * destruct isLeaf.
      ++ inv H1. remember (update_partial_cursor_rel c (root, prel)
          (btnode val entryzero (update_le e le) true First Last x)). destruct p.
         inv H3. unfold get_depth in *; destruct newr; simpl in *. Search update_partial_cursor_rel.
         admit.
      ++ 
Admitted.*)

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
unfold get_numrec. intros. 
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
     temp _key (Vptrofs key); temp _record (Vptrofs record))
     SEP (data_at_ Tsh (Tstruct _Entry noattr) v_newEntry; mem_mgr gv; relation_rep r;
     cursor_rep c r pc)).
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False). entailer!. contradiction.
  - fold tentry.
    forward.                    (* newentry.ptr.record=record *)
    forward.                    (* newentry.key=key *)
    assert_PROP(isptr v_newEntry).
    { entailer!. }
    forward_call(c,pc,r,key).   (* gotokey(cursor,key) *)
    { split3; auto. unfold correct_depth. lia. }
    (*forward_call((goToKey c r key),pc,r,(keyval val key record recordptr), v_newEntry, key, gv).*) (* putEntry(cursor,newEntry,key *)
    forward_call((goToKey c r key),pc,r,(keyval val key record (Vptrofs record)), v_newEntry, key, gv, Tsh). (* putEntry(cursor,newEntry,key *)
    (*+ instantiate (Frame := []). apply force_val_sem_cast_neutral_isptr in H5. apply Some_inj in H5. rewrite <- H5.
      rewrite <- H5.x
      simpl. 
      simpl. replace((get_numrec r + 1 - 1)) with (get_numrec r) by lia. cancel.      
*)
    + split3; auto. left. apply gotokey_complete. auto. apply I.
      split3; auto. split; auto. simpl.
      split3; auto.
      assert(complete_cursor (goToKey c r key) r) by (apply gotokey_complete; auto).
      apply eq_sym.
      apply complete_depth. auto. auto. split3; auto. discriminate. split. lia. apply writable_readable_share; apply writable_share_top.
    + Intros newx.
      destruct(putEntry val (goToKey c r key) r) as [newc newr] eqn:HPUTENTRY.
      forward_call(newc,pc,newr). (* RL_MoveToNext(cursor) *)
      * cancel.
      * apply gotokey_complete with (key:=key) in H.
        split3.
        eapply putentry_complete. eauto. eauto.
        eapply putentry_depth. eauto. unfold correct_depth. lia. eauto.
        split.
        eapply putentry_wf. eauto. auto. eauto.
        eapply putentry_integrity. eauto. auto. eauto.
      * forward.                (* return *)
        unfold RL_PutRecord_rel. 
        Exists (RL_MoveToNext newc newr) newr.
        entailer!. exists newx. unfold RL_PutRecord.
        rewrite HPUTENTRY. auto.
Qed.
