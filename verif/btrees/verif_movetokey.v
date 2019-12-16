(** * verif_movetokey.v : Correctness proof of moveToKey *)

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
Require Import index.
Require Import verif_findindex.

Lemma partial_correct_append: forall (c:cursor val) n i r child,
    partial_cursor_correct_rel c r ->
    next_node c (get_root r) = Some n ->
    nth_node i n = Some child ->
    partial_cursor_correct_rel ((n,i)::c) r.
Proof.
  intros. destruct c.
  simpl. simpl in H0. inv H0. rewrite H1. split; auto.
  simpl. rewrite H1. destruct p. split; auto.
  simpl in H0.
  split; auto.
  simpl in H. rewrite H0 in H. destruct H. auto.
Qed. 

Lemma body_moveToKey: semax_body Vprog Gprog f_moveToKey moveToKey_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
  unfold subcursor_rep. Intros anc_end. Intros idx_end. Intros length. unfold r.
  assert(CLENGTH: 0 <= Zlength c < 20).
  { unfold partial_cursor in H. destruct H. unfold correct_depth in H1.
    apply partial_rel_length in H. rep_omega. }
  assert(SUBNODE: subnode n root).
  { fold n in H2. unfold next_node in H2.
    destruct c as [|[n' i] c']. simpl in H2. inv H2. apply sub_refl.
    eapply sub_trans. apply nth_subnode in H2. eauto. unfold partial_cursor in H.
    destruct H. apply partial_cursor_subnode in H. simpl in H. auto. }
  assert (SUBREP: subnode n root) by auto. apply subnode_rep in SUBREP.
  assert (GETVAL: pn = getval n).
  { unfold n. simpl. auto. }
  assert_PROP(isptr pn).
  { unfold relation_rep. apply subnode_rep in SUBNODE. rewrite SUBNODE.
    rewrite GETVAL. Intros. entailer!. }
  assert(ISPTR: isptr pn) by auto. clear H4.
  
  forward.                      (* cursor->ancestors[level]=node *)
  forward.                      (* cursor->level = level *)
(*  gather_SEP 1 2.         (* the cursor, with a new node *) *)
  unfold relation_rep.
  rewrite SUBREP.
  rewrite unfold_btnode_rep at 1. unfold n. Intros. Intros ent_end.
  forward.                      (* t'3=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward_call (n,key).    (* t'1=findRecordIndex(node,key) *)
    + rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end. cancel.
    + forward.                  (* cursor->ancestorsIdx[level]=t'1 *)
      fold n. 
      sep_apply modus_ponens_wand.
      sep_apply fold_relation_rep; fold r.
      forward.                  (* return *)
      entailer!.
      unfold cursor_rep.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      cancel.
      pose (ii:=findRecordIndex' le key (ip 0)). fold ii.
      assert(moveToKey val (btnode val ptr0 le true First Last pn) key c = (n,ii)::c).
      { rewrite moveToKey_equation. simpl. fold n. fold ii. auto. }
      rename H4 into H13. rewrite H13. rewrite Zlength_cons.
      rewrite Zsuccminusone. autorewrite with sublist.
      rewrite upd_Znth_app2, upd_Znth_app2.
      autorewrite with sublist.
      rewrite upd_Znth0, upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. cancel.
      autorewrite with sublist; rep_omega. 
      autorewrite with sublist; rep_omega. 
  - forward_call(n,key).     (* t'2=findChildIndex(node,key) *)
    + rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end.
      cancel. 
    + split3.
      * unfold n. simpl. rewrite H4. auto.
      * unfold root_integrity in H0. unfold get_root in H0. simpl in H0. apply H0 in SUBNODE. auto.
      * unfold root_wf in H3. unfold get_root in H3. simpl in H3. apply H3 in SUBNODE. auto.
    + forward.                  (* cursor->ancestors[level]=i *)
      pose (i:=findChildIndex n key). fold i.
      gather_SEP (malloc_token Ews tcursor pc) (data_at Ews tcursor _ _).
      replace_SEP 0 (cursor_rep ((n,i)::c) r pc).
      { entailer!. unfold cursor_rep. unfold r.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      entailer!. autorewrite with sublist.
      rewrite upd_Znth_app2, upd_Znth_app2.
      autorewrite with sublist.
      rewrite upd_Znth0, upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite Zsuccminusone.
      cancel.
      autorewrite with sublist; rep_omega. 
      autorewrite with sublist; rep_omega.  }
{    forward_if (EX child:node val, PROP (nth_node i n = Some child)
     LOCAL (temp _i (Vint(Int.repr(rep_index i))); temp _t'3 (Val.of_bool isLeaf); temp _cursor pc; temp _child (getval child);
     temp _node pn; temp _key (key_repr key); temp _level (Vint (Int.repr (Zlength c))))
     SEP (cursor_rep ((n, i) :: c) r pc; btnode_rep n; malloc_token Ews trelation prel;
     data_at Ews trelation
       (getval root, (Vint (Int.repr (numrec)), Vint (Int.repr (get_depth r)))) prel;
     btnode_rep (btnode val ptr0 le isLeaf First Last pn) -* btnode_rep root))%assert.
     - rewrite unfold_btnode_rep with (n:=n). unfold n.
        destruct ptr0 eqn:HPTR0.
        + destruct n0 as [ptr00 le0 isLeaf0 F0 L0 x0]. Intros ent_end0.
        unfold optionally.
        forward.                (* child=node->ptr0 *)
        Exists (btnode val ptr00 le0 isLeaf0 F0 L0 x0).
        entailer!.
          * destruct i eqn:HI.
            auto.
            exfalso. simpl in H5.
            apply H3 in SUBNODE. apply node_wf_numKeys in SUBNODE.
            clear - HI H5 SUBNODE. subst i.
            pose proof (FCI_inrange' _ _ _ _ HI). 
            apply (f_equal Int.unsigned) in H5.
            change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned in H5.
            rewrite Int.unsigned_repr in H5 by rep_omega. rep_omega. 
          * fold n. cancel.
            rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end0. simpl. cancel.
        + unfold root_integrity in H0. unfold get_root in H0. simpl in H0.
          apply H0 in SUBNODE. unfold n in SUBNODE. rewrite H4 in SUBNODE. inv SUBNODE.
     - destruct isLeaf. easy. destruct ptr0. 
       rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
       fold n.
       destruct i as [|ii] eqn:HI.
       { simpl in H5. contradiction. } simpl.       
       assert(RANGE: 0 <= ii < numKeys_le le) by apply (FCI_inrange' _ _ _ _ HI). 
       destruct (nth_entry_le_in_range _ _ _ RANGE) as [e NTHENTRY].
       assert(ZNTH: nth_entry_le ii le = Some e) by auto.
       eapply Znth_to_list with (endle:=ent_end0) in ZNTH.
       destruct e as [k v x|k child].
       { unfold root_integrity in H0. apply H0 in SUBNODE. unfold n in SUBNODE.
         simpl in SUBNODE.
         exfalso. eapply intern_no_keyval; eauto. }
       forward.                 (* child=node->entries + i ->ptr.child *)
       { entailer!. split. omega.
         unfold root_wf in H3. apply H3 in SUBNODE. unfold node_wf in SUBNODE. simpl in SUBNODE.
         rep_omega. }
       { set (ptr0 := Some n0).
         change (getval n0) with (optionally getval nullval ptr0).
         change (btnode_rep n0) with (optionally btnode_rep emp ptr0).
         change Vfalse with (Val.of_bool false).
         sep_apply (fold_btnode_rep ptr0). subst ptr0. fold n.
         sep_apply modus_ponens_wand.
         assert(SUBCHILD: subnode child root).
         { eapply sub_trans with (m:=n). unfold n.
           apply (sub_child _ child). constructor. apply nth_entry_child in NTHENTRY. eapply nth_subchild. eauto.
           auto. }
         apply subnode_rep in SUBCHILD. rewrite SUBCHILD. rewrite ZNTH. entailer!.
        }
       rewrite ZNTH. Exists child.
       entailer!.
       unfold nth_node.
       eapply nth_entry_child. eauto.
       fold n. cancel. rewrite unfold_btnode_rep with (n:=n).
       unfold n. Exists ent_end0. entailer!.
       assert (node_integrity n). auto. easy.
     - Intros child.
       fold n. sep_apply (modus_ponens_wand (btnode_rep n)).
       sep_apply fold_relation_rep; fold r.
       forward_call(child,key,(n,i)::c,pc,r,numrec). (* recursive call *)
       + entailer!. rewrite Zlength_cons.
         repeat apply f_equal. rep_omega.
       + eapply derives_trans. eapply cursor_subcursor_rep. cancel.
       + split3.
         * unfold partial_cursor in H. destruct H. unfold partial_cursor. split; auto.
           unfold get_root in H2. simpl in H2. fold n in H2.
           eapply partial_correct_append; eauto.
         * auto.
         * split. auto. split; auto.
       + Ltac entailer_for_return ::= idtac.
          forward.            (* return: 3.6minutes *)
         entailer!.
         assert((moveToKey val child key ((n, i) :: c)) =  (moveToKey val (btnode val ptr0 le false First Last pn) key c)).
         { rewrite moveToKey_equation with (c:=c).
           fold n. fold i. rewrite H5. auto. }
         rewrite H4. apply derives_refl. }
Qed.
