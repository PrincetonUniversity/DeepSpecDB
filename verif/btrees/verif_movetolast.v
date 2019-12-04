(** * verif_movetolast.v : Correctness proof of moveToLast *)

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

Lemma body_moveToLast: semax_body Vprog Gprog f_moveToLast moveToLast_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
  assert(CLENGTH: 0 <= Zlength c < 20).
  { unfold partial_cursor in H. destruct H. unfold correct_depth in H3.
    rewrite Zlength_correct. apply partial_rel_length in H. rep_omega. }
  assert(GETVAL: pn = getval n). { unfold n. simpl. auto. }
  assert(SUBNODE: subnode n root).
  { unfold partial_cursor in H. destruct H.
    simpl in H1. unfold partial_cursor_correct_rel in H.
    destruct c as [|[n' i ] c'].
    - simpl in H2. inversion H2. unfold n. apply sub_refl.
    - simpl in H2. rewrite H2 in H. simpl in H. destruct H.
      apply partial_cursor_subnode' in H. apply nth_subnode in H2.
      apply sub_trans with (n0:=n) in H. auto. unfold n. auto. }
  assert_PROP(isptr pn).
  { unfold relation_rep. unfold r. apply subnode_rep in SUBNODE. rewrite SUBNODE.
    rewrite GETVAL. Intros. entailer!. }
  assert(ISPTR: isptr pn) by auto. clear H4.

  forward_if (
      PROP(pn<>nullval)
      LOCAL(temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
      SEP(relation_rep r numrec; cursor_rep c r pc))%assert.
  - apply denote_tc_test_eq_split. assert (SUBREP: subnode n root) by auto.
    apply subnode_rep in SUBREP. simpl. rewrite SUBREP. rewrite GETVAL. entailer!.
    entailer!.    
  - forward.                    (* skip *)
    entailer!.
  - assert (SUBREP: subnode n root) by auto.
    apply subnode_rep in SUBREP. unfold relation_rep. unfold r.
    rewrite SUBREP.
    assert_PROP(isptr (getval n)). entailer!.
    rewrite <- GETVAL in H5. rewrite H4 in H5. simpl in H5. contradiction.
  - forward_if (
        (PROP (pn <> nullval; pc <> nullval)
         LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
         SEP (relation_rep r numrec; cursor_rep c r pc))).
    + forward. entailer!.
    + assert_PROP(False).
      entailer!. contradiction.
    + forward_if ((PROP (pn <> nullval; pc <> nullval; (Zlength c) >= 0)
     LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
     SEP (relation_rep r numrec; cursor_rep c r pc))).
      * forward. entailer!.
      * assert_PROP(False). entailer. omega.
      * unfold cursor_rep.
        Intros anc_end. Intros idx_end. unfold r.
        forward.                (* cursor->ancestors[level]=node *)
        forward.                (* cursor->level = level *) 
        assert (SUBREP:subnode n root) by auto.
        apply subnode_rep in SUBREP. unfold relation_rep. rewrite SUBREP. unfold n.
        rewrite unfold_btnode_rep at 1. Intros ent_end.
        forward.                (* t'2=node->isLeaf *)
        { entailer!. destruct isLeaf; simpl; auto. }  
        forward_if.
{
  - forward.                    (* t'5=node->numKeys *)
    forward.                    (* cursor->ancestorsIdx[level]=t'5 *)
    + sep_apply (fold_btnode_rep ptr0).
        sep_apply modus_ponens_wand.
        sep_apply fold_relation_rep; fold r.
      gather_SEP 1 2. replace_SEP 0 (cursor_rep (moveToLast val n c (length c)) r pc).
      { entailer!. unfold cursor_rep.
        Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
        unfold r. fold n.
        assert (Zlength ((n,ip (numKeys_le le))::c) -1 = Zlength c). { rewrite Zlength_cons. omega. }
        rewrite moveToLast_equation. simpl.
        rewrite H7. cancel. 
        autorewrite with sublist. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
        rewrite upd_Znth_app2, upd_Znth_app2. autorewrite with sublist.
        rewrite upd_Znth0, upd_Znth0. simpl. cancel.
        autorewrite with sublist. pose proof (Zlength_nonneg anc_end); omega.
        autorewrite with sublist. pose proof (Zlength_nonneg idx_end); omega. }
      forward.                  (* return *)
      unfold r. fold n. entailer!.
} {
  forward.                      (* t'3=node->numKeys *)
  forward.                      (* cursor->ancestorsIdx[level]=t'3-1 *)
  { assert(Int.min_signed <= Z.of_nat (numKeys_le le) <= Int.max_signed).
    { split. rep_omega. unfold root_wf, node_wf in H1. simpl in H1.
      apply H1 in SUBNODE. unfold n in SUBNODE. simpl in SUBNODE. rep_omega. }
    entailer!. }
  -                             (* recursive call *)
    destruct ptr0 as [ptr0n|] eqn:EQPTR0.
    + destruct ptr0n eqn:EPTR0n.
      { 
      Intros.
      forward.                    (* t'1=node->ptr0 *)
(*
         replace (getval (btnode val o l b b0 b1 v))
         with  (optionally getval nullval ptr0)
         by (rewrite EQPTR0; reflexivity).
      replace (btnode_rep (btnode val o l b b0 b1 v))
       with (optionally btnode_rep emp ptr0)
       by (rewrite EQPTR0; reflexivity).
*)    rewrite <- EQPTR0.
      sep_apply (fold_btnode_rep ptr0).
      sep_apply modus_ponens_wand.
      sep_apply fold_relation_rep; fold r.
      deadvars!. simpl.

      rewrite SUBREP. rewrite unfold_btnode_rep with (n:=n) at 1. unfold n. clear ent_end.
      Intros ent_end. simpl. fold n.
      destruct le as [|firste le'] eqn:HLE.
      { exfalso. subst isLeaf. unfold root_integrity in H0. apply H0 in SUBNODE.
        unfold n in SUBNODE. simpl in SUBNODE. inv SUBNODE. }
      assert(HZNTH: (numKeys_le le - 1 < numKeys_le le)%nat).
      { rewrite HLE. simpl. omega. }
      apply nth_entry_le_in_range in HZNTH.
      destruct HZNTH as [laste HZNTH].
      assert(KC: nth_entry (numKeys_le le - 1) n = Some laste).
      { unfold n. rewrite <- HLE. simpl. auto. }
      apply integrity_nth in KC. destruct KC as [k [child HLAST]]. subst laste.
      assert (HNTH: nth_entry (numKeys_le le - 1) n = Some (keychild val k child)).
      { unfold n. rewrite <- HLE. simpl. auto. }
      eapply Znth_to_list with (endle := ent_end) in HZNTH.
      assert(SUBCHILD: subnode child root).
      { apply sub_trans with (m:=n). eapply entry_subnode. eauto. apply HNTH. auto. }
      rewrite HLE in HZNTH. simpl in HZNTH.
      rewrite Nat2Z.inj_sub in HZNTH by omega. simpl in HZNTH. rewrite Z.sub_0_r in HZNTH.
      forward.                  (* t'2=node->entries[t'1-1]->ptr.child *)
      { rewrite Zpos_P_of_succ_nat. rewrite Zsuccminusone.
        entailer!. unfold root_wf, node_wf in H1. apply H1 in SUBNODE.
        split. omega.
        rewrite Fanout_eq in SUBNODE. unfold n in SUBNODE. simpl in SUBNODE. rep_omega. }
      { rewrite Zpos_P_of_succ_nat. rewrite Zsuccminusone. rewrite HZNTH.
        apply subnode_rep in SUBCHILD.
      replace (btnode_rep (btnode val o l b b0 b1 v))
       with (optionally btnode_rep emp ptr0)
       by (rewrite EQPTR0; reflexivity).
        replace v
         with (optionally getval nullval ptr0)
         by (rewrite EQPTR0; reflexivity).
      sep_apply (fold_btnode_rep ptr0).
      rewrite EQPTR0 at 1. fold n.
      sep_apply modus_ponens_wand.
        rewrite SUBCHILD. entailer!. }        
      { entailer!. rewrite Zpos_P_of_succ_nat. rewrite Int.signed_repr with (z:=1) by rep_omega.
        clear -H1 SUBNODE. unfold root_wf, node_wf in H1. simpl in H1. apply H1 in SUBNODE.
        unfold n in SUBNODE. simpl in SUBNODE.
        rewrite Int.signed_repr. rewrite Zsuccminusone. rep_omega.
        rep_omega. }
      rewrite Zpos_P_of_succ_nat. rewrite Zsuccminusone.
      simpl le_to_list. rewrite <- app_comm_cons.
      rewrite HZNTH.
      replace (btnode_rep (btnode val o l b b0 b1 v))
       with (optionally btnode_rep emp ptr0)
       by (rewrite EQPTR0; reflexivity).
        replace v
         with (optionally getval nullval ptr0) 
         by (rewrite EQPTR0; reflexivity).
      change (?A::?B++?C) with ((A::B)++C).
      change (entry_val_rep firste :: le_to_list le')
            with (le_to_list (cons val firste le')).
      sep_apply (fold_btnode_rep ptr0). rewrite EQPTR0; fold n.
      sep_apply modus_ponens_wand.
      
      forward_call(r,((n,ip(numKeys_le le -1))::c),pc,child,numrec). (* moveToLast *)      
      * entailer!. repeat apply f_equal. rewrite Zlength_cons. omega.
      * unfold cursor_rep. unfold r.
        Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
        assert (Zlength ((n,ip(numKeys_le le -1))::c) -1 = Zlength c). rewrite Zlength_cons. omega.
        rewrite H8. cancel.
        autorewrite with sublist. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
        rewrite upd_Znth_app2, upd_Znth_app2. autorewrite with sublist. 
        rewrite upd_Znth0, upd_Znth0. autorewrite with norm.
        rewrite Zpos_P_of_succ_nat. rewrite Zsuccminusone. rewrite HLE.
        simpl. rewrite Nat2Z.inj_sub by omega. simpl. rewrite Z.sub_0_r. cancel.
        autorewrite with sublist. pose proof (Zlength_nonneg anc_end); omega.
        autorewrite with sublist. pose proof (Zlength_nonneg idx_end); omega.
      * split.
        { unfold partial_cursor in *.
          destruct H. split.
          - simpl. assert(nth_node_le (numKeys_le le -1) (cons val firste le') = Some child).
            { eapply nth_entry_child. unfold n in HNTH. simpl in HNTH. eauto. }
            rewrite H9. destruct isLeaf. easy. split; auto.
            unfold partial_cursor_correct.
            destruct c as [|[n' i] c']. simpl in H2. simpl. fold n in H2. inversion H2. auto.
            split.
            + simpl in H. destruct (nth_node i n').
              destruct H. auto.
              inv H.
            + fold n in H2. simpl in H2. auto.
          - auto. }
        { split.
          - auto.
          - split.
            + simpl. auto.
            + split. simpl. destruct isLeaf. easy. 
              eapply nth_entry_child. unfold n in HNTH. simpl in HNTH. eauto.
              auto. }
      * forward.
        (* instantiate (Frame:=[]). *) entailer!.
        fold r. simpl. rewrite moveToLast_equation with (c:=c).
        simpl.
        assert(nth_node_le (numKeys_le le' -0) (cons val firste le') = Some child).
        { eapply nth_entry_child. unfold n in HNTH. simpl in HNTH. eauto. }
        rewrite H7. fold n.
        replace (S (length c)) with ((length c + 1)%nat) by omega.
        cancel.
      * auto.
      * unfold n. simpl. rewrite H7. auto. }
    +                           (* ptr0 has to be defined on an intern node *)
      unfold root_integrity in H0. unfold get_root in H0. simpl in H0.
      apply H0 in SUBNODE. unfold node_integrity in SUBNODE.
      unfold n in SUBNODE. rewrite H7 in SUBNODE. contradiction. }
Qed.
