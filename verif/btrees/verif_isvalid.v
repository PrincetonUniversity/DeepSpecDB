(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

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
Require Import verif_currnode.
Require Import verif_entryindex.

Lemma body_isValid: semax_body Vprog Gprog f_isValid isValid_spec.
Proof.
  start_function.
  forward_call(r,c,pc,numrec).      (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc,numrec).      (* t'2=currNode *)
  assert (COMPLETE: complete_cursor c r) by auto.
  unfold complete_cursor in H. destruct H.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c'].
  simpl in H0. contradiction.          (* the empty cursor can't be complete *)
  pose (c:=(n,i)::c'). fold c.
  assert (n = currNode c r). simpl. auto.
  simpl in H0.
  apply complete_cursor_subnode in H. unfold get_root in H. simpl in H.
  assert (SUBNODE: subnode n root) by auto.
  unfold relation_rep. unfold r.
  rewrite subnode_rep with (n:=currNode c (root,prel)) by auto. Intros.
  rewrite unfold_btnode_rep at 1.
  assert(currNode c r = currNode c (root,prel)). auto.
  destruct (currNode c (root,prel)) as [ptr0 le b First Last pn]. Intros.
  pose (currnode:= btnode val ptr0 le b First Last pn). Intros ent_end.
  forward.                      (* t'5=t'2->numKeys *)
  sep_apply (fold_btnode_rep ptr0). rewrite <- H4 at 3.
  
  forward_if  (PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (numKeys (btnode val ptr0 le b First Last pn))));
     temp _t'2 (getval (btnode val ptr0 le b First Last pn)); temp _t'1 (Vint(Int.repr(entryIndex c)));
     temp _cursor pc; temp _t'3 (Val.of_bool (negb (isValid c r))) (* new local *))
     SEP (btnode_rep (currNode c r); malloc_token Ews trelation prel;
     data_at Ews trelation
       (getval root, (Vptrofs (Ptrofs.repr (numrec)), Vint (Int.repr (get_depth (root,prel))))) prel;
     btnode_rep (btnode val ptr0 le b First Last pn) -* btnode_rep root;
     cursor_rep c (root, prel) pc)).

  - forward_call(r,c,pc,numrec).
    + unfold r. cancel. unfold relation_rep.
      cancel. eapply derives_trans. fold r. rewrite H4. apply wand_frame_elim. cancel.
    + unfold relation_rep. unfold r. Intros.
      rewrite subnode_rep with (n:=currNode c r) by auto.
      rewrite H4. fold r.
      rewrite unfold_btnode_rep at 1.
      Intros. rewrite H4. Intros ent_end0.
      forward.                  (* t'6=t'4->Last *)
      * entailer!. destruct Last; simpl; auto.
      * forward.                (* t'3=(tbool) (t'6==1) *)
        entailer!.
        { unfold isValid. rewrite H4. destruct Last; simpl; auto.
          assert (Hii: 0 <= i < Zlength le). {
               clear - COMPLETE H4 H3. rewrite H3,H4 in COMPLETE.
               clear H3 H4. destruct COMPLETE. hnf in H. simpl in H.
               destruct (Znth_option i le) eqn:?H; try contradiction.
               apply nth_entry_le_some  in H1. auto.
          }
          assert(0 <= Zlength le <= Int.max_unsigned).
          { apply H1 in SUBNODE. apply node_wf_numKeys in SUBNODE. unfold numKeys in SUBNODE.
            rewrite H3 in SUBNODE. rewrite H4 in SUBNODE. rep_omega. }
          apply repr_inj_unsigned in H5.
          rewrite H5. rewrite Z.eqb_refl. auto.
          unfold complete_cursor in COMPLETE. destruct COMPLETE.
          unfold complete_cursor_correct_rel in H16.
          destruct (getCEntry ((n,i)::c')); try inv H16.
          destruct e; try inv H16.
          apply complete_correct_index in H16. rewrite H3, H4 in H16. simpl in H16.
          rep_omega. auto. }
        rewrite unfold_btnode_rep. rewrite H4.
        entailer!. Exists ent_end0. entailer!. fold r. cancel.
  - forward.                    (* t'3=0 *)
    entailer!.
    unfold isValid. rewrite H4.
    destruct Last; auto.
    assert(Z.eqb (entryIndex c) (Zlength le) = false).
    { unfold c. simpl. apply Z.eqb_neq. contradict H5; f_equal; auto. }      
    rewrite H11. auto.
  - rewrite <- H4. sep_apply modus_ponens_wand.
     sep_apply (fold_relation_rep).
    forward_if.
    + forward. fold c. entailer!. fold r. rewrite H5. auto.
    + forward. fold c. entailer!. fold r. rewrite H5. auto.
Qed.
  
Lemma body_RL_CursorIsValid: semax_body Vprog Gprog f_RL_CursorIsValid RL_CursorIsValid_spec.
Proof.
  start_function.
  forward_if (
      (PROP (pc<>nullval)  LOCAL (temp _cursor pc)  SEP (relation_rep r numrec; cursor_rep c r pc))).
  - forward. entailer!.
  - subst. assert_PROP(False).
    entailer!. contradiction.
  - forward_call(r,c,pc,numrec).
    Intros vret. subst vret.
    forward.
    entailer!.
Qed.

Lemma body_isFirst: semax_body Vprog Gprog f_isFirst isFirst_spec.
Proof.
  start_function.
  forward_call(r,c,pc,numrec).         (* t'1=entryIndex(cursor) *)
  assert (COMPLETE: complete_cursor c r) by auto.
  unfold complete_cursor in H. destruct H.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c'].
  { simpl in H0. contradiction. } (* the empty cursor can't be complete *)
  pose (c:=(n,i)::c'). fold c.
  assert (n = currNode c r). simpl. auto.
  apply complete_cursor_subnode in H. unfold get_root in H. simpl in H.
  assert (SUBNODE: subnode n root) by auto.
  unfold c. simpl. fold c.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n in c, H3, SUBNODE, COMPLETE.
  forward_if(
      PROP ( )
      LOCAL (temp _t'1 (Vint (Int.repr i)); temp _cursor pc;
             temp _t'2 (Val.of_bool(First && (Z.eqb i 0)))) (* new local *)
      SEP (malloc_token Ews trelation prel *
           data_at Ews trelation
           (getval root,
            (Vptrofs (Ptrofs.repr numrec), Vint (Int.repr (get_depth r))))
           prel * btnode_rep root; cursor_rep c r pc)).
  - forward_call(r,c,pc,numrec).       (* t'3=currnode *)
    rewrite <- H3.
    unfold relation_rep. assert(SUBREP: subnode n root) by auto.
    apply subnode_rep in SUBREP. unfold r. rewrite SUBREP.
    rewrite unfold_btnode_rep with (n:=n) at 1.
    unfold n. Intros ent_end. simpl.
    forward.                    (* t'4=t'3->First *)
    { destruct First; entailer!. }
    forward.                    (* t'2=(t'4==1) *)
    assert(i=0).
    { unfold complete_cursor in COMPLETE. destruct COMPLETE.
    unfold complete_cursor_correct_rel in H5.
    destruct( getCEntry ((n,i)::c')) eqn:?H; try contradiction.
    simpl in H7. apply nth_entry_le_some in H7.
    apply H1 in SUBNODE. apply node_wf_numKeys in SUBNODE.
    unfold n in SUBNODE. simpl in SUBNODE.
    apply (f_equal Int.unsigned) in H4.
    rewrite !Int.unsigned_repr in H4 by rep_omega. auto. } subst.
    sep_apply (fold_btnode_rep ptr0). fold n.
    sep_apply modus_ponens_wand.
    entailer!.
    + destruct First; simpl; auto.
    + fold r. cancel.
  - Intros.
    forward.                    (* t'2=0 *)
    entailer!.
    simpl. rewrite (proj2 (Z.eqb_neq i 0)). rewrite andb_comm. reflexivity.
    contradict H4; f_equal; auto. 
  - forward_if.
    + forward.                  (* return 1 *)
      simpl. fold c. fold r. rewrite H4. entailer!.
    + forward.                  (* return 0 *)
      simpl. fold c. fold r. 
      rewrite H4. entailer!.
Qed.      
