(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
Require Import index.

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
  simpl in H0. destruct i as [|ii]. contradiction.
  apply complete_cursor_subnode in H. unfold get_root in H. simpl in H.
  assert (SUBNODE: subnode n root) by auto.
  unfold relation_rep. unfold r.
  rewrite subnode_rep with (n:=currNode c (root,prel)) by auto. Intros.
  rewrite unfold_btnode_rep at 1.
  assert(currNode c r = currNode c (root,prel)). auto.
  destruct (currNode c (root,prel)) as [ptr0 le b First Last pn]. Intros.
  pose (currnode:= btnode val ptr0 le b First Last pn). Intros ent_end.
  forward.                      (* t'5=t'2->numKeys *)
  gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep (currNode c r)).
  { rewrite unfold_btnode_rep. rewrite H4. entailer!. Exists ent_end. entailer!. }
  
  forward_if  (PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last pn)))));
     temp _t'2 (getval (btnode val ptr0 le b First Last pn)); temp _t'1 (Vint(Int.repr(rep_index (entryIndex c))));
     temp _cursor pc; temp _t'3 (Val.of_bool (negb (isValid c r))) (* new local *))
     SEP (btnode_rep (currNode c r); malloc_token Tsh trelation prel;
     data_at Tsh trelation
       (getval root, (Vint (Int.repr (Z.of_nat (numrec))), Vint (Int.repr (Z.of_nat (get_depth (root,prel)))))) prel;
     btnode_rep (btnode val ptr0 le b First Last pn) -* btnode_rep root;
     cursor_rep c (root, prel) pc)).

  - forward_call(r,c,pc,numrec).
    + unfold r. cancel. unfold relation_rep.
      cancel.
      change_compspecs btrees.CompSpecs.
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
          assert(0 <= Z.of_nat (numKeys_le le) <= Int.max_unsigned).
          { unfold root_wf in H1. unfold get_root in H1. simpl in H1.
          apply H1 in SUBNODE. unfold node_wf in SUBNODE. unfold numKeys in SUBNODE.
          rewrite H3 in SUBNODE. rewrite H4 in SUBNODE. rep_omega. }
          apply repr_inj_unsigned in H5. apply Nat2Z.inj in H5.
          rewrite H5. rewrite Nat.eqb_refl. simpl. auto.
          unfold complete_cursor in COMPLETE. destruct COMPLETE.
          unfold complete_cursor_correct_rel in H16.
          destruct (getCEntry ((n,ip ii)::c')); try inv H16.
          destruct e; try inv H16.
          apply complete_correct_index in H16. rewrite H3, H4 in H16. simpl in H16.
          rep_omega. auto. }
        assert(n = currNode c r). simpl. auto. rewrite H15.
        rewrite unfold_btnode_rep. rewrite H4.
        entailer!. Exists ent_end0. entailer!. fold r. cancel. eapply derives_refl.
  - forward.                    (* t'3=0 *)
    entailer!.
    unfold isValid. rewrite H4.
    destruct Last; auto.
    assert(index.index_eqb (entryIndex c) (index.ip (numKeys_le le)) = false).
    { unfold c. simpl.
      destruct (ii =? numKeys_le le)%nat eqn:HEQ; auto.
      apply beq_nat_true in HEQ. subst ii. contradiction. }      
    rewrite H11. auto.
    apply derives_refl.
  - gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. rewrite unfold_btnode_rep at 1. assert(n = currNode c r) by (simpl; auto).
      rewrite H8. rewrite H4. apply wand_frame_elim. }
    gather_SEP 0 1 2. replace_SEP 0 (relation_rep r numrec).
    { entailer!. apply derives_refl. }
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
    Intros vret. forward.
    entailer!. unfold force_val, sem_cast_pointer.
    destruct (isValid c); simpl; auto.
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
  simpl in H0. destruct i as [|ii]. contradiction. 
  apply complete_cursor_subnode in H. unfold get_root in H. simpl in H.
  assert (SUBNODE: subnode n root) by auto.
  unfold c. simpl. fold c.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n in c, H3, SUBNODE, COMPLETE.
  forward_if(
      PROP ( )
      LOCAL (temp _t'1 (Vint (Int.repr (Z.of_nat ii))); temp _cursor pc;
             temp _t'2 (Val.of_bool(First && (index_eqb (ip ii) (ip 0))))) (* new local *)
      SEP (malloc_token Tsh trelation prel *
           data_at Tsh trelation
           (getval root,
            (Vint (Int.repr (Z.of_nat (numrec))), Vint (Int.repr (Z.of_nat (get_depth r)))))
           prel * btnode_rep root; cursor_rep c r pc)).
  - forward_call(r,c,pc,numrec).       (* t'3=currnode *)
    { unfold relation_rep. unfold r. cancel.
      repeat change_compspecs CompSpecs. cancel. } rewrite <- H3.
    unfold relation_rep. assert(SUBREP: subnode n root) by auto.
    apply subnode_rep in SUBREP. unfold r. rewrite SUBREP.
    rewrite unfold_btnode_rep with (n:=n) at 1.
    unfold n. Intros ent_end. simpl.
    forward.                    (* t'4=t'3->First *)
    { destruct First; entailer!. }
    forward.                    (* t'2=(t'4==1) *)
    assert(ii=O).
    { unfold complete_cursor in COMPLETE. destruct COMPLETE.
    unfold complete_cursor_correct_rel in H5.
    destruct( getCEntry ((n,ip ii)::c')); try contradiction.
    destruct e; try contradiction.
    apply complete_correct_index in H5.
    apply (f_equal Int.unsigned) in H4. rewrite Int.unsigned_repr in H4.
    rewrite Int.unsigned_repr in H4 by rep_omega. destruct ii; auto. inv H4.
    split; try omega.
    simpl in H5. unfold root_wf in H1. simpl in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE.
    unfold n in SUBNODE. simpl in SUBNODE. rep_omega. } subst.
    gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep n).
    { rewrite unfold_btnode_rep with (n:=n). unfold n. entailer!. Exists ent_end. cancel. }
    gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. apply wand_frame_elim. }    
    entailer!.
    + destruct First; simpl; auto.
    + fold r. cancel. apply derives_refl.
  - Intros.
    forward.                    (* t'2=0 *)
    entailer!.
    destruct ii.
    { simpl in H4. exfalso. apply H4. auto. }
    simpl. rewrite andb_false_r. auto. apply derives_refl.
  - forward_if.
    + forward.                  (* return 1 *)
      rewrite H4. entailer!.
    + forward.                  (* return 0 *)
      rewrite H4. entailer!.
Qed.      
