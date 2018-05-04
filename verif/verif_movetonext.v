(** * verif_movetonext.v : Correctness proof of firstpointer, moveToNext and RL_MoveToNext *)

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
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_movetofirst.

Lemma body_lastpointer: semax_body Vprog Gprog f_lastpointer lastpointer_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'1=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward.                    (* t'3=node->numKeys *)
    forward.                    (* return *)
    destruct isLeaf.
    + unfold rep_index. entailer!. fold n. rewrite unfold_btnode_rep with (n:=n). unfold n.
      Exists ent_end. entailer!.
    + simpl in H0. inv H0.
  - forward.                    (* t'2=node->numKeys *)
    forward.                    (* return *)
    { entailer!. unfold node_wf in H.
      simpl in H. clear -H. rewrite Int.signed_repr. rewrite Int.signed_repr.
      rep_omega. rep_omega. rep_omega. }
    destruct isLeaf.
    + simpl in H0. inv H0.
    + destruct (numKeys_le le) eqn:HNUM.
      * unfold rep_index. simpl. entailer!. fold n. rewrite unfold_btnode_rep with (n:=n).
        unfold n. Exists ent_end. entailer!. simpl. rewrite HNUM. cancel.
      * assert (Z.of_nat (S n0) -1 = Z.of_nat n0).
        { rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. auto. }
        rewrite H6. unfold rep_index. entailer!. fold n. rewrite unfold_btnode_rep with (n:=n).
        unfold n. Exists ent_end. simpl. rewrite HNUM. entailer!.
Qed.

Lemma complete_sublist_partial: forall (X:Type) (c:cursor X) r i,
    complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (sublist 0 (Zlength c - i) c) r.
Proof.
Admitted.

Lemma body_moveToNext: semax_body Vprog Gprog f_moveToNext moveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c']. { inv H. inv H2. }
  pose (c:=(n,i)::c'). fold c.
  unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
  forward.                      (* t'17=cursor->relation *)
  unfold relation_rep. Intros.
  forward.                      (* t'18=t'17->numRecords *)
  forward_if.
  {  forward.                   (* return *)
     entailer!.
     unfold moveToNext.
     assert (get_numrec(root,prel) = O) by admit. rewrite H10.
     fold c. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. }
  forward.                      (* skip *)
  forward_call(r,c,pc).         (* t'1=isValid(cursor) *)
  { unfold relation_rep, cursor_rep. unfold r. Exists anc_end. Exists idx_end. cancel.
    change_compspecs CompSpecs. cancel. }
  forward_if.                              (* if t'1 == 0 *)
  { forward.                    (* return *)
    destruct (isValid c r) eqn:INVALID. inv H3.
    assert (moveToNext c r = c).
    { unfold moveToNext. destruct (get_numrec r). auto. rewrite INVALID. auto. }
    fold c. fold r. rewrite H9.
    entailer!.  }
  forward.                      (* skip *)
  assert (VALID: isValid c r = true).
  { destruct (isValid c r). auto. inv H3. } rewrite VALID.

  forward_loop
    (EX i:Z, PROP(up_at_last c = up_at_last (sublist 0 (Zlength c - i) c))
             LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat (get_numrec (root,prel))))); temp _t'17 prel; temp _cursor pc)
             SEP (relation_rep r; cursor_rep (sublist 0 (Zlength c - i) c) r pc))
    break:(PROP()
           LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat (get_numrec (root,prel))))); temp _t'17 prel; temp _cursor pc)
           SEP (relation_rep r; cursor_rep (up_at_last c) r pc)).
  - Exists 0. entailer!.
    + rewrite sublist_same. simpl. auto. auto. omega.
    + rewrite sublist_same. cancel. auto. omega.
  - Intros i0.
    pose (subc:=sublist 0 (Zlength c - i0) c). fold subc.
    unfold cursor_rep.
    Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'16 = cursor->level *)
    gather_SEP 1 2. replace_SEP 0 (cursor_rep subc r pc).
    { entailer!. unfold cursor_rep. Exists anc_end0. Exists idx_end0. unfold r. cancel. }
    forward_if (PROP ( )
     LOCAL (temp _t'16 (Vint (Int.repr (Zlength subc - 1))); temp _t'1 (Val.of_bool true);
            temp _t'18 (Vint (Int.repr (Z.of_nat (get_numrec (root,prel))))); temp _t'17 prel; temp _cursor pc;
            temp _t'2 (Val.of_bool (andb (Z.gtb (Zlength subc - 1) 0) (index_eqb (entryIndex subc) (lastpointer (currNode subc r)))))) 
     SEP (cursor_rep subc r pc; relation_rep (root, prel))).
    + assert(PARTIAL: ne_partial_cursor subc r).
      { unfold complete_cursor in H. destruct H as [CORRECT BALANCED].
        unfold ne_partial_cursor. split3.
        - unfold subc. apply complete_sublist_partial. auto.
        - destruct subc. simpl in H5. inv H5. simpl. omega.
        - auto. }
      forward_call(r,subc,pc).     (* t'3=entryIndex(cursor) *)
      { fold r. cancel. }
      forward_call(r,subc,pc).                (* t'4 = curnode(cursor) *)
      destruct subc as [|[currnode i'] subc'] eqn:HSUBC.
      { simpl in H5. inv H5. }
      simpl. assert (SUBNODE: subnode currnode root).
      { unfold ne_partial_cursor in PARTIAL. destruct PARTIAL.
        apply partial_cursor_subnode in H6. simpl in H6. auto. }
      assert(CURRNODE: currnode = currNode subc r). { rewrite HSUBC. simpl. auto. }
      forward_call(currNode subc r). (* 't'5=lastpointer t'4 *)
      { entailer!. }
      { apply subnode_rep in SUBNODE. rewrite SUBNODE. rewrite CURRNODE. cancel. }
      { unfold get_root in H1. unfold root_wf in H1. simpl in H1. rewrite <- CURRNODE.
        apply H1. apply SUBNODE. }
      forward.                  (* t'2= (t'3==t'5) *)
      entailer!.
      { rewrite Zlength_cons. rewrite Zsuccminusone. 
        pose (lastp :=  (lastpointer (currNode (sublist 0 (Zlength c - i0) c) r))).
        fold lastp. rewrite Zlength_cons in H5. rewrite Zsuccminusone in H5.
        admit.                  (* true from H5 *) }
      change_compspecs CompSpecs. cancel. apply wand_frame_elim.
    + forward.                  (* t'2=0 *)
      entailer!.
      rewrite Int.signed_repr in H5.
      assert(Zlength subc -1 >? 0 = false).
      { destruct subc. auto. destruct subc. auto. rewrite Zlength_cons in H5.
        rewrite Zlength_cons in H5. rewrite Zsuccminusone in H5. rewrite Zlength_correct in H5.
        omega. }
      rewrite H10. simpl. auto.      
      admit.                    (* subc length in range *)
    + forward_if.
      * forward.                (* skip *)
        unfold cursor_rep. unfold r. Intros anc_end1. Intros idx_end1.
        forward.                (* t'15=cursor->level *)
        forward.                (* cursor->level = t'15-1 *)
        { entailer!. admit. }   (* length subc in Int range *)
        Exists (i0+1). entailer!. unfold cursor_rep. unfold r.
        { simpl in H4. rewrite H4. admit. } (* up_at_last conservation *)
        Exists ((getval (currNode subc r))::anc_end1).
        Exists ((Vint(Int.repr(rep_index(entryIndex subc))))::idx_end1).
        cancel.
        rewrite Zlength_sublist. unfold subc. rewrite Zlength_sublist. unfold r.
        admit.                  (* should be ok *)
        admit. admit. admit. admit.
      * forward.                (* break *)
        entailer!. simpl in H4. rewrite H4. fold subc.
        admit. (* TODO: prove that when the loop stops, we have up_at_last *)
  - unfold cursor_rep. Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'12=cursor->level *)
    forward.                    (* t'13=cursor->level *)
    forward.                    (* t'14=cursor->ancidx[t'13] *)
    { entailer!. admit. }       (* up_at_last correct_length *)
    { entailer!. admit. }
    forward.                    (* cursor->ancestors[t'12] = t'14 +1 *)
    { admit. }
    { admit. }
    gather_SEP 1 2. pose(cincr := next_cursor (up_at_last c)).
    replace_SEP 0 (cursor_rep cincr r pc).
    { unfold cursor_rep. entailer!.
    Exists anc_end0. Exists idx_end0. cancel. admit. }
    forward_call(r,cincr,pc).       (* t'6=currNode(cursor) *)
    { fold r. cancel. }
    { unfold r. split; auto. admit. }
    destruct (currNode cincr r).
    simpl. Intros.
    (* here I need a representation for the current node of cincr *)
    (* I will have that once I've proved that cincr is correct cursor *)
    admit.
Admitted.

Lemma movetonext_complete : forall c r,
    complete_cursor c r -> complete_cursor (moveToNext c r) r.
Proof.
Admitted.

Lemma body_RL_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c'].
  inv H. inv H2. pose (c:=(n,i)::c'). fold c.
  forward_call(r,c,pc).         (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc).         (* t'2=currNode(cursor) *)
  unfold c. simpl.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). simpl.
  assert (SUBNODE: subnode n root).
  { unfold complete_cursor in H. destruct H. apply complete_cursor_subnode in H. auto. }
  unfold relation_rep. rewrite subnode_rep with (n:=n) by auto.
  rewrite unfold_btnode_rep at 1. unfold n. Intros ent_end.
  forward.                      (* t'3=t'2->numKeys *)
  simpl.
  gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep n).
  { entailer!. rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end. entailer!. }
  gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
  { entailer!. apply wand_frame_elim. } gather_SEP 0 1 2. replace_SEP 0 (relation_rep r).
  { entailer!. } fold c.
  forward_if(PROP ( )
     LOCAL (temp _t'3 (Vint (Int.repr (Z.of_nat (numKeys_le le)))); temp _t'2 pn;
     temp _t'1 (Vint(Int.repr(rep_index i))); temp _cursor pc)
     SEP (relation_rep r; match (index_eqb i (ip (numKeys n))) with true => cursor_rep (moveToNext c r) r pc | false => cursor_rep c r pc end)).
  - forward_call(c,pc,r).       (* moveToNext(cursor) *)
    entailer!.
    destruct H. apply complete_correct_rel_index in H.
    unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. fold n  in H.
    assert(Z.of_nat (numKeys_le le) <= Z.of_nat Fanout).
    { simpl in SUBNODE. omega. } simpl in H.
      destruct i as [|ii].
    + simpl in H2. simpl in H. clear -H2 H8. apply (f_equal Int.unsigned) in H2.
      rewrite Fanout_eq in H8. simpl in H8. apply eq_sym in H2. autorewrite with norm in H2.
      rewrite H2 in H8. exfalso. compute in H8. apply H8. auto.
    + simpl in H2. apply (f_equal Int.unsigned) in H2. rewrite Fanout_eq in H8. simpl in H8.
      clear -H2 H8 H. apply eq_sym in H2. simpl in H.
      autorewrite with norm in H2. apply Nat2Z.inj in H2. subst. simpl.
      rewrite Nat.eqb_refl. cancel.
  - forward.                                            (* skip *)
    destruct H. apply complete_correct_rel_index in H.
    unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. fold n  in H.
    assert(Z.of_nat (numKeys_le le) <= Z.of_nat Fanout).
    { simpl in SUBNODE. omega. } simpl in H.
    destruct i as [|ii].
    { entailer!. } unfold index_eqb, numKeys. unfold n.
    destruct (ii =? numKeys_le le)%nat eqn:HII.
    + exfalso. apply beq_nat_true in HII. subst. simpl in H2. contradiction.
    + entailer!.
  - pose (newc:=if index_eqb i (ip (numKeys n)) then (moveToNext c r) else c).
    forward_call(newc,pc,r).                               (* moveToNext(cursor) *)
    + unfold newc. destruct (index_eqb i (ip (numKeys n))); cancel.
      unfold Frame. simpl. cancel.
    + split; auto. unfold newc.
      destruct (index_eqb i (ip (numKeys n))).
      * apply movetonext_complete. auto.
      * auto.
    + forward.                                          (* return *)
      entailer!. unfold newc. simpl.
      destruct (index_eqb i (ip (numKeys_le le))); fold c; fold r; cancel.
Qed.