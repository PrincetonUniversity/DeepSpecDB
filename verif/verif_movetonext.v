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
    partial_cursor_correct_rel (sublist i (Zlength c) c) r.
Proof.
Admitted.

Lemma sublist_tl: forall (A:Type) c i (a:A) c',
    0 <= i < Zlength c ->
    sublist i (Zlength c) c = a :: c' ->
    c' = sublist (i+1) (Zlength c) c.
Proof.
  intros. 
Admitted.

Lemma up_at_last_range: forall (X:Type) (c:cursor X) m,
    0 <= Zlength c - 1 < m ->
    0 <= Zlength (up_at_last c) - 1 < m.
Proof.
  intros.
  induction c.
  - simpl in H. omega.
  - destruct a as [n i]. simpl. destruct c.
    + simpl. omega.
    + destruct(index_eqb i (lastpointer n)).
      * apply IHc. split. rewrite Zlength_cons. rewrite Zsuccminusone. apply Zlength_nonneg.
        rewrite Zlength_cons in H. omega.
      * auto.
Qed.

Lemma complete_partial_upatlast: forall (X:Type) (c:cursor X) r,
    partial_cursor_correct_rel c r \/ complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (up_at_last c) r \/ complete_cursor_correct_rel (up_at_last c) r.
Proof.
  intros.
  induction c.
  - simpl. left. auto.
  - simpl. destruct a as [n i].
    destruct c.
    + auto.
    + destruct(index_eqb i (lastpointer n)).
      * apply IHc. destruct H.
        { left. admit. }
        { left. admit. }
      * auto.
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
    (EX i:Z, PROP(up_at_last c = up_at_last (sublist i (Zlength c) c); 0 <= i <= Zlength c)
             LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat (get_numrec (root,prel))))); temp _t'17 prel; temp _cursor pc)
             SEP (relation_rep r; cursor_rep (sublist i (Zlength c) c) r pc))
    break:(EX i:Z, PROP(up_at_last c = sublist i (Zlength c) c)
           LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat (get_numrec (root,prel))))); temp _t'17 prel; temp _cursor pc)
           SEP (relation_rep r; cursor_rep (up_at_last c) r pc)).
  - Exists 0. entailer!.
    + rewrite sublist_same. simpl. auto. auto. omega.
    + rewrite sublist_same. cancel. auto. omega.
  - Intros i0.
    pose (subc:=sublist i0 (Zlength c) c). fold subc.
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
        - destruct subc. simpl in H6. inv H6. simpl. omega.
        - auto. }
      forward_call(r,subc,pc).     (* t'3=entryIndex(cursor) *)
      { fold r. cancel. }
      forward_call(r,subc,pc).                (* t'4 = curnode(cursor) *)
      destruct subc as [|[currnode i'] subc'] eqn:HSUBC.
      { simpl in H6. inv H6. }
      simpl. assert (SUBNODE: subnode currnode root).
      { unfold ne_partial_cursor in PARTIAL. destruct PARTIAL.
        apply partial_cursor_subnode in H7. simpl in H7. auto. }
      assert(CURRNODE: currnode = currNode subc r). { rewrite HSUBC. simpl. auto. }
      forward_call(currNode subc r). (* 't'5=lastpointer t'4 *)
      { entailer!. }
      { apply subnode_rep in SUBNODE. rewrite SUBNODE. rewrite CURRNODE. cancel. }
      { unfold get_root in H1. unfold root_wf in H1. simpl in H1. rewrite <- CURRNODE.
        apply H1. apply SUBNODE. }
      forward.                  (* t'2= (t'3==t'5) *)
      entailer!.
      { rewrite Zlength_cons. rewrite Zsuccminusone. 
        pose (lastp :=  (lastpointer (currNode (sublist i0 (Zlength c) c) r))).
        fold lastp. rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6.
        assert(LENGTH: Zlength subc' >? 0 = true).
        { destruct(subc'). rewrite Zlength_nil in H6. rewrite Int.signed_repr in H6.
          omega. rep_omega. rewrite Zlength_cons. apply Z.gtb_lt. rep_omega. }
        rewrite LENGTH. simpl.
        destruct(index_eqb i' lastp) eqn:HEQ.
        + destruct i' as [|i''].
          * destruct lastp. simpl. auto. simpl in HEQ. inv HEQ.
          * destruct lastp. simpl in HEQ. inv HEQ. simpl. inv HEQ.
            apply beq_nat_true in H14. subst. rewrite Int.eq_true. simpl. auto.
        + unfold Int.eq.
          unfold ne_partial_cursor in PARTIAL. destruct PARTIAL.
          apply partial_correct_rel_index in H13. unfold root_wf in H1.
          apply H1 in SUBNODE. unfold node_wf in SUBNODE.
          assert(idx_to_Z lastp <= Z.of_nat (numKeys (currNode (sublist i0 (Zlength c) c) r))).
          { unfold lastpointer in lastp. destruct (currNode (sublist i0 (Zlength c) c) r).
            destruct b. unfold lastp. simpl. omega. simpl.
            destruct (numKeys_le l). unfold lastp. simpl. omega.
            unfold lastp. simpl. rewrite Zpos_P_of_succ_nat. omega. }
          clear -H13 SUBNODE H15 HEQ.
          destruct i' as [|ii]; destruct lastp as [|pp]; unfold rep_index; unfold idx_to_Z in H15;
            simpl in H15; unfold index_eqb in HEQ; simpl in HEQ; unfold idx_to_Z in H13; simpl in H13.
          * inv HEQ.
          * rewrite if_false. simpl. auto. unfold not. intros.
            apply eq_sym in H. autorewrite with norm in H.
            assert(Z.of_nat pp <= Z.of_nat Fanout).
            { apply inj_le  in SUBNODE. rep_omega. }
            rewrite H in H0. rewrite Fanout_eq in H0. simpl in H0. compute in H0. apply H0. auto.
          * rewrite if_false. simpl. auto. unfold not. intros.
            autorewrite with norm in H.
            assert(Z.of_nat ii <= Z.of_nat Fanout).
            { apply inj_le  in SUBNODE. rep_omega. }
            rewrite H in H0. rewrite Fanout_eq in H0. simpl in H0. compute in H0. apply H0. auto.
          * rewrite if_false. simpl. auto. unfold not. intros.
            rewrite Int.unsigned_repr in H by rep_omega. rewrite Int.unsigned_repr in H by rep_omega.
            apply Nat2Z.inj in H. subst. rewrite <- beq_nat_refl in HEQ. inv HEQ. }
      change_compspecs CompSpecs. cancel. apply wand_frame_elim.
    + forward.                  (* t'2=0 *)
      entailer!.
      rewrite Int.signed_repr in H6.
      assert(Zlength subc -1 >? 0 = false).
      { destruct subc. auto. destruct subc. auto. rewrite Zlength_cons in H6.
        rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6. rewrite Zlength_correct in H6.
        omega. }
      rewrite H11. simpl. auto.
      split. rep_omega. assert(0 <= Zlength c - 1 < 20).
      { eapply partial_complete_length. right. eauto. auto. }
      unfold subc. rewrite Zlength_sublist. rep_omega.
      split. omega. rep_omega. rep_omega.
    + forward_if.
      * forward.                (* skip *)
        unfold cursor_rep. unfold r. Intros anc_end1. Intros idx_end1.
        forward.                (* t'15=cursor->level *)
        forward.                (* cursor->level = t'15-1 *)
        { entailer!. unfold subc.
          assert(0 <= Zlength c - 1 < 20).
          { eapply partial_complete_length. right. eauto. auto. }
          rewrite Zlength_sublist.
          rewrite Int.signed_repr. rewrite Int.signed_repr.
          rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. }
        assert(i0 + 1 <= Zlength c).
        { apply andb_true_iff in H6. destruct H6.
          unfold subc in H6. rewrite Zlength_sublist in H6 by rep_omega.
          apply Zgt_is_gt_bool in H6. omega. }
        Exists (i0+1). entailer!. unfold cursor_rep. unfold r.
        { simpl in H4. rewrite H4. fold subc.
          apply andb_true_iff in H6. destruct H6.
          destruct subc as [|[subn subi] subc'] eqn:HSUBC.
          - simpl in H6. apply Z.gtb_lt in H6. omega.
          - simpl in H16. simpl. rewrite H16.
            unfold subc in HSUBC.
            apply sublist_tl in HSUBC. rewrite HSUBC.
            rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6. rewrite <- HSUBC.
            destruct subc'. rewrite Zlength_nil in H6. apply Z.gtb_lt in H6. omega.
            auto. omega. }
        Exists ((getval (currNode subc r))::anc_end1).
        Exists ((Vint(Int.repr(rep_index(entryIndex subc))))::idx_end1).
        cancel.
        rewrite Zlength_sublist. unfold subc. rewrite Zlength_sublist. unfold r.
        replace (Zlength c - (i0 + 1) - 1) with  (Zlength c - i0 - 1 - 1) by rep_omega.
        unfold_data_at 1%nat. unfold_data_at 1%nat. cancel. repeat rewrite <- map_rev.

        rewrite sublist_split with (mid:=i0+1) at 1. rewrite rev_app_distr.
        erewrite sublist_len_1. simpl. rewrite list_append_map. rewrite <- app_assoc.
        simpl.
        replace(snd (Znth i0 c)) with (entryIndex (sublist i0 (Zlength c) c)).
        cancel.
        rewrite sublist_split with (mid:=i0+1) at 1. rewrite rev_app_distr.
        erewrite sublist_len_1. simpl. rewrite list_append_map. rewrite list_append_map.
        rewrite <- app_assoc.
        simpl.
        replace(fst(Znth i0 c)) with (currNode (sublist i0 (Zlength c) c) (root,prel)).
        cancel.
        rewrite sublist_split with (mid:=i0+1).
        erewrite sublist_len_1. simpl. unfold fst. auto.
        rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega.
        rewrite sublist_split with (mid:=i0+1).
        erewrite sublist_len_1. simpl. unfold snd. auto.
        rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega.
        rep_omega. rep_omega. rep_omega.
      * forward.                (* break *)
        entailer!. simpl in H4. rewrite H4. fold subc.
        apply andb_false_iff in H6.
        assert(subc = up_at_last subc).
        { destruct H6.
          - destruct subc. simpl. auto. destruct subc. simpl. destruct p. auto.
            repeat rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6.
            rewrite Z.gtb_ltb in H6. apply Z.ltb_ge in H6.
            assert(0 <= Zlength subc) by apply Zlength_nonneg. omega.
          - destruct subc as [|[subn subi] subc'].
            + simpl. auto.
            + simpl. simpl in H6. rewrite H6. destruct subc'. auto. auto. }
        Exists i0.
        rewrite H12 at 1. entailer!.
  - unfold cursor_rep. Intros uali. Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'12=cursor->level *)
    forward.                    (* t'13=cursor->level *)
    assert(UPATLAST: up_at_last c = match c' with
            | [] => [(n, i)]
            | _ :: _ => if index_eqb i (lastpointer n) then up_at_last c' else (n, i) :: c'
                                    end).
    { simpl. auto. }
    assert(RANGE: 0 <= Zlength (up_at_last c) - 1 < 20).
    { apply up_at_last_range. fold c in H. eapply partial_complete_length; eauto. }
    forward.                    (* t'14=cursor->ancidx[t'13] *)
    { entailer!. rewrite <- UPATLAST.
      autorewrite with sublist. rewrite Znth_rev.
      rewrite Zlength_map. replace (Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
      destruct (up_at_last c).
      - simpl in RANGE. omega.
      - simpl. auto.
      - rep_omega.
      - rewrite Zlength_map. rep_omega. }
    forward.                    (* cursor->ancestors[t'12] = t'14 +1 *)
    { entailer!. rewrite <- UPATLAST.
      rewrite app_Znth1. rewrite Znth_rev. rewrite Zlength_map.
      replace (Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
      destruct (up_at_last c) as [|[n' i'] up'].
      - simpl in RANGE. omega.
      - simpl. entailer!. unfold complete_cursor in H. destruct H.
        assert(SUBNODE: subnode n' root).
        { assert(partial_cursor_correct_rel ((n, i) :: c') (root, prel) \/ complete_cursor_correct_rel ((n, i) :: c') (root, prel)) by (right; auto).
          apply complete_partial_upatlast in H15. simpl in H15. rewrite <- UPATLAST in H15.
          destruct H15. 
          - apply partial_cursor_subnode in H15. simpl in H15. auto.
          - apply complete_cursor_subnode in H15. simpl in H15. auto. }
        assert((numKeys n' <= Fanout)%nat).
        { unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. auto. }
        clear -H UPATLAST H15.
        assert(partial_cursor_correct_rel ((n, i) :: c') (root, prel) \/ complete_cursor_correct_rel ((n, i) :: c') (root, prel)) by (right; auto).
        apply complete_partial_upatlast in H0.
        assert((n',i')::up' = up_at_last((n,i)::c')).
        { simpl. rewrite UPATLAST. auto. } clear UPATLAST.
        destruct i'. simpl. rep_omega. simpl.
        destruct H0.
        + unfold partial_cursor_correct_rel in H0. rewrite <- H1 in H0.
          destruct(nth_node (ip n0) n'); try contradiction.        
          apply partial_correct_index in H0. simpl in H0.
          rewrite Int.signed_repr. rep_omega. rep_omega.
        + unfold complete_cursor_correct_rel in H0.
          destruct(getCEntry (up_at_last ((n, i) :: c'))); try contradiction.
          destruct e; try contradiction.
          rewrite <- H1 in H0.
          apply complete_correct_index in H0. simpl in H0.
          rewrite Int.signed_repr. rep_omega. rep_omega.
      - rep_omega.
      - rewrite Zlength_map. rep_omega.
      - rewrite Zlength_rev. rewrite Zlength_map. rep_omega. } deadvars!. rewrite <- UPATLAST.
    gather_SEP 1 2. pose(cincr := next_cursor (up_at_last c)).
    replace_SEP 0 (cursor_rep cincr r pc).
    {  unfold cursor_rep. entailer!.
       Exists anc_end0. Exists idx_end0. cancel.
       rewrite <- UPATLAST. unfold cincr.

       Lemma length_next_cursor: forall (X:Type) (c:cursor X),
           Zlength (next_cursor c) = Zlength c.
       Proof.
         intros. destruct c. simpl. auto. simpl. destruct p.
         rewrite Zlength_cons. rewrite Zlength_cons. auto.
       Qed.

       rewrite length_next_cursor.
       rewrite upd_Znth_app1.
       
       Lemma fst_next_cursor: forall (X:Type) (c:cursor X),
           map fst c = map fst (next_cursor c).
       Proof.
         intros. destruct c. simpl. auto. destruct p. simpl. auto.
       Qed.

       rewrite fst_next_cursor. (* rewrite <- map_rev. *)

       Lemma upd_Znth_rev: forall (X:Type) (l:list X) v,
           l <> [] ->
           upd_Znth (Zlength l -1) (rev l) v = rev(upd_Znth 0 l v).
       Proof.
         intros. destruct l.
         - exfalso. apply H. auto.
         - simpl. rewrite Zlength_cons. rewrite Zsuccminusone.
           rewrite upd_Znth_app2. rewrite Zlength_rev.
           replace (Zlength l - Zlength l) with 0.
           rewrite upd_Znth0. rewrite Zlength_cons. simpl. rewrite sublist_nil.
           rewrite sublist_1_cons. rewrite Zsuccminusone. rewrite sublist_same. auto.
           auto. auto. omega. rewrite Zlength_rev. rewrite Zlength_cons.
           simpl. omega.
       Qed.

       rewrite app_Znth1.
       rewrite Znth_rev. rewrite Zlength_map.
       replace(Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
       
       destruct (up_at_last c) as [|[upn upi] upc] eqn:HUP.
       { simpl in RANGE. omega. }
       simpl.
       rewrite upd_Znth_app2.
       rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_cons.
       rewrite Zsuccminusone. replace (Zlength upc - Zlength upc) with 0.
       rewrite upd_Znth0. rewrite Zlength_cons. simpl. rewrite sublist_nil.
       assert(Vint (Int.add (Int.repr (rep_index upi)) (Int.repr 1)) = Vint (Int.repr (rep_index (next_index upi)))).
       { rewrite add_repr.

         Lemma next_rep: forall i,
             (rep_index i) + 1 = rep_index (next_index i).
         Proof.
           intros. destruct i.
           - simpl. auto.
           - simpl. rewrite Zpos_P_of_succ_nat. omega.
         Qed.

         rewrite next_rep. auto. }
       rewrite H8. cancel.
       omega.
       rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
       rewrite Zlength_cons. simpl. omega.
       omega.
       rewrite Zlength_map. omega.
       rewrite Zlength_rev. rewrite Zlength_map. omega.
       split. destruct(up_at_last c). simpl in RANGE. omega. rewrite Zlength_cons. rewrite Zsuccminusone.
       apply Zlength_nonneg.
       rewrite Zlength_rev. rewrite Zlength_map. omega. }
    forward_call(r,cincr,pc).       (* t'6=currNode(cursor) *)
    { fold r. cancel. }

    Lemma movetonext_correct: forall c r,
        complete_cursor c r -> isValid c r = true ->
        ne_partial_cursor (next_cursor (up_at_last c)) r \/ complete_cursor (next_cursor(up_at_last c)) r.
    Proof.
    Admitted.

    { unfold r. split; auto. apply movetonext_correct. auto. auto. }
    assert(SUBNODE: subnode (currNode cincr r) root).
    { apply movetonext_correct in H. fold c cincr in H.
      destruct H. inv H. apply partial_cursor_subnode in H5. simpl in H5. auto.
      inv H. apply complete_cursor_subnode in H5. simpl in H5. auto. auto. }
    pose(currnode:= currNode cincr r). fold currnode.
    destruct currnode eqn:HCURR. simpl.
    apply subnode_rep in SUBNODE. rewrite SUBNODE. Intros. fold currnode.
    rewrite unfold_btnode_rep with (n:=currnode) at 1. rewrite HCURR.
    Intros ent_end.
    forward.                    (* t'11=t'6->isLeaf *)
    { entailer!. destruct b; simpl; auto. }
    gather_SEP 2 3 4 5.
    replace_SEP 0 (btnode_rep (btnode val o l b b0 b1 v)).
    { entailer!. rewrite unfold_btnode_rep with (n:=btnode val o l b b0 b1 v).
      Exists ent_end. entailer!. }
    gather_SEP 0 3.
    replace_SEP 0 (btnode_rep root).
    { entailer!. apply wand_frame_elim. }
    forward_if.                 (* if t'11 *)
    + forward.                  (* return *)
      entailer!. fold r. fold c.
      assert(cincr = moveToNext c r).
      { unfold cincr. unfold moveToNext. fold r in H2.
        destruct (get_numrec r).
        { simpl in H2. exfalso. apply H2. auto. }
        rewrite VALID. unfold cincr in HCURR.
        destruct(next_cursor(up_at_last c)).
        { admit. }              (* can't be empty *)
        destruct p. simpl in HCURR.
        destruct b.
        rewrite HCURR. simpl. auto.
        apply typed_true_of_bool in H5. inv H5. }
      rewrite H11. cancel.
    + forward.                  (* skip *)
      forward_call(r,cincr,pc).     (* t'7=currnode(cursor) *)
      { unfold relation_rep. unfold r. change_compspecs CompSpecs. cancel. }
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. }
      forward_call(r,cincr,pc). (* t'8 = entryIndex(cursor) *)
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. }
      (* forward.                  (* t'9=t'7 -> entries + t'8 ->ptr.child *) *)
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