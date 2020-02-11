(** * verif_gotokey.v : Correctness proof of AscendToParent and goToKey *)

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
Require Import verif_findindex.
Require Import verif_isnodeparent.
Require Import verif_movetokey.

Lemma body_AscendToParent: semax_body Vprog Gprog f_AscendToParent AscendToParent_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  forward.                      (* t'4=cursor->level *)
  forward_if.
  - forward.                    (* return *)
    entailer!. destruct c.
    + simpl. unfold cursor_rep.
      Exists anc_end. Exists idx_end. simpl. cancel.
    + rewrite Zlength_cons in H3. rewrite Zsuccminusone in H3.
      apply partial_complete_length in H; auto. rewrite Zlength_cons in H. rewrite Zsuccminusone in H.
      apply (f_equal Int.unsigned) in H3. rewrite Int.unsigned_repr in H3; try rep_omega.
      rewrite Int.unsigned_repr in H3; try rep_omega. destruct c as [|[n i] c'].
      * simpl. destruct p. simpl. unfold cursor_rep.
        Exists anc_end. Exists idx_end. cancel.
      * rewrite Zlength_cons in H3. rep_omega.
  - forward_call(r,c,pc).       (* t'1=currnode(cursor) *)
    { unfold r. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. }
    destruct c as [|[n i] c'] eqn:HC.
    { destruct H. inv H. simpl in H5. rewrite Zlength_nil in H5; omega. inv H. inv H4. } simpl.
    assert(SUBNODE: subnode n root).
    { destruct H.
      - inv H. apply partial_cursor_subnode in H4. simpl in H4. auto.
      - inv H. apply complete_cursor_subnode in H4. simpl in H4. auto. }
    forward_call(n,key).          (* t'2=isNodeParent(t'1,key) *)
    { apply subnode_rep in SUBNODE. rewrite SUBNODE. cancel. }
    sep_apply modus_ponens_wand.
    forward_if.                 (* if t'2=1 *)
    + forward.                  (* return *)
      entailer!.
      destruct c' as [|ni' c'].
      { simpl in H3. exfalso. apply H3. auto. }
      unfold AscendToParent.
      destruct (isNodeParent n key); unfold r, relation_rep.
      cancel.
      rewrite <- Vptrofs_repr_Vlong_repr by auto. cancel. 
      simpl in H4. inv H4.
    + unfold cursor_rep.
      Intros anc_end0. Intros idx_end0. unfold r.
      forward.                  (* t'3=cursor->level *)
      forward.                  (* cursor->level = t'3 -1 *)
      { entailer!. rewrite Zlength_cons. rewrite Zsuccminusone.
        apply partial_complete_length in H. rewrite Zlength_cons in H. rewrite Zsuccminusone in H.
        rewrite Int.signed_repr by rep_omega.
        rewrite Int.signed_repr by rep_omega. rep_omega. auto. }
      forward_call(c',pc,key,r).   (* ascendtoparent(cursor,key) *)
      * unfold cursor_rep. Exists (getval n :: anc_end0). Exists (Vint(Int.repr i) :: idx_end0).
        unfold r.
        simpl. cancel. rewrite Zlength_cons. rewrite Zsuccminusone.
        replace (Int.sub (Int.repr (Zlength c')) (Int.repr 1)) with (Int.repr(Zlength c' - 1)).
        rewrite <- app_assoc. rewrite <- app_assoc. simpl. cancel.
        apply partial_complete_length in H; auto.
        rewrite Zlength_cons in H. rewrite Zsuccminusone in H. unfold Int.sub.
        rewrite Int.unsigned_repr by rep_omega. rewrite Int.unsigned_repr by rep_omega. auto.
      * split. left. unfold ne_partial_cursor.
        split.
        { destruct H.
          - inv H. simpl in H5. destruct (nth_node i n) eqn:NTH; try contradiction.
            destruct H5. unfold partial_cursor_correct_rel.
            destruct c'. auto. destruct p.
            assert(CORRECT:partial_cursor_correct ((n1, z) :: c') n root) by auto.
            simpl in CORRECT. destruct CORRECT. rewrite H8. auto.
          - inv H. unfold complete_cursor_correct_rel in H5.
            destruct (getCEntry ((n,i)::c')); try contradiction.
            destruct e; try contradiction.
            simpl in H5.
            destruct H5. unfold partial_cursor_correct_rel.
            destruct c'. auto. destruct p. simpl in H. destruct H. rewrite H7.
            unfold r; simpl; auto. }
        destruct c'. simpl in H3. exfalso. apply H3. auto. list_solve.
        destruct H; inv H; auto. 
      *
         destruct (isNodeParent n key) eqn:?H; inv H4.
         entailer!. fold r.
         replace (AscendToParent ((n, i) :: c') key) with (AscendToParent c' key)   
            by (simpl; rewrite H5; destruct c'; auto; contradiction H3; reflexivity).
        destruct c' as [|ni' c'']. contradiction H3; reflexivity.
        clear H3. subst r.
        simpl cursor_rep.
        destruct ni'. unfold cursor_rep; Intros al bl; Exists al bl; cancel.
Qed.     

Lemma ne_ascend: forall (X:Type) (c:cursor X) key,
    c <> [] -> AscendToParent c key <> [].
Proof.
  destruct c as [|[n i] c'].
  - intros. exfalso. apply H. auto.
  - intros. generalize dependent n. generalize dependent i. induction c' as [|[n0 i0] c''].
    + simpl. auto.
    + intros. replace (AscendToParent ((n, i) :: (n0, i0) :: c'') key) with (if (isNodeParent n key) then (n,i)::(n0,i0)::c'' else AscendToParent ((n0,i0)::c'') key).
      destruct(isNodeParent n key).
      * auto.
      * apply IHc''. unfold not. intros. inv H0.
      * simpl. auto.
Qed.

Lemma ascend_correct: forall c r key,
    complete_cursor c r ->
    ne_partial_cursor (AscendToParent c key) r \/ complete_cursor (AscendToParent c key) r.
Proof.
Admitted.

Lemma partial_tl: forall (X:Type) p (c:cursor X) r,
    partial_cursor_correct_rel (p::c) r ->
    partial_cursor_correct_rel c r.
Proof.
  intros.
Admitted.

Lemma complete_tl: forall (X:Type) p (c:cursor X) r,
    complete_cursor_correct_rel (p::c) r ->
    partial_cursor_correct_rel c r.
Proof.
  intros.
Admitted.

Lemma body_goToKey: semax_body Vprog Gprog f_goToKey goToKey_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  forward_if(PROP (pc<>nullval) LOCAL (temp _cursor pc; temp _key (Vptrofs key))  SEP (relation_rep r; cursor_rep c r pc)).
  - forward.                    (* skip *)
    fold r. entailer!.
  - assert_PROP(False). entailer!. inv H4.
  - forward_call(c,pc,key,r).   (* ascendtoparent(cursor,key) *)
    forward_call(r,(AscendToParent c key),pc).       (* t'1=currnode(cursor) *)
    { split; auto. destruct c as [|[n i] c]. right. auto.
      apply ascend_correct. auto. }
    unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
    forward.                    (* t'2=cursor-level *)
    destruct(AscendToParent c key) as [|[n i] asc'] eqn:HAS.
    { exfalso. apply ne_ascend in HAS. auto. destruct c. inv H. inv H4. unfold not. intros. inv H4. }
    simpl.
    forward_call(n,key,asc',pc,r). (* movetoKey(t'1,key,cursor,t'2) *)
    { entailer!. rewrite Zlength_cons. rewrite Zsuccminusone. auto. }
    + unfold subcursor_rep. Exists (getval n :: anc_end).
      Exists (Vint(Int.repr i) :: idx_end).
      Exists (Zlength((n,i)::asc') -1).
      unfold r. rewrite <- app_assoc.
      rewrite <- app_assoc. simpl. cancel.
    + split3; auto. apply ascend_correct with (key:=key) in H.
      { rewrite HAS in H. destruct H; inv H.
        - unfold partial_cursor. split; auto.
          eapply partial_tl. eauto.
        - unfold partial_cursor. split; auto.
          eapply complete_tl. eauto. }          
      split3; auto.
      apply ascend_correct with (key:=key) in H. rewrite HAS in H.
      destruct H.
      * inv H. unfold partial_cursor_correct_rel in H4. destruct  (nth_node i n).
        simpl in H4. destruct H4.
        destruct asc'. simpl. subst. auto. simpl in H. destruct p.
        destruct H. simpl. auto. contradiction.
      * inv H. unfold complete_cursor_correct_rel in H4.
        destruct(getCEntry ((n,i)::asc')); try contradiction.
        destruct e; try contradiction. simpl in H4.
        destruct H4.
        destruct asc'. simpl. simpl in H. subst. auto.
        simpl. destruct p. simpl in H. destruct H. auto.
    + forward.                  (* return *)
        entailer!.
      cancel. unfold goToKey. rewrite HAS. fold r. cancel.
Qed.
