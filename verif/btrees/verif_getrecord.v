(** * verif_getrecord.v : Correctness proof of RL_GetRecord  *)

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
Require Import verif_entryindex.
Require Import verif_currnode.
Require Import verif_isvalid.
Require Import verif_movetonext.
Require Import index.

Lemma body_RL_GetRecord: semax_body Vprog Gprog f_RL_GetRecord RL_GetRecord_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H; inv H; inv H2. }
  pose (c:=(n,i)::c').
  forward_call(r,c,pc,numrec).  (* t'1=isValid(cursor) *)
  { unfold r. unfold c. cancel. }
  forward_if (PROP () LOCAL (temp _cursor pc) SEP (relation_rep (root, prel) numrec; cursor_rep ((n, i) :: c') (root, prel) pc)).
  - forward.                    (* skip *)
    unfold r. unfold c. entailer!.
  - assert_PROP(False). fold c r in H1. rewrite H1 in H4. simpl in H4. inv H4. contradiction.
  - forward_call(r,c,pc,numrec). (* t'2=entryIndex(cursor) *)
    { fold r c. cancel. }
    forward_call(r,c,pc,numrec). (* t'3=currnode(cursor) *)
    unfold c. simpl.
    assert(SUBNODE: subnode n root).
    { destruct H. apply complete_cursor_subnode in H. simpl in H. auto. }
    assert(SUBREP: subnode n root) by auto. apply subnode_rep in SUBREP.
    rewrite SUBREP.
    destruct n as [ptr0 le isLeaf First Last pn].
    pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
    rewrite unfold_btnode_rep with (n:=n) at 1. unfold n.
    Intros ent_end.
    forward.                    (* t'7=t'3->numKeys *)
    gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep n).
    { entailer!. rewrite unfold_btnode_rep. unfold n. Exists ent_end. entailer!. }
    gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. unfold n. apply wand_frame_elim. }
    gather_SEP 0 1 2. replace_SEP 0 (relation_rep r numrec).
    { unfold relation_rep, r. entailer!. } deadvars!. simpl numKeys. fold n. fold n in c. fold c.
    pose (normc := normalize c r).
    forward_if(PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Z.of_nat (numKeys_le le))));
     temp _t'2 (Vint (Int.repr (rep_index i))); temp _cursor pc)
     SEP (relation_rep r numrec; cursor_rep normc r pc; emp)).
    { forward_call(c,pc,r,numrec).
      entailer!. unfold normc. simpl.
      apply (f_equal Int.signed) in H4.
      unfold root_wf, node_wf, n in H2. apply H2 in SUBNODE. simpl in SUBNODE.
      rewrite Int.signed_repr in H4.
      rewrite Int.signed_repr in H4.
      destruct i as [|ii]. simpl in H4. omega.
      simpl in H4. apply Nat2Z.inj in H4. subst. simpl.
      rewrite Nat.eqb_refl. cancel.
      rep_omega. destruct H. apply complete_correct_rel_index in H.
      destruct i. simpl. rep_omega. simpl in H. simpl. rep_omega. }
    { forward.                  (* skip *)
      entailer!. unfold normc. unfold n. simpl.
      destruct i as [|ii].
      - simpl. cancel.
      - simpl in H4.
        destruct (ii =? numKeys_le le)%nat eqn:HII.
    + exfalso. apply beq_nat_true in HII. subst. apply H4. auto.
    + simpl. rewrite HII. cancel. }
    assert(CORRECT: complete_cursor normc r).
    { unfold normc. unfold normalize. unfold c.
      destruct (index_eqb i (ip(numKeys n))). apply movetonext_complete. auto.
      auto. }
    forward_call(r,normc,pc,numrec). (* t'4=currnode(cursor) *)
    forward_call(r,normc,pc,numrec). (* t'5=entryIndex(cursor) *)
    unfold relation_rep. unfold r.
    assert(CORRECTNORM: complete_cursor normc r) by auto.
    destruct CORRECT.
    destruct normc as [|[normn normi] normc'] eqn:HNORMC.
    inv H4.
    assert(SUBNODE': subnode normn root).
    { apply complete_cursor_subnode in H4. simpl in H4. auto. }
    assert(SUBREP': subnode normn root) by auto. apply subnode_rep in SUBREP'.
    apply complete_correct_rel_index in H4. simpl.
    rewrite SUBREP'. rewrite unfold_btnode_rep with (n:=normn) at 1.
    destruct normn as [nptr0 nle nleaf nfirst nlast nx] eqn:HNORMN.
    Intros ent_end0. simpl. deadvars!.
    destruct normi as [|normii]. { simpl. inv CORRECTNORM. inv H6. } simpl.
    assert(ZNTH: (normii < numKeys_le nle)%nat).
    { simpl in H4. rewrite <- Nat2Z.inj_lt in H4. auto. }
    apply nth_entry_le_in_range in ZNTH.
    destruct ZNTH as [e ZNTH].
    assert(ZTL: nth_entry_le normii nle = Some e) by auto.
    eapply Znth_to_list with (endle:=ent_end0) in ZTL.
    assert(INTEGRITY: subnode normn root) by (rewrite HNORMN; auto).
    apply H3 in INTEGRITY. rewrite HNORMN in INTEGRITY.
    assert(LEAF: nleaf = true).
    { destruct nleaf. auto. apply complete_leaf in CORRECTNORM. simpl in CORRECTNORM.
      contradiction. auto. }
    eapply integrity_nth_leaf in INTEGRITY.
    2: rewrite LEAF; auto.
    2: eauto.
    
    destruct INTEGRITY as [k [v [x HE]]].
    assert(LESPLIT: nth_entry_le normii nle = Some e) by auto.
    apply le_iter_sepcon_split in LESPLIT. rewrite LESPLIT. Intros.
    
    forward.                    (* t'6=t'4->entries[t'5]->ptr.record *)
    { entailer!. apply H2 in SUBNODE'. unfold node_wf in SUBNODE'.
      simpl in SUBNODE'. simpl in H4. rewrite Fanout_eq in SUBNODE'. rep_omega. }
    { rewrite ZTL. rewrite HE. simpl entry_val_rep.
      unfold entry_rep at 1, value_rep at 1.  entailer.
    }
    gather_SEP 5 6. replace_SEP 0 (le_iter_sepcon nle).
    { entailer!. apply wand_frame_elim. }
    gather_SEP 0 3 4 5. replace_SEP 0 (btnode_rep (btnode val nptr0 nle nleaf nfirst nlast nx)).
    { entailer!. rewrite unfold_btnode_rep with (n:=(btnode val nptr0 nle true nfirst nlast nx)). Exists ent_end0. entailer!. }
    gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. apply wand_frame_elim. }
    forward.                    (* return t'6 *)
    rewrite ZTL. entailer!.
    { simpl. unfold RL_GetRecord. fold n. fold c. fold r. rewrite HNORMC.
      unfold getCVal. simpl. rewrite ZNTH. auto. }
    rewrite <- HNORMC. unfold normalize. unfold c. unfold n. simpl. unfold r. cancel.
Qed.
