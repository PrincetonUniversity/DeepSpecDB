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
Require Import btrees.btrees_spec.
Require Import btrees.verif_movetonext.

Lemma body_RL_GetKey: 
  semax_body Vprog Gprog f_RL_GetKey RL_GetKey_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H2; inv H2. }
  pose (c:=(n,i)::c').
  forward_call(r,c,pc).  (* t'1=isValid(cursor) *)
  { unfold r. unfold c. cancel. }
  forward_if 
  (PROP () 
  LOCAL (temp _cursor pc) 
  SEP (mem_mgr gv; relation_rep (root, prel); cursor_rep ((n, i) :: c') (root, prel) pc)).
  - forward.                    (* skip *)
    unfold r. unfold c. entailer!.
  - assert_PROP(False). (*fold c r in H1.*) rewrite H1 in H6. simpl in H6. inv H6. contradiction.
  - forward_call(r,c,pc). (* t'2=entryIndex(cursor) *)
    { fold r c. cancel. }
    forward_call(r,c,pc). (* t'3=currnode(cursor) *)
    unfold c. simpl.
    assert(SUBNODE: subnode n root).
    { destruct H2. apply complete_cursor_subnode in H2. simpl in H2. auto. }
    assert(SUBREP: subnode n root) by auto. apply subnode_rep in SUBREP.
    rewrite SUBREP.
    destruct n as [ptr0 le isLeaf First Last pn].
    pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
    rewrite unfold_btnode_rep with (n:=n) at 1. unfold n.
    Intros ent_end.
    forward.                    (* t'7=t'3->numKeys *)
    sep_apply (fold_btnode_rep ptr0). fold n.
    sep_apply modus_ponens_wand.
    unfold r.
    sep_apply fold_relation_rep. fold r.
    deadvars!. simpl node_le. fold n. fold n in c. fold c.
    pose (normc := normalize c r).
    forward_if(PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Zlength le)));
     temp _t'2 (Vint (Int.repr i)); temp _cursor pc)
     SEP (mem_mgr gv; relation_rep r; cursor_rep normc r pc; emp)).
     { forward_call(c,pc,r).
      entailer!. unfold normc. simpl.
      apply (f_equal Int.signed) in H6.
      unfold root_wf, node_wf, n in H4. apply H4 in SUBNODE. simpl in SUBNODE.
      rewrite Int.signed_repr in H6.
      rewrite Int.signed_repr in H6.
      subst.
      rewrite Z.eqb_refl. cancel.
      rep_lia. destruct H2. 
      clear - SUBNODE H2. hnf in H2. simpl in H2.
      destruct (Znth_option i le) eqn:?H2; try contradiction.
       apply Znth_option_some in H0. rep_lia. }
      { forward.                  (* skip *)
        entailer!. unfold normc. unfold n. simpl.
        rewrite (proj2 (Z.eqb_neq i (Zlength le))); auto. 
        contradict H6. f_equal; auto. }
    assert(CORRECT: complete_cursor normc r).
    unfold normc. unfold normalize. unfold c.
    destruct (Z.eqb i (Zlength (node_le n))). apply movetonext_complete. auto.
      auto.
    forward_call(r,normc,pc). (* t'4=currnode(cursor) *)
    forward_call(r,normc,pc). (* t'5=entryIndex(cursor) *)
    unfold relation_rep. unfold r.
    assert(CORRECTNORM: complete_cursor normc r) by auto.
    destruct CORRECT.
    destruct normc as [|[normn normi] normc'] eqn:HNORMC.
    inv H6.
    assert(SUBNODE': subnode normn root).
    { apply complete_cursor_subnode in H6. simpl in H6. auto. }
    assert(SUBREP': subnode normn root) by auto. apply subnode_rep in SUBREP'.
    simpl.
    rewrite SUBREP'. rewrite unfold_btnode_rep with (n:=normn) at 1.
    destruct normn as [nptr0 nle nleaf nfirst nlast nx] eqn:HNORMN.
    Intros ent_end0. simpl. deadvars!.
    assert(ZNTH: 0 <= normi < Zlength nle). {
      clear - H6.
      hnf in H6; simpl in H6.
      destruct (Znth_option normi nle) eqn:?H; try contradiction.
      apply Znth_option_some in H; auto.
   } 
   apply Znth_option_in_range in ZNTH. 
    destruct ZNTH as [e ZNTH].
    assert(ZTL: Znth_option normi nle = Some e) by auto.
    apply Znth_to_list' with (endle:=ent_end0) in ZTL.
    assert(INTEGRITY: subnode normn root) by (rewrite HNORMN; auto).
    apply H5 in INTEGRITY. rewrite HNORMN in INTEGRITY.
    assert(LEAF: nleaf = true).
    { destruct nleaf. auto. apply complete_leaf in CORRECTNORM. simpl in CORRECTNORM.
      contradiction. }
    eapply integrity_nth_leaf in INTEGRITY.
    2: rewrite LEAF; simpl; auto.
    2: eauto.
    destruct INTEGRITY as [k [v [x HE]]].
    assert(LESPLIT: Znth_option normi nle = Some e) by auto.
    apply le_iter_sepcon_split in LESPLIT. rewrite LESPLIT. Intros.
    assert (H99: 0 <= normi < Fanout). {
     pose proof (H4 _ SUBNODE').
     apply node_wf_numKeys in H8. simpl in H8. clear - H8 H6.
      hnf in H6; simpl in H6.
      destruct (Znth_option normi nle) eqn:?H; try contradiction.
      apply Znth_option_some in H. rep_lia. 
    }
    forward.                    (* t'6=t'4->entries[t'5]->ptr.record *)
    { unfold Inhabitant_entry_val_rep in ZTL. 
      rewrite ZTL. rewrite HE. simpl entry_val_rep.
      unfold entry_rep at 1, value_rep at 1.  entailer!.
    }
    sep_apply (modus_ponens_wand (entry_rep e)).
    sep_apply (fold_btnode_rep nptr0). rewrite <- HNORMN.
    sep_apply (modus_ponens_wand).
    forward. entailer!.                   (* return t'6 *)
    unfold Inhabitant_entry_val_rep in ZTL. rewrite ZTL. entailer!. 
    { simpl. unfold RL_GetKey. fold n. fold c. fold r. rewrite HNORMC.
      unfold getCKey. simpl. rewrite ZNTH. auto. }
    rewrite <- HNORMC. unfold normalize. unfold c. unfold n. simpl. unfold r. cancel.
    rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel.
Qed.