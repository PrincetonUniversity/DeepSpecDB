(** * verif_getrecord.v : Correctness proof of RL_GetRecord  *)

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
Require Import verif_entryindex.
Require Import verif_currnode.
Require Import verif_isvalid.
Require Import verif_movetonext.

Lemma body_RL_GetRecord: semax_body Vprog Gprog f_RL_GetRecord RL_GetRecord_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H; inv H; inv H2. }
  pose (c:=(n,i)::c').
  forward_call(r,c,pc).  (* t'1=isValid(cursor) *)
  { unfold r. unfold c. cancel. }
  forward_if (PROP () LOCAL (temp _cursor pc) SEP (relation_rep (root, prel); cursor_rep ((n, i) :: c') (root, prel) pc)).
  - forward.                    (* skip *)
    unfold r. unfold c. entailer!.
  - assert_PROP(False). fold c r in H1. rewrite H1 in H4. simpl in H4. inv H4. contradiction.
  - forward_call(r,c,pc). (* t'2=entryIndex(cursor) *)
    { fold r c. cancel. }
    forward_call(r,c,pc). (* t'3=currnode(cursor) *)
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
    sep_apply (fold_btnode_rep ptr0). fold n.
    sep_apply modus_ponens_wand.
    change (get_numrec r) with (get_numrec (root,prel)).
    sep_apply fold_relation_rep. fold r.
    deadvars!. simpl node_le. fold n. fold n in c. fold c.
    pose (normc := normalize c r).
    forward_if(PROP ( )
     LOCAL (temp _t'8 (Vint (Int.repr (Zlength le)));
     temp _t'3 (Vint (Int.repr i)); temp _cursor pc)
     SEP (relation_rep r; cursor_rep normc r pc; emp)).
    { forward_call(c,pc,r). 
      entailer!. unfold normc. simpl.
      apply (f_equal Int.signed) in H4.
      unfold root_wf, node_wf, n in H2. apply H2 in SUBNODE. simpl in SUBNODE.
      rewrite Int.signed_repr in H4.
      rewrite Int.signed_repr in H4.
      subst.
      rewrite Z.eqb_refl. cancel.
      pose proof (Zlength_nonneg le);
      rep_omega. destruct H. 
      clear - SUBNODE H. hnf in H. simpl in H.
      destruct (Znth_option i le) eqn:?H; try contradiction.
       apply Znth_option_some in H0. rep_omega. }
    { forward.                  (* skip *)
      entailer!. unfold normc. unfold n. simpl.
      rewrite (proj2 (Z.eqb_neq i (Zlength le))); auto. contradict H4. f_equal; auto. }
    assert(CORRECT: complete_cursor normc r).
    { unfold normc. unfold normalize. unfold c.
      destruct (Z.eqb i (Zlength (node_le n))). apply movetonext_complete. auto.
      auto. }
    forward_call(r,normc,pc). (* t'4=currnode(cursor) *)
    forward_call(r,normc,pc). (* t'5=entryIndex(cursor) *)
    unfold relation_rep. unfold r.
    assert(CORRECTNORM: complete_cursor normc r) by auto.
    destruct CORRECT.
    destruct normc as [|[normn normi] normc'] eqn:HNORMC.
    inv H4.
    assert(SUBNODE': subnode normn root).
    { apply complete_cursor_subnode in H4. simpl in H4. auto. }
    assert(SUBREP': subnode normn root) by auto. apply subnode_rep in SUBREP'.
(*    apply complete_correct_rel_index in H4.*)  simpl. 
    rewrite SUBREP'. rewrite unfold_btnode_rep with (n:=normn) at 1.
    destruct normn as [nptr0 nle nleaf nfirst nlast nx] eqn:HNORMN.
    Intros ent_end0. simpl. deadvars!.
    assert(ZNTH: 0 <= normi < Zlength nle). {
      clear - H4.
      hnf in H4; simpl in H4.
      destruct (Znth_option normi nle) eqn:?H; try contradiction.
      apply Znth_option_some in H; auto.
   }
    apply Znth_option_in_range in ZNTH.
    destruct ZNTH as [e ZNTH].
    assert(ZTL: Znth_option normi nle = Some e) by auto.
    apply Znth_to_list' with (endle:=ent_end0) in ZTL.
    assert(INTEGRITY: subnode normn root) by (rewrite HNORMN; auto).
    apply H3 in INTEGRITY. rewrite HNORMN in INTEGRITY.
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
     pose proof (H2 _ SUBNODE').
     apply node_wf_numKeys in H6. simpl in H6. clear - H6 H4.
      hnf in H4; simpl in H4.
      destruct (Znth_option normi nle) eqn:?H; try contradiction.
      apply Znth_option_some in H. rep_omega. 
    }
    
    forward.                    (* t'6=t'4->entries[t'5]->ptr.record *)
    { fold Inhabitant_entry_val_rep. rewrite ZTL. rewrite HE. simpl entry_val_rep.
      unfold entry_rep at 1, value_rep at 1.  entailer!.
    }
    sep_apply (modus_ponens_wand (entry_rep e)).
    sep_apply (fold_btnode_rep nptr0). rewrite <- HNORMN.
    sep_apply (modus_ponens_wand).
    forward.                    (* return t'6 *)
    fold Inhabitant_entry_val_rep. rewrite ZTL. entailer!.
    fold Inhabitant_entry_val_rep. rewrite ZTL. entailer!.
    { simpl. unfold RL_GetRecord. fold n. fold c. fold r. rewrite HNORMC.
      unfold getCVal. simpl. rewrite ZNTH. auto. }
    rewrite <- HNORMC. unfold normalize. unfold c. unfold n. simpl. unfold r. cancel.
    rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel.
Qed.
