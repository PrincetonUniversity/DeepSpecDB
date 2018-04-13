(** * verif_movetofirst.v : Correctness proof of moveToFirst *)

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
Require Import index.

Lemma body_moveToFirst: semax_body Vprog Gprog f_moveToFirst moveToFirst_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct n as [ptr0 le isLeaf First Last xn].
  pose (n:=btnode val ptr0 le isLeaf First Last xn). fold n.
  forward_if (
      PROP(pn<>nullval)
      LOCAL(temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
      SEP(relation_rep r pr; cursor_rep c r pc))%assert.
  - apply denote_tc_test_eq_split.
    fold n in H. apply cursor_subnode in H.
    unfold get_root in H. simpl in H.
    rewrite subnode_rep with (n:=n) by auto. Intros pn.
    entailer!.
    entailer!.
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False).
    admit.                      (* we must deduce pn because n is a subnode at pn *)
    contradiction.
  - forward_if (
        (PROP (pn <> nullval; pc <> nullval)
         LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
         SEP (relation_rep r pr; cursor_rep c r pc))).
    + forward. entailer!.
    + assert_PROP(False).
      entailer!. contradiction.
    + forward_if ((PROP (pn <> nullval; pc <> nullval; (Zlength c) >= 0)
     LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
     SEP (relation_rep r pr; cursor_rep c r pc))).
      * forward. entailer!.
      * assert_PROP(False). entailer.
        admit.                  (* contradiction in H4 *)
        contradiction.
      * unfold cursor_rep.
        Intros anc_end. Intros idx_end.        
        forward.                (* cursor->ancestors[level]=node *)
        { entailer!. unfold partial_cursor_wf in H0. destruct H0.
          split. omega. rewrite MTD_eq in H1. auto. }
        forward.                (* cursor->level = level *)
        assert (partial_cursor_correct c n root) by auto.
        apply cursor_subnode in H. unfold get_root in H. simpl in H.
        unfold relation_rep. unfold r. Intros proot. subst pr.
        assert_PROP(proot = getval root).
        rewrite btnode_rep_getval. entailer!.        
        apply subnode_rep with (proot:=proot) in H. rewrite H.
        Intros pn0. rewrite btnode_rep_getval at 1. Intros. subst pn0. rewrite <- H1.
        simpl in H1. subst xn.
        rewrite unfold_btnode_rep at 1. Intros.
        gather_SEP 0 10 11 12.
        replace_SEP 0 (btnode_rep root proot -* relation_rep r prel).
        entailer!. rewrite <- wand_sepcon_adjoint. Exists (getval root). entailer!.
        forward.                (* t'2=node->isLeaf *)
        { entailer!. destruct isLeaf; simpl; auto. }  
        forward_if.
{
  - forward.                    (* cursor->ancestorsIdx[level]=0 *)
    + entailer!. split. omega. unfold partial_cursor_wf in H0. rewrite MTD_eq in H0. destruct H0. auto.
    + gather_SEP 1 2 3 4 5 6 7 8.
      replace_SEP 0 (btnode_rep (btnode val ptr0 le isLeaf First Last pn) pn ).
      entailer!.
      gather_SEP 0 2.
      replace_SEP 0 (btnode_rep root (getval root)).
      entailer!. apply wand_frame_elim.
      gather_SEP 0 1.
      replace_SEP 0 (relation_rep r prel).
      entailer!. eapply derives_trans. apply wand_frame_elim. Intros x. Exists x. entailer!.
      gather_SEP 1 2 3 4 5.
      replace_SEP 0 (cursor_rep (moveToFirst n c (length c)) r pc).
      entailer!. unfold cursor_rep.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      unfold r. fold n.
      assert (Zlength ((n,ip 0)::c) -1 = Zlength c). rewrite Zlength_cons. omega.
      rewrite H1. cancel. 
      autorewrite with sublist. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
      rewrite upd_Znth0. rewrite upd_Znth0. cancel.      
      forward.                  (* return *)
      Exists (getval root). fold r. entailer!.
} {
  forward.                      (* skip *)
  forward.                      (* cursor->ancestorsidx[level]=-1 *)
  - entailer!. split. omega. unfold partial_cursor_wf in H0. destruct H0. rewrite MTD_eq in H1. auto.
  -                             (* recursive call *)
    destruct ptr0 as [ptr0n|] eqn:EQPTR0.
    + destruct ptr0n eqn:EPTR0n. Intros.
      forward.                    (* t'1=node->ptr0 *)
      gather_SEP 1 2 3 4 5 6 7 8 9.
      replace_SEP 0 (btnode_rep (btnode val ptr0 le isLeaf First Last pn) pn ).
      entailer!. rewrite unfold_btnode_rep at 1. entailer!.
      subst proot.
      gather_SEP 0 2.
      replace_SEP 0 (btnode_rep root (getval root)).
      rewrite EQPTR0. pose (btnoderep:=btnode_rep (btnode val (Some (btnode val o l b b0 b1 v)) le isLeaf First Last pn) pn). fold btnoderep.
      pose(btroot:=btnode_rep root (getval root)). fold btroot.
      entailer!. apply wand_frame_elim.
      gather_SEP 0 1.
      replace_SEP 0 (relation_rep r prel).
      entailer!. eapply derives_trans. apply wand_frame_elim. Intros x. Exists x. entailer!.
      forward_call(r,prel,((n,im)::c),pc,ptr0n,v). (* moveToFirst *)
      * clear -H0.
        unfold partial_cursor_wf in H0. destruct H0.
        (* rep_omega does not work here. should it? *)
        admit.
      * entailer!. repeat apply f_equal. rewrite Zlength_cons. omega.
      * unfold cursor_rep. unfold r.
        Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
        assert (Zlength ((n,im)::c) -1 = Zlength c). rewrite Zlength_cons. omega.
        rewrite H7. change_compspecs CompSpecs. cancel.
        autorewrite with sublist. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
        rewrite upd_Znth0. rewrite upd_Znth0. cancel.
        admit.                  (* force val *)
      * split. simpl. split; auto.
        split. admit.           (* cursor might be too big *)
        split. rewrite EPTR0n. auto. auto.
      * forward.                (* return *)
        instantiate (Frame:=[]).
        Exists (getval root). entailer!.
        fold r. destruct b eqn:HB; simpl; fold n.
        cancel.
        assert((S (length c + 1)) = (length c + 1 + 1)%nat) by omega.
        rewrite H14. cancel. 
    +                           (* ptr0 has to be defined on an intern node *)
      assert (subnode n root). apply cursor_subnode with (c:=c). auto.
      unfold root_integrity in H2. unfold get_root in H2. simpl in H2.
      apply H2 in H8. unfold node_integrity in H8.
      unfold n in H8. rewrite H1 in H8. contradiction.
Admitted.