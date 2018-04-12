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
  forward_if (
      PROP(pn<>nullval)
      LOCAL(temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
      SEP(relation_rep r pr; cursor_rep c r pc))%assert.
  - apply denote_tc_test_eq_split.
    admit.                       (* valid pointer (getval n) *)
    entailer!.
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False).
    entailer!.                  (* contradiction in H2? *)
    admit.
    inv H4.
  - forward_if (
        (PROP (pn <> nullval; pc <> nullval)
         LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
         SEP (relation_rep r pr; cursor_rep c r pc))).
    + forward. entailer!.
    + assert_PROP(False).
      entailer. inv H5.
    + forward_if ((PROP (pn <> nullval; pc <> nullval; (Zlength c) >= 0)
     LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
     SEP (relation_rep r pr; cursor_rep c r pc))).
      * forward. entailer!.
      * assert_PROP(False). entailer.
        admit.                  (* contradiction in H2 *)
        inv H6.
      * unfold cursor_rep.
        Intros anc_end. Intros idx_end.
        destruct r as [[[root numRec] depth] prel].
        pose (r:=(root,numRec,depth,prel)). fold r.
        forward.                (* cursor->ancestors[level]=node *)
        { entailer!. unfold partial_cursor_wf in H0. destruct H0.
          split. omega. rewrite MTD_eq in H1. auto. }
        forward.                (* cursor->level = level *)
        assert (partial_cursor_correct c n root) by auto.
        apply cursor_subnode in H. unfold get_root in H. simpl in H.
        unfold relation_rep. unfold r. Intros proot. subst pr.
        apply subnode_rep with (proot:=proot) in H. rewrite H.
        Intros pn0. rewrite btnode_rep_getval at 1. Intros. subst pn0. rewrite <- H1.
        destruct n as [ptr0 le isLeaf First Last xn].
        pose (n:=btnode val ptr0 le isLeaf First Last xn). simpl in H1. subst xn.
        rewrite unfold_btnode_rep at 1. Intros.
        forward.                (* t'2=node->isLeaf *)
        { entailer!. destruct isLeaf; simpl; auto. }

forward_if
    (PROP (isLeaf=false)
     LOCAL (temp _t'2 (Val.of_bool isLeaf); temp _cursor pc; temp _node pn;
     temp _level (Vint (Int.repr (Zlength c))))
     SEP (field_at Tsh trelation [StructField _root] proot prel; malloc_token Tsh tbtnode pn;
     field_at Tsh tbtnode [StructField _numKeys]
       (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le isLeaf First Last pn))))) pn;
     field_at Tsh tbtnode [StructField _isLeaf] (Val.of_bool isLeaf) pn;
     field_at Tsh tbtnode [StructField _FirstLeaf] (Val.of_bool First) pn;
     field_at Tsh tbtnode [StructField _LastLeaf] (Val.of_bool Last) pn;
     match ptr0 with
     | Some (@btnode _ _ _ _ _ _ p' as n') =>
         field_at Tsh tbtnode [StructField _ptr0] p' pn * btnode_rep n' p'
     | None => field_at Tsh tbtnode [StructField _ptr0] nullval pn
     end; field_at Tsh tbtnode [StructField _entries] (le_to_list_complete le) pn; 
     le_iter_sepcon le;
     btnode_rep (btnode val ptr0 le isLeaf First Last pn) pn -* btnode_rep root proot;
     field_at Tsh trelation [StructField _numRecords] (Vint (Int.repr (Z.of_nat numRec))) prel;
     field_at Tsh trelation [StructField _depth] (Vint (Int.repr (Z.of_nat depth))) prel;
     malloc_token Tsh trelation prel; malloc_token Tsh tcursor pc;
     field_at Tsh tcursor [StructField _relation] prel pc;
     field_at Tsh tcursor [StructField _level] (Vint (Int.repr (Zlength c))) pc;
     field_at Tsh tcursor [StructField _ancestorsIdx]
       (rev (map (fun x : node val * index => rep_index (snd x)) c) ++ idx_end) pc;
     field_at Tsh tcursor [StructField _ancestors]
       (upd_Znth (Zlength c) (rev (map getval (map fst c)) ++ anc_end)
                 (force_val (sem_cast_pointer pn))) pc))%assert.
{
  - forward.                    (* cursor->ancestorsIdx[level]=0 *)
    + entailer!. split. omega. unfold partial_cursor_wf in H0. rewrite MTD_eq in H0. destruct H0. auto.
    + forward.                  (* return *)
      Exists proot. normalize. cancel.
      eapply derives_trans.
      rewrite wand_sepcon_adjoint. rewrite wand_sepcon_adjoint. rewrite wand_sepcon_adjoint.
      rewrite wand_sepcon_adjoint. rewrite wand_sepcon_adjoint.
      eapply derives_trans.
      apply wand_frame_elim.
      rewrite <- wand_sepcon_adjoint. rewrite <- wand_sepcon_adjoint. rewrite <- wand_sepcon_adjoint.
      rewrite <- wand_sepcon_adjoint. rewrite <- wand_sepcon_adjoint. apply derives_refl.
      cancel.
      unfold cursor_rep. fold n.
      assert (Zlength ((n,ip 0)::c) -1 = Zlength c). rewrite Zlength_cons. omega.
      rewrite H1. autorewrite with sublist. simpl.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      cancel. rewrite <- app_assoc. rewrite <- app_assoc.
      rewrite upd_Znth0. rewrite upd_Znth0. cancel.
} {
  forward.                      (* skip *)
  entailer!.
  apply derives_refl.
} {
  forward.                      (* cursor->ancestorsidx[level]=-1 *)
  - entailer!. split. omega. unfold partial_cursor_wf in H0. destruct H0. rewrite MTD_eq in H33. auto.
  -                             (* recursive call *)
    destruct ptr0 as [ptr0n|] eqn:EQPTR0.
    + destruct ptr0n eqn:EPTR0n. Intros.
      forward.                    (* t'1=node->ptr0 *)
      forward_call(r,prel,((n,im)::c),pc,ptr0n,v). (* moveToFirst *)
      * admit.                                     (* Int.min_signed <= ... <= Int.max_signed *)
      * entailer!. repeat apply f_equal. rewrite Zlength_cons. omega.
      * admit.                  (* relation_rep * cursor_rep *)
      * split.
{ admit.
} {
  split.
  - admit.
    (* we need to be able to prove that the cursor is still partial if we did the recursive call *)
  - rewrite EPTR0n. simpl. auto.
}
      * forward.                (* return *)
        Exists (getval root). entailer!.
        admit.                  (* same cursor_rep *)
    +                           (* ptr0 has to be defined on an intern node *)
      assert (subnode n root). fold n in H6. apply cursor_subnode with (c:=c). auto.
      unfold root_integrity in H2. unfold get_root in H2. simpl in H2.
      apply H2 in H7. unfold node_integrity in H7.
      unfold n in H7. rewrite H1 in H7. inv H7.
Admitted.