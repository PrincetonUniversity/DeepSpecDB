(** * verif_putrecord.v : Correctness proof of putEntry and RL_PutRecord *)

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
Require Import verif_newnode.
Require Import verif_movetokey.
Require Import verif_currnode.
Require Import verif_entryindex.
Require Import verif_splitnode.

Lemma body_putEntry: semax_body Vprog Gprog f_putEntry putEntry_spec.
Proof.
  start_function.
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  destruct r as [root prel]. pose (r:=(root,prel)).
  forward.                      (* t'44=cursor->level *)
  forward_if.                   (* if t'44=-1 *)
  (* split root case *)
  - forward_call(false,true,true). (* t'1=createnewnode(false,true,true) *)
    Intros vnewnode.
    gather_SEP 1 2. replace_SEP 0 (cursor_rep c r pc).
    { entailer!. unfold cursor_rep. Exists anc_end. Exists idx_end. unfold r. cancel.
      change_compspecs CompSpecs. cancel. } clear anc_end. clear idx_end.
    forward_if(PROP (vnewnode <> nullval) LOCAL (temp _currNode__1 vnewnode; temp _t'44 (Vint (Int.repr (Zlength c - 1))); temp _cursor pc; temp _newEntry pe; temp _key (key_repr oldk)) SEP (cursor_rep c r pc; btnode_rep (empty_node false true true vnewnode); relation_rep (root, prel); entry_rep e)).
    + apply denote_tc_test_eq_split.
      replace (vnewnode) with (getval (empty_node false true true vnewnode)). entailer!.
      simpl. auto.
      entailer!.
    + forward.                  (* skip *)
      entailer!.
    + assert_PROP(False). unfold empty_node. entailer!. contradiction.
    + unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
      forward.                  (* t'52=cursor->relation *)
      unfold relation_rep. Intros.
      forward.                  (* t'53=t'52->root *)
      unfold empty_node.
      rewrite unfold_btnode_rep. Intros ent_end.
      forward.                  (* currnode1->ptr0=t'53 *)
      forward.                  (* currnode1->numKeys=1 *)
      admit.
  - forward.                    (* skip *)
    destruct c as [|[currnode entryidx] c'] eqn:HC.
    { simpl in H0. exfalso. apply H3. rewrite Int.neg_repr. auto. }
    forward_call(r,c,pc).       (* t'26=currnode(cursor) *)
    { unfold r. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. change_compspecs CompSpecs.
      cancel. rewrite HC. simpl. cancel. }
    { rewrite HC. unfold r. split.
      destruct H. right. auto. left. unfold ne_partial_cursor.
      destruct H. split; auto. split; auto. simpl. omega. auto. }
    rewrite HC. simpl.
    assert(SUBNODE: subnode currnode root).
    { destruct H. destruct H. apply complete_cursor_subnode in H. simpl in H. auto.
      destruct H. apply partial_cursor_subnode in H. simpl in H. auto. }
    assert(SUBREP: subnode currnode root) by auto.
    apply subnode_rep in SUBREP.
    destruct currnode as [ptr0 le isLeaf First Last x].
    pose(currnode := btnode val ptr0 le isLeaf First Last x). simpl.
    rewrite SUBREP. fold currnode.
    rewrite unfold_btnode_rep with (n:=currnode) at 1. unfold currnode. Intros ent_end.
    forward.                    (* t'27=t'26->isLeaf *)
    { destruct isLeaf; entailer!. }
    admit.
Admitted.

Lemma gotokey_complete: forall c r key,
    complete_cursor c r ->
    complete_cursor (goToKey c r key) r.
Proof.
Admitted.

Lemma putentry_complete: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    complete_cursor newc newr.
Proof.
Admitted.

Lemma putentry_depth: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    correct_depth r ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    correct_depth newr.
Proof.
Admitted.

Lemma putentry_wf: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    root_wf (get_root r) ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    root_wf (get_root newr).
Proof.
Admitted.

Lemma putentry_integrity: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    root_integrity (get_root r) ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    root_integrity (get_root newr).
Proof.
Admitted.

Lemma putentry_numrec: forall c r e oldk newx d newc newr,
    complete_cursor c r ->
    Z.of_nat(get_numrec r) < Int.max_signed - 1 ->
    putEntry val c r e oldk newx d = (newc, newr) ->
    Z.of_nat(get_numrec newr) < Int.max_signed.
Proof.
Admitted.

Lemma body_RL_PutRecord: semax_body Vprog Gprog f_RL_PutRecord RL_PutRecord_spec.
Proof.
  start_function.
  forward_if(PROP (pc <> nullval)
     LOCAL (lvar _newEntry (Tstruct _Entry noattr) v_newEntry; temp _cursor pc;
     temp _key (key_repr key); temp _record (value_repr record))
     SEP (data_at_ Tsh (Tstruct _Entry noattr) v_newEntry; relation_rep r; cursor_rep c r pc)).
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False). entailer!. contradiction.
  - fold tentry.
    forward.                    (* newentry.ptr.record=record *)
    forward.                    (* newentry.key=key *)
    forward_call(c,pc,r,key).   (* gotokey(cursor,key) *)
    forward_call((goToKey c r key),pc,r,(keyval val key record (field_address tentry [UnionField _record; StructField _ptr] v_newEntry)), v_newEntry, key). (* putEntry(cursor,newEntry,key *)
    + unfold entry_rep, value_rep, value_repr.
      unfold_data_at 1%nat.
      erewrite field_at_Tunion with (t:=tentry) (gfs:=[StructField _ptr]) (v1:=(inr(Vint(Int.repr(v_ record))))) (p:=v_newEntry).
      2:reflexivity. 2:apply JMeq_refl.
      simpl. unfold withspacer. rewrite if_true by omega.
      rewrite field_at_data_at with (gfs:=[UnionField _record; StructField _ptr]).
      simpl. cancel.
    + split3; auto. left. apply gotokey_complete. auto.
    + Intros newx.
      destruct(putEntry val (goToKey c r key) r) as [newc newr] eqn:HPUTENTRY.
      forward_call(newc,pc,newr). (* RL_MoveToNext(cursor) *)
      * cancel.
      * apply gotokey_complete with (key:=key) in H.
        split3.
        eapply putentry_complete. eauto. eauto.
        eapply putentry_depth. eauto. eauto. eauto.
        split3.
        eapply putentry_wf. eauto. auto. eauto.
        eapply putentry_integrity. eauto. auto. eauto.
        eapply putentry_numrec. eauto. auto. eauto.
      * forward.                (* return *)
        Exists newx.
        Exists((field_address tentry [UnionField _record; StructField _ptr] v_newEntry)).
        entailer!. unfold RL_PutRecord.
        rewrite HPUTENTRY.
        cancel. fold tentry. unfold value_rep.
        eapply derives_trans.
        2:eapply data_at_data_at_ with (v:=(key_repr key, inr (value_repr record))).
        unfold_data_at 2%nat.
        erewrite field_at_Tunion with (t:=tentry) (gfs:=[StructField _ptr]) (v1:=(inr(Vint(Int.repr(v_ record))))) (p:=v_newEntry).
        2: reflexivity. 2: apply JMeq_refl.
        simpl. unfold withspacer. rewrite if_true by omega. cancel.
        rewrite field_at_data_at. simpl. cancel.
Qed.
