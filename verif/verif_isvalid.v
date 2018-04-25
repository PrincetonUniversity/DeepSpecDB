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
  forward_call(r,c,pc).      (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc).      (* t'2=currNode *)
  assert (COMPLETE: complete_cursor c r) by auto.
  unfold complete_cursor in H. destruct H.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct c as [|[n i] c'].
  simpl in H0. contradiction.          (* the empty cursor can't be complete *)
  pose (c:=(n,i)::c'). fold c.
  assert (n = currNode c r). simpl. auto.
  simpl in H0. destruct i as [|ii]. contradiction.
  apply complete_cursor_subnode in H. unfold get_root in H. simpl in H.
  unfold relation_rep. unfold r.
  rewrite subnode_rep with (n:=currNode c (root,numRec,depth,prel)) by auto. Intros.
  rewrite unfold_btnode_rep at 1.
  assert(currNode c r = currNode c (root,numRec,depth,prel)). auto.
  destruct (currNode c (root,numRec,depth,prel)) as [ptr0 le b First Last pn]. Intros.
  pose (currnode:= btnode val ptr0 le b First Last pn).
  forward.                      (* t'5=t'2->numKeys *)
  gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep (currNode c r)).
  { rewrite unfold_btnode_rep. rewrite H2. entailer!. }
  
  forward_if  (PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last pn)))));
     temp _t'2 (getval (btnode val ptr0 le b First Last pn)); temp _t'1 (rep_index (entryIndex c));
     temp _cursor pc; temp _t'3 (Val.of_bool (negb (isValid c r))) (* new local *))
     SEP (btnode_rep (currNode c r); malloc_token Tsh trelation prel;
     data_at Tsh trelation
       (getval root, (Vint (Int.repr (Z.of_nat numRec)), Vint (Int.repr (Z.of_nat depth)))) prel;
     btnode_rep (btnode val ptr0 le b First Last pn) -* btnode_rep root;
     cursor_rep c (root, numRec, depth, prel) pc)).

  - forward_call(r,c,pc).
    + unfold r. cancel. unfold relation_rep.
      cancel.
      change_compspecs btrees.CompSpecs.
      cancel. eapply derives_trans. fold r. rewrite H2. apply wand_frame_elim. cancel.
    + unfold relation_rep. unfold r. Intros.
      rewrite subnode_rep with (n:=currNode c r) by auto.
      rewrite H2. fold r.
      rewrite unfold_btnode_rep at 1.
      Intros. rewrite H2.
      forward.                  (* t'6=t'4->LastLeaf *)
      * autorewrite with norm. entailer!. destruct Last; simpl; auto.
      * forward.                (* t'3=(tbool) (t'6==1) *)
        entailer!.
        { unfold isValid.
          rewrite H2. destruct Last; simpl; auto.
          admit.                (* true from H3 *)
        }
        assert(n = currNode c r). simpl. auto. rewrite H13.
        rewrite unfold_btnode_rep. rewrite H2.
        entailer!. fold r. apply derives_refl.
  - forward.                    (* t'3=0 *)
    entailer!.
    unfold isValid. rewrite H2.
    destruct Last; auto.
    assert(index.index_eqb (entryIndex c) (index.ip (numKeys_le le)) = false).
    { unfold index.index_eqb.
      unfold entryIndex. unfold c.
      admit.                    (* true from H3 *)
    }
    rewrite H9. auto.
    apply derives_refl.
  - gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. rewrite unfold_btnode_rep at 1. assert(n = currNode c r) by (simpl; auto).
      rewrite H6. rewrite H2. apply wand_frame_elim. }
    gather_SEP 0 1 2. replace_SEP 0 (relation_rep r).
    { entailer!. apply derives_refl. }
    forward_if.
    + forward. fold c. entailer!. fold r. rewrite H3. auto.
    + forward. fold c. entailer!. fold r. rewrite H3. auto.
Admitted.
  
Lemma body_RL_CursorIsValid: semax_body Vprog Gprog f_RL_CursorIsValid RL_CursorIsValid_spec.
Proof.
  start_function.
  forward_if (
      (PROP (pc<>nullval)  LOCAL (temp _cursor pc)  SEP (relation_rep r; cursor_rep c r pc))).
  - forward. entailer!.
  - subst. assert_PROP(False).
    entailer!. contradiction.
  - forward_call(r,c,pc).
    Intros vret. forward.
    entailer!. unfold force_val, sem_cast_pointer.
    destruct (isValid c); simpl; auto.
Qed.

Lemma body_isFirst: semax_body Vprog Gprog f_isFirst isFirst_spec.
Proof.
  start_function.
  (* proof should be similar to isvalid *)
Admitted.
