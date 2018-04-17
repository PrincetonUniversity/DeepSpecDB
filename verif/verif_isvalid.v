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
  forward_call(r,pr,c,pc).      (* t'1=entryIndex(cursor) *)
  forward_call(r,pr,c,pc).      (* t'2=currNode *)
  unfold cursor_correct_rel in H0.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct c as [|[n i] c'].
  simpl in H0. contradiction.          (* the empty cursor can't happen with cursor_correct_rel *)
  pose (c:=(n,i)::c'). fold c.
  simpl in H0. destruct i as [|ii]. contradiction.
  destruct (nth_entry ii n) eqn:NthEntry; try contradiction.
  destruct e as [k v xv|k child]; try contradiction.
  destruct H0. clear H1.
  apply cursor_subnode in H0.
  unfold relation_rep. unfold r.
  Intros proot. rewrite btnode_rep_getval. Intros.
  rewrite subnode_rep with (n:=currNode c (root,numRec,depth,prel)) by auto.
  Intros pcurr. subst prel. rewrite btnode_rep_getval at 1. Intros.
  rewrite unfold_btnode_rep at 1. rewrite <- H1.
  assert(currNode c r = currNode c (root,numRec,depth,pr)). auto.
  destruct (currNode c (root,numRec,depth,pr)) as [ptr0 le b First Last x]. Intros.
  pose (currnode:= btnode val ptr0 le b First Last x).
  forward.                      (* t'5=t'2->numKeys *)
  simpl in pcurr.

  forward_if (
     (PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last x)))));
            temp _t'2 pcurr; temp _t'1 (rep_index (entryIndex c)); temp _cursor pc;
            temp _t'3 (Val.of_bool (negb (isValid c r))) (* new local *)
           )
     SEP (field_at Tsh trelation [StructField _root] proot pr; malloc_token Tsh tbtnode pcurr;
     field_at Tsh tbtnode [StructField _numKeys]
       (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last x))))) pcurr;
     field_at Tsh tbtnode [StructField _isLeaf] (Val.of_bool b) pcurr;
     field_at Tsh tbtnode [StructField _FirstLeaf] (Val.of_bool First) pcurr;
     field_at Tsh tbtnode [StructField _LastLeaf] (Val.of_bool Last) pcurr;
     match ptr0 with
     | Some (@btnode _ _ _ _ _ _ p' as n') =>
         field_at Tsh tbtnode [StructField _ptr0] p' pcurr * btnode_rep n' p'
     | None => field_at Tsh tbtnode [StructField _ptr0] nullval pcurr
     end; field_at Tsh tbtnode [StructField _entries] (le_to_list_complete le) pcurr;
     le_iter_sepcon le; btnode_rep (btnode val ptr0 le b First Last x) pcurr -* btnode_rep root proot;
     field_at Tsh trelation [StructField _numRecords] (Vint (Int.repr (Z.of_nat numRec))) pr;
     field_at Tsh trelation [StructField _depth] (Vint (Int.repr (Z.of_nat depth))) pr;
     malloc_token Tsh trelation pr; cursor_rep c (root, numRec, depth, pr) pc; emp)))%assert.

  - forward_call(r,pr,c,pc).
    + unfold r. cancel. unfold relation_rep. Exists proot. rewrite prop_true_andp by auto.
      cancel. rewrite fold_btnode_rep by auto.
      change_compspecs btrees.CompSpecs.
      cancel. eapply derives_trans. apply wand_frame_elim. cancel.
    + unfold relation_rep. unfold r. Intros proot'. rewrite btnode_rep_getval. Intros.
      unfold get_root in H0. simpl in H0.
      rewrite subnode_rep with (n:=currNode c r) by auto.
      rewrite H1. Intros pn.
      fold r. rewrite H3. unfold getval.
      rewrite unfold_btnode_rep at 1.
      Intros. subst pn.
      forward.                  (* t'6=t'4->LastLeaf *)
      * autorewrite with norm. entailer!. unfold is_int. destruct Last; simpl; auto.
      * forward.                (* t'3=(tbool) (t'6==1) *)
        entailer!.
        { unfold isValid.
          rewrite H3. destruct Last; simpl; auto.
          admit.                (* true from H5 *)
        }
        apply derives_refl.
  - forward.                    (* t'3=0 *)
    entailer!.
    unfold isValid. rewrite H3.
    destruct Last; auto.
    assert(index.index_eqb (entryIndex c) (index.ip (numKeys_le le)) = false).
    { unfold index.index_eqb.
      unfold entryIndex. unfold c.
      admit.                    (* true from H5 *)
    }
    rewrite H2. auto.
    apply derives_refl.
  - gather_SEP 1 2 3 4 5 6 7 8.
    replace_SEP 0 (btnode_rep (btnode val ptr0 le b First Last x) pcurr).
    entailer!. apply derives_refl.
    gather_SEP 0 2.
    replace_SEP 0 (btnode_rep root proot).
    entailer!. apply wand_frame_elim.
    gather_SEP 0 1 2 3 4.
    replace_SEP 0 (relation_rep r pr).
    entailer!. Exists (getval root). cancel. apply derives_refl.
    forward_if.
    + forward. Exists (getval root). fold c. entailer!. fold r. rewrite H5. auto.
    + forward. Exists (getval root). fold c. entailer!. fold r. rewrite H5. auto.
Admitted.
  
Lemma body_RL_CursorIsValid: semax_body Vprog Gprog f_RL_CursorIsValid RL_CursorIsValid_spec.
Proof.
  start_function.
  forward_if (
      (PROP (pc<>nullval)  LOCAL (temp _cursor pc)  SEP (relation_rep r pr; cursor_rep c r pc))).
  - forward. entailer!.
  - subst. assert_PROP(False).
    entailer!. inv H1.
  - forward_call(r,pr,c,pc).
    Intros vret. forward.
    entailer!. unfold force_val, sem_cast_pointer.
    destruct (isValid c); simpl; auto.
Qed.

Lemma body_isFirst: semax_body Vprog Gprog f_isFirst isFirst_spec.
Proof.
  start_function.
  (* proof should be similar to isvalid *)
Admitted.
