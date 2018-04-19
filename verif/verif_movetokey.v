(** * verif_movetokey.v : Correctness proof of moveToKey *)

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
Require Import verif_findindex.

Lemma Zsuccminusone: forall x,
    (Z.succ x) -1 = x.
Proof. intros. rep_omega. Qed.

Lemma body_moveToKey: semax_body Vprog Gprog f_moveToKey moveToKey_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct n as [ptr0 le isLeaf First Last xn].
  pose (n:=btnode val ptr0 le isLeaf First Last xn). fold n.
  unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
  forward.                      (* cursor->ancestors[level]=node *)
  { unfold partial_cursor_wf in H0. entailer!. destruct H0.
    (* TODO: rep_omega should work here? *)
    split. omega. rewrite MTD_eq in H1. simpl in H1. auto. }
  forward.                      (* cursor->level = level *)
  gather_SEP 1 2 3 4 5.         (* the cursor, we a new node *)
  assert(subnode n root).
  { unfold get_root in H. simpl in H. fold n in H. apply cursor_subnode in H. auto. }
  apply subnode_rep with (proot:=getval root) in H3.
  unfold relation_rep. Intros proot. rewrite btnode_rep_getval. Intros. subst proot.
  rewrite H3. simpl in H1. subst xn. Intros xn. rewrite btnode_rep_getval. Intros. subst.
  normalize.
  assert (getval n = pn). unfold n. simpl. auto. rewrite H1.
  unfold n.
  (* for some reason, unfold_btnode_rep at 1 takes a long time here *)
  replace_SEP 6 (malloc_token Tsh tbtnode pn *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) pn *
  field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool isLeaf) pn *
  field_at Tsh tbtnode (DOT _FirstLeaf) (Val.of_bool First) pn *
  field_at Tsh tbtnode (DOT _LastLeaf) (Val.of_bool Last) pn *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _ptr0) nullval pn
  | Some n' => match n' with btnode _ _ _ _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' pn * btnode_rep n' p' end end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) pn *
  le_iter_sepcon le).
  entailer!. apply derives_refl.
  Intros.
  forward.                      (* t'3=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward_call (n,key,pn).    (* t'1=findRecordIndex(node,key) *)
    + admit.
    + simpl. entailer!. admit.  (* what is this goal? *)
    + rewrite unfold_btnode_rep with (n:=n) (p:=pn). unfold n.
      rewrite prop_true_andp by auto. cancel.
      change_compspecs CompSpecs. cancel.
    + unfold n. simpl. rewrite H4. auto.
    + forward.                  (* cursor->ancestorsIdx[level]=t'1 *)
      { entailer!. clear -H0. unfold partial_cursor_wf in H0. destruct H0.
        split. omega. rewrite MTD_eq in H0. simpl in H0. auto. }
      gather_SEP 0 7.
      replace_SEP 0 (btnode_rep root (getval root)).
      entailer!. apply wand_frame_elim.
      gather_SEP 0 6 7 8 9.
      replace_SEP 0 (relation_rep r pr).
      entailer!. Exists (getval root). cancel. apply derives_refl.
      forward.                  (* return *)
      Exists (getval root). entailer!.
      unfold cursor_rep.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      cancel.
      pose (ii:=findRecordIndex' le key (ip 0)). fold ii.
      assert(moveToKey val (btnode val ptr0 le true First Last pn) key c (length c) = (n,ii)::c).
      (* this should be true *) admit.
      rewrite H24. rewrite Zlength_cons.
      rewrite Zsuccminusone. autorewrite with sublist. rewrite upd_Znth0. rewrite upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. cancel.
      apply derives_refl.
  - forward_call(n,key,pn).     (* t'2=findChildIndex(node,key) *)
    + admit.
    + simpl. entailer!.
      destruct (pTree_from_elements).
      admit.                    (* THIS IS FALSE *)
      admit.
    + rewrite unfold_btnode_rep with (n:=n) (p:=pn). unfold n. rewrite prop_true_andp by auto.
      cancel. change_compspecs CompSpecs. cancel.
    + unfold n. simpl. rewrite H4. auto.
    + forward.                  (* cursor->ancestors[level]=i *)
      { entailer!. clear -H0. unfold partial_cursor_wf in H0. destruct H0. split. omega.
        rewrite MTD_eq in H0. simpl in H0. auto. }
      pose (i:=findChildIndex n key). fold i.
      gather_SEP 1 2 3 4 5.
      replace_SEP 0 (cursor_rep ((n,i)::c) r pc).
      entailer!. unfold cursor_rep. unfold r.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      entailer!. autorewrite with sublist. rewrite upd_Znth0. rewrite upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite Zsuccminusone.
      cancel. apply derives_refl.
      (* gather_SEP 1 3. *)
      (* replace_SEP 0 (btnode_rep root (getval root)). *)
      (* entailer!. apply wand_frame_elim. *)
      (* gather_SEP 0 2 3 4 5. *)
      (* replace_SEP 0 (relation_rep r pr). *)
      (* entailer!. Exists (getval root). cancel. apply derives_refl. *)
      forward_if ( EX pchild:val, EX child:node val, PROP (pchild=getval child; nth_node i n = Some child)
     LOCAL (temp _i (rep_index i); temp _t'3 (Val.of_bool isLeaf); temp _cursor pc; 
     temp _node pn; temp _level (Vint (Int.repr (Zlength c))); temp _child pchild)
     SEP (cursor_rep ((n, i) :: c) r pc; btnode_rep n pn;
     field_at Tsh trelation [StructField _root] (getval root) pr;
     btnode_rep (btnode val ptr0 le isLeaf First Last pn) pn -* btnode_rep root (getval root);
     field_at Tsh trelation [StructField _numRecords] (Vint (Int.repr (Z.of_nat numRec))) pr;
     field_at Tsh trelation [StructField _depth] (Vint (Int.repr (Z.of_nat depth))) pr;
     malloc_token Tsh trelation pr))%assert.
      * rewrite unfold_btnode_rep. unfold n. Intros.
        destruct ptr0 eqn:HPTR0.
        destruct n0 as [ptr00 le0 isLeaf0 F0 L0 x0]. Intros.
        forward.                (* child=node->ptr0 *)
        Exists x0. Exists (btnode val ptr00 le0 isLeaf0 F0 L0 x0).
        entailer!.
        destruct i eqn:HI. auto.
        (* contradiction in H5 *) admit.
        fold n. apply derives_refl.
        (* ptr0 can't be none if isLeaf is false *)
        admit.
      * rewrite unfold_btnode_rep. unfold n. Intros.
        (* I need to show that entries[i] is rep somewhere *)
        (* forward.               (* child=node->entries+i.ptr.child *) *)
        admit.
      * Intros pchild. Intros child.
        gather_SEP 1 3.
        replace_SEP 0 (btnode_rep root (getval root)).
        entailer!. apply wand_frame_elim.
        gather_SEP 0 2 3 4 5.
        replace_SEP 0 (relation_rep r pr).
        entailer!. Exists (getval root). cancel. apply derives_refl.
        { forward_call(child,key,pchild,(n,i)::c,pc,r,pr).
          - admit.              (* cursor length *)
          - admit.              (* false *)
          - admit.              (* false *)
          - split3.
            + simpl. split. auto. destruct i. unfold n in H6. simpl in H6. auto. auto.
            + unfold partial_cursor_wf. admit. (* cursor length *)
            + split; auto.
          - forward.            (* return *)
            Exists p'. entailer!.
            assert((moveToKey val child key ((n, i) :: c) (S (length c))) =  (moveToKey val (btnode val ptr0 le false First Last pn) key c (length c))).
            admit.
            rewrite H14. apply derives_refl. }
Admitted.