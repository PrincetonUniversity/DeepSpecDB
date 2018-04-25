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

Lemma body_moveToKey: semax_body Vprog Gprog f_moveToKey moveToKey_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
  unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
  forward.                      (* cursor->ancestors[level]=node *)
  forward.                      (* cursor->level = level *)
  gather_SEP 1 2.         (* the cursor, with a new node *)
  assert(subnode n root).
  { unfold get_root in H. simpl in H. fold n in H. apply cursor_subnode in H. auto. }
  assert (SUBNODE: subnode n root) by auto.
  apply subnode_rep in H2.
  unfold relation_rep.
  rewrite H2. unfold get_root in H1. simpl in H1. unfold n.
  rewrite unfold_btnode_rep at 1. Intros.
  forward.                      (* t'3=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward_call (n,key).    (* t'1=findRecordIndex(node,key) *)
    + admit.                 (* actual parameters cannot be coerced to formal parameters type *)
    + simpl. entailer!. admit.  (* what is this goal? *)
    + rewrite unfold_btnode_rep with (n:=n). unfold n. cancel.
      change_compspecs CompSpecs. cancel.
    + unfold n. simpl. rewrite H3. split. auto.
      unfold root_integrity in H1. apply H1 in SUBNODE. unfold n in SUBNODE. split. eapply leaf_ptr0. 
      unfold n in SUBNODE. eauto. rewrite H3. simpl. auto.
      unfold node_integrity in SUBNODE. rewrite H3 in SUBNODE. destruct SUBNODE. auto.      
    + forward.                  (* cursor->ancestorsIdx[level]=t'1 *)
      gather_SEP 0 5. replace_SEP 0 (btnode_rep root).
      { entailer!. apply wand_frame_elim. }
      gather_SEP 0 3 4. replace_SEP 0 (relation_rep r).
      { entailer!. apply derives_refl. }
      forward.                  (* return *)
      entailer!.
      unfold cursor_rep.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      cancel.
      pose (ii:=findRecordIndex' le key (ip 0)). fold ii.
      assert(moveToKey val (btnode val ptr0 le true First Last pn) key c (length c) = (n,ii)::c).
      (* this should be true *) admit.
      rewrite H13. rewrite Zlength_cons.
      rewrite Zsuccminusone. autorewrite with sublist. rewrite upd_Znth0. rewrite upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. cancel.
      apply derives_refl.
  - forward_call(n,key).     (* t'2=findChildIndex(node,key) *)
    + admit.
    + simpl. entailer!.
      destruct (pTree_from_elements).
      admit.                    (* THIS IS FALSE *)
      admit.
    + rewrite unfold_btnode_rep with (n:=n). unfold n.
      cancel. change_compspecs CompSpecs. cancel.
    + unfold n. simpl. rewrite H3. auto. split. auto.
      unfold root_integrity in H1. apply H1 in SUBNODE. unfold node_integrity in SUBNODE.
      destruct ptr0 eqn:HPTR0. 
      unfold n in SUBNODE. rewrite H3 in SUBNODE. auto.
      unfold n in SUBNODE. rewrite H3 in SUBNODE. inv SUBNODE.
    + forward.                  (* cursor->ancestors[level]=i *)
      pose (i:=findChildIndex n key). fold i.
      gather_SEP 1 2. replace_SEP 0 (cursor_rep ((n,i)::c) r pc).
      { entailer!. unfold cursor_rep. unfold r.
      Exists (sublist 1 (Zlength anc_end) anc_end). Exists (sublist 1 (Zlength idx_end) idx_end).
      entailer!. autorewrite with sublist. rewrite upd_Znth0. rewrite upd_Znth0. simpl.
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite Zsuccminusone.
      cancel. apply derives_refl. }
      forward_if (EX child:node val, PROP (nth_node i n = Some child)
     LOCAL (temp _i (rep_index i); temp _t'3 (Val.of_bool isLeaf); temp _cursor pc; temp _child (getval child);
     temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
     SEP (cursor_rep ((n, i) :: c) r pc; btnode_rep n; malloc_token Tsh trelation prel;
     data_at Tsh trelation
       (getval root, (Vint (Int.repr (Z.of_nat numRec)), Vint (Int.repr (Z.of_nat depth)))) prel;
     btnode_rep (btnode val ptr0 le isLeaf First Last pn) -* btnode_rep root))%assert.
      * rewrite unfold_btnode_rep. unfold n. Intros.
        destruct ptr0 eqn:HPTR0.
        destruct n0 as [ptr00 le0 isLeaf0 F0 L0 x0]. Intros.
        forward.                (* child=node->ptr0 *)
        Exists (btnode val ptr00 le0 isLeaf0 F0 L0 x0).
        entailer!.
        destruct i eqn:HI. auto.
        (* contradiction in H4 *) admit.
        fold n. apply derives_refl.
        unfold root_integrity in H1. apply H1 in SUBNODE. unfold node_integrity in SUBNODE.
        unfold n in SUBNODE. rewrite H3 in SUBNODE. inv SUBNODE.
      * rewrite unfold_btnode_rep. unfold n. Intros.
        (* I need to show that entries[i] is rep somewhere *)
        (* forward.               (* child=node->entries+i.ptr.child *) *)
        admit.
      * Intros child.
        gather_SEP 1 4. replace_SEP 0 (btnode_rep root).
        { entailer!. apply wand_frame_elim. }
        gather_SEP 0 2 3. replace_SEP 0 (relation_rep r).
        { entailer!. apply derives_refl. }
        { forward_call(child,key,(n,i)::c,pc,r).
          - admit.              (* cursor length *)
          - admit.              (* false *)
          - admit.              (* false *)
          - split3.
            + simpl. split. auto. destruct i. unfold n in H4. simpl in H4. auto. auto.
            + unfold partial_cursor_wf. admit. (* cursor length *)
            + unfold r. unfold get_root. simpl. auto.
          - forward.            (* return *)
            entailer!.
            assert((moveToKey val child key ((n, i) :: c) (S (length c))) =  (moveToKey val (btnode val ptr0 le false First Last pn) key c (length c))).
            admit.
            rewrite H3. apply derives_refl. }
Admitted.