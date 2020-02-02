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

(* ==================== DEFS & HELPERS ==================== *)

Definition RL_GetKey := fun (c : cursor val) (r : relation val) =>
  let normc := normalize c r in
  match getCKey normc with
  | Some x => Vptrofs x
  | None => Vundef
  end.

Definition eqKey {X: Type} (c: cursor X) (key: key): bool :=
  match (getCKey c) with
  | None => false
  | Some k => if (Int64.eq (Ptrofs.to_int64 k) (Ptrofs.to_int64 key)) then true else false
  end.

(* admitted lemma from verif_movetonext *)
Lemma movetonext_complete : forall c r,
    complete_cursor c r -> complete_cursor (moveToNext c r) r.
Proof.
Admitted.


(* ==================== SPECS ==================== *)

(* cardinality *)
Definition RL_NumRecords_spec : ident * funspec :=
  DECLARE _RL_NumRecords
  WITH r:relation val, c:cursor val, pc:val, numrec: Z
  PRE[ 1%positive OF tptr tcursor ]
    PROP( get_numrec r = numrec )
    LOCAL(temp 1%positive pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ size_t ]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr numrec)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition RL_MoveToFirst_spec : ident * funspec :=
  DECLARE _RL_MoveToFirst
  WITH r:relation val, c:cursor val, pc:val, n:node val, gv: globals
  PRE[ 1%positive OF tptr tcursor ]
    PROP(partial_cursor [] r; root_integrity (get_root r); 
             next_node [] (get_root r) = Some n; correct_depth r;
             root_wf (get_root r); 
             complete_cursor (moveToFirst (get_root r) [] O) r)
    LOCAL(temp 1%positive pc)
    SEP(mem_mgr gv; relation_rep r; cursor_rep empty_cursor r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid (moveToFirst (get_root r) empty_cursor O) r)))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (moveToFirst (get_root r) empty_cursor O) r pc).

Definition RL_MoveToLast_spec : funspec :=
  WITH r:relation val, c:cursor val, pc:val, n:node val, gv: globals
  PRE[ 1%positive OF tptr tcursor ]
    PROP(partial_cursor [] r; root_integrity (get_root r); 
             next_node [] (get_root r) = Some n; correct_depth r;
             root_wf (get_root r); 
             complete_cursor (moveToFirst (get_root r) [] O) r)
    LOCAL(temp 1%positive pc)
    SEP(mem_mgr gv; relation_rep r; cursor_rep empty_cursor r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid (moveToLast val (get_root r) empty_cursor 0) r)))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (moveToLast val (get_root r) empty_cursor 0) r pc).


Definition RL_GetKey_spec : ident * funspec :=
  DECLARE _RL_GetKey
  WITH r:relation val, c:cursor val, pc:val, gv: globals
  PRE[ 1%positive OF tptr tcursor]
    PROP(ne_partial_cursor c r \/ complete_cursor c r; correct_depth r; isValid c r = true;
             complete_cursor c r; correct_depth r; root_wf (get_root r); root_integrity (get_root r))
    LOCAL(temp 1%positive pc)
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc)
  POST[ size_t ]
    PROP()
    LOCAL(temp ret_temp (RL_GetKey c r))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (normalize c r) r pc).


Definition RL_MoveToKey_spec : ident * funspec :=
  DECLARE _RL_MoveToKey
  WITH r:relation val, c:cursor val, pc:val, n:node val, key:key, gv: globals
  PRE[ 1%positive OF tptr tcursor, 2%positive OF size_t ]
    PROP(complete_cursor c r; root_integrity (get_root r); correct_depth r; 
             next_node c (get_root r) = Some n; root_wf (get_root r);
             complete_cursor (goToKey c r key) r)
    LOCAL(temp 1%positive pc; temp 2%positive (Vptrofs key))
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool 
               (andb  (isValid (goToKey c r key) r) (eqKey (normalize (goToKey c r key) r) key))))
    SEP(mem_mgr gv; relation_rep r; 
          if (isValid (goToKey c r key) r) then (cursor_rep (normalize (goToKey c r key) r) r pc)
          else (cursor_rep (goToKey c r key) r pc)).

Definition Gprog : funspecs := [RL_MoveToFirst_spec; moveToFirst_spec; RL_NumRecords_spec;
                                                  isValid_spec; RL_GetKey_spec; entryIndex_spec; currNode_spec;
                                                  moveToNext_spec; RL_MoveToKey_spec; goToKey_spec ].


(* ==================== BODY PROOFS ==================== *)

Lemma body_NumRecords: 
  semax_body Vprog Gprog f_RL_NumRecords RL_NumRecords_spec.
Proof. 
  start_function. forward_if True.
  { forward. entailer!. }
  { assert_PROP(False). entailer!. contradiction. }
  { unfold cursor_rep. Intros andc_end idx_end.
    unfold relation_rep. destruct r as (n0, v). (* r = (n0, v) *)
    Intros. forward. forward. forward. entailer!. 
    { unfold relation_rep. cancel. unfold cursor_rep.
      Exists andc_end idx_end. 
      assert (K: Vlong (Int64.repr (get_numrec (n0, v))) = 
                     Vptrofs (Ptrofs.repr (get_numrec (n0, v)))).
      rewrite Vptrofs_unfold_true; auto.
      rewrite ptrofs_to_int64_repr; auto.
      rewrite K.
      cancel. }}
Qed.

Lemma body_RL_MoveToKey: 
  semax_body Vprog Gprog f_RL_MoveToKey RL_MoveToKey_spec.
Proof.
  unfold f_RL_MoveToKey. unfold RL_MoveToKey_spec.
  start_function.
  forward_call (c, pc, r, key).
  forward_call (r, (goToKey c r key), pc).
  forward_if.
  { forward. 
    assert (K: isValid (goToKey c r key) r = false). 
    { destruct (isValid (goToKey c r key) r); auto.
      simpl in H5. inv H5. }
    entailer!.
    rewrite K. easy. rewrite K. easy. }
  { assert (K: isValid (goToKey c r key) r = true).
    { destruct (isValid (goToKey c r key) r); auto.
      simpl in H5. inv H5. }
    forward_call (r, (goToKey c r key), pc, gv).
    repeat split; auto. unfold complete_cursor in H4.
    inversion H4. auto.
    forward_if.
    { forward. 
      assert (M: eqKey (normalize (goToKey c r key) r) key = true).
      { unfold eqKey. unfold RL_GetKey in H6.
        destruct (getCKey (normalize (goToKey c r key) r)).
        simpl in H6. destruct (Int64.eq (Ptrofs.to_int64 k) (Ptrofs.to_int64 key)); auto.
        inv H6. inv H6. }
      entailer!. rewrite K. rewrite M. easy.
      rewrite K. easy. }
    { forward.
      assert (M: eqKey (normalize (goToKey c r key) r) key = false).
      { unfold eqKey. unfold RL_GetKey in H6.
        destruct (getCKey (normalize (goToKey c r key) r)).
        simpl in H6. destruct (Int64.eq (Ptrofs.to_int64 k) (Ptrofs.to_int64 key)); auto.
        inv H6. inv H6. }
      entailer!. rewrite K. rewrite M. easy.
      rewrite K. easy. }}
Qed. 


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
  - assert_PROP(False). fold c r in H1. rewrite H1 in H6. simpl in H6. inv H6. contradiction.
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
      rep_omega. destruct H2. 
      clear - SUBNODE H2. hnf in H2. simpl in H2.
      destruct (Znth_option i le) eqn:?H2; try contradiction.
       apply Znth_option_some in H0. rep_omega. }
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
      contradiction. auto. }
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
      apply Znth_option_some in H. rep_omega. 
    }
    forward.                    (* t'6=t'4->entries[t'5]->ptr.record *)
    { unfold Inhabitant_entry_val_rep in ZTL. 
      rewrite ZTL. rewrite HE. simpl entry_val_rep.
      unfold entry_rep at 1, value_rep at 1.  entailer!.
    }
    sep_apply (modus_ponens_wand (entry_rep e)).
    sep_apply (fold_btnode_rep nptr0). rewrite <- HNORMN.
    sep_apply (modus_ponens_wand).
    forward.                    (* return t'6 *)
    unfold Inhabitant_entry_val_rep in ZTL. rewrite ZTL. entailer!. 
    { simpl. unfold RL_GetKey. fold n. fold c. fold r. rewrite HNORMC.
      unfold getCKey. simpl. rewrite ZNTH. auto. }
    rewrite <- HNORMC. unfold normalize. unfold c. unfold n. simpl. unfold r. cancel.
    rewrite <- ?Vptrofs_repr_Vlong_repr by auto. cancel.
Qed.

Lemma body_RL_MoveToFirst: 
  semax_body Vprog Gprog f_RL_MoveToFirst RL_MoveToFirst_spec.
Proof.
  start_function. forward_if True.
  { forward. entailer!. }
  { assert_PROP(False). entailer!. contradiction. }
  { unfold cursor_rep. Intros. Intros andc_end idx_end.
    unfold relation_rep. destruct r as (n0, v). (* r = (n0, v) *)
    Intros. forward. forward. forward. deadvars!.
    autorewrite with norm.
    forward_call ((n0, v), empty_cursor, pc, n).
    { entailer!. simpl in H1. inversion H1. subst. auto. }
    { instantiate (Frame:=[mem_mgr gv]). unfold Frame. simpl.
      unfold relation_rep, cursor_rep. entailer!. 
      Exists andc_end. Exists idx_end. entailer!. }
    { forward_call ((n0, v), (moveToFirst n0 empty_cursor O), pc); try entailer!.
      instantiate (Frame:=[mem_mgr gv]). unfold Frame. simpl.
      simpl in H1. inversion H1. subst. entailer!.
      forward. entailer!; simpl. entailer!. }}
Qed.


