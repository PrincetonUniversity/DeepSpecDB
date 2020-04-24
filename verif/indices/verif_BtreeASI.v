Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.

Require Import indices.spec_BtreeASI.
Require Import indices.btree_wrappers.

Require Import btrees.relation_mem.
Require Import btrees.btrees_spec.
Require Import btrees.verif_newrel.
Require Import btrees.verif_newcursor.
Require Import btrees.verif_gotokey.
Require Import btrees.verif_getrecord.
Require Import btrees.verif_putrecord.
Require Import btrees.verif_movetonext.
Require Import btrees.verif_movetoprev.

Instance BtreeCompSpecs : compspecs. make_compspecs prog. Defined.

Section Btree_Component.

Definition BtreeVprog : varspecs. mk_varspecs prog. Defined.

Definition internal_specs: funspecs := BtreeASI.

Definition imported_specs := 
  [moveToFirst_spec; isValid_spec; 
  RL_GetKey_spec; entryIndex_spec; 
  currNode_spec; moveToNext_spec; 
  RL_MoveToKey_spec; surely_malloc_spec; 
  createNewNode_spec; moveToLast_spec;
  RL_CursorIsValid_spec; isFirst_spec; 
  findChildIndex_spec; findRecordIndex_spec;
  moveToKey_spec; isNodeParent_spec; 
  AscendToParent_spec; lastpointer_spec; 
  firstpointer_spec; splitnode_spec; 
  putEntry_spec; RL_IsEmpty_spec;
  moveToPrev_spec

  (* these have functions in the C file but no specs *)

  (*RL_DeleteRelation_spec; *)
  (*RL_FreeCursor_spec;*)
  (*RL_DeleteRecord_spec; *)
  (*RL_MoveToNextValid_spec;*)
  (*RL_MoveToPreviousNotFirst_spec;*)
  (*RL_PrintTree_spec;
  RL_PrintCursor_spec;
  handleDeleteBtree_spec; 
  printTree_spec;
  printCursor_spec*)].


Definition BtreeGprog:funspecs := imported_specs ++ internal_specs.


(* these are the two Gprogs from proof files that verify Btree functions.
   the first one is from the original btree spec file.
   the second one is from file with wrapper functions that i had to write *)
Definition spec_gprog: funspecs := btrees_spec.Gprog.
Definition wrap_gprog: funspecs := btree_wrappers.Gprog.

Lemma list_norepet1: 
  list_norepet
  [_RL_MoveToFirst; _moveToFirst; _RL_NumRecords; _isValid; _RL_GetKey; _entryIndex;
  _currNode; _moveToNext; _RL_MoveToKey; _goToKey].
Proof. Admitted. 

Lemma list_norepet2: 
  list_norepet
  (map fst BtreeVprog ++
   map fst
     ([surely_malloc_spec; createNewNode_spec; moveToLast_spec; RL_CursorIsValid_spec;
      isFirst_spec; findChildIndex_spec; findRecordIndex_spec; moveToKey_spec;
      isNodeParent_spec; AscendToParent_spec; lastpointer_spec; firstpointer_spec;
      splitnode_spec; putEntry_spec; RL_GetRecord_spec; RL_IsEmpty_spec;
      create_cursor_funspec; create_index_funspec; move_to_next_funspec;
      move_to_previous_funspec; get_record_funspec; put_record_funspec] ++
      [RL_MoveToFirst_spec; moveToFirst_spec; RL_NumRecords_spec; isValid_spec;
      RL_GetKey_spec; entryIndex_spec; currNode_spec; moveToNext_spec; RL_MoveToKey_spec;
      goToKey_spec])).
Proof. Admitted.

(* need this to show that the BtreeGprog subsumes the wrap_gprog
    for functions that were proven with respect to wrap_gprog *)
Lemma body_sub_wrap_gprog: 
  forall f s, 
  semax_body BtreeVprog wrap_gprog f s ->
  semax_body BtreeVprog BtreeGprog f s.
Proof. Admitted.
(*  intros. eapply semax_body_subsumption; eauto.
  unfold wrap_gprog. unfold btree_wrappers.Gprog.
  unfold BtreeGprog. unfold imported_specs.
  unfold internal_specs. unfold BtreeASI. simpl.
  remember [surely_malloc_spec; createNewNode_spec;
     moveToLast_spec; RL_CursorIsValid_spec; isFirst_spec; findChildIndex_spec;
     findRecordIndex_spec; moveToKey_spec; isNodeParent_spec; AscendToParent_spec;
     lastpointer_spec; firstpointer_spec; splitnode_spec; putEntry_spec; RL_GetRecord_spec;
     RL_IsEmpty_spec; create_cursor_funspec; create_index_funspec;
     move_to_next_funspec; move_to_previous_funspec;
     get_record_funspec; put_record_funspec] as L1. 
  remember  [RL_MoveToFirst_spec; moveToFirst_spec; RL_NumRecords_spec; isValid_spec;
     RL_GetKey_spec; entryIndex_spec; currNode_spec; moveToNext_spec; RL_MoveToKey_spec;
     goToKey_spec] as L2.
  assert (K: [moveToFirst_spec; isValid_spec; RL_GetKey_spec; entryIndex_spec; currNode_spec;
     moveToNext_spec; RL_MoveToKey_spec; surely_malloc_spec; createNewNode_spec; moveToLast_spec;
     RL_CursorIsValid_spec; isFirst_spec; findChildIndex_spec; findRecordIndex_spec;
     moveToKey_spec; isNodeParent_spec; AscendToParent_spec; lastpointer_spec; firstpointer_spec;
     splitnode_spec; putEntry_spec; RL_IsEmpty_spec; cardinality_funspec; create_cursor_funspec;
     create_index_funspec; move_to_next_funspec; move_to_previous_funspec; go_to_key_funspec;
     move_to_first_funspec; get_record_funspec; put_record_funspec] = L1 ++ L2).
  { subst. simpl. admit. } 
  rewrite K. apply tycontext_sub_Gprog_app2; subst.
  simpl. apply list_norepet1. apply list_norepet2.
Admitted.*)

(* need this to show that the BtreeGprog subsumes the spec_gprog
    for functions that were proven with respect to spec_gprog *)
Lemma body_sub_spec_gprog: 
  forall f s, 
  semax_body BtreeVprog spec_gprog f s ->
  semax_body BtreeVprog BtreeGprog f s.
Proof. Admitted. 

Lemma cardinality_verif: 
  semax_body BtreeVprog BtreeGprog f_RL_NumRecords cardinality_funspec.
Proof.
  unfold cardinality_funspec. 
  apply body_sub_wrap_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NumRecords.
Qed.

Lemma create_cursor_verif:
  semax_body BtreeVprog BtreeGprog f_RL_NewCursor create_cursor_funspec.
Proof.
  unfold create_cursor_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NewCursor.
Qed.

Lemma create_index_verif: 
  semax_body BtreeVprog BtreeGprog f_RL_NewRelation create_index_funspec.
Proof.
  unfold create_index_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NewRelation.
Qed.

Lemma move_to_next_verif:
  semax_body BtreeVprog BtreeGprog f_RL_MoveToNext move_to_next_funspec.
Proof.
  unfold move_to_next_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_MoveToNext.
Qed.

Lemma move_to_previous_verif:
  semax_body BtreeVprog BtreeGprog f_RL_MoveToPrevious move_to_previous_funspec.
Proof.
  unfold move_to_previous_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_MoveToPrevious.
Qed.

Lemma go_to_key_verif:
  semax_body BtreeVprog BtreeGprog f_goToKey go_to_key_funspec.
Proof.
  unfold go_to_key_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_goToKey.
Qed.

Lemma move_to_first_verif:
  semax_body BtreeVprog BtreeGprog f_RL_MoveToFirst move_to_first_funspec.
Proof.
  unfold move_to_first_funspec. 
  apply body_sub_wrap_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_MoveToFirst.
Qed.

Lemma get_record_verif:
  semax_body BtreeVprog BtreeGprog f_RL_GetRecord get_record_funspec.
Proof.
  unfold get_record_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_GetRecord.
Qed.

Lemma put_record_verif:
  semax_body BtreeVprog BtreeGprog f_RL_PutRecord put_record_funspec.
Proof.
  unfold put_record_funspec. 
  apply body_sub_spec_gprog.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_PutRecord.
Qed.

Definition BtreeComponent: @Component NullExtension.Espec BtreeVprog _ 
      nil imported_specs prog BtreeASI internal_specs.
Proof.
  mkComponent.
  + admit. (* has something to do with imported_specs? *)
  + intros. admit. 
  + intros. admit.
  + solve_SF_internal create_index_verif.
  + solve_SF_internal create_cursor_verif.
  + solve_SF_internal put_record_verif.
  + solve_SF_internal get_record_verif.
  + solve_SF_internal go_to_key_verif.
  + solve_SF_internal move_to_first_verif.
  + solve_SF_internal move_to_next_verif.
  + solve_SF_internal move_to_previous_verif.
  + solve_SF_internal cardinality_verif.
Admitted.

End Btree_Component.
