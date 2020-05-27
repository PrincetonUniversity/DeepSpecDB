Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.

Require Import indices.spec_BtreeASI.
Require Import indices.btree_placeholders.

Require Import btrees.relation_mem.
Require Import btrees.btrees_spec.
Require Import btrees.verif_newrel.
Require Import btrees.verif_newcursor.
Require Import btrees.verif_gotokey.
Require Import btrees.verif_getrecord.
Require Import btrees.verif_putrecord.
Require Import btrees.verif_movetonext.
Require Import btrees.verif_movetonextvalid.
Require Import btrees.verif_movetoprev.
Require Import btrees.verif_newnode.
Require Import btrees.verif_entryindex.
Require Import btrees.verif_currnode.
Require Import btrees.verif_movetofirst.
Require Import btrees.verif_movetolast.
Require Import btrees.verif_isvalid.
Require Import btrees.verif_isempty.
Require Import btrees.verif_findindex.
Require Import btrees.verif_movetokey.
Require Import btrees.verif_isnodeparent.
Require Import btrees.verif_splitnode.
Require Import btrees.verif_numrecords.
Require Import btrees.verif_getkey.

Instance BtreeCompSpecs : compspecs. make_compspecs prog. Defined.

Section Btree_Component.

Definition BtreeVprog : varspecs. mk_varspecs prog. Defined.

 Definition internal_specs: funspecs := btrees_spec.all_specs.

Definition imported_specs: funspecs := [ (_malloc, library.malloc_spec'); (_free, library.free_spec'); 
    (_exit, library.exit_spec') ].

(* this is imported + internal *)
Definition BtreeGprog:funspecs := imported_specs ++ internal_specs.

Lemma cursor_has_next_verif:
  semax_body BtreeVprog BtreeGprog f_RL_CursorIsValid cursor_has_next_funspec.
Proof.
  unfold cursor_has_next_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_CursorIsValid.
Qed.

Lemma create_index_verif: 
  semax_body BtreeVprog BtreeGprog f_RL_NewRelation create_index_funspec.
Proof.
  unfold create_index_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NewRelation.
Qed.
 
Lemma cardinality_verif: 
  semax_body BtreeVprog BtreeGprog f_RL_NumRecords cardinality_funspec.
Proof.
  unfold cardinality_funspec. 
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NumRecords.
Qed.

Lemma create_cursor_verif:
  semax_body BtreeVprog BtreeGprog f_RL_NewCursor create_cursor_funspec.
Proof.
  unfold create_cursor_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_NewCursor.
Qed.

Lemma move_to_next_verif:
  semax_body BtreeVprog BtreeGprog f_RL_MoveToNextValid move_to_next_funspec.
Proof.
  unfold move_to_next_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_MoveToNextValid.
Qed.

Lemma go_to_key_verif:
  semax_body BtreeVprog BtreeGprog f_goToKey go_to_key_funspec.
Proof.
  unfold go_to_key_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_goToKey.
Qed.

Lemma move_to_first_verif:
  semax_body BtreeVprog BtreeGprog f_RL_MoveToFirst move_to_first_funspec.
Proof.
  unfold move_to_first_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_MoveToFirst.
Qed.

Lemma get_record_verif:
  semax_body BtreeVprog BtreeGprog f_RL_GetRecord get_record_funspec.
Proof.
  unfold get_record_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_GetRecord.
Qed.

Lemma put_record_verif:
  semax_body BtreeVprog BtreeGprog f_RL_PutRecord put_record_funspec.
Proof.
  unfold put_record_funspec.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_RL_PutRecord.
Qed.

Lemma surely_malloc_verif:
  semax_body BtreeVprog BtreeGprog f_surely_malloc surely_malloc_spec.
Proof.
  replace BtreeVprog with btrees_sep.Vprog by auto.
  apply body_surely_malloc.
Qed.

Definition BtreeComponent: @Component NullExtension.Espec BtreeVprog _ 
      nil imported_specs prog BtreeASI internal_specs.
Proof. 
  mkComponent. 
  + intros. decompose [or] H; clear H.
      left; auto.
      all: repeat (right; try auto).
  + intros. decompose [or] H; clear H.
      left; auto.
      all: repeat (right; try auto).
  all: replace BtreeVprog with btrees_sep.Vprog by auto.
  + solve_SF_internal body_surely_malloc.
  + solve_SF_internal body_entryIndex.
  + solve_SF_internal body_currNode.
  + solve_SF_internal body_isValid.
  + solve_SF_internal body_isFirst.
  + solve_SF_internal create_index_verif.
  + solve_SF_internal body_RL_DeleteRelation.
  + solve_SF_internal create_cursor_verif.
  + solve_SF_internal body_RL_FreeCursor.
  + solve_SF_internal cursor_has_next_verif.
  + solve_SF_internal put_record_verif.
  + solve_SF_internal body_isNodeParent.
  + solve_SF_internal body_AscendToParent.
  + solve_SF_internal get_record_verif.
  + solve_SF_internal body_RL_GetKey.
  + solve_SF_internal go_to_key_verif.
  + solve_SF_internal body_RL_MoveToKey.
  + solve_SF_internal body_RL_DeleteRecord.
  + solve_SF_internal move_to_first_verif.
  + solve_SF_internal body_lastpointer.
  + solve_SF_internal body_firstpointer.
  + solve_SF_internal body_moveToNext.
  + solve_SF_internal body_moveToPrev.
  + solve_SF_internal body_RL_MoveToNext.
  + solve_SF_internal body_RL_MoveToPrevious.
  + solve_SF_internal move_to_next_verif.
  + solve_SF_internal body_RL_MoveToPreviousNotFirst.
  + solve_SF_internal body_isempty.
  + solve_SF_internal cardinality_verif.
  + solve_SF_internal body_RL_PrintTree.
  + solve_SF_internal body_RL_PrintCursor.
  + solve_SF_internal body_createNewNode.
  + solve_SF_internal body_splitnode.
  + solve_SF_internal body_putEntry.
  + solve_SF_internal body_findChildIndex.
  + solve_SF_internal body_findRecordIndex.
  + solve_SF_internal body_moveToKey.
  + solve_SF_internal body_moveToFirst.
  + solve_SF_internal body_moveToLast.
  + solve_SF_internal body_handleDeleteBtree.
  + solve_SF_internal body_printTree.
  + solve_SF_internal body_printCursor.
Qed.

Definition BtreeVSU: @VSU NullExtension.Espec BtreeVprog _ 
      nil imported_specs prog BtreeASI.
  Proof. eexists; apply BtreeComponent. Qed.

End Btree_Component.
