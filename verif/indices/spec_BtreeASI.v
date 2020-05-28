Require Export VST.floyd.proofauto.
Require Import btrees.relation_mem.
Require Import btrees.btrees_spec.
Require Import indices.btree_wrappers.

Section BtreeASI. 

  Definition cardinality_funspec := RL_NumRecords_spec.
  Definition create_cursor_funspec := RL_NewCursor_spec.
  Definition create_index_funspec := RL_NewRelation_spec.
  Definition cursor_has_next_funspec := RL_CursorIsValid_spec.
  Definition move_to_next_funspec := RL_MoveToNextValid_spec.
  Definition move_to_first_funspec := RL_MoveToFirst_spec.
  Definition go_to_key_funspec := goToKey_spec.
  Definition get_record_funspec := RL_GetRecord_spec.
  Definition put_record_funspec := RL_PutRecord_spec.

  Definition BtreeASI:funspecs := 
      [ cardinality_funspec; create_cursor_funspec; create_index_funspec; 
        move_to_next_funspec; cursor_has_next_funspec; go_to_key_funspec;
        move_to_first_funspec; get_record_funspec; put_record_funspec].

Definition Btree_exportedFunIDs :list ident := map fst BtreeASI.

End BtreeASI.