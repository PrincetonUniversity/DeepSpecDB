Require Export VST.floyd.proofauto.
Require Import indices.btree_instance.
Require Import indices.ordered_interface.
Require Import btrees.relation_mem.

Import OrderedIndex.

Section BtreeIndexASI. 
  Variable BtreeIndexPreds: index. 

  Definition cardinality_funspec := 
    (_RL_NumRecords, cardinality_spec btree_index).
  Definition create_cursor_funspec := 
    (_RL_NewCursor, create_cursor_spec btree_index).
  Definition create_index_funspec := 
    (_RL_NewRelation, create_index_spec btree_index).
  Definition cursor_has_next_funspec := 
    (_RL_CursorIsValid, cursor_has_next_spec btree_index).
  Definition go_to_key_funspec :=
    (_goToKey, go_to_key_spec btree_index).
  Definition move_to_first_funspec :=
    (_RL_MoveToFirst, move_to_first_spec btree_index).
  Definition move_to_next_funspec := 
    (_RL_MoveToNextValid, move_to_next_spec btree_index).
  Definition get_record_funspec :=
    (_RL_GetRecord, get_record_spec btree_index).
  Definition put_record_funspec :=
    (_RL_PutRecord, put_record_spec btree_index).

  Definition BtreeIndexASI:funspecs := 
      [ cardinality_funspec; create_cursor_funspec; create_index_funspec; 
        move_to_next_funspec; cursor_has_next_funspec; go_to_key_funspec;
        move_to_first_funspec; get_record_funspec; put_record_funspec].

Definition BtreeIndex_exportedFunIDs :list ident := map fst BtreeIndexASI.

End BtreeIndexASI.
