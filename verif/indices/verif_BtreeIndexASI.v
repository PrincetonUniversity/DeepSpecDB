Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.

Require Import indices.spec_BtreeIndexASI.
Require Import indices.btree_instance.
Require Import indices.btree_wrappers.
Require Import indices.verif_BtreeASI.

Require Import btrees.relation_mem.

Instance BtreeIndexCompSpecs : compspecs. make_compspecs prog. Defined.

Section BtreeIndex_Component.

Definition BtreeIndexVprog : varspecs. mk_varspecs prog. Defined.

 Definition internal_specs: funspecs := btrees_spec.all_specs.

Definition imported_specs: funspecs := [ (_malloc, library.malloc_spec'); (_free, library.free_spec'); 
    (_exit, library.exit_spec') ].

(* this is imported + internal *)
Definition BtreeIndexGprog:funspecs := imported_specs ++ internal_specs.

Definition BtreeIndexComponent: @Component NullExtension.Espec BtreeIndexVprog _ 
      nil imported_specs prog BtreeIndexASI internal_specs.
Proof.
  eapply Comp_Exports_sub.
  eapply BtreeComponent.
  LNR_tac.
  inversion 1. repeat if_tac in H1; subst.
  all: inversion H1; subst; clear H1.
  + exists (snd btrees_spec.RL_NumRecords_spec).
      split. auto. apply sub_cardinality.
  + exists (snd btrees_spec.RL_NewCursor_spec).
      split. auto. apply sub_create_cursor.
  + exists (snd btrees_spec.RL_NewRelation_spec).
      split. auto. apply sub_create_index.
  + exists (snd btrees_spec.RL_MoveToNext_spec).
      split. auto. apply sub_move_to_next.
  + exists (snd btrees_spec.RL_MoveToPrevious_spec).
      split. auto. apply sub_move_to_previous.
  + exists (snd btrees_spec.goToKey_spec).
      split. auto. apply sub_go_to_key.
  + exists (snd btrees_spec.RL_MoveToFirst_spec).
      split. auto. apply sub_move_to_first.
  + exists (snd btrees_spec.RL_GetRecord_spec).
      split. auto. apply sub_get_record.
  + exists (snd btrees_spec.RL_PutRecord_spec).
      split. auto. apply sub_put_record.
Qed.

Definition BtreeIndexVSU: @VSU NullExtension.Espec BtreeIndexVprog _ 
      nil imported_specs prog BtreeIndexASI.
Proof.
  eapply VSU_Exports_sub.
  eapply BtreeVSU.
  LNR_tac.
  inversion 1. repeat if_tac in H1; subst.
  all: inversion H1; subst; clear H1.
  + exists (snd btrees_spec.RL_NumRecords_spec).
      split. auto. apply sub_cardinality.
  + exists (snd btrees_spec.RL_NewCursor_spec).
      split. auto. apply sub_create_cursor.
  + exists (snd btrees_spec.RL_NewRelation_spec).
      split. auto. apply sub_create_index.
  + exists (snd btrees_spec.RL_MoveToNext_spec).
      split. auto. apply sub_move_to_next.
  + exists (snd btrees_spec.RL_MoveToPrevious_spec).
      split. auto. apply sub_move_to_previous.
  + exists (snd btrees_spec.goToKey_spec).
      split. auto. apply sub_go_to_key.
  + exists (snd btrees_spec.RL_MoveToFirst_spec).
      split. auto. apply sub_move_to_first.
  + exists (snd btrees_spec.RL_GetRecord_spec).
      split. auto. apply sub_get_record.
  + exists (snd btrees_spec.RL_PutRecord_spec).
      split. auto. apply sub_put_record.
Qed.

End BtreeIndex_Component.
