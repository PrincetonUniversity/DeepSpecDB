Require Import btrees.relation_mem. (*needed for defining Vprog *)

Require Import indices.spec_BtreeIndexASI.
Require Import btrees.btrees_spec.
Require Import indices.btree_instance.
Require Import indices.btree_wrappers.
Require Import btrees.verif_newrel.
(* Require Import btrees.verif_newcursor.
Require Import btrees.verif_gotokey.
Require Import btrees.verif_getrecord.
Require Import btrees.verif_putrecord.
Require Import btrees.verif_movetonext.
Require Import btrees.verif_movetoprev. *)

Instance BtreeIndexCompSpecs : compspecs. make_compspecs prog. Defined.

Require Import indices.Component.

Section BtreeIndex_Component.

  Definition BtreeIndexVprog : varspecs. mk_varspecs prog. Defined.

  Definition BI_ASI: funspecs := BtreeIndexASI.

  (*Definition conn_imported_specs := surely_malloc_specs.*)

  Definition internal_specs: funspecs := BI_ASI.

  Definition BtreeIndexGprog:funspecs := (*conn_imported_specs ++ *) internal_specs.

  Lemma cardinality_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NumRecords cardinality_funspec.
  Proof.
    eapply semax_body_funspec_sub. 
    { replace BtreeIndexVprog with btrees_sep.Vprog by auto.
      assert (K: BtreeIndexGprog = btree_wrappers.Gprog). admit. rewrite K.
      apply body_NumRecords. } apply sub_cardinality.
      simpl. repeat apply list_norepet_cons; auto.
      unfold not. intros. inversion H. inversion H0. 
      inversion H0. inversion H1. inversion H1.
      unfold not. intros. inversion H. inversion H0. inversion H0.
      apply list_norepet_nil.
  Admitted.

  Lemma create_index_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NewRelation create_index_funspec.
  Proof.
    eapply semax_body_funspec_sub. 
    { replace BtreeIndexVprog with btrees_sep.Vprog by auto.
      assert (K: BtreeIndexGprog = btrees_spec.Gprog). admit. rewrite K.
      apply body_NewRelation. } apply sub_create_index.
      simpl. repeat apply list_norepet_cons; auto; 
      try apply list_norepet_nil. 
      unfold not. intros. inversion H. inversion H0. 
      inversion H0. inversion H1. inversion H1. inversion H2. inversion H2.
      unfold not. intros. inversion H. inversion H0. inversion H0. inversion H1.
      inversion H1. unfold not. intros. inversion H. inversion H0. inversion H0.
  Admitted.

(*
Lemma create_cursor_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NewCursor create_cursor_funspec.
Proof. 
  eapply semax_body_funspec_sub. 
    { replace BtreeIndexVprog with btrees_sep.Vprog by auto.
      assert (K: BtreeIndexGprog = btrees_spec.Gprog). admit. rewrite K.
      apply body_NewCursor. }  apply sub_create_cursor.
      simpl. repeat apply list_norepet_cons; auto; 
      try apply list_norepet_nil. 
      unfold not. intros. inversion H. inversion H0. 
      inversion H0. inversion H1. inversion H1. inversion H2. inversion H2.
      unfold not. intros. inversion H. inversion H0. inversion H0. inversion H1.
      inversion H1. unfold not. intros. inversion H. inversion H0. inversion H0.

Admitted. 

Lemma move_to_next_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_MoveToNext move_to_next_funspec.
Proof. 
    eapply semax_body_funspec_sub. 
    { replace BtreeIndexVprog with btrees_sep.Vprog by auto.
      assert (K: BtreeIndexGprog = btrees_spec.Gprog). admit. rewrite K.
      apply  } apply sub_create_index.
      simpl. repeat apply list_norepet_cons; auto; 
      try apply list_norepet_nil. 
      unfold not. intros. inversion H. inversion H0. 
      inversion H0. inversion H1. inversion H1. inversion H2. inversion H2.
      unfold not. intros. inversion H. inversion H0. inversion H0. inversion H1.
      inversion H1. unfold not. intros. inversion H. inversion H0. inversion H0.


*)

Lemma move_to_previous_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_MoveToPrevious move_to_previous_funspec.
Proof. Admitted.

Lemma move_to_first_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_MoveToFirst move_to_first_funspec.
Proof. Admitted.

Lemma go_to_key_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_goToKey go_to_key_funspec.
Proof. Admitted.

Lemma get_record_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_GetRecord get_record_funspec.
Proof. Admitted.

Lemma put_record_verif:
    semax_body BtreeIndexVprog BtreeIndexGprog f_RL_PutRecord put_record_funspec.
Proof. Admitted.
    


  Definition BtreeIndexComponent: @Component NullExtension.Espec BtreeIndexVprog _ 
      nil [] prog BI_ASI.
  Proof. Admitted. (*
    mkComponent internal_specs.
   
  + solve_SF_internal consConn_verif.
  + solve_SF_internal newDB_verif.
  + discriminate.
  Defined.*)

End BtreeIndex_Component.
Check BtreeIndexComponent. (*: Component [] conn_imported_specs prog C_ASI*)

Definition BtreeIndexCanComp := C_to_CC BtreeIndexComponent.  
