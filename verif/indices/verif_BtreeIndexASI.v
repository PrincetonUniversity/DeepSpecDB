Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.

Require Import indices.spec_BtreeIndexASI.
Require Import indices.btree_instance.
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

Instance BtreeIndexCompSpecs : compspecs. make_compspecs prog. Defined.

Section BtreeIndex_Component.

Definition BtreeIndexVprog : varspecs. mk_varspecs prog. Defined.

Definition BI_ASI: funspecs := BtreeIndexASI.

Definition spec_gprog: funspecs := btrees_spec.Gprog.
Definition wrap_gprog: funspecs := btree_wrappers.Gprog.

Definition internal_specs: funspecs := G_merge spec_gprog wrap_gprog.

Definition imported_specs := [currNode_spec].

Definition BtreeIndexGprog:funspecs := (* imported_specs ++ *) internal_specs.

Lemma gprog_app_sub:  forall V G1 G2 f spec, 
  list_norepet (map fst G2) -> 
  list_norepet (map fst V ++ map fst (G1 ++ G2)) ->
  semax_body V G2 f spec -> 
  semax_body V (G1 ++ G2) f spec.
Proof. 
  intros. eapply semax_body_subsumption; eauto.
  apply tycontext_sub_Gprog_app2; auto.
Qed.

Lemma gprog_gmerge_sub: forall V G1 G2 f spec, 
  list_norepet (map fst G2) -> 
  list_norepet (map fst V ++ map fst (G_merge G1 G2)) ->
  semax_body V G2 f spec -> 
  semax_body V (G_merge G1 G2) f spec.
Proof. Admitted.


Lemma list_norepet_spec_gprog: 
  list_norepet (map fst spec_gprog).
Proof. Admitted.

Lemma list_norepet_vprog:
  list_norepet (map fst BtreeIndexVprog).
Proof. Admitted.


Lemma list_norepet_wrap_gprog: 
    list_norepet (map fst wrap_gprog).
Proof. Admitted. 

Lemma list_disjoint_vprog_gprog:
  list_disjoint (map fst BtreeIndexVprog) (map fst (G_merge spec_gprog wrap_gprog)).
Proof. Admitted.

Lemma g_merge_comm: forall G1 G2, 
  G_merge G1 G2 = G_merge G2 G1.
Proof. Admitted.

Lemma gprog_wrap_sub: forall f s,
  semax_body BtreeIndexVprog wrap_gprog f s ->
  semax_body BtreeIndexVprog BtreeIndexGprog f s.
Proof.
  intros. apply gprog_gmerge_sub; auto.
  apply list_norepet_wrap_gprog.
  apply list_norepet_append.
  apply list_norepet_vprog.
  apply G_merge_LNR.
  apply list_norepet_spec_gprog.
  apply list_norepet_wrap_gprog.
  apply list_disjoint_vprog_gprog.
Qed.

Lemma gprog_spec_sub: forall f s,
  semax_body BtreeIndexVprog spec_gprog f s ->
  semax_body BtreeIndexVprog BtreeIndexGprog f s.
Proof.
  intros. unfold BtreeIndexGprog. 
  unfold internal_specs.
  rewrite g_merge_comm. 
  apply gprog_gmerge_sub; auto.
  apply list_norepet_spec_gprog.
  apply list_norepet_append.
  apply list_norepet_vprog.
  apply G_merge_LNR.
  apply list_norepet_wrap_gprog.
  apply list_norepet_spec_gprog.
  rewrite g_merge_comm.
  apply list_disjoint_vprog_gprog.
Qed.

Lemma cardinality_verif:
  semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NumRecords cardinality_funspec.
Proof.
  eapply semax_body_funspec_sub. 
  2: eapply sub_cardinality.
  apply gprog_wrap_sub.
  apply body_NumRecords.
  simpl. 
  assert (K: list_norepet [_t'1]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'2; _t'1]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
Qed.

Definition BtreeIndexComponent: @Component NullExtension.Espec BtreeIndexVprog _ 
      nil [] prog [] [].
Proof.
  mkComponent. 
  admit. admit. admit.
  + solve_SF_internal create_index_verif.
  + solve_SF_internal newDB_verif.
  + discriminate.
  Defined.


Lemma create_index_verif:
  semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NewRelation create_index_funspec.
Proof. 
  eapply semax_body_funspec_sub.
  2: eapply sub_create_index.
  apply gprog_spec_sub.
  apply body_NewRelation.
  simpl.
  assert (K: list_norepet [_t'1]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'2; _t'1]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_pNewRelation; _t'2; _t'1]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  apply list_norepet_cons; auto.
  inversion 1. inversion H0. inversion H0.
  inversion H1. inversion H1. inversion H2. inversion H2.
Qed.


Lemma create_cursor_verif:
  semax_body BtreeIndexVprog BtreeIndexGprog f_RL_NewCursor create_cursor_funspec.
Proof. 
  eapply semax_body_funspec_sub.
  2: eapply sub_create_cursor.
  apply gprog_spec_sub.
  apply body_NewCursor.
  simpl.
  assert (K: list_norepet [_t'2]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'1; _t'2]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_i; _t'1; _t'2]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  assert (O: list_norepet [_cursor; _i; _t'1; _t'2]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  inversion H2. inversion H2.
  apply list_norepet_cons; auto.
  inversion 1. inversion H0. inversion H0.
  inversion H1. inversion H1. inversion H2. inversion H2.
  inversion H3. inversion H3.
Qed.

(*
Lemma move_to_next_verif:
  semax_body BtreeIndexVprog btrees_spec.Gprog f_RL_MoveToNext move_to_next_funspec.
Proof. 
  eapply semax_body_funspec_sub.
  2: eapply sub_move_to_next.
  apply body_RL_MoveToNext.
  simpl.
  assert (K: list_norepet [_t'3]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'1; _t'3]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_t'2; _t'1; _t'3]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  inversion H2. inversion H2.
Qed.

Lemma move_to_previous_verif:
    semax_body BtreeIndexVprog btrees_spec.Gprog f_RL_MoveToPrevious move_to_previous_funspec.
Proof.
  eapply semax_body_funspec_sub.
  2: eapply sub_move_to_previous.
  apply body_RL_MoveToPrevious.
  simpl.
  assert (K: list_norepet [_t'1]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0.
Qed.

Lemma move_to_first_verif:
  semax_body BtreeIndexVprog btree_wrappers.Gprog f_RL_MoveToFirst move_to_first_funspec.
Proof. 
  eapply semax_body_funspec_sub.
  2: eapply sub_move_to_first.
  apply body_RL_MoveToFirst.
  simpl.
  assert (K: list_norepet [_t'2]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'3; _t'2]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_t'1; _t'3; _t'2]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  inversion H2. inversion H2.
Qed.


Lemma go_to_key_verif:
  semax_body BtreeIndexVprog btrees_spec.Gprog f_goToKey go_to_key_funspec.
Proof.
  eapply semax_body_funspec_sub.
  2: eapply sub_go_to_key.
  apply body_goToKey.
  simpl.
  assert (K: list_norepet [_t'2]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'1; _t'2]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_key; _t'1; _t'2]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
  inversion H2. inversion H2.
Qed.


Lemma get_record_verif:
  semax_body BtreeIndexVprog btrees_spec.Gprog f_RL_GetRecord get_record_funspec.
Proof.
  eapply semax_body_funspec_sub.
  2: eapply sub_get_record.
  apply body_RL_GetRecord.
  simpl.
  assert (K: list_norepet [_t'6]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_t'7; _t'6]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  assert (N: list_norepet [_t'1; _t'7; _t'6]).
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
Admitted.

Lemma put_record_verif:
  semax_body BtreeIndexVprog btrees_spec.Gprog f_RL_PutRecord put_record_funspec.
Proof.
  eapply semax_body_funspec_sub.
  2: eapply sub_put_record.
  apply body_RL_PutRecord.
  simpl.
  assert (K: list_norepet [_record]). 
  apply list_norepet_cons. 2: apply list_norepet_nil.
  inversion 1. assert (M: list_norepet[_key; _record]).
  apply list_norepet_cons; auto. inversion 1.
  inversion H0. inversion H0.
  apply list_norepet_cons; auto. 
  inversion 1.
  inversion H0. inversion H0. inversion H1. inversion H1.
Qed. 
*)



End BtreeIndex_Component.
