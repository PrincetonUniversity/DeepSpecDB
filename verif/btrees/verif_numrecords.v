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