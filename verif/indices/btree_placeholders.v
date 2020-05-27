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

Lemma body_RL_DeleteRelation: 
  semax_body Vprog Gprog f_RL_DeleteRelation RL_DeleteRelation_spec.
Proof. Admitted. 

Lemma body_RL_DeleteRecord: 
  semax_body Vprog Gprog f_RL_DeleteRecord RL_DeleteRecord_spec.
Proof. Admitted.

Lemma body_RL_FreeCursor: 
  semax_body Vprog Gprog f_RL_FreeCursor RL_FreeCursor_spec.
Proof. Admitted.

Lemma body_RL_MoveToNextValid: 
  semax_body Vprog Gprog f_RL_MoveToNextValid RL_MoveToNextValid_spec.
Proof. Admitted.

Lemma body_RL_MoveToPreviousNotFirst: 
  semax_body Vprog Gprog f_RL_MoveToPreviousNotFirst RL_MoveToPreviousNotFirst_spec.
Proof. Admitted.

Lemma body_RL_PrintTree: 
  semax_body Vprog Gprog f_RL_PrintTree RL_PrintTree_spec.
Proof. Admitted.

Lemma body_RL_PrintCursor: 
  semax_body Vprog Gprog f_RL_PrintCursor RL_PrintCursor_spec.
Proof. Admitted.

Lemma body_handleDeleteBtree: 
  semax_body Vprog Gprog f_handleDeleteBtree handleDeleteBtree_spec.
Proof. Admitted.

Lemma body_printTree: 
  semax_body Vprog Gprog f_printTree printTree_spec.
Proof. Admitted.

Lemma body_printCursor: 
  semax_body Vprog Gprog f_printCursor printCursor_spec.
Proof. Admitted.


