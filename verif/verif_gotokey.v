(** * verif_gotokey.v : Correctness proof of AscendToParent and goToKey *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_findindex.
Require Import verif_isnodeparent.

Lemma body_AscendToParent: semax_body Vprog Gprog f_AscendToParent AscendToParent_spec.
Proof.
  start_function.
Admitted.

Lemma body_goToKey: semax_body Vprog Gprog f_goToKey goToKey_spec.
Proof.
  start_function.
Admitted.