(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

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
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_currnode.
Require Import verif_entryindex.

Lemma body_isValid: semax_body Vprog Gprog f_isValid isValid_spec.
Proof.
  start_function.
  forward_call(r,pr,c,pc).      (* t'1=entryIndex(cursor) *)
  forward_call(r,pr,c,pc).      (* t'2=currNode *)
  (* forward.                      (* t'5=t'2->numKeys *) *)
Admitted.


  
Lemma body_RL_CursorIsValid: semax_body Vprog Gprog f_RL_CursorIsValid RL_CursorIsValid_spec.
Proof.
  start_function.
  (* need to prove entryIndex and currNode first *)
Admitted.

Lemma body_isFirst: semax_body Vprog Gprog f_isFirst isFirst_spec.
Proof.
  start_function.
  (* need to prove entryIndex and currNode first *)
Admitted.
 