Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking. (* just for mk_body *)

Definition Gprog : funspecs := external_specs ++ private_specs.

Lemma body_list_from_block: semax_body Vprog Gprog f_list_from_block list_from_block_spec.







Definition module := [mk_body body_list_from_block].
 