(** * verif_relation_mem.v: Correctness proof of relation_mem.c *)

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

Require Import index.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_findindex.
Require Import verif_entryindex.
Require Import verif_currnode.
Require Import verif_isvalid.
Require Import verif_movetofirst.
Require Import verif_movetokey.
Require Import verif_newnode.
Require Import verif_newrel.
Require Import verif_newcursor.

