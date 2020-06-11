Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.db_client.
Require Import indices.ordered_interface.
Require Import indices.btree_instance.
Require Import btrees.btrees_spec.
Require Import btrees.btrees_sep.
Require Import btrees.relation_mem.
Require Import FunInd.
Require Coq.Strings.String.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import OrderedIndex.

(* =============== TYPES =============== *)

Definition btree_cursor_t := Tstruct _BtreeCursor noattr.

(* =============== REPRESENTATIONS =============== *)

(* =============== SPECS =============== *)

Definition btree_create_index_spec (oi: OrderedIndex.index) :=
  DECLARE _btree_create_index
  WITH u:unit, gv: globals
  PRE [ ]
    PROP ()
    PARAMS() GLOBALS(gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid]
    EX m: oi.(t), EX pr: val,
    PROP (oi.(create_index) m)
    LOCAL(temp ret_temp pr)
    SEP (mem_mgr gv; oi.(t_repr) m pr). 

Definition db_client_rl_newindex_spec := (_RL_NewRelation, create_index_spec btree_index).

Lemma body_btree_create_index: 
  semax_body Vprog Gprog f_btree_create_index (btree_create_index_spec btree_index).
Proof.
  start_function.
  forward_call (u, gv).






