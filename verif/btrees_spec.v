(** * btrees_spec.v : Specifications of relation_mem.c functions *)

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

(**
    FUNCTION SPECIFICATIONS
 **)
Definition empty_node (b:bool) (p:val):node val := (btnode val) None (nil val) b p.
Definition empty_relation (pr:val) (pn:val): relation val := ((empty_node true pn),0%nat,pr).
Definition empty_cursor := []:cursor val.

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool
  PRE [ _isLeaf OF tint ]       (* why tint and not tbool? *)
  PROP ()
  LOCAL (temp _isLeaf (Val.of_bool isLeaf))
  SEP ()
  POST [ tptr tbtnode ]
  EX p:val, PROP ()
  LOCAL (temp ret_temp p)
  SEP (if (eq_dec p nullval) then emp else btnode_rep (empty_node isLeaf p) p).
(* not strong enough? *)

Definition RL_NewRelation_spec : ident * funspec :=
  DECLARE _RL_NewRelation
  WITH u:unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr trelation ]
  EX pr:val, EX pn:val, PROP ()
  LOCAL(temp ret_temp pr)
  SEP (if (eq_dec pr nullval) then emp else relation_rep (empty_relation pr pn) pr).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation val, p:val
  PRE [ _relation OF tptr trelation ]
  PROP ()
  LOCAL (temp _relation p)
  SEP (relation_rep r p)
  POST [ tptr tcursor ]
  EX p':val, PROP ()
  LOCAL(temp ret_temp p')
  SEP (relation_rep r p * (if (eq_dec p' nullval)
                           then emp
                           else cursor_rep empty_cursor r p')).

Definition RL_MoveToNext_spec : ident * funspec :=
  DECLARE _RL_MoveToNext
  WITH c:cursor val, p:val, rel:relation val, prel:val
  PRE [ _btCursor OF tptr tcursor ]
  PROP (cursor_correct_rel c rel)
  LOCAL (temp _btCursor p)
  SEP (cursor_rep c rel p; relation_rep rel prel)
  POST [ tint ]
  EX b:bool, EX c':cursor val,
  PROP (move_to_next c = (c',b); cursor_correct_rel c' rel)
  LOCAL (temp ret_temp (Val.of_bool b))
  SEP(cursor_rep c' rel p; relation_rep rel prel).
                             
(**
    GPROG
 **)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                             createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec;
                             RL_MoveToNext_spec
 ]).
