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
Require Import index.

(**
    FUNCTION SPECIFICATIONS
 **)
Definition empty_node (b:bool) (F:bool) (L:bool) (p:val):node val := (btnode val) None (nil val) b F L p.
Definition empty_relation (pr:val) (pn:val): relation val := ((empty_node true true true pn),0%nat,0%nat,pr).
Definition empty_cursor := []:cursor val.
Definition cursor_wf (c:cursor val) : Prop := Zlength c > 0 /\ Zlength c <= Z.of_nat(MaxTreeDepth).

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool, FirstLeaf:bool, LastLeaf:bool
  PRE [ _isLeaf OF tint, _FirstLeaf OF tint, _LastLeaf OF tint ]       (* why tint and not tbool? *)
  PROP ()
  LOCAL (temp _isLeaf (Val.of_bool isLeaf);
         temp _FirstLeaf (Val.of_bool FirstLeaf);
         temp _LastLeaf (Val.of_bool LastLeaf))
  SEP ()
  POST [ tptr tbtnode ]
  EX p:val, PROP ()
  LOCAL (temp ret_temp p)
  SEP (if (eq_dec p nullval) then emp else btnode_rep (empty_node isLeaf FirstLeaf LastLeaf p) p).
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
  PROP (snd r <> nullval)
  LOCAL (temp _relation p)
  SEP (relation_rep r p)
  POST [ tptr tcursor ]
  EX p':val,
  PROP ()
  LOCAL(temp ret_temp p')
  SEP (relation_rep r p * (if (eq_dec p' nullval)
                           then emp
                           else cursor_rep empty_cursor r p')).

Definition entryIndex_spec : ident * funspec :=
  DECLARE _entryIndex
  WITH r:relation val, pr:val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor ]                                                  
  PROP(cursor_wf c)
  LOCAL(temp _cursor pc)
  SEP(relation_rep r pr; cursor_rep c r pc)
  POST[ tint ]
  PROP()
  LOCAL(temp ret_temp (rep_index (entryIndex c)))
  SEP(relation_rep r pr; cursor_rep c r pc).

Definition currNode_spec : ident * funspec :=
  DECLARE _currNode
  WITH r:relation val, pr:val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor ]
  PROP(cursor_wf c)
  LOCAL(temp _cursor pc)
  SEP(relation_rep r pr; cursor_rep c r pc)
  POST[ tptr tbtnode ]
  PROP()
  LOCAL(temp ret_temp (getval(currNode c r)))
  SEP(relation_rep r pr; cursor_rep c r pc).
(* We could have a stronger spec removing the getval, and saying
EX pcurr:va, temp ret_temp pcurr, 
btnode_rep (currNode c r) pcurr *  
btnode_rep (currNode c r) pcurr -* relation_rep r  *)
                                                  
Definition isValid_spec : ident * funspec :=
  DECLARE _isValid
  WITH r:relation val, pr:val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
  PROP(cursor_wf c; cursor_correct_rel c r)
  LOCAL(temp _cursor pc)
  SEP(relation_rep r pr; cursor_rep c r pc)
  POST [ tint ]
  PROP()
  LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
  SEP(relation_rep r pr; cursor_rep c r pc).

Definition RL_CursorIsValid_spec : ident * funspec :=
  DECLARE _RL_CursorIsValid
  WITH r:relation val, pr:val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
  PROP(cursor_wf c; cursor_correct_rel c r)
  LOCAL(temp _cursor pc)
  SEP(relation_rep r pr; cursor_rep c r pc)
  POST [ tint ]
  PROP()
  LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
  SEP(relation_rep r pr; cursor_rep c r pc).

Definition isFirst_spec : ident * funspec :=
  DECLARE _isFirst
  WITH r:relation val, pr:val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
  PROP(cursor_wf c)
  LOCAL(temp _cursor pc)
  SEP(relation_rep r pr; cursor_rep c r pc)
  POST [ tint ]
  LOCAL(temp ret_temp (Val.of_bool (isFirst c)))
  SEP(relation_rep r pr; cursor_rep c r pc).
          
(**
    GPROG
 **)

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec;
    entryIndex_spec; currNode_spec;
    isValid_spec; RL_CursorIsValid_spec; isFirst_spec

                               
 ]).

Ltac start_function_hint ::= idtac.