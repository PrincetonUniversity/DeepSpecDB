Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec.

Definition normalized_RL_PutRecord_funspec : funspec :=
  WITH r:relation val, c:cursor val, pc:val, key:key, recordptr:val, record:V, gv: globals
  PRE[tptr tcursor, size_t, tptr tvoid ] 
    PROP(complete_cursor c r; Z.succ (get_depth r) < MaxTreeDepth;
             root_integrity (get_root r); root_wf (get_root r);
             get_numrec r < Int.max_signed - 1)
    PARAMS(pc; Vptrofs key; recordptr) GLOBALS(gv)
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc; value_rep record recordptr)
  POST[ tvoid ]
    EX newc: cursor val,  EX newr: relation val,
    PROP(RL_PutRecord_rel c r key record recordptr newr newc)
    LOCAL()
    SEP(mem_mgr gv * relation_rep newr * cursor_rep newc newr pc).

Definition normalized_goToKey_funspec : funspec :=
  WITH c:cursor val, pc:val, r:relation val, key:key
  PRE[ tptr tcursor, size_t ]
    PROP(complete_cursor c r; correct_depth r;
             root_integrity (get_root r); root_wf (get_root r)) 
    PARAMS(pc; Vptrofs key) GLOBALS()
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (goToKey c r key) r pc).

Definition normalized_getRecord_funspec :=
  WITH r:relation val, c:cursor val, pc:val
  PRE[ tptr tcursor ]
    PROP(complete_cursor c r; correct_depth r; isValid c r = true; 
              root_wf(get_root r); root_integrity(get_root r))
    PARAMS(pc) GLOBALS()
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tptr tvoid ]
    PROP()
    LOCAL(temp ret_temp (RL_GetRecord c r))
    SEP(relation_rep r; cursor_rep (normalize c r) r pc).

Definition normalized_moveToNext_funspec := 
  WITH c:cursor val, pc:val, r:relation val
  PRE[ tptr tcursor ]
    PROP(complete_cursor c r; correct_depth r;
             root_wf(get_root r); root_integrity (get_root r))
    PARAMS(pc) GLOBALS()
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToNext c r) r pc).

Definition normalized_moveToPrevious_funspec := 
  WITH c:cursor val, pc:val, r:relation val
  PRE[ tptr tcursor ]
    PROP(complete_cursor c r)
    PARAMS(pc) GLOBALS()
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToPrevious c r) r pc).

Definition normalized_newCursor_funspec :=
  WITH r:relation val, gv: globals
  PRE [ tptr trelation ]
    PROP (snd r <> nullval; root_integrity (get_root r); correct_depth r)
    PARAMS(getvalr r) GLOBALS(gv)
    SEP (mem_mgr gv; relation_rep r)
  POST [ tptr tcursor ]
    EX p':val,
    PROP ()
    LOCAL(temp ret_temp p')
    SEP (mem_mgr gv; relation_rep r; cursor_rep (first_cursor (get_root r)) r p').
