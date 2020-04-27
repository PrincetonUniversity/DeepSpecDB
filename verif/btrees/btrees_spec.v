(** * btrees_spec.v : Specifications of relation_mem.c functions *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.

(*Require Import VST.floyd.Funspec_old_Notation. *)
(**
    FUNCTION SPECIFICATIONS
 **)
Definition empty_node (b:bool) (F:bool) (L:bool) (p:val):node val := (btnode val) None nil b F L p.
Definition empty_relation (pr:val) (pn:val): relation val := ((empty_node true true true pn),pr).
Definition empty_cursor := []:cursor val.
Definition first_cursor (root:node val) := moveToFirst root empty_cursor 0.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
     PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
           complete_legal_cosu_type t = true;
           natural_aligned natural_alignment t = true)
     PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
(*     LOCAL (gvars gv; temp _n (Vptrofs (Ptrofs.repr (sizeof t)))) *)
     SEP (mem_mgr gv)
   POST [ tptr tvoid ] EX p:_,
     PROP ()
     LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p).

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool, First:bool, Last:bool, gv: globals
  PRE [ (*_isLeaf OF*) tint, (*_First OF*) tint, (*_Last OF*) tint ]
    PROP ()
    PARAMS (Val.of_bool isLeaf; Val.of_bool First; Val.of_bool Last) 
    GLOBALS (gv)
(*
    LOCAL (gvars gv; temp _isLeaf (Val.of_bool isLeaf);
         temp _First (Val.of_bool First);
         temp _Last (Val.of_bool Last))
*)
    SEP (mem_mgr gv)
  POST [ tptr tbtnode ]
    EX p:val, PROP ()
    LOCAL (temp ret_temp p)
    SEP (mem_mgr gv; btnode_rep (empty_node isLeaf First Last p)).

Definition empty_relation_rel newr: Prop :=
  exists pr pn, newr = empty_relation pr pn.

Definition RL_NewRelation_spec : ident * funspec :=
  DECLARE _RL_NewRelation
  WITH u:unit, gv: globals
  PRE [ ]
    PROP () PARAMS()
    GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr trelation ]
    EX newr: relation val,
    PROP (empty_relation_rel newr)
    LOCAL(temp ret_temp (snd newr))
    SEP (mem_mgr gv; relation_rep newr).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation val, gv: globals
  PRE [ (*_relation OF*) tptr trelation ]
    PROP (snd r <> nullval; root_integrity (get_root r); correct_depth r)
    PARAMS (getvalr r) GLOBALS (gv)
    SEP (mem_mgr gv; relation_rep r)
  POST [ tptr tcursor ]
    EX p':val,
    PROP ()
    LOCAL(temp ret_temp p')
    SEP (mem_mgr gv; relation_rep r; cursor_rep (first_cursor (get_root r)) r p').

Definition entryIndex_spec : ident * funspec :=
  DECLARE _entryIndex
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(ne_partial_cursor c r \/ complete_cursor c r;
             correct_depth r)
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint(Int.repr(entryIndex c))))
    SEP(relation_rep r; cursor_rep c r pc).

Definition currNode_spec : ident * funspec :=
  DECLARE _currNode
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(ne_partial_cursor c r \/ complete_cursor c r;
             correct_depth r) (* non-empty partial or complete *)
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc) *)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tptr tbtnode ]
    PROP()
    LOCAL(temp ret_temp (getval(currNode c r)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition isValid_spec : ident * funspec :=
  DECLARE _isValid
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor]
    PROP(complete_cursor c r; correct_depth r; root_wf (get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition RL_CursorIsValid_spec : ident * funspec :=
  DECLARE _RL_CursorIsValid
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor]
    PROP(complete_cursor c r; correct_depth r; root_wf (get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition isFirst_spec : ident * funspec :=
  DECLARE _isFirst
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor]
    PROP(complete_cursor c r; correct_depth r; root_wf (get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isFirst c)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition moveToFirst_spec : ident * funspec :=
  DECLARE _moveToFirst
  WITH r:relation val, c:cursor val, pc:val, n:node val
  PRE[ (*_node OF*) tptr tbtnode, (*_cursor OF*) tptr tcursor, (*_level OF*) tint ]
    PROP(partial_cursor c r; root_integrity (get_root r);
             next_node c (get_root r) = Some n; correct_depth r)
    PARAMS(getval n; pc; Vint(Int.repr(Zlength c))) GLOBALS()
(*    LOCAL(temp _cursor pc; temp _node (getval n); temp _level (Vint(Int.repr(Zlength c)))) *)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToFirst n c (length c)) r pc).

Definition moveToLast_spec : ident * funspec :=
  DECLARE _moveToLast
  WITH r:relation val, c:cursor val, pc:val, n:node val
  PRE[ (*_node OF*) tptr tbtnode, (*_cursor OF*) tptr tcursor, (*_level OF*) tint ]
    PROP(partial_cursor c r; root_integrity (get_root r);
             root_wf (get_root r); next_node c (get_root r) = Some n;
             correct_depth r)
    PARAMS(getval n; pc; Vint(Int.repr(Zlength c))) GLOBALS()
(*    LOCAL(temp _cursor pc; temp _node (getval n); temp _level (Vint(Int.repr(Zlength c)))) *)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToLast val n c (Zlength c)) r pc).

Definition findChildIndex_spec : ident * funspec :=
  DECLARE _findChildIndex
  WITH n:node val, key:key
  PRE[ (*_node OF*) tptr tbtnode, (*_key OF*) size_t ]
    PROP(is_true (negb (node_isLeaf n)); node_integrity n; node_wf n)
    PARAMS(getval n; Vptrofs key) GLOBALS()
(*    LOCAL(temp _node (getval n); temp _key (Vptrofs key))*)
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint(Int.repr(findChildIndex n key))))
    SEP(btnode_rep n).

Definition findRecordIndex_spec : ident * funspec :=
  DECLARE _findRecordIndex
  WITH n:node val, key:key
  PRE[ (*_node OF*) tptr tbtnode, (*_key OF*) size_t ]
    PROP(node_integrity n; node_wf n)
    PARAMS(getval n; Vptrofs key) GLOBALS()
(*    LOCAL(temp _node (getval n); temp _key (Vptrofs key))*)
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint(Int.repr(findRecordIndex n key))))
    SEP(btnode_rep n).

Definition moveToKey_spec : ident * funspec :=
  DECLARE _moveToKey
  WITH n:node val, key:key, c:cursor val, pc:val, r:relation val
  PRE [ (*_node OF*) tptr tbtnode, (*_key OF*) size_t, (*_cursor OF*) tptr tcursor, (*_level OF*) tint ]
    PROP(partial_cursor c r; root_integrity (get_root r);
             correct_depth r; next_node c (get_root r) = Some n;
             root_wf (get_root r))
    PARAMS(getval n; Vptrofs key; pc; Vint(Int.repr(Zlength c))) GLOBALS()
(*    LOCAL(temp _cursor pc; temp _node (getval n);
               temp _key (Vptrofs key); temp _level (Vint(Int.repr(Zlength c)))) *)
    SEP(relation_rep r; subcursor_rep c r pc) (* _length in cursor can contain something else *)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToKey val n key c) r pc).

Definition isNodeParent_spec : ident * funspec :=
  DECLARE _isNodeParent
  WITH n:node val, key:key
  PRE[ (*_node OF*) tptr tbtnode, (*_key OF*) size_t ]
    PROP(node_integrity n; node_wf n)
    PARAMS(getval n; Vptrofs key) GLOBALS()
(*    LOCAL( temp _node (getval n); temp _key (Vptrofs key))*)
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isNodeParent n key)))
    SEP(btnode_rep n).

Definition AscendToParent_spec : ident * funspec :=
  DECLARE _AscendToParent
  WITH c:cursor val, pc:val, key:key, r:relation val
  PRE[ (*_cursor OF*) tptr tcursor, (*_key OF*) size_t ]
    PROP(ne_partial_cursor c r \/ complete_cursor c r;
             correct_depth r; root_integrity (get_root r);
             root_wf (get_root r))
    PARAMS(pc; Vptrofs key) GLOBALS()
(*    LOCAL(temp _cursor pc; temp _key (Vptrofs key))*)
    SEP(cursor_rep c r pc; relation_rep r)
  POST [ tvoid ]
    PROP()
    LOCAL()
    SEP(cursor_rep (AscendToParent c key) r pc; relation_rep r).

Definition goToKey_spec : ident * funspec :=
  DECLARE _goToKey
  WITH c:cursor val, pc:val, r:relation val, key:key
  PRE[ (*_cursor OF*) tptr tcursor, (*_key OF*) size_t ]
    PROP(complete_cursor c r; correct_depth r;
             root_integrity (get_root r); root_wf (get_root r))   (* would also work for partial cursor, but always called for complete *)
    PARAMS(pc; Vptrofs key) GLOBALS()
(*    LOCAL(temp _cursor pc; temp  _key (Vptrofs key))*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (goToKey c r key) r pc).

Definition lastpointer_spec : ident * funspec :=
  DECLARE _lastpointer
  WITH n:node val
  PRE[ (*_node OF*) tptr tbtnode ]
    PROP(node_wf n)
    PARAMS(getval n) GLOBALS()
(*    LOCAL(temp _node (getval n))*)
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint(Int.repr (lastpointer n))))
    SEP(btnode_rep n).

Definition firstpointer_spec : ident * funspec :=
  DECLARE _firstpointer
  WITH n:node val
  PRE[ (*_node OF*) tptr tbtnode ]
    PROP(node_wf n)
    PARAMS(getval n) GLOBALS()
(*    LOCAL(temp _node (getval n))*)
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint(Int.repr(firstpointer n))))
    SEP(btnode_rep n).

Definition moveToNext_spec : ident * funspec :=
  DECLARE _moveToNext
  WITH c:cursor val, pc:val, r:relation val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(complete_cursor c r; correct_depth r; root_wf (get_root r); root_integrity (get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToNext c r) r pc).

Definition moveToPrev_spec : ident * funspec :=
  DECLARE _moveToPrev
  WITH c:cursor val, pc:val, r:relation val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(complete_cursor c r \/ partial_cursor c r)
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToPrev c r) r pc).

Definition RL_MoveToNext_spec : ident * funspec :=
  DECLARE _RL_MoveToNext
  WITH c:cursor val, pc:val, r:relation val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(complete_cursor c r; correct_depth r;
             root_wf(get_root r); root_integrity (get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToNext c r) r pc).

Definition RL_MoveToPrevious_spec : ident * funspec :=
  DECLARE _RL_MoveToPrevious
  WITH c:cursor val, pc:val, r:relation val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(complete_cursor c r)
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToPrevious c r) r pc).

Definition splitnode_spec : ident * funspec :=
  DECLARE _splitnode
  WITH n:node val, e:entry val, pe: val, gv: globals
  PRE[ (*_node OF*) tptr tbtnode, (*_entry OF*) tptr tentry, (*_isLeaf OF*) tint ]
    PROP(node_integrity n; Zlength (node_le n) = Fanout; LeafEntry e = is_true (node_isLeaf n)) (* splitnode only called on full nodes *)
    PARAMS(getval n; pe; Val.of_bool (isnodeleaf n)) GLOBALS(gv)
(*    LOCAL(gvars gv; temp _node (getval n); temp _entry pe; temp _isLeaf (Val.of_bool (isnodeleaf n)))*)
    SEP(mem_mgr gv; btnode_rep n; entry_rep e; data_at Ews tentry (entry_val_rep e) pe)
  POST[ tvoid ]
    EX newx:val,
    PROP()
    LOCAL()
    SEP(mem_mgr gv; btnode_rep (splitnode_left n e); entry_rep (splitnode_right n e newx);
          data_at Ews tentry (Vptrofs(splitnode_key n e),inl newx) pe).

Definition putEntry_spec : ident * funspec :=
  DECLARE _putEntry
  WITH c:cursor val, pc:val, r:relation val, e:entry val, pe:val, oldk:key, gv: globals
  PRE[ (*_cursor OF*) tptr tcursor, (*_newEntry OF*) tptr tentry, (*_key OF*) size_t ]
  PROP(complete_cursor c r \/ partial_cursor c r; LeafEntry e;
           Z.succ (get_depth r) < MaxTreeDepth; 
           root_integrity (get_root r); root_wf (get_root r); 
           entry_depth e = cursor_depth c r; entry_integrity e; entry_wf e;
           entry_numrec e > 0)
    PARAMS(pc; pe; Vptrofs oldk) GLOBALS(gv)
(*    LOCAL(gvars gv; temp _cursor pc; temp _newEntry pe; temp _key (Vptrofs oldk)) *)
    SEP(mem_mgr gv; cursor_rep c r pc; relation_rep r; entry_rep e; data_at Tsh tentry (entry_val_rep e) pe)
  POST[ tvoid ]
    EX newx:list val,
    PROP()
    LOCAL()
    SEP(let (newc,newr) := putEntry val c r e oldk newx nullval in
        (mem_mgr gv * cursor_rep newc newr pc * relation_rep newr *
         data_at Tsh tentry (entry_val_rep e) pe)).

Definition RL_PutRecord_rel (c:cursor val) (r:relation val) (key:key) 
  (record:V) (recordptr:val) (newr: relation val) (newc: cursor val) : Prop := 
exists newx, (newc, newr) = RL_PutRecord c r key record recordptr newx nullval.

Definition RL_PutRecord_spec : ident * funspec :=
  DECLARE _RL_PutRecord
  WITH r:relation val, c:cursor val, pc:val, key:key, recordptr:val, record:V, gv: globals
  PRE[ (*_cursor OF*) tptr tcursor, (*_key OF*) size_t, (*_record OF*) tptr tvoid ] 
    PROP(complete_cursor c r; Z.succ (get_depth r) < MaxTreeDepth;
             root_integrity (get_root r); root_wf (get_root r);
             get_numrec r < Int.max_signed - 1)
    PARAMS(pc; Vptrofs key; recordptr) GLOBALS(gv)
(*    LOCAL(gvars gv; temp _cursor pc; temp _key (Vptrofs key); temp _record recordptr)*)
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc; value_rep record recordptr)
  POST[ tvoid ]
    EX newc: cursor val,  EX newr: relation val,
    PROP(RL_PutRecord_rel c r key record recordptr newr newc)
    LOCAL()
    SEP(mem_mgr gv * relation_rep newr * cursor_rep newc newr pc).

Definition RL_GetRecord_spec : ident * funspec :=
  DECLARE _RL_GetRecord
  WITH r:relation val, c:cursor val, pc:val
  PRE[ (*_cursor OF*) tptr tcursor ]
    PROP(complete_cursor c r; correct_depth r; isValid c r = true; root_wf(get_root r); root_integrity(get_root r))
    PARAMS(pc) GLOBALS()
(*    LOCAL(temp _cursor pc)*)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tptr tvoid ]
    PROP()
    LOCAL(temp ret_temp (RL_GetRecord c r))
    SEP(relation_rep r; cursor_rep (normalize c r) r pc).

Definition RL_IsEmpty_spec :=
    DECLARE _RL_IsEmpty
  WITH r: relation val, c: cursor val, cursor: val, gv: globals
  PRE [ (*_cursor OF*) (tptr tcursor)]
     PROP(root_wf (get_root r))
     PARAMS(cursor) GLOBALS(gv)
(*     LOCAL (gvars gv; temp _cursor cursor)*)
     SEP (mem_mgr gv; relation_rep r; cursor_rep c r cursor)
  POST [ tint ]
     PROP()
     LOCAL(temp ret_temp (if eq_dec (Int.repr (Zlength (node_le (fst r)))) (Int.repr 0) 
                then Vint (Int.repr 1) else (Vint (Int.repr 0))))
     SEP (mem_mgr gv; relation_rep r; cursor_rep c r cursor).

(* ==================== ADDED SPECS ==================== *)

(* cardinality *)
Definition RL_NumRecords_spec : ident * funspec :=
  DECLARE _RL_NumRecords
  WITH r:relation val, c:cursor val, pc:val, numrec: Z
  PRE[ tptr tcursor ]
    PROP( get_numrec r = numrec )
    PARAMS(pc) GLOBALS()
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ size_t ]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr numrec)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition RL_MoveToFirst_spec : ident * funspec :=
  DECLARE _RL_MoveToFirst
  WITH r:relation val, c:cursor val, pc:val, n:node val, gv: globals
  PRE[ tptr tcursor ]
    PROP(partial_cursor empty_cursor r; root_integrity (get_root r); 
             next_node empty_cursor (get_root r) = Some n; correct_depth r;
             root_wf (get_root r); (getval n) <>Vundef;
             complete_cursor (moveToFirst (get_root r) empty_cursor O) r)
    PARAMS(pc) GLOBALS()
    SEP(mem_mgr gv; relation_rep r; cursor_rep empty_cursor r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid (moveToFirst (get_root r) empty_cursor O) r)))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (moveToFirst (get_root r) empty_cursor O) r pc).

Definition RL_MoveToLast_spec : funspec :=
  WITH r:relation val, c:cursor val, pc:val, n:node val, gv: globals
  PRE[tptr tcursor ]
    PROP(partial_cursor empty_cursor r; root_integrity (get_root r); 
             next_node empty_cursor (get_root r) = Some n; correct_depth r;
             root_wf (get_root r);
             complete_cursor (moveToLast val (get_root r) empty_cursor 0) r )
    PARAMS(pc) GLOBALS()
    SEP(mem_mgr gv; relation_rep r; cursor_rep empty_cursor r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid (moveToLast val (get_root r) empty_cursor 0) r)))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (moveToLast val (get_root r) empty_cursor 0) r pc).


(* ==== helpers for RL_GetKey_spec ===== *)

Definition RL_GetKey := fun (c : cursor val) (r : relation val) =>
  let normc := normalize c r in
  match getCKey normc with
  | Some x => Vptrofs x
  | None => Vundef
  end.

Definition eqKey {X: Type} (c: cursor X) (key: key): bool :=
  match (getCKey c) with
  | None => false
  | Some k => if (Int64.eq (Ptrofs.to_int64 k) (Ptrofs.to_int64 key)) then true else false
  end.

Definition RL_GetKey_spec : ident * funspec :=
  DECLARE _RL_GetKey
  WITH r:relation val, c:cursor val, pc:val, gv: globals
  PRE[ tptr tcursor]
    PROP(ne_partial_cursor c r \/ complete_cursor c r; correct_depth r; isValid c r = true;
             complete_cursor c r; correct_depth r; root_wf (get_root r); root_integrity (get_root r))
    PARAMS(pc) GLOBALS()
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc)
  POST[ size_t ]
    PROP()
    LOCAL(temp ret_temp (RL_GetKey c r))
    SEP(mem_mgr gv; relation_rep r; cursor_rep (normalize c r) r pc).


Definition RL_MoveToKey_spec : ident * funspec :=
  DECLARE _RL_MoveToKey
  WITH r:relation val, c:cursor val, pc:val, n:node val, key:key, gv: globals
  PRE[ tptr tcursor, size_t ]
    PROP(complete_cursor c r; root_integrity (get_root r); correct_depth r; 
             next_node c (get_root r) = Some n; root_wf (get_root r);
             complete_cursor (goToKey c r key) r)
    PARAMS(pc; Vptrofs key) GLOBALS()
    SEP(mem_mgr gv; relation_rep r; cursor_rep c r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool 
               (andb  (isValid (goToKey c r key) r) (eqKey (normalize (goToKey c r key) r) key))))
    SEP(mem_mgr gv; relation_rep r; 
          if (isValid (goToKey c r key) r) then (cursor_rep (normalize (goToKey c r key) r) r pc)
          else (cursor_rep (goToKey c r key) r pc)).

Definition RL_DeleteRelation_spec :=
 DECLARE _RL_DeleteRelation
 WITH u:unit
 PRE [tptr (Tstruct _Relation noattr),
        tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition RL_DeleteRecord_spec :=
 DECLARE _RL_DeleteRecord
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr), tulong]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition RL_FreeCursor_spec :=
 DECLARE _RL_FreeCursor
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition RL_MoveToNextValid_spec :=
 DECLARE _RL_MoveToNextValid
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition RL_MoveToPreviousNotFirst_spec :=
 DECLARE _RL_MoveToPreviousNotFirst
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition RL_PrintTree_spec :=
 DECLARE _RL_PrintTree
 WITH u:unit
 PRE [tptr (Tstruct _Relation noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition RL_PrintCursor_spec :=
 DECLARE _RL_PrintCursor
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition handleDeleteBtree_spec :=
 DECLARE _handleDeleteBtree
 WITH u:unit
 PRE [tptr (Tstruct _BtNode noattr),
        tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition printTree_spec :=
 DECLARE _printTree
 WITH u:unit
 PRE [tptr (Tstruct _BtNode noattr), tint]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().

Definition printCursor_spec :=
 DECLARE _printCursor
 WITH u:unit
 PRE [tptr (Tstruct _Cursor noattr)]
   PROP (False) PARAMS() GLOBALS() SEP()
 POST [ tvoid ]
   PROP() LOCAL() SEP().


(**
    GPROG
 **)

Definition all_specs : funspecs :=
   [surely_malloc_spec; createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec;
    entryIndex_spec; currNode_spec; moveToFirst_spec; moveToLast_spec;
    isValid_spec; RL_CursorIsValid_spec; isFirst_spec;
    findChildIndex_spec; findRecordIndex_spec;
    moveToKey_spec; isNodeParent_spec; AscendToParent_spec; goToKey_spec;
    lastpointer_spec; firstpointer_spec; moveToNext_spec;
    RL_MoveToNext_spec; RL_MoveToPrevious_spec;
    splitnode_spec; putEntry_spec; RL_PutRecord_spec; RL_GetRecord_spec; RL_IsEmpty_spec;
    (* added *)
     moveToPrev_spec;
     RL_MoveToFirst_spec; RL_NumRecords_spec;
     RL_GetKey_spec; RL_MoveToKey_spec;
     RL_DeleteRelation_spec; RL_DeleteRecord_spec;
     RL_FreeCursor_spec; RL_MoveToNextValid_spec; 
     RL_MoveToPreviousNotFirst_spec; RL_PrintTree_spec; 
     RL_PrintCursor_spec; handleDeleteBtree_spec; 
     printTree_spec; printCursor_spec].

Definition Gprog: funspecs := ltac:(with_library prog all_specs).

Ltac start_function_hint ::= idtac.

(* proof from VST/progs/verif_queue.v *)
Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
Admitted.  (* This seems to blow up in forward_call, very possibly
    because (sizeof t) blows up as described in VST issue #379,
    during prove_call_setup2.  The blowup (undesired simplification)
    may possibly be occuring during the "exploit" tactic. 
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Ews t p * data_at_ Ews t p; mem_mgr gv)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!. 
*
  forward. Exists p; entailer!.
Qed.
*)
