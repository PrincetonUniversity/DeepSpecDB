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
Definition first_cursor (root:node val) := moveToFirst root empty_cursor 0.
Definition cursor_wf (c:cursor val) : Prop := 0 < Zlength c <= Z.of_nat(MaxTreeDepth).
Definition partial_cursor_wf (c:cursor val) : Prop := 0 <= Zlength c < Z.of_nat(MaxTreeDepth).
Definition node_wf (n:node val) : Prop := (numKeys n <= Fanout)%nat.
Definition root_wf (root:node val) : Prop := forall n, subnode n root -> node_wf n.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type
   PRE [ _n OF tuint ]
     PROP (0 <= sizeof t <= Int.max_unsigned;
           complete_legal_cosu_type t = true;
           natural_aligned natural_alignment t = true)
     LOCAL (temp _n (Vint (Int.repr (sizeof t))))
     SEP ()
   POST [ tptr tvoid ] EX p:_,
     PROP ()
     LOCAL (temp ret_temp p)
     SEP (malloc_token Tsh t p * data_at_ Tsh t p).

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool, FirstLeaf:bool, LastLeaf:bool
  PRE [ _isLeaf OF tint, _FirstLeaf OF tint, _LastLeaf OF tint ]
    PROP ()
    LOCAL (temp _isLeaf (Val.of_bool isLeaf);
         temp _FirstLeaf (Val.of_bool FirstLeaf);
         temp _LastLeaf (Val.of_bool LastLeaf))
    SEP ()
  POST [ tptr tbtnode ]
    EX p:val, PROP ()
    LOCAL (temp ret_temp p)
    SEP (btnode_rep (empty_node isLeaf FirstLeaf LastLeaf p)).

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
    SEP (relation_rep (empty_relation pr pn)).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation val
  PRE [ _relation OF tptr trelation ]
    PROP (snd r <> nullval; root_integrity (get_root r))
    LOCAL (temp _relation (getvalr r))
    SEP (relation_rep r)
  POST [ tptr tcursor ]
    EX p':val,
    PROP ()
    LOCAL(temp ret_temp p')
    SEP (relation_rep r * cursor_rep (first_cursor (get_root r)) r p').

Definition entryIndex_spec : ident * funspec :=
  DECLARE _entryIndex
  WITH r:relation val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor ]                                                  
    PROP(cursor_wf c)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (rep_index (entryIndex c)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition currNode_spec : ident * funspec :=
  DECLARE _currNode
  WITH r:relation val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor ]
    PROP(cursor_wf c)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tptr tbtnode ]
    PROP()
    LOCAL(temp ret_temp (getval(currNode c r)))
    SEP(relation_rep r; cursor_rep c r pc).
                                                  
Definition isValid_spec : ident * funspec :=
  DECLARE _isValid
  WITH r:relation val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition RL_CursorIsValid_spec : ident * funspec :=
  DECLARE _RL_CursorIsValid
  WITH r:relation val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isValid c r)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition isFirst_spec : ident * funspec :=
  DECLARE _isFirst
  WITH r:relation val, c:cursor val, pc:val
  PRE[ _cursor OF tptr tcursor]
    PROP(cursor_wf c)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isFirst c)))
    SEP(relation_rep r; cursor_rep c r pc).

Definition moveToFirst_spec : ident * funspec :=
  DECLARE _moveToFirst
  WITH r:relation val, c:cursor val, pc:val, n:node val
  PRE[ _node OF tptr tbtnode, _cursor OF tptr tcursor, _level OF tint ]
    PROP(partial_cursor_correct c n (get_root r); partial_cursor_wf c; root_integrity (get_root r))
    LOCAL(temp _cursor pc; temp _node (getval n); temp _level (Vint(Int.repr(Zlength c))))
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToFirst n c (length c)) r pc).

Definition moveToLast_spec : ident * funspec :=
  DECLARE _moveToLast
  WITH r:relation val, c:cursor val, pc:val, n:node val
  PRE[ _node OF tptr tbtnode, _cursor OF tptr tcursor, _level OF tint ]
    PROP(partial_cursor_correct c n (get_root r); partial_cursor_wf c; root_integrity (get_root r))
    LOCAL(temp _cursor pc; temp _node (getval n); temp _level (Vint(Int.repr(Zlength c))))
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToLast n c (length c)) r pc).

Definition findChildIndex_spec : ident * funspec :=
  DECLARE _findChildIndex
  WITH n:node val, key:key
  PRE[ _node OF tptr tbtnode, _key OF tuint ]
    PROP(InternNode n; node_integrity n)
    LOCAL(temp _node (getval n); temp _key (Vint (Int.repr key)))
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (rep_index(findChildIndex n key)))
    SEP(btnode_rep n).

Definition findRecordIndex_spec : ident * funspec :=
  DECLARE _findRecordIndex
  WITH n:node val, key:key
  PRE[ _node OF tptr tbtnode, _key OF tuint ]
    PROP(LeafNode n; node_integrity n)
    LOCAL(temp _node (getval n); temp _key (Vint (Int.repr key)))
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (rep_index(findRecordIndex n key)))
    SEP(btnode_rep n).

Definition moveToKey_spec : ident * funspec :=
  DECLARE _moveToKey
  WITH n:node val, key:key, c:cursor val, pc:val, r:relation val
  PRE [ _node OF tptr tbtnode, _key OF tuint, _cursor OF tptr tcursor, _level OF tint ]
    PROP(partial_cursor_correct c n (get_root r); partial_cursor_wf c; root_integrity (get_root r))
    LOCAL(temp _cursor pc; temp _node (getval n); temp _key (Vint(Int.repr key)); temp _level (Vint(Int.repr(Zlength c))))
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP()
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToKey val n key c (length c)) r pc).

Definition isNodeParent_spec : ident * funspec :=
  DECLARE _isNodeParent
  WITH n:node val, key:key
  PRE[ _node OF tptr tbtnode, _key OF tuint ]
    PROP(InternNode n; node_integrity n)
    LOCAL( temp _node (getval n); temp _key (Vint (Int.repr key)))
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (isNodeParent n key)))
    SEP(btnode_rep n).

Definition lastpointer_spec : ident * funspec :=
  DECLARE _lastpointer
  WITH n:node val
  PRE[ _node OF tptr tbtnode ]
    PROP(node_wf n)
    LOCAL(temp _node (getval n))
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (rep_index (lastpointer n)))
    SEP(btnode_rep n).

Definition firstpointer_spec : ident * funspec :=
  DECLARE _firstpointer
  WITH n:node val
  PRE[ _node OF tptr tbtnode ]
    PROP(node_wf n)
    LOCAL(temp _node (getval n))
    SEP(btnode_rep n)
  POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (rep_index (firstpointer n)))
    SEP(btnode_rep n).

Definition moveToNext_spec : ident * funspec :=
  DECLARE _moveToNext
  WITH c:cursor val, pc:val, r:relation val
  PRE[ _cursor OF tptr tcursor ]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP(cursor_wf (moveToNext c r); cursor_correct_rel (moveToNext c r) r)
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToNext c r) r pc).

Definition moveToPrev_spec : ident * funspec :=
  DECLARE _moveToPrev
  WITH c:cursor val, pc:val, r:relation val
  PRE[ _cursor OF tptr tcursor ]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP(cursor_wf (moveToPrev c r); cursor_correct_rel (moveToPrev c r) r)
    LOCAL()
    SEP(relation_rep r; cursor_rep (moveToPrev c r) r pc).

Definition RL_MoveToNext_spec : ident * funspec :=
  DECLARE _RL_MoveToNext
  WITH c:cursor val, pc:val, r:relation val
  PRE[ _cursor OF tptr tcursor ]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP(cursor_wf (RL_MoveToNext c r); cursor_correct_rel (RL_MoveToNext c r) r)
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToNext c r) r pc).

Definition RL_MoveToPrevious_spec : ident * funspec :=
  DECLARE _RL_MoveToPrevious
  WITH c:cursor val, pc:val, r:relation val
  PRE[ _cursor OF tptr tcursor ]
    PROP(cursor_wf c; cursor_correct_rel c r)
    LOCAL(temp _cursor pc)
    SEP(relation_rep r; cursor_rep c r pc)
  POST[ tvoid ]
    PROP(cursor_wf (RL_MoveToPrevious c r); cursor_correct_rel (RL_MoveToPrevious c r) r)
    LOCAL()
    SEP(relation_rep r; cursor_rep (RL_MoveToPrevious c r) r pc).

(**
    GPROG
 **)

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    surely_malloc_spec; createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec;
    entryIndex_spec; currNode_spec; moveToFirst_spec; moveToLast_spec;
    isValid_spec; RL_CursorIsValid_spec; isFirst_spec;
    findChildIndex_spec; findRecordIndex_spec;
    moveToKey_spec; isNodeParent_spec;
    lastpointer_spec; firstpointer_spec; moveToNext_spec;
    RL_MoveToNext_spec; RL_MoveToPrevious_spec

       ]).

Ltac start_function_hint ::= idtac.

(* proof from VST/progs/verif_queue.v *)
Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     t.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh t p * data_at_ Tsh t p)).
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
