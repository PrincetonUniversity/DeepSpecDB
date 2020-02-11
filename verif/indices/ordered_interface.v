Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import indices.unordered_flat.
Require Import VST.floyd.library.
Module OrderedIndex.

Record index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_val: key -> val;
    key_type: type;
    
    value : Type;
    default_value: Inhabitant value;
    value_repr: value -> val -> mpred;

    t: Type;
    t_repr: t -> val -> mpred;
    t_type: type;
    
    cursor : Type;
    cursor_repr: cursor -> val -> mpred;
    cursor_type: type;

    (* helpers *)
    valid_cursor: cursor -> bool;
    norm: cursor -> cursor;

    (* interface *)

    create_cursor: t -> cursor;
    create_index: t -> Prop;
    
    cardinality: cursor -> Z;

    go_to_key: cursor -> key -> cursor;

    move_to_next: cursor -> cursor;

    move_to_previous: cursor -> cursor;

    move_to_first: cursor -> cursor;

    move_to_last: cursor -> cursor;
   
    get_record: cursor -> val;

    put_record: cursor -> key -> value -> val -> cursor -> Prop;

  }.



(* ================= VERIFIED =============== *)

Definition go_to_key_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH cur:oi.(cursor), pc:val, key:oi.(key)
  PRE [ 1%positive OF tptr oi.(cursor_type), 2%positive OF oi.(key_type)]
    PROP()
    LOCAL(temp 1%positive pc; temp 2%positive (oi.(key_val) key))
    SEP(oi.(cursor_repr) cur pc)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(go_to_key) cur key) pc).

Definition create_index_spec (oi: OrderedIndex.index): funspec :=
  WITH u:unit, gv: globals
  PRE [ ]
    PROP ()
    LOCAL (gvars gv)
    SEP (mem_mgr gv)
  POST [ tptr oi.(t_type) ]
    EX m: oi.(t), EX pr: val,
    PROP (oi.(create_index) m)
    LOCAL(temp ret_temp pr)
    SEP (mem_mgr gv; oi.(t_repr) m pr). 


Definition create_cursor_spec
  (oi: OrderedIndex.index): funspec :=
  WITH r: oi.(t), gv: globals, p: val
  PRE [ 1%positive OF tptr oi.(t_type)]
    PROP()
    LOCAL(gvars gv; temp 1%positive p)
    SEP(mem_mgr gv; oi.(t_repr) r p)
  POST [tptr oi.(cursor_type)]
    EX p':val,
    PROP()
    LOCAL(temp ret_temp p')
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(create_cursor) r) p').

Definition move_to_next_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL(temp 1%positive p)
    SEP(oi.(cursor_repr) cur p)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(move_to_next) cur) p).

Definition move_to_previous_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL(temp 1%positive p)
    SEP(oi.(cursor_repr) cur p)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(move_to_previous) cur) p).

Definition cardinality_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) cur p)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (oi.(cardinality) cur))))
    SEP(oi.(cursor_repr) cur p).

Definition move_to_first_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(valid_cursor) (oi.(move_to_first) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_first) cur) p).

Definition move_to_last_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(valid_cursor) (oi.(move_to_last) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_last) cur) p).

Definition get_record_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) cur p)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (oi.(get_record) cur))
    SEP(oi.(cursor_repr) (oi.(norm) cur) p).

Definition put_record_spec 
  (oi: OrderedIndex.index): funspec :=
   WITH cur: oi.(cursor), pc:val, key:oi.(key), recordptr:val, record:oi.(value), gv: globals
  PRE [ 1%positive OF tptr oi.(cursor_type), 2%positive OF oi.(key_type), 3%positive OF tptr tvoid]
    PROP()
    LOCAL(gvars gv; temp 1%positive pc; temp 2%positive (oi.(key_val) key); temp 3%positive recordptr)
    SEP(mem_mgr gv; oi.(cursor_repr) cur pc * oi.(value_repr) record recordptr)
  POST [tvoid]
    EX newc: oi.(cursor), 
    PROP(oi.(put_record) cur key record recordptr newc)
    LOCAL()
    SEP(mem_mgr gv; oi.(cursor_repr) newc pc).

End OrderedIndex.