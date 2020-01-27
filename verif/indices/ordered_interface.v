Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import indices.unordered_flat.
Require Import VST.floyd.library.

Infix ">=" := Z.geb : Z_scope.
Infix "<=" := Z.leb : Z_scope.
Infix "<" := Z.ltb: Z_scope.
Infix ">" := Z.gtb: Z_scope.
Infix "=" := Z.eqb: Z_scope.

Module OrderedIndex.

Record index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_val: key -> val;
    key_type: type;
    
    value := val;
    default_value: Inhabitant value;

    t: Type;
    t_repr: t -> Z -> mpred;
    t_type: type;
    
    cursor : Type;
    cursor_repr: cursor -> val -> Z -> mpred;
    cursor_type: type;

    (* helpers *)
    valid_cursor: cursor -> bool;
    norm: cursor -> cursor;
    get_num_rec_levels: t -> Z;

    (* interface *)

    create_cursor: t -> cursor;
    create: val -> val -> t;
    
    cardinality: cursor -> Z;

    (* this is like get_cursor in unordered *)
    go_to_key: cursor -> key -> cursor;

    move_to_next: cursor -> cursor;

    move_to_previous: cursor -> cursor;

    move_to_first: cursor -> cursor;

    move_to_last: cursor -> cursor;
   
    get_record: cursor -> val;

    put_record: cursor -> key -> value -> val -> list val -> cursor;

  }.

(* ================= VERIFIED =============== *)

Definition go_to_key_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH cur:oi.(cursor), pc:val, key:oi.(key), numrec:Z
  PRE [ 1%positive OF tptr oi.(cursor_type), 2%positive OF oi.(key_type)]
    PROP()
    LOCAL(temp 1%positive pc; temp 2%positive (oi.(key_val) key))
    SEP(oi.(cursor_repr) cur pc numrec)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(go_to_key) cur key) pc numrec).

Definition create_spec (oi: OrderedIndex.index): funspec :=
  (* what is unit for? *)
  WITH u:unit, gv: globals
  PRE [ ]
    PROP ()
    LOCAL (gvars gv)
    SEP (mem_mgr gv)
  POST [ tptr oi.(t_type) ]
    EX pr:val, EX pn:val, 
    PROP ()
    LOCAL(temp ret_temp pr)
    SEP (mem_mgr gv; oi.(t_repr) (oi.(create) pr pn) 0).

(* 
Definition put_record_spec
  (oi: OrderedIndex.index): funspec :=
  WITH cur: oi.(cursor), m: oi.(t), pc:val, key:oi.(key), recordptr:val, record:oi.(value), gv: globals
  PRE[ 1%positive OF tptr oi.(cursor_type), 2%positive OF oi.(key_type), 3%positive OF tptr tvoid ] 
    PROP()
    LOCAL(gvars gv; temp 1%positive pc; temp 2%positive (oi.(key_val) key); temp 3%positive recordptr)
    SEP(mem_mgr gv; oi.(cursor_repr) cur pc (oi.(get_num_rec_levels) m))
  POST[ tvoid ]
    EX newx:list val,
    PROP()
    LOCAL()
    SEP(let newc := oi.(put_record) cur key record recordptr newx in 
        (mem_mgr gv * oi.(cursor_repr) newc pc (oi.(get_num_rec_levels) newr) )). *)

(*Definition normalized_putRecord_funspec :=
  WITH r:relation val, c:cursor val, pc:val, key:key, recordptr:val, record:V, gv: globals
  PRE[ 1%positive OF tptr tcursor, 2%positive OF size_t, 3%positive OF tptr tvoid ] 
    PROP(complete_cursor c r; Z.succ (get_depth r) < MaxTreeDepth;
             root_integrity (get_root r); root_wf (get_root r);
             get_numrec r < Int.max_signed - 1)
    LOCAL(gvars gv; temp 1%positive pc; temp 2%positive (key_repr key); temp 3%positive recordptr)
    SEP(mem_mgr gv; relation_rep r (get_numrec r); cursor_rep c r pc; value_rep record recordptr)
  POST[ tvoid ]
    EX newx:list val,
    PROP()
    LOCAL()
    SEP(let (newc,newr) := RL_PutRecord c r key record recordptr newx nullval in
        (mem_mgr gv * relation_rep newr (get_numrec newr) * cursor_rep newc newr pc)). *)

Definition create_cursor_spec
  (oi: OrderedIndex.index): funspec :=
  WITH r: oi.(t), numrec: Z, gv: globals, p: val
  PRE [ 1%positive OF tptr oi.(t_type)]
    PROP()
    LOCAL(gvars gv; temp 1%positive p)
    SEP(mem_mgr gv; oi.(t_repr) r numrec)
  POST [tptr oi.(cursor_type)]
    EX p':val,
    PROP()
    LOCAL(temp ret_temp p')
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(create_cursor) r) p' numrec).

Definition move_to_next_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL(temp 1%positive p)
    SEP(oi.(cursor_repr) cur p numrec)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(move_to_next) cur) p numrec).

Definition move_to_previous_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL(temp 1%positive p)
    SEP(oi.(cursor_repr) cur p numrec)
  POST [tvoid]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(move_to_previous) cur) p numrec).

Definition cardinality_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) cur p numrec)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (oi.(cardinality) cur))))
    SEP(oi.(cursor_repr) cur p numrec).

Definition move_to_first_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p numrec)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(valid_cursor) (oi.(move_to_first) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_first) cur) p numrec).

Definition move_to_last_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p numrec)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(valid_cursor) (oi.(move_to_last) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_last) cur) p numrec).

Definition get_record_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) cur p numrec)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (oi.(get_record) cur))
    SEP(oi.(cursor_repr) (oi.(norm) cur) p numrec).

End OrderedIndex.