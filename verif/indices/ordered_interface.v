Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import indices.unordered_flat.
Require Import VST.floyd.library.
Require Import indices.definitions.

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
    key_repr: share -> key -> val -> mpred;
    
    value := val;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;
    
    cursor : Type;
    cursor_repr: cursor -> val -> Z -> mpred;
    cursor_type: type;

    (* helpers *)
    valid_cursor: cursor -> bool;

    (* interface *)
    
    cardinality: t -> Z;

    move_to_key: cursor -> key -> cursor;

    move_to_next: cursor -> cursor;

    move_to_previous: cursor -> cursor;

    move_to_first: cursor -> cursor;

    move_to_last: cursor -> cursor;

  }.

(* ================= VERIFIED =============== *)

(* takes t, returns cursor pointing to 0 *)
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


(*
Definition create_index_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share
  PRE [ ]
    PROP()
    LOCAL(gvars gv)
    SEP(mem_mgr gv)
  POST [tptr tvoid]
    EX p: val, EX m: oi.(t),
    PROP( oi.(cardinality) m = 0 )
    LOCAL(temp ret_temp p)
    SEP(oi.(t_repr) sh m p; mem_mgr gv).

Definition create_cursor_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, m: oi.(t), p: val
  PRE [1 OF tptr tvoid ]
    PROP()
    LOCAL(gvars gv)
    SEP(mem_mgr gv; oi.(t_repr) sh m p)
  POST [tptr tvoid]
    EX q: val, EX cur: oi.(cursor),
    PROP ( )
    LOCAL(temp ret_temp p)
    SEP(oi.(cursor_repr) cur q; mem_mgr gv).

(* takes t, returns Z *)
Definition cardinality_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, m: oi.(t)
  PRE [ 1 OF tptr tvoid]
    PROP()
    LOCAL( temp 1 p)
    SEP(oi.(t_repr) sh m p)
  POST [tulong]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (oi.(cardinality) m))))
    SEP(oi.(t_repr) sh m p).

Definition get_cursor_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: oi.(t), k: oi.(key)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL(gvars gv; temp 1%positive p; temp 2%positive q)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    EX r: val, EX c: oi.(cursor),
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(key_repr) sh k q *oi.(cursor_repr) c r). *)

(* takes t, returns cursor pointing to 0 *)
Definition move_to_first_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr oi.(cursor_type)]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p numrec)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(valid_cursor) (oi.(move_to_first) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_first) cur) p numrec).



Definition move_to_previous_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p numrec)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_previous) cur) p numrec).

Definition move_to_last_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, cur: oi.(cursor), numrec: Z
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(cursor_repr) cur p numrec)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_last) cur) p numrec).

(*
Definition lookup_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: oi.(t), k: oi.(key)
  PRE [ 1 OF tptr tvoid, 2 OF tptr tvoid]
    PROP()
    LOCAL( temp 1 p; temp 2 q)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (proj1_sig (oi.(lookup) m k)))
    SEP(mem_mgr gv; oi.(t_repr) sh m p * oi.(key_repr) sh k q).

(* spec does not allow inserting into null structure *)
Definition insert_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, mptr: val, kptr: val, m: oi.(t), k: oi.(key), v: V
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tptr tvoid]
    PROP()
    LOCAL(gvars gv; temp 1%positive mptr; temp 2%positive kptr; temp 3%positive (V_repr v))
    SEP(mem_mgr gv; oi.(t_repr) sh m mptr *  oi.(key_repr) sh k kptr)
  POST [tptr tvoid]
    EX newm: oi.(t),
    PROP( oi.(lookup) newm k = v)
    LOCAL(temp ret_temp (proj1_sig (oi.(lookup) m k)))
    SEP(mem_mgr gv; oi.(t_repr) sh newm mptr * oi.(key_repr) sh k kptr).

*)

End OrderedIndex.