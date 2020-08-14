Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import indices.unordered_flat.
Require Import VST.floyd.library.
Module OrderedIndex.

(* ================= ORDERED INDEX DEFINITION =============== *)

Record index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_val: key -> val;
    key_type: type;
    key_repr: key -> val -> mpred;
    
    value : Type;
    default_value: Inhabitant value;
    value_repr: value -> val -> mpred;
    value_ptr: value -> val;

    t: Type;
    t_repr: t -> val -> mpred;
    t_type: type;
    
    cursor : Type;
    cursor_repr: cursor -> val -> mpred;
    cursor_type: type;

    (* props *)
    cursor_has_next_props: cursor -> Prop;
    create_cursor_props: t -> val -> Prop;
    go_to_key_props: cursor -> Prop;
    move_to_next_props: cursor -> Prop;
    move_to_first_props: cursor -> Prop;
    get_record_props: cursor -> Prop;
    put_record_props: cursor -> Prop;

    (* interface *)

    cursor_has_next:  cursor -> bool;

    create_cursor: t -> cursor;
    create_index: t -> Prop;
    
    cardinality: cursor -> Z;

    go_to_key: cursor -> key -> cursor;

    move_to_next: cursor -> cursor;

    move_to_first: cursor -> cursor;
   
    get_record: cursor -> val;

    put_record: cursor -> key -> value -> cursor -> Prop;

     (* axioms *)
    lookup := fun cur key => get_record (go_to_key cur key);

    (* when we create empty index, cardinality zero *)
    (* cardinality increases when insert new key, doesn't change if key is old *)

    (* either we have all the axioms about insert-cardinality interactions, 
        or define cardinality in terms of the other operators and derive these axioms *)

    index_lookup_empty: 
      forall cur key, 
      cardinality (cur) = 0 -> 
      lookup cur key = nullval;

    index_update_eq: 
      forall cur key v newc, 
      put_record cur key v newc -> 
      lookup newc key = value_ptr v;

    index_update_neq:
      forall cur key key' v newc, 
      key <> key' -> 
      put_record cur key v newc -> 
      lookup newc key' = lookup cur key'; 
  }.


(* ================= ORDERED INDEX FUNSPECS =============== *)

Definition cursor_has_next_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH cur:oi.(cursor), pc:val
  PRE [ tptr oi.(cursor_type) ]
    PROP(oi.(cursor_has_next_props) cur)
    PARAMS(pc) GLOBALS()
    SEP(oi.(cursor_repr) cur pc)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) cur)))
    SEP(oi.(cursor_repr) cur pc).

Definition go_to_key_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH cur:oi.(cursor), pc:val, key:oi.(key), pkey: val
  PRE [ tptr oi.(cursor_type), oi.(key_type)]
    PROP(oi.(go_to_key_props) cur)
    PARAMS(pc; (oi.(key_val) key)) GLOBALS()
    SEP(oi.(cursor_repr) cur pc * oi.(key_repr) key pkey)
  POST [ tvoid ]
    PROP()
    LOCAL()
    SEP(oi.(cursor_repr) (oi.(go_to_key) cur key) pc * oi.(key_repr) key pkey).

Definition create_index_spec (oi: OrderedIndex.index): funspec :=
  WITH u:unit, gv: globals
  PRE [ ]
    PROP ()
    PARAMS() GLOBALS(gv)
    SEP (mem_mgr gv)
  POST [ tptr oi.(t_type) ]
    EX m: oi.(t), EX pr: val,
    PROP (oi.(create_index) m)
    LOCAL(temp ret_temp pr)
    SEP (mem_mgr gv; oi.(t_repr) m pr). 

(* magic wand to allow for multiple cursors
on one data structure *)
Definition create_cursor_spec
  (oi: OrderedIndex.index): funspec :=
  WITH r: oi.(t), gv: globals, p: val
  PRE [tptr oi.(t_type)]
    PROP(oi.(create_cursor_props) r p)
    PARAMS(p) GLOBALS(gv)
    SEP(mem_mgr gv; oi.(t_repr) r p)
  POST [tptr oi.(cursor_type)]
    EX p':val,
    PROP()
    LOCAL(temp ret_temp p')
    SEP(mem_mgr gv; oi.(t_repr) r p; (oi.(t_repr) r p -* oi.(cursor_repr) (oi.(create_cursor) r) p')).

Definition move_to_next_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [ tptr oi.(cursor_type)]
    PROP(oi.(move_to_next_props) cur)
    PARAMS(p) GLOBALS()
    SEP(oi.(cursor_repr) cur p)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) (oi.(move_to_next) cur))))
    SEP(oi.(cursor_repr) (oi.(move_to_next) cur) p).

Definition cardinality_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [tptr oi.(cursor_type)]
    PROP()
    PARAMS(p) GLOBALS()
    SEP(oi.(cursor_repr) cur p)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (oi.(cardinality) cur))))
    SEP(oi.(cursor_repr) cur p).

Definition move_to_first_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, p: val, cur: oi.(cursor)
  PRE [ tptr oi.(cursor_type)]
    PROP(oi.(move_to_first_props) cur)
    PARAMS(p) GLOBALS()
    SEP(mem_mgr gv; oi.(cursor_repr) cur p)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) (oi.(move_to_first) cur))))
    SEP(mem_mgr gv; oi.(cursor_repr) (oi.(move_to_first) cur) p).
 
Definition get_record_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH p: val, cur: oi.(cursor)
  PRE [tptr oi.(cursor_type)]
    PROP(oi.(get_record_props) cur)
    PARAMS(p) GLOBALS()
    SEP(oi.(cursor_repr) cur p)
  POST [tptr tvoid]
    EX newc,
    PROP()
    LOCAL(temp ret_temp (oi.(get_record) cur))
    SEP(oi.(cursor_repr) newc p).

Definition put_record_spec 
  (oi: OrderedIndex.index): funspec :=
   WITH cur: oi.(cursor), pc:val, key:oi.(key), pkey: val, record:oi.(value), gv: globals
  PRE [ tptr oi.(cursor_type), oi.(key_type), tptr tvoid]
    PROP(oi.(put_record_props) cur)
    PARAMS(pc; (oi.(key_val) key); oi.(value_ptr) record) GLOBALS(gv)
    SEP(mem_mgr gv; oi.(cursor_repr) cur pc; oi.(key_repr) key pkey)
  POST [tvoid]
    EX newc: oi.(cursor), 
    PROP(oi.(put_record) cur key record newc)
    LOCAL()
    SEP(mem_mgr gv; oi.(cursor_repr) newc pc).

End OrderedIndex.