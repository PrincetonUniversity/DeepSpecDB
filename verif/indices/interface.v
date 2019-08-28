Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import unordered_flat.
Require Import VST.floyd.library.

Infix ">=" := Z.geb : Z_scope.
Infix "<=" := Z.leb : Z_scope.
Infix "<" := Z.ltb: Z_scope.
Infix ">" := Z.gtb: Z_scope.
Infix "=" := Z.eqb: Z_scope.

Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

Definition get_cursor_unordered {key: Type} {eq_dec: EqDec key} (k0: key) (l: flat key): Z :=
  (fix f l i :=
     match l with
     | nil => i
     | (k, v) :: tl =>
       if eq_dec k k0 then i
       else f tl (i + 1)
     end) (elements l) 0.

Module OrderedIndex.

Record index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_repr: share -> key -> val -> mpred;
    
    value := sig is_pointer_or_null;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;

    kvpair := (key * value)%type;
    
    cursor := (t * Z)%type;
    cursor_repr: cursor -> val -> mpred;

    flatten: t -> flat key;
    
    cardinality: t -> Z := 
        fun m => Zlength (elements (flatten m));

    (* returns cursor that points to some key in the index
        or to the end if no key found *)
    get_cursor: t -> key -> cursor := 
        fun m k => (m, get_cursor_unordered k (flatten m));

    (* returns a valid kvpair from the list or None if cursor invalid
        or reached end of structure *)
    get_pair: cursor -> option kvpair :=
        fun '(m, c) => let lst := elements (flatten m) in
                              if c >= (Zlength lst) then None
                              else if c < 0 then None
                              else Some (Znth c (elements (flatten m)));

    (* moves cursor to next position *)
    move_to_next: cursor -> cursor:= 
        fun '(m, c) => let newcur := (m, (c + 1)) in
                              let lst := elements (flatten m) in
                              let lastcur := (Zlength lst - 1) in
                              (* if moving past end, return cursor pointing to end *)
                              if (c + 1) > (Zlength lst) then (m, lastcur)
                              (* if cursor before start, return cursor pointing to start *)
                              else if (c + 1) <= 0 then (m, 0) else newcur;

    (* moves cursor to prev position*)
    move_to_previous: cursor -> cursor := 
        fun '(m, c) => let newcur := (m, (c - 1)) in
                              let lst := elements (flatten m) in
                              let lastcur := (Zlength lst - 1) in
                              (* if cursor past end, return last cursor *)
                              if (c - 1) >= (Zlength lst) then (m, lastcur)
                              (* if cursor before start, return cursor pointing to start *)
                              else if (c -1) < 0 then (m, 0) else newcur;

    move_to_first: t -> cursor := fun m => (m, 0);

    move_to_last: t -> cursor := 
        fun m => let lst := (elements (flatten m)) in (m, (Zlength lst - 1));

    insert: cursor -> kvpair -> cursor;

    delete: cursor -> key -> cursor;

    (* move to key operation *)

    lookup: t -> key -> value :=
      fun m k => let kv := get_pair (move_to_next (get_cursor m k)) in
                         match kv with
                         | None => nullV
                         | Some (k0, v0) => if eq_dec_key k0 k then v0 else nullV
                         end;
  }.

(* takes t, returns Z *)
Definition cardinality_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, m: oi.(t)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(t_repr) sh m p)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (Zlength (elements(oi.(flatten) m))))))
    SEP(oi.(t_repr) sh m p).

(* takes t, k, returns cursor *)
(* for now, for simplicity, returns pointer to cursor *)
Definition get_cursor_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: oi.(t), k: oi.(key)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL(temp 1%positive p; temp 2%positive q)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    EX r: val, EX c: oi.(cursor),
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(key_repr) sh k q * oi.(cursor_repr) c r).

(* change these to reflect move_to_next, move_to_previous, add get_pair
Definition get_next_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, mc: oi.(cursor)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) mc p)
  POST [tptr tvoid]
    EX q: val, EX k: oi.(key), EX v: oi.(value), EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(kvpair_repr) sh (k, v) q * oi.(cursor_repr) (fst mc, snd mc + 1) r).
         (* how to represent the case where cursor is null ? can we just have a null pointer? *)

(* move_to_next don't change the cursor if you're at the end *)


Definition get_previous_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, mc: oi.(cursor)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) mc p)
  POST [tptr tvoid]
    EX q: val, EX k: oi.(key), EX v: oi.(value), EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(kvpair_repr) sh (k, v) q * oi.(cursor_repr) (fst mc, snd mc - 1) r). *)

(* takes t, returns cursor pointing to 0 *)
Definition move_to_first_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, m: oi.(t)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(t_repr) sh m p)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(cursor_repr) (m, 0) r).

(* takes t, returns cursor pointing to last *)
Definition move_to_last_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, m: oi.(t)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; oi.(t_repr) sh m p)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; oi.(t_repr) sh m p *  oi.(cursor_repr) (m, (Zlength (elements (oi.(flatten) m))-1)) r).

(* takes cursor, kvpair, returns cursor *)
(*
Definition insert_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, q: val, mc: oi.(cursor), kv: oi.(kvpair)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(cursor_repr) mc p *  oi.(kvpair_repr) sh kv q)
  POST [tptr tvoid]
    EX c: Z, EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(cursor_repr) (fst mc, c) r *  oi.(kvpair_repr) sh kv q). *)
(* use flat to represent insertion, calculate new cursor using get cursor *)

(* takes cursor, key, returns cursor *)
(*
Definition delete_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, q: val, mc: oi.(cursor), kv: oi.(kvpair)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(cursor_repr) mc p *  oi.(kvpair_repr) sh kv q)
  POST [tptr tvoid]
    EX c: Z, EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(cursor_repr) (fst mc, c) r). *)

Definition lookup_spec 
  (oi: OrderedIndex.index): funspec :=
  WITH sh: share, p: val, q: val, m: oi.(t), k: oi.(key)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (proj1_sig (oi.(lookup) m k)))
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q).

(* flatten? *)

End OrderedIndex.

Fixpoint find{key value: Type} (equal: EqDec key) (l: list (key * value)) (k: key): option value :=
  match l with
  | nil => None
  | (k0, v0) :: t => if equal k0 k then Some v0 else find equal t k
  end.

Module UnorderedIndex.

Record index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_repr: share -> key -> val -> mpred;
    key_type: type;
    
    value := sig is_pointer_or_null;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;
    t_type: type;

    kvpair := (key * value)%type;

    cursor := (t * Z)%type;
    cursor_repr: cursor -> val -> mpred;

    flatten: t -> flat key;
    
    cardinality := fun m => Zlength (elements (flatten m));

    get_cursor: t -> key -> cursor := 
        fun m k => (m, get_cursor_unordered k (flatten m));

    (* returns a valid kvpair from the list or None if cursor invalid
        or reached end of structure *)
    get_pair: cursor -> option kvpair :=
        fun '(m, c) => let lst := elements (flatten m) in
                              if c >= (Zlength lst) then None
                              else if c < 0 then None
                              else Some (Znth c (elements (flatten m)));

    (* moves cursor to next position *)
    move_to_next: cursor -> cursor:= 
        fun '(m, c) => let newcur := (m, (c + 1)) in
                              let lst := elements (flatten m) in
                              let lastcur := (Zlength lst - 1) in
                              (* if moving past end, return cursor pointing to end *)
                              if (c + 1) > (Zlength lst) then (m, lastcur)
                              (* if cursor before start, return cursor pointing to start *)
                              else if (c + 1) <= 0 then (m, 0) else newcur;

    move_to_first: t -> cursor := fun m => (m, 0);

    lookup: t -> key -> value :=
      fun m k => let v := find eq_dec_key (elements (flatten m)) k in
                         match v with
                         | None => nullV
                         | Some v0 => v0
                         end;

    insert: t -> key -> value -> t;

    delete: cursor -> key -> cursor;
}.

(* takes t, returns Z *)
Definition cardinality_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH sh: share, p: val, m: ui.(t)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(ui.(t_repr) sh m p)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (Zlength (elements(ui.(flatten) m))))))
    SEP(ui.(t_repr) sh m p).

(* takes t, k, returns cursor *)
(* for now, for simplicity, returns pointer to cursor *)
Definition get_cursor_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: ui.(t), k: ui.(key)
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL(temp 1%positive p; temp 2%positive q)
    SEP(mem_mgr gv; ui.(t_repr) sh m p *  ui.(key_repr) sh k q)
  POST [tptr tvoid]
    EX r: val, EX c: ui.(cursor),
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; ui.(t_repr) sh m p *  ui.(key_repr) sh k q *ui.(cursor_repr) c r).

(* TODO add get_pair, move_to_next *)

(* takes t, returns cursor pointing to 0 *)
Definition move_to_first_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, m: ui.(t)
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(mem_mgr gv; ui.(t_repr) sh m p)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(mem_mgr gv; ui.(t_repr) sh m p *  ui.(cursor_repr) (m, 0) r).

Definition lookup_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: ui.(t), k: ui.(key)
  PRE [ 1%positive OF tptr ui.(t_type), 2%positive OF tptr ui.(key_type)]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(mem_mgr gv; ui.(t_repr) sh m p *  ui.(key_repr) sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (proj1_sig (ui.(lookup) m k)))
    SEP(mem_mgr gv; ui.(t_repr) sh m p * ui.(key_repr) sh k q).

Definition V_repr: V -> val := @proj1_sig _ _.
Definition maybe {A: Type} (o: option A) (default: A) :=
  match o with Some a => a | None => default end.

(* spec does not allow inserting into null structure *)
Definition insert_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share, mptr: val, kptr: val, m: ui.(t), k: ui.(key), v: V
  PRE [ 1%positive OF tptr ui.(t_type), 2%positive OF tptr ui.(key_type), 3%positive OF tptr tvoid]
    PROP()
    LOCAL(gvars gv; temp 1%positive mptr; temp 2%positive kptr; temp 3%positive (V_repr v))
    SEP(mem_mgr gv; ui.(t_repr) sh m mptr *  ui.(key_repr) sh k kptr)
  POST [tptr tvoid]
    EX newm: ui.(t),
    PROP( ui.(lookup) newm k = v)
    LOCAL(temp ret_temp (proj1_sig (ui.(lookup) m k)))
    SEP(mem_mgr gv; ui.(t_repr) sh newm mptr * ui.(key_repr) sh k kptr).

(* TODO add delete *)

End UnorderedIndex.


