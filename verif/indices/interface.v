Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.

Infix ">=" := Z.geb : Z_scope.
Infix "<" := Z.ltb: Z_scope.
Infix "=" := Z.eqb: Z_scope.

Record flattened (key value: Type) :=
  mk_flattened
  {
    elements: list (key * value);
    nodup: NoDup elements;
  }.

Arguments elements {key value}.

Definition get_cursor_unordered {key value: Type} {eq_dec: EqDec key} (k0: key) (l: flattened key value): Z :=
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
    
    value := val;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;

    kvpair := (key * value)%type;
    kvpair_repr: share -> kvpair -> val -> mpred;
    
    cursor := (t * Z)%type;
    cursor_repr: cursor -> val -> mpred;

    flatten: t -> flattened key value;
    
    cardinality: t -> Z := 
        fun m => Zlength (elements (flatten m));

    (* returns cursor that points to some key in the index,
        or the next key in ordering *)
    get_cursor: t -> key -> cursor := 
        fun m k => (m, get_cursor_unordered k (flatten m));


    (* Q: should the following two return option kvpair or just assume cursor is valid? *)
    (* Q: how do we represent the cursor being *between* two keys ? *)

    (* returns next kvpair and moves cursor *)
    get_next: cursor -> (kvpair * option cursor)%type := 
        fun '(m, c) => let newcur := (m, (c + 1)) in
                              let pair := Znth c (elements (flatten m)) in
                              let lst := elements (flatten m) in
                              if (c + 1) >= (Zlength lst) then (pair, None) 
                              else (pair, Some newcur);

    (* returns prev kvpair and moves cursor *)
    get_previous: cursor -> (kvpair * option cursor)%type := 
        fun '(m, c) => let newcur := (m, (c - 1)) in
                              let pair := Znth c (elements (flatten m)) in
                              if (c - 1) < 0 then (pair, None) 
                              else (pair, Some newcur);

    move_to_first: t -> cursor := fun m => (m, 0);

    move_to_last: t -> cursor := 
        fun m => let lst := (elements (flatten m)) in (m, (Zlength lst - 1));

    (* what have we decided on whether we need to take 
        a cursor for insert and represent it being moved? *)
    insert: cursor -> kvpair -> cursor;

    delete: cursor -> key -> cursor;

    lookup: t -> key -> val :=
      fun m k => let (kv, _) := get_next (get_cursor m k) in
                               let k0 := fst kv in let v0 := snd kv in
                               if eq_dec_key k0 k then v0 else nullval;
  }.

(* takes t, returns Z *)
Definition cardinality_spec 
  (oi: OrderedIndex.index) (m: oi.(t)): funspec :=
  WITH sh: share, p: val
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
  (oi: OrderedIndex.index) (m: oi.(t)) (k: oi.(key)): funspec :=
  WITH sh: share, p: val, q: val
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL(temp 1%positive p; temp 2%positive q)
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    EX r: val, EX c: oi.(cursor),
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q * oi.(cursor_repr) c r).

(* takes cursor, returns (kvpair, cursor) *)
Definition get_next_spec 
  (oi: OrderedIndex.index) (mc: oi.(cursor)): funspec :=
  WITH sh: share, p: val
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

(* takes cursor, returns (kvpair, cursor) *)
Definition get_previous_spec 
  (oi: OrderedIndex.index) (mc: oi.(cursor)): funspec :=
  WITH sh: share, p: val
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(cursor_repr) mc p)
  POST [tptr tvoid]
    EX q: val, EX k: oi.(key), EX v: oi.(value), EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(kvpair_repr) sh (k, v) q * oi.(cursor_repr) (fst mc, snd mc - 1) r).

(* takes t, returns cursor pointing to 0 *)
Definition move_to_first_spec 
  (oi: OrderedIndex.index) (m: oi.(t)): funspec :=
  WITH sh: share, p: val
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(t_repr) sh m p)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(t_repr) sh m p *  oi.(cursor_repr) (m, 0) r).

(* takes t, returns cursor pointing to last *)
Definition move_to_last_spec 
  (oi: OrderedIndex.index) (m: oi.(t)): funspec :=
  WITH sh: share, p: val
  PRE [ 1%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p)
    SEP(oi.(t_repr) sh m p)
  POST [tptr tvoid]
    EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(t_repr) sh m p *  oi.(cursor_repr) (m, (Zlength (elements (oi.(flatten) m))-1)) r).

(* takes cursor, kvpair, returns cursor *)
(* if we don't take cursor, take t instead:
        - have a flattened list for before and after (len and len + 1)
        - how do we make sure that the inserted element is in the correct place? *)
Definition insert_spec 
  (oi: OrderedIndex.index) (mc: oi.(cursor)) (kv: oi.(kvpair)): funspec :=
  WITH sh: share, p: val, q: val
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(cursor_repr) mc p *  oi.(kvpair_repr) sh kv q)
  POST [tptr tvoid]
    EX c: Z, EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(cursor_repr) (fst mc, c) r *  oi.(kvpair_repr) sh kv q).

(* takes cursor, key, returns cursor *)
(* if we don't take cursor, take t instead:
        - have a flattened list for before and after (len and len -1)
        - how do we make sure that the deleted element is gone? *)
Definition delete_spec 
  (oi: OrderedIndex.index) (mc: oi.(cursor)) (kv: oi.(kvpair)): funspec :=
  WITH sh: share, p: val, q: val
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(cursor_repr) mc p *  oi.(kvpair_repr) sh kv q)
  POST [tptr tvoid]
    EX c: Z, EX r: val,
    PROP()
    LOCAL(temp ret_temp r)
    SEP(oi.(cursor_repr) (fst mc, c) r).

Definition lookup_spec 
  (oi: OrderedIndex.index) (m: oi.(t)) (k: oi.(key)): funspec :=
  WITH sh: share, p: val, q: val
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid]
    PROP()
    LOCAL( temp 1%positive p; temp 2%positive q)
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (oi.(lookup) m k))
    SEP(oi.(t_repr) sh m p *  oi.(key_repr) sh k q).

(* flatten? *)

End OrderedIndex.

Definition get_position_unordered 
  {key value: Type} {eq_dec: EqDec key} (k0: key) (l: flattened key value): Z :=
  (fix f l i :=
     match l with
     | nil => i
     | (k, v) :: tl =>
       if eq_dec k k0 then i
       else f tl (i + 1)
     end) (elements l) 0.

Fixpoint find {key value: Type} (equal: EqDec key) (l: list (key * value)) (k: key): option value :=
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
    
    value := val;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;

    kvpair := (key * value)%type;

    cursor := (t * Z)%type;
    cursor_rep: cursor -> val -> mpred;

    flatten: t -> flattened key value;
    
    cardinality := fun m => Zlength (elements (flatten m));

    get_cursor: t -> key -> cursor := 
        fun m k => (m, get_cursor_unordered k (flatten m));

    (* returns next kvpair and moves cursor *)
    get_next: cursor -> (kvpair * option cursor)%type := 
        fun '(m, c) => let newcur := (m, (c + 1)) in
                              let pair := Znth c (elements (flatten m)) in
                              let lst := elements (flatten m) in
                              if (c + 1) >= (Zlength lst) then (pair, None) 
                              else (pair, Some newcur);

    move_to_first: t -> cursor := fun m => (m, 0);

    lookup: t -> key -> option value :=
      fun m k => find eq_dec_key (elements (flatten m)) k;

    insert: t -> kvpair -> t;

    delete: cursor -> key -> cursor;

  }.

End UnorderedIndex.


