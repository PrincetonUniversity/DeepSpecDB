Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import Coq.ZArith.BinInt.
Require Import unordered_flat.
Require Import VST.floyd.library.
Require Import definitions.

Infix ">=" := Z.geb : Z_scope.
Infix "<=" := Z.leb : Z_scope.
Infix "<" := Z.ltb: Z_scope.
Infix ">" := Z.gtb: Z_scope.
Infix "=" := Z.eqb: Z_scope.

Definition get_cursor_unordered {key: Type} {eq_dec: EqDec key} (k0: key) (l: flat key): Z :=
  (fix f l i :=
     match l with
     | nil => i
     | (k, v) :: tl =>
       if eq_dec k k0 then i
       else f tl (i + 1)
     end) (elements l) 0.

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
    
    value := V;
    default_value: Inhabitant value;

    t: Type;
    t_repr: share -> t -> val -> mpred;
    t_type: type;

    kvpair := (key * value)%type;

    cursor := (t * Z)%type;
    cursor_repr: cursor -> val -> mpred;

    flatten: t -> flat key;
    
    cardinality := fun m => Zlength (elements (flatten m));

    create: t;

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
}.


Definition create_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share
  PRE [ ]
    PROP()
    LOCAL(gvars gv)
    SEP(mem_mgr gv)
  POST [tptr ui.(t_type)]
    EX p: val, EX m: ui.(t),
    PROP( elements(ui.(flatten) m) = [] )
    LOCAL(temp ret_temp p)
    SEP(ui.(t_repr) sh m p; mem_mgr gv).

Definition lookup_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH gv: globals, sh: share, p: val, q: val, m: ui.(t), k: ui.(key)
  PRE [ 1 OF tptr ui.(t_type), 2 OF tptr ui.(key_type)]
    PROP()
    LOCAL( temp 1 p; temp 2 q)
    SEP(mem_mgr gv; ui.(t_repr) sh m p *  ui.(key_repr) sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp (proj1_sig (ui.(lookup) m k)))
    SEP(mem_mgr gv; ui.(t_repr) sh m p * ui.(key_repr) sh k q).

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

(* takes t, returns Z *)
Definition cardinality_spec 
  (ui: UnorderedIndex.index): funspec :=
  WITH sh: share, p: val, m: ui.(t)
  PRE [ 1 OF tptr ui.(t_type)]
    PROP()
    LOCAL( temp 1 p)
    SEP(ui.(t_repr) sh m p)
  POST [tint]
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

End UnorderedIndex.


