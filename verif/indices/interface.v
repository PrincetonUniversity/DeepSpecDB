Require Import VST.floyd.functional_base VST.floyd.proofauto.

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

Record ordered_index :=
  {
    key: Type;
    eq_dec_key: EqDec key;
    default_key: Inhabitant key;
    key_repr: share -> key -> val -> mpred;
    
    value: Type;
    default_value: Inhabitant value;
    value_repr: share -> value -> val -> mpred;

    t: Type;
    t_repr: share -> t -> val -> mpred;

    kvpair := (key * value)%type;
    
    cursor := (t * Z)%type;
    
    cursor_rep: cursor -> val -> mpred;

    flatten: t -> flattened key value;
    
    cardinality: t -> Z := 
        fun m => Zlength (elements (flatten m));

    get_cursor: t -> key -> cursor := 
        fun m k => (m, get_cursor_unordered k (flatten m));

    (* when do we use current and when do we use next? *)
    current: cursor -> kvpair := 
        fun '(m, c) => (Znth c (elements (flatten m)));

    next: cursor -> (kvpair * cursor)%type := 
        fun '(m, c) => let newcur := (m, (c + 1)) in
                              (Znth (c+1) (elements (flatten m)), newcur);

    previous: cursor -> (kvpair * cursor)%type := 
        fun '(m, c) => let newcur := (m, (c - 1)) in
                              (Znth (c-1) (elements (flatten m)), newcur);

    (* do we also want to move the cursor to beginning / end ? *)
    first: t -> kvpair := 
        fun m => Znth 0 (elements (flatten m));

    last: t -> kvpair := 
        fun m => let lst := (elements (flatten m)) in Znth (Zlength lst - 1) lst;

    (* how do we represent the cursor moving 
        to the proper insertion spot? *)
    insert: cursor -> kvpair -> cursor;

    delete: cursor -> key -> cursor;
  }.

Definition get_position_unordered 
  {key value: Type} {eq_dec: EqDec key} (k0: key) (l: flattened key value): Z :=
  (fix f l i :=
     match l with
     | nil => i
     | (k, v) :: tl =>
       if eq_dec k k0 then i
       else f tl (i + 1)
     end) (elements l) 0.

Record unordered_index :=
  {
    u_key: Type;
    u_eq_dec_key: EqDec u_key;
    u_default_key: Inhabitant u_key;
    u_key_repr: share -> u_key -> val -> mpred;
    
    u_value: Type;
    (* do we need something like this for lookup? *)
    u_nullval: u_value;
    u_default_value: Inhabitant u_value;
    u_value_repr: share -> u_value -> val -> mpred;

    u_t: Type;
    u_t_repr: share -> u_t -> val -> mpred;

    u_kvpair := (u_key * u_value)%type;

    u_flatten: u_t -> flattened u_key u_value;
    
    u_cardinality := fun m => Zlength (elements (u_flatten m));

    get_position: u_t -> u_key -> Z := fun m k => get_position_unordered k (u_flatten m);

    nth_pair: u_t -> Z -> u_kvpair := fun m n => Znth n (elements (u_flatten m));

    lookup: u_t -> u_key -> u_value;

    u_insert: u_t -> u_kvpair -> u_t;

  }.

Definition lookup_spec 
  {key value t: Type} (sh: share) (lst: t) (k: key)
  (t_rep: share -> t -> val -> mpred)
  (key_rep: share -> key -> val -> mpred) 
  (lookup: t -> key -> value) : funspec :=
  WITH p: val, q: val
  PRE [ ]
    PROP()
    LOCAL()
    SEP(t_rep sh lst p *  key_rep sh k q)
  POST [tptr tvoid]
    PROP()
    LOCAL(temp ret_temp nullval)
    (* LOCAL(temp ret_temp (lookup lst k)) *)
    SEP(t_rep sh lst p *  key_rep sh k q).

(*
 WITH gv: globals, lst: stringlist.t V, key: Z, p: val, k: val, str: string
 PRE [ _p OF tptr t_stringlist, _key OF tptr tschar ] 
   PROP()
   LOCAL(gvars gv; temp _p p; temp _key k)
   SEP(mem_mgr gv; stringlist_rep lst p * string_rep str k)
 POST [ tptr tvoid ] 
      PROP() 
      LOCAL(temp ret_temp (V_repr (maybe (stringlist.find str lst) nullV))) 
      SEP(mem_mgr gv; stringlist_rep lst p * string_rep str k). *)
