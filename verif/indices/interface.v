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

Record index :=
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
    
    cursor := (t * Z)%type;
    
    cursor_rep: cursor -> val -> mpred;

    flatten: t -> flattened key value;
    
    cardinal := fun m => Zlength (elements (flatten m));

    get_cursor: t -> key -> cursor := fun m k => (m, get_cursor_unordered k (flatten m));

    value_at: cursor -> value := fun '(m, c) => snd (Znth c (elements (flatten m)));
    
  }.
