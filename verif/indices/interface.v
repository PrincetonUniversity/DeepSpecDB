Require Import VST.floyd.functional_base VST.floyd.proofauto.

Require FMapList. Require Import DecidableTypeEx.
(* Cannot use/(instantiate with given key/values) a module inside a record *)

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

(* Shouldn't all shares be Ews ?! *)
(* Share of pointer vs share of location of the string ? *)

Definition string := list byte.

Definition stringlist_index {cs: compspecs} (vrepr: forall (p: val), is_pointer_or_null p -> mpred): index :=
  {| key := string;
     key_repr := fun sh s p =>
                   EX q, data_at sh (tptr tschar) q p * cstring sh s q;

     value := { p: val | is_pointer_or_null p };
     default_value := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval;
     value_repr := fun sh v p => data_at sh (tptr tvoid) (proj1_sig v) p *
                           vrepr (proj1_sig v) (proj2_sig v);

     t := list (string * { p: val | is_pointer_or_null p });
     t_repr := fun _ _ _ => emp;
     
     cursor_rep := fun n p => emp;

     flatten := fun l => mk_flattened _ _ [] (NoDup_nil _);

     |}.
