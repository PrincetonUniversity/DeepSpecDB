Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import stringlist.
Require Import interface.

(* from stringlist.v *)
Definition string := list byte.
Definition V := sig is_pointer_or_null.
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.
Definition V_repr: V -> val := @proj1_sig _ _.
Definition t_scell := Tstruct _scell noattr.
Definition t_stringlist := Tstruct _stringlist noattr.

Definition string_rep {cs: compspecs} (sh: share) (s: string) (p: val) : mpred := 
  !! (~ List.In Byte.zero s) && 
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p.

Fixpoint scell_rep  {cs: compspecs} (sh: share) (l: list (string*V)) (p: val): mpred :=
  match l with
  | [] => !!(p = nullval) && emp
  | (k, v) :: tl => EX q str_ptr: val, malloc_token sh t_scell p *
                    (* data_at sh t_scell (str_ptr, ((V_repr v), q)) p * *)
                    string_rep sh k str_ptr *
                    scell_rep sh tl q
  end.

Definition stringlist_rep {cs: compspecs} (sh: share) (lst: list (string*V)) (p: val): mpred :=
  EX cell_ptr: val,
  malloc_token Ews t_stringlist p *
  (* data_at Ews t_stringlist cell_ptr p * *)
  scell_rep sh lst cell_ptr.

Definition stringlist_index {cs: compspecs} (vrepr: forall (p: val), is_pointer_or_null p -> mpred): index :=
  {| key := string;
     key_repr := fun sh s p =>
                   EX q, data_at sh (tptr tschar) q p * string_rep sh s q;

     value := V;
     default_value := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval;
     value_repr := fun sh v p => data_at sh (tptr tvoid) (proj1_sig v) p *
                           vrepr (proj1_sig v) (proj2_sig v);

     t := list (string * V);
     t_repr := fun sh lst p => stringlist_rep sh lst p;
     
     cursor_rep := fun n p => emp;

     flatten := fun l => mk_flattened _ _ [] (NoDup_nil _);

     |}.
