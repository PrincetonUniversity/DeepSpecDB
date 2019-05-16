Require Import VST.floyd.proofauto.


Module Type Stringpool. 

Parameter stringpool: Type.
Parameter size: stringpool -> Z.
Parameter empty: stringpool -> Prop.
Parameter add: list byte -> val -> stringpool -> stringpool.
Parameter lookup_val: val -> stringpool -> option(list byte).
Parameter lookup_str: list byte -> stringpool -> option(val).
Parameter contains_val: val -> stringpool -> Prop.
Parameter contains_str: list byte -> stringpool -> Prop.

(* axioms for pool size *)
Axiom size_non_neg: 
  forall pool, size (pool) >= 0.

Axiom size_empty:
  forall pool, empty (pool) -> size (pool) = 0.

(* using contains_val for the following bc pointers are unique,
    and we wanted to allow copies of strings in the pool *)

Axiom size_add_contains:
  forall str p pool, contains_val p pool -> size (add str p pool) = size (pool).

Axiom size_add_new:
  forall str p pool, ~contains_val p pool -> size (add str p pool) = size (pool) + 1.

(* axioms for pool lookups *)
Axiom add_then_lookup_val: 
  forall str p pool, lookup_val p (add str p pool) = Some str.

Axiom add_then_lookup_str: 
  forall str p pool, lookup_str str (add str p pool) = Some p.

Axiom empty_lookup_val:
  forall p pool, empty (pool) -> lookup_val p pool = None.

Axiom empty_lookup_str:
  forall str pool, empty (pool) -> lookup_str str pool = None.

Axiom contains_lookup_val:
  forall str p pool, contains_val p pool -> lookup_val p pool = Some str.

Axiom contains_lookup_str:
  forall str p pool, contains_str str pool -> lookup_str str pool = Some p.

(* better name for these two? *)
Axiom not_contains_lookup_val:
  forall p pool, ~contains_val p pool -> lookup_val p pool = None.

Axiom not_contains_lookup_str:
  forall str pool, ~contains_str str pool -> lookup_str str pool = None.

End Stringpool.