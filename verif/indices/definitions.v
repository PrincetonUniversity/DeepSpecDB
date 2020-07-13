Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Definition V := sig is_pointer_or_null. 
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.
Definition V_repr: V -> val := @proj1_sig _ _.
Definition maybe {A: Type} (o: option A) (default: A) :=
  match o with Some a => a | None => default end.

