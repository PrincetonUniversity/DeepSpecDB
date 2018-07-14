(** * common.v : Common definitions *)
Require Import VST.floyd.functional_base.

Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec.
