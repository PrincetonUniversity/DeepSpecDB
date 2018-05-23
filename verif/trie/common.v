(** * common.v : Common definitions *)
Require Import VST.floyd.functional_base.
Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec.

Module Type VALUE_TYPE.
  Parameter type: Type.
  Parameter default: type.
  Parameter inhabitant_value: Inhabitant type.
End VALUE_TYPE.
