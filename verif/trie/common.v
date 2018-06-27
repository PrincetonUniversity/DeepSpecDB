(** * common.v : Common definitions *)
Require Import VST.floyd.functional_base.

Module Type KEY_TYPE.
  Parameter type: Type.
End KEY_TYPE.

Module Type ORD_KEY_TYPE <: KEY_TYPE.
  Include KEY_TYPE.
  Parameter lt: type -> type -> Prop.
  Notation "A < B" := (lt A B).
  Notation "A >= B" := (~ (lt A B)).
  Parameter lt_dec: forall (x y: type), {x < y} + {x >= y}.
  Axiom lt_trans: forall (x y z: type), x < y -> y < z -> x < z.
  Axiom lt_neq: forall (x y: type), x < y -> x <> y.
  Axiom ge_neq_lt: forall (x y: type), y >= x -> x <> y -> x < y.
  Parameter EqDec: EqDec type.
End ORD_KEY_TYPE.

Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec.

Module Type VALUE_TYPE.
  Parameter type: Type.
  Parameter default: type.
  Parameter inhabitant_value: Inhabitant type.
End VALUE_TYPE.
