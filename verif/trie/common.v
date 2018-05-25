(** * common.v : Common definitions *)
Require Import VST.floyd.proofauto.
Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec.

Module Type VALUE_TYPE.
  Parameter type: Type.
  Parameter default: type.
  Parameter inhabitant_value: Inhabitant type.
End VALUE_TYPE.

Ltac elim_cast_pointer' term t :=
  match t with
  | force_val (sem_cast_pointer ?t') => elim_cast_pointer' term t'
  | _ =>
    let H := fresh "H" in
    first [
        apply (assert_later_PROP (is_pointer_or_null t))
      | apply (assert_PROP (is_pointer_or_null t))
      | apply (assert_PROP' (is_pointer_or_null t))];
    [ now entailer!
    | intro H ];
    idtac term;
    idtac t;
    replace term with t by (destruct t; first [contradiction | reflexivity]);
    clear H
  end.

Ltac elim_cast_pointer :=
  match goal with
  | |- context [force_val (sem_cast_pointer ?t)] =>
    elim_cast_pointer' (force_val (sem_cast_pointer t)) t
  end.