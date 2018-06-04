(** * tactics.v : General Tactics *)
Require Import VST.floyd.proofauto.

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
