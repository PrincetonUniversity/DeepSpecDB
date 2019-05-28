(************************************************************************************)
(**                                                                                 *)
(**                             The SQLEngines Library                              *)
(**                                                                                 *)
(**            LRI, CNRS & Université Paris-Sud, Université Paris-Saclay            *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Require Import String.
Require Import OrderedSet.

(** * Definition of relation's names, and finite sets of relation's names *)


Inductive relname : Set := Rel : string -> relname.

Definition relname_compare r1 r2 :=
  match r1, r2 with
    | Rel s1, Rel s2 => string_compare s1 s2
  end.

Definition ORN : Oset.Rcd relname.
split with relname_compare.
intros [s1] [s2]; simpl.
generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
apply f_equal.
intros H1 H2; injection H2; apply H1.
intros H1 H2; injection H2; apply H1.
intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring).
intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring).
Defined.

