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

Require Import Arith NArith ZArith String.
Require Import OrderedSet FiniteSet.

Require Import compcert.lib.Integers.

(** Types a.k.a domains in the database textbooks. *)
Inductive type := 
 | type_string 
 | type_ptrofs.

Definition type_dec_eq : forall x y : type, {x = y} + {x <> y}. decide equality. Qed.

(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : string -> value
  | Value_ptrofs : ptrofs -> value.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_ptrofs _ => type_ptrofs
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string EmptyString
    | type_ptrofs => Value_ptrofs Ptrofs.zero
  end.

(** injection of domain names into natural numbers in order to
    build an ordering on them.
*)

Open Scope N_scope.

Definition N_of_type := 
    fun d => 
    match d with   
    | type_string => 0
    | type_ptrofs => 1
    end.

Definition OT : Oset.Rcd type.
apply Oemb with N_of_type.
intros d1 d2; case d1; case d2;
(exact (fun _ => refl_equal _) || (intro Abs; discriminate Abs)).
Defined.

(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
 *)

Definition value_compare x y := 
  match x, y with
    | Value_string s1, Value_string s2 => string_compare s1 s2
    | Value_string _, Value_ptrofs _ => Lt 
    | Value_ptrofs n1, Value_ptrofs n2 => ptrofs_compare n1 n2
    | Value_ptrofs _, Value_string _ => Gt
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
(* 1/3 *)
intros [s1 | p1] [s2 | p2]; try discriminate.
generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
apply f_equal.
intros H1 H2; injection H2; apply H1.
intros H1 H2; injection H2; apply H1.
generalize (Oset.eq_bool_ok Optrofs p1 p2); simpl; case (ptrofs_compare p1 p2).
apply f_equal.
intros H1 H2; injection H2; apply H1.
intros H1 H2; injection H2; apply H1.
(* 1/2 *)
intros [s1 | p1 ] [s2 | p2 ] [s3 | p3 ]; trivial; try discriminate; simpl.
apply (Oset.compare_lt_trans Ostring).
apply (Oset.compare_lt_trans Optrofs).
(* 1/1 *)
intros [s1 | p1] [s2 | p2]; trivial; simpl.
apply (Oset.compare_lt_gt Ostring).
apply (Oset.compare_lt_gt Optrofs).
Defined.

Definition FVal := Fset.build OVal.
