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

Require Import Arith NArith ZArith String List. 
Require Import ListFacts OrderedSet FiniteSet FlatData Values. 

(** * Definition of attributes, and finite sets of attributes *)

(** There are several constructors for attributes, one for each type. This allows to have an infinite number of attributes, usefull for renaming for instance, but also to a generic function [type_of_attribute]. *)
Inductive attribute : Set :=
  | Attr_string : N -> string -> attribute
  | Attr_ptrofs : N -> string -> attribute.

Definition type_of_attribute (a : attribute) :=
  match a with
    | Attr_string _ _ => type_string
    | Attr_ptrofs _ _ => type_ptrofs
  end.

Open Scope N_scope.

Definition N_of_attribute a := 
  match a with   
    | Attr_string _ _ => 0
    | Attr_ptrofs _ _ => 1
  end.

Definition N3_of_attribute a :=
  match a with
    | Attr_string n s
    | Attr_ptrofs n s => (N_of_attribute a, n, s)
  end.

Definition attribute_compare a1 a2 :=
  compareAB (compareAB Ncompare Ncompare) string_compare (N3_of_attribute a1) (N3_of_attribute a2).

Definition OAN : Oset.Rcd attribute.
Proof.
split with attribute_compare.
- intros a1 a2; unfold attribute_compare.
  assert (match compareAB (compareAB N.compare N.compare) string_compare
                           (N3_of_attribute a1) (N3_of_attribute a2) with
             | Eq => (N3_of_attribute a1) = (N3_of_attribute a2)
             | Lt => (N3_of_attribute a1) <> (N3_of_attribute a2)
             | Gt => (N3_of_attribute a1) <> (N3_of_attribute a2)
           end).
  {
    destruct (N3_of_attribute a1) as [[n1 m1] s1];
    destruct (N3_of_attribute a2) as [[n2 m2] s2].
    compareAB_eq_bool_ok_tac.
    - compareAB_eq_bool_ok_tac.
      + apply (Oset.eq_bool_ok ON).
      + apply (Oset.eq_bool_ok ON).
    - apply (Oset.eq_bool_ok Ostring).
  }
  case_eq (N3_of_attribute a1); intros [n1 m1] s1 H1;
  case_eq (N3_of_attribute a2); intros [n2 m2] s2 H2;
  rewrite H1, H2 in H.
  destruct (compareAB 
              (compareAB N.compare N.compare) string_compare
              (n1, m1, s1) (n2, m2, s2)).
  + injection H; clear H; do 3 intro.
    subst s2 m2 n2; rewrite <- H2 in H1.
    destruct a1; destruct a2; (try discriminate H1) || (injection H1; intros; subst; trivial).
  + intro Ha; apply H; rewrite <- Ha in H2; rewrite H1 in H2.
    apply H2.
  + intro Ha; apply H; rewrite <- Ha in H2; rewrite H1 in H2.
    apply H2.
- intros a1 a2 a3; unfold attribute_compare.
  compareAB_tac.
  + compareAB_tac.
    * apply (Oset.compare_eq_trans ON).
    * apply (Oset.compare_eq_trans ON).
  + compareAB_tac.
    * apply (Oset.compare_eq_trans ON).
    * apply (Oset.compare_eq_lt_trans ON).
    * apply (Oset.compare_eq_lt_trans ON).
  + compareAB_tac.    
    * apply (Oset.compare_eq_trans ON).
    * apply (Oset.compare_lt_eq_trans ON).
    * apply (Oset.compare_lt_eq_trans ON).
  + compareAB_tac.    
    * apply (Oset.compare_eq_trans ON).
    * apply (Oset.compare_eq_lt_trans ON).
    * apply (Oset.compare_lt_eq_trans ON).
    * apply (Oset.compare_lt_trans ON).
    * apply (Oset.compare_lt_trans ON).
  + apply (Oset.compare_lt_trans Ostring).
- intros a1 a2; unfold attribute_compare.
  compareAB_tac.
  + compareAB_tac.
    * apply (Oset.compare_lt_gt ON).
    * apply (Oset.compare_lt_gt ON).
  + apply (Oset.compare_lt_gt Ostring).
Defined.

Definition FAN := Fset.build OAN.

Definition extract_N_of_att a :=
  match a with
    | Attr_string n _
    | Attr_ptrofs n _ => n
  end.

Definition incr_att m a :=
  match a with
    | Attr_string n s => Attr_string (n + m) s
    | Attr_ptrofs n s => Attr_ptrofs (n + m) s
  end.

Lemma incr_att_inj : forall m a1 a2, incr_att m a1 = incr_att m a2 -> a1 = a2.
Proof.
intros m a1 a2 H; destruct a1; destruct a2; 
try discriminate H; injection H; clear H;
intro; subst; intro H;
rewrite N.add_cancel_r in H; subst; apply refl_equal.
Qed.

Lemma extract_N_of_incr_att : 
  forall a n, extract_N_of_att (incr_att n a) = (n + extract_N_of_att a)%N.
Proof.
intros a n; destruct a; simpl; apply N.add_comm.
Qed.
