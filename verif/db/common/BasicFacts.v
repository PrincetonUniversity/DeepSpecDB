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

Set Implicit Arguments.

Require Import NArith List.

Lemma app_nil : forall (A : Type) (l : list A), nil ++ l = l.
Proof.
intros A l; apply refl_equal.
Qed.

Lemma f_equal6 :
 forall (A1 A2 A3 A4 A5 A6 B : Type) 
        (f : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> B)
        (x1 y1 : A1) (x2 y2 : A2) (x3 y3 : A3) (x4 y4 : A4)  (x5 y5 : A5) (x6 y6 : A6),
   x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> 
   f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6.
Proof.
intros; subst; trivial.
Qed.

Lemma f_equal7 :
 forall (A1 A2 A3 A4 A5 A6 A7 B : Type) 
        (f : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> B)
        (x1 y1 : A1) (x2 y2 : A2) (x3 y3 : A3) (x4 y4 : A4)  (x5 y5 : A5) (x6 y6 : A6)
        (x7 y7 : A7),
   x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> 
   f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7.
Proof.
intros; subst; trivial.
Qed.

Lemma f_equal8 :
 forall (A1 A2 A3 A4 A5 A6 A7 A8 B : Type) 
        (f : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> B)
        (x1 y1 : A1) (x2 y2 : A2) (x3 y3 : A3) (x4 y4 : A4)  (x5 y5 : A5) (x6 y6 : A6)
        (x7 y7 : A7) (x8 y8 : A8),
   x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 ->
   f x1 x2 x3 x4 x5 x6 x7 x8 = f y1 y2 y3 y4 y5 y6 y7 y8.
Proof.
intros; subst; trivial.
Qed.

Lemma if_if :
  forall (A : Type) (b1 b2 : bool) (x y : A), 
    (if b1 then if b2 then x else y else y) = if (andb b1 b2) then x else y.
Proof.
intros A b1 b2 x y; case b1; [case b2 | ]; apply refl_equal.
Qed.

Lemma eq_bool_iff :
  forall b1 b2, b1 = b2 <-> (b1 = true -> b2 = true) /\ (b2 = true -> b1 = true).
Proof.
intros b1 b2; split.
- intro H; subst b2; split; exact (fun h => h).
- intros [H1 H2]; destruct b1; destruct b2; trivial.
  + apply sym_eq; apply H1; apply refl_equal.
  + apply H2; apply refl_equal.
Qed.

Lemma if_eq :
  forall (A : Type) (b1 b2 : bool) (a1 a2 c1 c2 : A),
    b1 = b2 -> (b1 = true -> a1 = a2) -> (b1 = false -> c1 = c2) -> 
    (if b1 then a1 else c1) = (if b2 then a2 else c2).
Proof.
intros A b1 b2 a1 a2 c1 c2 Hb Ha Hc; subst.
case_eq b2; assumption.
Qed.

Lemma if_eq_mul :
  forall (b1 b2 : bool) (a1 a2 : N),
    b1 = b2 -> (b1 = true -> a1 = a2) ->
    (a1 * (if b1 then 1 else 0))%N = (if b2 then a2 else 0)%N.
Proof.
intros b1 b2 a1 a2 Hb Ha; subst.
case_eq b2.
- rewrite N.mul_1_r; apply Ha.
- intros; rewrite N.mul_0_r; apply refl_equal.
Qed.

Lemma match_bool_eq :
  forall (A : Type) (b1 b2 : bool) (a1 a2 : A), 
    b1 = b2 ->
    match b1 with true => a1 | false => a2 end = match b2 with true => a1 | false => a2 end.
Proof.
intros A b1 b2 a1 a2 H; subst b2; apply refl_equal.
Qed.

Lemma match_option_eq :
  forall (A C : Type) (a1 a2 : option A) (c : C) (f : A -> C), 
    a1 = a2 ->
    match a1 with Some b => f b | None => c end = match a2 with Some b => f b | None => c end. 
Proof.
intros A C a1 a2 c f H; subst a2.
apply refl_equal.
Qed.

Lemma match_option_eq2 :
  forall (A B C : Type) (a1 a2 : option A) (b1 b2 : B) (c : C) (f : A -> B -> C), 
    a1 = a2 -> (forall a, f a b1 = f a b2) -> 
    match a1 with Some a1' => f a1' b1 | None => c end = match a2 with Some a2' => f a2' b2 | None => c end. 
Proof.
intros A B C a1 a2 b1 b2 c f H K; subst a2.
destruct a1 as [a1 | ]; [ | apply refl_equal].
apply K.
Qed.

Require Import List.

Lemma In_app : 
  forall (A : Type) (a : A) (l1 l2 : list A), In a (l1 ++ l2) <-> (In a l1 \/ In a l2).
Proof.
intros A a l1 l2; split; intro H.
- destruct (in_app_or _ _ _ H) as [H1 | H2]; [left | right]; assumption.
- apply in_or_app; assumption.
Qed.

Require Import Relations.

Lemma equivalence_eq :
forall (A : Type), equivalence _ (@eq A).
Proof.
intro A; split.
- intro; apply refl_equal.
- do 5 intro; subst; trivial.
- do 3 intro; subst; trivial.
Qed.

Require Import NArith.

Lemma N_diff_0_ge_1 :
  forall n, match (n ?= 0)%N with Eq | Lt => false | Gt => true end = true <-> (n >= 1)%N.
Proof.
intro n; destruct n; simpl; split.
- intro Abs; discriminate Abs.
- intro Abs; unfold N.ge in Abs; simpl in Abs.
  apply False_rec; apply Abs; apply refl_equal.
- intros _; destruct p; discriminate.
- intros _; apply refl_equal.
Qed.

(* A lemma that vanished between coq-8.4 and coq-8.6 *)

Lemma nat_iter_succ_r n {A} (f : A->A) (x : A) :
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  induction n; intros; simpl; rewrite <- ?IHn; trivial.
Qed.

Lemma nat_iter_plus : 
  forall (n1 n2 : nat) (A : Type) (f : A -> A) x,
    Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
Proof.
intro n1; induction n1 as [ | n1]; intros n2 A f x; simpl; [ | rewrite IHn1]; trivial.
Qed.
