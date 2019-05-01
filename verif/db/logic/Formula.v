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

Require Import Bool List NArith.
Require Import BasicFacts ListFacts OrderedSet Tree FiniteSet ListPermut ListSort.

Inductive and_or : Type :=
  | And_F 
  | Or_F.

Inductive quantifier : Type :=
  | Forall_F
  | Exists_F.

Definition interp_conj a := 
  match a with 
    | And_F => andb 
    | Or_F => orb 
  end.

Definition interp_quant qf :=
  match qf with
      Forall_F => forallb
    | Exists_F => existsb
  end.

Section Interp.

Hypothesis dom_value : Type.
Hypothesis ODVal : Oeset.Rcd dom_value.

Notation "s1 '=PE=' s2" := (forall x, Oeset.mem_bool ODVal x s1 = Oeset.mem_bool ODVal x s2) (at level 70, no associativity).
Notation "a 'inE' s" := (Oeset.mem_bool ODVal a s = true) (at level 70, no associativity).

Lemma interp_quant_eq :
  forall q i1 i2 s1 s2, 
    s1 =PE= s2 -> 
    (forall x1 x2, x1 inE s1 -> Oeset.compare ODVal x1 x2 = Eq -> i1 x1 = i2 x2) ->
    interp_quant q i1 s1 = interp_quant q i2 s2.
Proof.
intros q i1 i2 s1 s2 Hs Hi; unfold interp_quant; destruct q; rewrite eq_bool_iff.
- rewrite 2 forallb_forall; split.
  + intros H x Hx.
    assert (Kx : x inE s1).
    {
      rewrite Hs, Oeset.mem_bool_true_iff.
      exists x; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    assert (Jx := Kx).
    rewrite Oeset.mem_bool_true_iff in Jx.
    destruct Jx as [x' [Jx Hx']].
    assert (Jx' : x' inE s1).
    {
      rewrite Oeset.mem_bool_true_iff.
      exists x'; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    rewrite <- (H x' Hx'); apply sym_eq.
    apply (Hi _ _ Jx').
    rewrite Oeset.compare_lt_gt, Jx; apply refl_equal.
  + intros H x Hx.
    assert (Kx : x inE s2).
    {
      rewrite <- Hs, Oeset.mem_bool_true_iff.
      exists x; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    assert (Jx := Kx).
    rewrite Oeset.mem_bool_true_iff in Jx.
    destruct Jx as [x' [Jx Hx']].
    assert (Jx' : x' inE s2).
    {
      rewrite Oeset.mem_bool_true_iff.
      exists x'; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    rewrite <- (H x' Hx').
    apply Hi.
    rewrite Hs; assumption.
    assumption.
- rewrite 2 existsb_exists.
  split.
  + intros [x [Hx Kx]].
    assert (Kx1 : x inE s1).
    {
      rewrite Oeset.mem_bool_true_iff.
      exists x; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    assert (Jx := Kx1).
    rewrite Hs, Oeset.mem_bool_true_iff in Jx.
    destruct Jx as [x' [Jx Hx']].
    exists x'; split; [assumption | ].
    rewrite <- Kx; apply sym_eq; apply Hi; trivial.
  + intros [x [Hx Kx]].
    assert (Kx1 : x inE s1).
    {
      rewrite Hs, Oeset.mem_bool_true_iff.
      exists x; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    }
    assert (Jx := Kx1).
    rewrite Oeset.mem_bool_true_iff in Jx.
    destruct Jx as [x' [Jx Hx']].
    exists x'; split; [assumption | ].
    rewrite <- Kx; apply Hi.
    * rewrite Oeset.mem_bool_true_iff.
      exists x'; split; [ | assumption].
      apply Oeset.compare_eq_refl.
    * rewrite Oeset.compare_lt_gt, Jx; apply refl_equal.
Qed.

End Interp.

