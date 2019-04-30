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
(**                  Chantal Keller                                                 *)
(**                  Eunice-Raquel Martins                                          *)
(**                                                                                 *)
(************************************************************************************)

Require Import List NArith.

Require Import OrderedSet FiniteSet.

Set Implicit Arguments.

Open Scope N_scope.

Section FilterSpec.

Hypothesis A containerA containerA': Type.
Hypothesis OA : Oeset.Rcd A.
Hypothesis contentA : containerA -> list A.
Hypothesis contentA' : containerA' -> list A.

Notation nb_occA a b := (Oeset.nb_occ OA a (contentA b)).
Notation nb_occA' a b := (Oeset.nb_occ OA a (contentA' b)).

Definition is_a_filter_op_strong (fltr : (A -> bool) -> containerA -> containerA') :=
  forall (f : A -> bool) (s : containerA),
  forall t, nb_occA' t (fltr f s) = (nb_occA t s) * (if f t then 1 else 0).

Definition is_a_filter_op (f : A -> bool) (fltr : containerA -> containerA') :=
  forall (s : containerA),
  forall t, nb_occA' t (fltr s) = (nb_occA t s) * (if f t then 1 else 0).

Lemma is_a_filter_op_strong_is_a_filter_op :
  forall fltr, is_a_filter_op_strong fltr <-> (forall f, is_a_filter_op f (fltr f)).
Proof.
intro fltr; unfold is_a_filter_op_strong, is_a_filter_op; split.
- intros H f; apply (H f).
- intros H; apply H.
Qed.

End FilterSpec.

Section MapSpec.

Hypothesis A B containerA containerB: Type.
Hypothesis OA : Oeset.Rcd A.
Hypothesis OB : Oeset.Rcd B.
Hypothesis contentA : containerA -> list A.
Hypothesis contentB : containerB -> list B.

Notation nb_occA a b := (Oeset.nb_occ OA a (contentA b)).
Notation nb_occB a b := (Oeset.nb_occ OB a (contentB b)).

Definition is_a_map_op_strong (mp : (A -> B) -> containerA -> containerB) := 
  forall (f : A -> B) (s : containerA),
  forall t, nb_occB t (mp f s) = Oeset.nb_occ OB t (map f (contentA s)).

Definition is_a_map_op (f : A -> B) (mp : containerA -> containerB) := 
  forall (s : containerA),
  forall t, nb_occB t (mp s) = Oeset.nb_occ OB t (map f (contentA s)).

Lemma is_a_map_op_strong_is_a_map_op :
  forall mp, is_a_map_op_strong mp <-> (forall f, is_a_map_op f (mp f)).
Proof.
intro mp; unfold is_a_map_op_strong, is_a_map_op; split.
- intros H f; apply (H f).
- intros H; apply H.
Qed.

End MapSpec.

Section JoinSpec.
Hypotheses A1 A2 A containerA1 containerA2 containerA: Type.
Hypothesis OA1 : Oeset.Rcd A1.
Hypothesis OA2 : Oeset.Rcd A2.
Hypothesis OA : Oeset.Rcd A.
Hypothesis contentA1 : containerA1 -> list A1.
Hypothesis contentA2 : containerA2 -> list A2.
Hypothesis contentA : containerA -> list A.
Notation nb_occA1 a b := (Oeset.nb_occ OA1 a (contentA1 b)).
Notation nb_occA2 a b := (Oeset.nb_occ OA2 a (contentA2 b)).
Notation nb_occA a b := (Oeset.nb_occ OA a (contentA b)).

Hypothesis Att : Type.
Hypothesis OAtt : Oset.Rcd Att.
Hypothesis FAtt : Fset.Rcd OAtt.

Notation setAtt := (Fset.set FAtt).

Hypothesis sup1 : A1 -> setAtt.
Hypothesis sup2 : A2 -> setAtt.
Hypothesis sup : A -> setAtt.
Hypothesis proj1_ : A -> A1.
Hypothesis proj2_ : A -> A2.

Definition is_a_join_op sa1 sa2 j :=
    forall (s1 : containerA1) (s2 : containerA2), 
      (forall t1, 0 < nb_occA1 t1 s1 -> sup1 t1 =S= sa1) ->
      (forall t2, 0 < nb_occA2 t2 s2 -> sup2 t2 =S= sa2) ->
      
      ((forall t, 0 < nb_occA t (j s1 s2) -> sup t =S= (sa1 unionS sa2)) /\
       (forall t, sup t =S= (sa1 unionS sa2) -> 
                  nb_occA t (j s1 s2) = nb_occA1 (proj1_ t) s1 * nb_occA2 (proj2_ t) s2)).


Definition is_a_join_op_alt sa1 sa2 j :=
    forall (s1 : containerA1) (s2 : containerA2), 
      (forall t1, 0 < nb_occA1 t1 s1 -> sup1 t1 =S= sa1) ->
      (forall t2, 0 < nb_occA2 t2 s2 -> sup2 t2 =S= sa2) ->
      forall t, nb_occA t (j s1 s2) = nb_occA1 (proj1_ t) s1 * nb_occA2 (proj2_ t) s2 *
                                      (if sup t =S?= (sa1 unionS sa2) then 1 else 0).

Lemma is_a_join_op_is_a_join_op_alt :
  forall sa1 sa2 j, is_a_join_op sa1 sa2 j <-> is_a_join_op_alt sa1 sa2 j.
Proof.
  intros sa1 sa2 j; 
    unfold is_a_join_op, is_a_join_op_alt; split;
    intros H s1 s2 H1 H2;
    assert (H' := H _ _ H1 H2).
  - intro t.
    case_eq (sup t =S?= (sa1 unionS sa2)); intro Ht.
    + rewrite (proj2 H' _ Ht), N.mul_1_r; apply refl_equal.
    + rewrite N.mul_0_r; apply Oeset.not_mem_nb_occ.
      case_eq (Oeset.mem_bool OA t (contentA (j s1 s2))); intro Kt; [ | apply refl_equal].
      generalize (proj1 H' t); rewrite Ht; intro Abs; apply sym_eq; apply Abs.
      rewrite <- Oeset.nb_occ_diff_0_pos.
      apply Oeset.mem_nb_occ; apply Kt.
  - split. 
    + intros t Ht.
      case_eq (sup t =S?= (sa1 unionS sa2)); intro Kt; [apply refl_equal | ].
      assert (Ht' := H' t).
      rewrite Kt, N.mul_0_r in Ht'.
      rewrite Ht' in Ht; discriminate Ht.
    + intros t Ht; rewrite H', Ht, N.mul_1_r; apply refl_equal.
Qed.

End JoinSpec.

Section FilterJoinSpec.

Hypotheses A1 A2 A containerA1 containerA2 containerA : Type.
Hypothesis OA1 : Oeset.Rcd A1.
Hypothesis OA2 : Oeset.Rcd A2.
Hypothesis OA : Oeset.Rcd A.
Hypothesis contentA1 : containerA1 -> list A1.
Hypothesis contentA2 : containerA2 -> list A2.
Hypothesis contentA : containerA -> list A.
Notation nb_occA1 a b := (Oeset.nb_occ OA1 a (contentA1 b)).
Notation nb_occA2 a b := (Oeset.nb_occ OA2 a (contentA2 b)).
Notation nb_occA a b := (Oeset.nb_occ OA a (contentA b)).

Hypothesis Att : Type.
Hypothesis OAtt : Oset.Rcd Att.
Hypothesis FAtt : Fset.Rcd OAtt.

Notation setAtt := (Fset.set FAtt).

Hypothesis sort1 : containerA1 -> setAtt.
Hypothesis sort2 : containerA2 -> setAtt.
Hypothesis sup1 : A1 -> setAtt.
Hypothesis sup2 : A2 -> setAtt.
Hypothesis sup : A -> setAtt.
Hypothesis proj1_ : A -> A1.
Hypothesis proj2_ : A -> A2.

Definition is_a_filter_join_op (f : A -> bool) sa1 sa2 j :=
    forall (s1 : containerA1) (s2 : containerA2), 
      (forall t1, 0 < nb_occA1 t1 s1 -> sup1 t1 =S= sa1) ->
      (forall t2, 0 < nb_occA2 t2 s2 -> sup2 t2 =S= sa2) ->
      
      ((forall t, 0 < nb_occA t (j s1 s2) -> sup t =S= (sa1 unionS sa2)) /\
       (forall t, sup t =S= (sa1 unionS sa2) -> 
                  nb_occA t (j s1 s2) = 
                  nb_occA1 (proj1_ t) s1 * nb_occA2 (proj2_ t) s2 * (if f t then 1 else 0))).

End FilterJoinSpec.

Section GroupSpec.

Hypothesis A B containerA containerA': Type.
Hypothesis OA : Oeset.Rcd A.
Hypothesis contentA : containerA -> list A.
Hypothesis contentA' : containerA' -> list A.
Notation nb_occA a b := (Oeset.nb_occ OA a (contentA b)).
Notation nb_occA' a b := (Oeset.nb_occ OA a (contentA' b)).

Hypothesis Att : Type.
Hypothesis OAtt : Oset.Rcd Att.
Hypothesis FAtt : Fset.Rcd OAtt.

Notation setAtt := (Fset.set FAtt).

Definition is_a_grouping_op_strong (G : Type) (mk_g : G -> containerA' -> list B) grp :=
  forall (g : G) (f : B -> bool) (build : B -> A) (s : containerA') t, 
    nb_occA t (grp g f build s) = Oeset.nb_occ OA t (map build (filter f (mk_g g s))).

Definition is_a_grouping_op 
   (G : Type) (mk_g : G -> containerA' -> list B) (g : G) (f : B -> bool) (build : B -> A) grp :=
  forall (s : containerA') t,
    nb_occA t (grp s) = Oeset.nb_occ OA t (map build (filter f (mk_g g s))).

Lemma is_a_grouping_op_strong_is_a_grouping_op :
  forall (G : Type) (mk_g : G -> containerA' -> list B) grp,
    is_a_grouping_op_strong mk_g grp <-> 
    (forall g f build, is_a_grouping_op mk_g g f build (grp g f build)).
Proof.
  intros G mk_g grp; unfold is_a_grouping_op, is_a_grouping_op_strong; split.
- intros H g f build; apply (H g f build).
- intros H g f build; apply H.
Qed.

End GroupSpec.

