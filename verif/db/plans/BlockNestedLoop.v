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

Require Import List.
Require Import OrderedSet Signatures NestedLoop.

Set Implicit Arguments.

Module BlockNestedLoop.
Section Sec.
Hypotheses o1 o2 o : Type.
Hypothesis O1 : Oeset.Rcd o1.
Hypothesis O2 : Oeset.Rcd o2.
Hypothesis O : Oeset.Rcd o.

Hypothesis build_ : o1 -> o2 -> o.
Hypothesis build_eq_1  : 
  forall x1 x1' x2, 
    Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
Hypothesis build_eq_2  : 
  forall x1 x2 x2', 
    Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.

Definition OL1 := mk_oelists O1.
Definition OL2 := mk_oelists O2.
Definition OL := mk_oelists O.

Hypothesis C1 : Cursor.Rcd OL1.
Hypothesis C2 : Cursor.Rcd OL2.

Definition build : Cursor.Rcd OL.
apply NestedLoop.build with 
    (list o1) (list o2) OL1 OL2 
    (fun l1 l2 => flat_map (fun e1 => map (fun e2 => build_ e1 e2) l2) l1).
- intros l1; induction l1 as [ | x1 l1]; intros [ | x1' l1'] l2 H1; try discriminate H1; trivial.
  simpl in H1; case_eq (Oeset.compare O1 x1 x1'); intro Hx1; rewrite Hx1 in H1; try discriminate H1.
  simpl.
  apply comparelA_eq_app.
  + induction l2 as [ | x2 l2]; simpl; trivial.
    rewrite (build_eq_1 _ _ _ Hx1).
    apply IHl2.
  + assert (IH := IHl1 l1' l2 H1); simpl in IH; apply IH.
- intro l1; induction l1 as [ | x1 l1]; intros x2 x2' Hx2; simpl; trivial.
  apply comparelA_eq_app.
  + revert x2' Hx2; induction x2 as [ | a2 l2]; intros [ | a2' l2'] Hl2; simpl; trivial.
    simpl in Hl2.
    case_eq (Oeset.compare O2 a2 a2'); intro Ha2; rewrite Ha2 in Hl2; try discriminate Hl2.
    rewrite (build_eq_2 _ _ _ Ha2).
    apply IHl2; trivial.
  + assert (IH := IHl1 x2 x2' Hx2); simpl in IH; apply IH.
- exact C1. 
- exact C2.
Defined.

End Sec.
End BlockNestedLoop.


