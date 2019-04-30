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
Require Import OrderedSet Signatures Filter NestedLoop.

Set Implicit Arguments.

Module ThetaNestedLoop.
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

Hypothesis theta : o -> bool.
Hypothesis theta_eq : forall x y, Oeset.compare O x y = Eq -> theta x = theta y.

Hypothesis C1 : Cursor.Rcd O1.
Hypothesis C2 : Cursor.Rcd O2.

Definition build : Cursor.Rcd O :=
  Filter.build _ theta_eq (NestedLoop.build O _ build_eq_1 build_eq_2 C1 C2).

End Sec.

End ThetaNestedLoop.
