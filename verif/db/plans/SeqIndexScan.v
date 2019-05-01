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

Require Import ListFacts OrderedSet Signatures SeqScan.

Set Implicit Arguments.

Module SeqIndexScan.

Section Sec.

Hypotheses o1 o2 : Type.
Hypothesis O1 : Oeset.Rcd o1.
Hypothesis O2 : Oeset.Rcd o2.
Hypothesis proj : o1 -> o2.
Hypothesis proj_eq : 
        forall x y, Oeset.compare O1 x y = Eq -> Oeset.compare O2 (proj x) (proj y) = Eq.

Notation P := (fun (x y : o2) => true).

Definition containers := list o1.

Definition c1 : containers -> list o1 := fun l => l.

Definition dummy_containers : containers := nil.

Definition C1 := SeqScan.build O1.

Definition i : containers -> o2 -> Cursor.cursor C1 :=
    fun c _ => SeqScan.mk_cursor nil c c.
    
Lemma i_collection_strong : 
  forall c x, Cursor.collection (i c x) = filter (fun y => P x (proj y)) (c1 c).
Proof. intros. rewrite filter_true; intros; apply refl_equal. Qed.

Lemma i_collection : 
  forall c x, 
    comparelA 
      (Oeset.compare O1) (Cursor.collection (i c x)) (filter (fun y => P x (proj y)) (c1 c)) = Eq.
Proof. 
  intros; rewrite i_collection_strong; apply comparelA_eq_refl. 
  intros; apply Oeset.compare_eq_refl.
Qed.

Lemma i_visited : forall c x, Cursor.visited (i c x) = nil. 
Proof. reflexivity. Qed.

Lemma i_coherent : forall c x, Cursor.coherent (i c x). 
Proof. reflexivity. Qed.

Definition build : Index.Rcd O1 O2.
apply Index.mk_R with proj P C1 containers c1 i.
- apply proj_eq.
- intros; apply refl_equal.
- intros; apply refl_equal.
- exact nil.
- apply i_collection.
- apply i_visited.
- apply i_coherent.
Defined.

End Sec.
End SeqIndexScan.
 

