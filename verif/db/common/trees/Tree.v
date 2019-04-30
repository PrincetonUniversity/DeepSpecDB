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

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import ListFacts OrderedSet FiniteSet.

Section Sec.

Hypothesis All : Type.
Hypothesis OAll : Oeset.Rcd All.

Inductive tree : Type :=
  | Leaf : All -> tree 
  | Node : N -> list tree -> tree.

Fixpoint tree_compare (t1 t2 : tree) : comparison :=
  match t1, t2 with
  | Leaf a1, Leaf a2 => Oeset.compare OAll a1 a2
  | Leaf _, Node _ _ => Lt
  | Node _ _, Leaf _ => Gt
  | Node n1 l1, Node n2 l2 =>
    compareAB (Oset.compare ON) (comparelA tree_compare) (n1, l1) (n2, l2)
  end.

Lemma tree_compare_unfold :
  forall t1 t2, tree_compare t1 t2 =
  match t1, t2 with
  | Leaf a1, Leaf a2 => Oeset.compare OAll a1 a2
  | Leaf _, Node _ _ => Lt
  | Node _ _, Leaf _ => Gt
  | Node n1 l1, Node n2 l2 =>
    compareAB (Oset.compare ON) (comparelA tree_compare) (n1, l1) (n2, l2)
  end.
Proof.
intros t1 t2; destruct t1; destruct t2; apply refl_equal.
Qed.

Close Scope N_scope.

Fixpoint tree_size (t : tree) : nat :=
  match t with
  | Leaf _ => 1
  | Node _ l => 1 + list_size tree_size l
  end.

Lemma tree_size_unfold :
  forall t,
    tree_size t = 
  match t with
  | Leaf _ => 1
  | Node _ l => 1 + list_size tree_size l
  end.
Proof.
intro t; destruct t; apply refl_equal.
Qed.

Notation suitable_x n size_a a_compare x1 :=
  (size_a x1 <= n -> 
      a_compare x1 x1 = Eq /\ 
      forall x2, (a_compare x1 x2 = CompOpp (a_compare x2 x1)) /\
      forall x3, 
      (a_compare x1 x2 = Eq -> a_compare x2 x3 = Eq -> a_compare x1 x3 = Eq) /\
      (a_compare x1 x2 = Eq -> a_compare x2 x3 = Lt -> a_compare x1 x3 = Lt) /\
      (a_compare x1 x2 = Lt -> a_compare x2 x3 = Eq -> a_compare x1 x3 = Lt) /\
      (a_compare x1 x2 = Lt -> a_compare x2 x3 = Lt -> a_compare x1 x3 = Lt)).

Notation suitable n size_a a_compare :=
  (forall x1, suitable_x n size_a a_compare x1).

Lemma all_suitable_tree_rec1 : 
   forall n, suitable n tree_size tree_compare -> 
   forall a, suitable_x (S n) tree_size tree_compare (Leaf a).
Proof.
intros n IHt a1 _.
split; [ | intro t2; split; [ | intro t3; split; [ | split; [ | split]]]].
- (* 1/6 *)
  simpl; (trivial || discriminate || oeset_compare_tac).
- (* 1/5 *)
  case t2; simpl; intros; (trivial || discriminate || oeset_compare_tac).
- (* 1/4 *)
  case t2; clear t2; try discriminate.
  intro a2; case t3; simpl; intros; (trivial || discriminate || oeset_compare_tac).
- (* 1/3 *)
  case t2; clear t2; try discriminate.
  intro a2; case t3; simpl; intros; (trivial || discriminate || oeset_compare_tac).
- (* 1/2 *)
  case t2; clear t2; try discriminate;
  intro a2; case t3; simpl; intros; (trivial || discriminate || oeset_compare_tac).
- (* 1/1 *)
  case t2; clear t2; try discriminate;
  intro a2; case t3; simpl; intros; (trivial || discriminate || oeset_compare_tac).
Qed.

Lemma all_suitable_tree_rec2 : 
   forall n, suitable n tree_size tree_compare -> 
   forall m l, suitable_x (S n) tree_size tree_compare (Node m l).
Proof.
intros n IHt m l L. 
assert (Sl : forall t, List.In t l -> tree_size t <= n).
{
 intros t Ht; apply le_trans with (list_size tree_size l).
 - apply in_list_size; apply Ht.
 - apply le_S_n; apply L.
} 
assert (IH := fun t (h : List.In t l) => IHt t (Sl t h)).
split; [ | intro t2; split; [ | intro t3; split; [ | split; [ | split]]]].
- (* 1/6 *)
  rewrite tree_compare_unfold; compareAB_tac.
  apply comparelA_eq_refl.
  intros t Ht; apply (proj1 (IH t Ht)).
- (* 1/5 *)
  destruct t2 as [a2 | m2 l2]; [simpl; apply refl_equal | ].
  rewrite 2 tree_compare_unfold; compareAB_tac.
  + oset_compare_tac.
  + comparelA_tac.
    apply (proj1 (proj2 (IH _ H) _)).
- (* 1/4 *)
  destruct t2 as [a1 | m2 l2]; [intro H1; discriminate H1 | ].
  destruct t3 as [a3 | m3 l3]; [intros H1 H2; discriminate H2 | ].
  rewrite 3 tree_compare_unfold; compareAB_tac.
  + oset_compare_tac.
  + comparelA_tac.
    apply (proj1 (proj2 (proj2 (IH _ H) _) _)).
- (* 1/3 *)
  destruct t2 as [a2 | m2 l2]; [intro H1; discriminate H1 | ].
  destruct t3 as [a3 | m3 l3]; [intros H1 H2; discriminate H2 | ].
  rewrite 3 tree_compare_unfold; compareAB_tac; (oset_compare_tac || comparelA_tac).
  + apply (proj1 (proj2 (proj2 (IH _ H) _) _)).
  + apply (proj1 (proj2 (proj2 (proj2 (IH _ H) _) _))).
- (* 1/2 *)
  destruct t2 as [a2 | m2 l2]; [intro H1; discriminate H1 | ].
  destruct t3 as [a3 | m3 l3]; [intros H1 H2; discriminate H2 | ].
  rewrite 3 tree_compare_unfold; compareAB_tac; (oset_compare_tac || comparelA_tac).
  + apply (proj1 (proj2 (proj2 (IH _ H) _) _)).
  + apply (proj1 (proj2 (proj2 (proj2 (proj2 (IH _ H) _) _)))).
- (* 1/1 *)
  destruct t2 as [a2 | m2 l2]; [intro H1; discriminate H1 | ].
  destruct t3 as [a3 | m3 l3]; [intros H1 H2; discriminate H2 | ].
  rewrite 3 tree_compare_unfold; compareAB_tac; (oset_compare_tac || comparelA_tac).
  + apply (proj1 (proj2 (proj2 (IH _ H) _) _)).
  + apply (proj1 (proj2 (proj2 (proj2 (IH _ H) _) _))).
  + apply (proj1 (proj2 (proj2 (proj2 (proj2 (IH _ H) _) _)))).
  + apply (proj2 (proj2 (proj2 (proj2 (proj2 (IH _ H) _) _)))).
Qed.

Lemma all_suitable_tree : 
  forall x1,
      tree_compare x1 x1 = Eq /\ 
      forall x2, (tree_compare x1 x2 = CompOpp (tree_compare x2 x1)) /\
      forall x3, 
      (tree_compare x1 x2 = Eq -> tree_compare x2 x3 = Eq -> tree_compare x1 x3 = Eq) /\
      (tree_compare x1 x2 = Eq -> tree_compare x2 x3 = Lt -> tree_compare x1 x3 = Lt) /\
      (tree_compare x1 x2 = Lt -> tree_compare x2 x3 = Eq -> tree_compare x1 x3 = Lt) /\
      (tree_compare x1 x2 = Lt -> tree_compare x2 x3 = Lt -> tree_compare x1 x3 = Lt).
Proof.
intro x1.
set (n := tree_size x1).
assert (Sx : tree_size x1 <= n).
apply le_n.
clearbody n.
revert x1 Sx; induction n as [ | n].
intros x1 Sx; destruct x1; simpl in Sx; inversion Sx.
intro x1; case x1.
apply all_suitable_tree_rec1; assumption.
apply all_suitable_tree_rec2; assumption.
Qed.

Lemma tree_compare_lt_gt :
  forall x1 x2, tree_compare x1 x2 = CompOpp (tree_compare x2 x1).
Proof.
intros x1 x2.
destruct (all_suitable_tree x1) as [_ H]; apply (proj1 (H x2)).
Qed.

Lemma tree_compare_eq_refl :
  forall x1, tree_compare x1 x1 = Eq.
Proof.
intros x1.
destruct (all_suitable_tree x1) as [H _]; apply H.
Qed.

Lemma tree_compare_size_eq :
  forall t1 t2, tree_compare t1 t2 = Eq -> tree_size t1 = tree_size t2.
Proof.
intro t1; set (n := tree_size t1).
assert (Hn := le_n n); unfold n at 1 in Hn.
unfold n; clearbody n.
revert t1 Hn; induction n as [ | n];
intros [a1 | f1 l1] Hn [a2 | f2 l2] Ht; simpl; simpl in Hn;
try (trivial || discriminate Ht).
- inversion Hn.
- subst; apply f_equal.
  rewrite tree_compare_unfold in Ht; unfold compareAB in Ht.
  case_eq (Oset.compare ON f1 f2);
    intro Hl; rewrite Hl in Ht; try discriminate Ht.
  generalize (le_S_n _ _ Hn); clear Hn; intro Hn.
  clear Hl.
  assert (IH : forall t1 : tree, List.In t1 l1 ->
                                 forall t2 : tree,
                                   tree_compare t1 t2 = Eq -> tree_size t1 = tree_size t2).
    {
      intros t1 Ht1 t2; apply IHn.
      clear Ht.
      refine (le_trans _ _ _ _ Hn).
      apply in_list_size; assumption.
    }
    clear IHn.
    revert l2 Ht; induction l1 as [ | t1 l1]; intros [ | t2 l2] Ht.
    * apply refl_equal.
    * discriminate Ht.
    * discriminate Ht.
    * simpl in Ht; simpl.
      case_eq (tree_compare t1 t2); 
        intro Kt; rewrite Kt in Ht; try discriminate Ht.
      apply f_equal2; [apply (IH t1 (or_introl _ (refl_equal _)) t2 Kt) | ].
      {
        apply IHl1.
        - refine (le_trans _ _ _ _ Hn).
          simpl; apply le_plus_r.
        - do 3 intro; apply IH; right; assumption.
        - assumption.
      } 
Qed.

Lemma tree_rec3 :
  forall (P : tree -> Type), 
    (forall a, P (Leaf a)) -> 
    (forall m l, (forall t, In t l -> P t) -> P (Node m l)) -> forall t, P t.
Proof.
intros P IH1 IH2 t.
set (n := tree_size t).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert t Hn; induction n as [ | n].
- intros t Hn; destruct t; simpl in Hn; (assert (H : False); [inversion Hn | contradiction H]).
- intros t Hn; destruct t as [a | m l]; [apply IH1 | ].
  apply IH2; intros t Ht; apply IHn.
  simpl in Hn.
  refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
  apply in_list_size; assumption.
Qed.

End Sec.

Section Equality.

Hypothesis All : Type.
Hypothesis OAll : Oset.Rcd All.

Definition OTree : Oset.Rcd (tree All).
set (AST := all_suitable_tree (oeset_of_oset OAll)).
split with (tree_compare (oeset_of_oset OAll)).
- intros x1; pattern x1; apply tree_rec3; clear x1.
  + intros a1 [a2 | m2 l2]; simpl; [ | discriminate].
    oset_compare_tac.
  + intros m1 l1 IH1 [a1 | m2 l2]; [simpl; discriminate | ].
    rewrite tree_compare_unfold.
    unfold compareAB.
    generalize (Oset.eq_bool_ok ON m1 m2).
    case (Oset.compare ON m1 m2).
    * intros H1; subst m2.
      {
        case_eq (comparelA (tree_compare (oeset_of_oset OAll)) l1 l2); intro H2.
        - apply f_equal.
          revert l2 H2; induction l1 as [ | a1 l1]; intros [ | a2 l2] H2; 
          try (trivial || discriminate H2).
          simpl in H2.
          case_eq (tree_compare (oeset_of_oset OAll) a1 a2); 
            intro Ha; rewrite Ha in H2; try discriminate H2.
          apply f_equal2.
          + assert (IHa1 := IH1 a1 (or_introl _ (refl_equal _)) a2).
            rewrite Ha in IHa1; apply IHa1.
          + apply IHl1; [ | assumption].
            do 2 intro; apply IH1; right; assumption.
        - intro H; injection H; clear H; intro; subst l2.
          induction l1 as [ | a1 l1]; [discriminate H2 | ].
          simpl in H2.
          assert (IHa1 := IH1 a1 (or_introl _ (refl_equal _)) a1).
          case_eq (tree_compare (oeset_of_oset OAll) a1 a1); intro Ha1; rewrite Ha1 in IHa1, H2.
          + refine (IHl1 _ H2).
            do 2 intro; apply IH1; right; assumption.
          + apply False_rec; apply IHa1; apply refl_equal.
          + apply False_rec; apply IHa1; apply refl_equal.
        - intro H; injection H; clear H; intro; subst l2.
          induction l1 as [ | a1 l1]; [discriminate H2 | ].
          simpl in H2.
          assert (IHa1 := IH1 a1 (or_introl _ (refl_equal _)) a1).
          case_eq (tree_compare (oeset_of_oset OAll) a1 a1); intro Ha1; rewrite Ha1 in IHa1, H2.
          + refine (IHl1 _ H2).
            do 2 intro; apply IH1; right; assumption.
          + apply False_rec; apply IHa1; apply refl_equal.
          + apply False_rec; apply IHa1; apply refl_equal.
      } 
    * intros H1 H2; injection H2; clear H2; do 2 intro; subst; apply H1; apply refl_equal.
    * intros H1 H2; injection H2; clear H2; do 2 intro; subst; apply H1; apply refl_equal.
- intros x1 x2 x3.
  destruct (AST x1) as [_ H]; apply (proj2 (proj2 (proj2 (proj2 (H x2) x3)))).
- intros x1 x2.
  destruct (AST x1) as [_ H]; apply (proj1 (H x2)).
Defined.

End Equality.

Section Equivalence.

Hypothesis All : Type.
Hypothesis OEAll : Oeset.Rcd All.

Definition OETree : Oeset.Rcd (tree All).
set (AST := all_suitable_tree OEAll).
split with (tree_compare OEAll).
- intros x1 x2 x3; destruct (AST x1) as [_ H].
  apply (proj1 ((proj2 (H x2)) x3)).
- intros x1 x2 x3; destruct (AST x1) as [_ H].
  apply (proj1 (proj2 ((proj2 (H x2)) x3))).
- intros x1 x2 x3; destruct (AST x1) as [_ H].
  apply (proj1 (proj2 (proj2 ((proj2 (H x2)) x3)))).
- intros x1 x2 x3; destruct (AST x1) as [_ H].
  apply (proj2 (proj2 (proj2 ((proj2 (H x2)) x3)))).
- intros x1 x2.
  destruct (AST x1) as [_ H]; apply (proj1 (H x2)).
Defined.

End Equivalence.
  
