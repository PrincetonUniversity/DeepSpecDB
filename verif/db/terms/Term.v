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

Require Import Arith NArith List.

Require Import BasicFacts ListFacts FiniteSet OrderedSet.

Section Sec.

Hypothesis dom : Type.
Hypothesis symbol : Type.

(** Definition of variables as an type independant from term, in order to be able to build sets of variables *)
Inductive variable : Type :=
  | Vrbl : dom -> N -> variable.

(** Definition of terms *)
Inductive term : Type :=
  | Var : variable -> term 
  | Term : symbol -> list term -> term.

Fixpoint term_size (t : term) :=
  match t with
    | Var _ => 1
    | Term _ l => S (list_size term_size l)
  end.

Lemma term_size_ge_one : forall t, 1 <= term_size t.
Proof.
intros [v | f l]; [apply le_refl | ].
simpl; apply le_n_S; apply le_O_n.
Qed.

Definition term_rec3 :
  forall (P : term -> Type), 
    (forall v, P (Var v)) -> 
    (forall f l, (forall t, List.In t l -> P t) -> P (Term f l)) ->
    forall t, P t.
Proof.
intros P Hv IH t.
set (n := term_size t).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert t Hn; induction n as [ | n].
- intros [v | f l] Hn.
  + apply Hv.
  + simpl in Hn.
    apply False_rect.
    inversion Hn.
- intros [v | f l] Hn.
  + apply Hv.
  + simpl in Hn; generalize (le_S_n _ _ Hn).
    clear Hn; intro Hn.
    apply IH.
    intros t Ht.
    apply IHn.
    refine (le_trans _ _ _ _ Hn).
    apply in_list_size; apply Ht.
Defined.

Hypothesis OX : Oset.Rcd variable.
Hypothesis X : Fset.Rcd OX.

Fixpoint variables_t (t : term) : Fset.set X :=
  match t with
  | Term _ l => Fset.Union X (map variables_t l)
  | Var x => Fset.singleton X x
  end.

Lemma variables_t_unfold :
  forall t, variables_t t = 
  match t with
  | Term _ l => Fset.Union X (map variables_t l)
  | Var x => Fset.singleton X x
  end.
Proof.
intro t; case t; intros; apply refl_equal.
Qed.

Fixpoint variables_t_list (t : term) :=
  match t with
  | Term _ l => flat_map variables_t_list l
  | Var x => x :: nil
  end.

Lemma in_variables_t_var :
  forall x y, x inS variables_t (Var y) <-> y = x.
Proof.
intros x y; rewrite (variables_t_unfold (Var y)), Fset.singleton_spec, Oset.eq_bool_true_iff.
split; exact (fun h => sym_eq h).
Qed.

Lemma variables_t_variables_t_list :
  forall t, variables_t t =S= Fset.mk_set _ (variables_t_list t).
Proof.
intro t; pattern t; apply term_rec3.
- intro v; rewrite Fset.equal_spec; intro x.
  rewrite variables_t_unfold, Fset.singleton_spec.
  rewrite Fset.mem_mk_set; simpl variables_t_list.
  rewrite Oset.mem_bool_unfold, Bool.orb_false_r.
  apply refl_equal.
- intros f l IHl; rewrite Fset.equal_spec; intro x.
  rewrite variables_t_unfold, Fset.mem_mk_set.
  simpl variables_t_list.
  rewrite eq_bool_iff, Fset.mem_Union, Oset.mem_bool_true_iff, in_flat_map; split.
  + intros [s [Hs Hx]].
    rewrite in_map_iff in Hs.
    destruct Hs as [ts [Hs Hts]].
    exists ts; split; [assumption | ].
    assert (IH := IHl _ Hts).
    rewrite Fset.equal_spec in IH.
    subst s; rewrite IH, Fset.mem_mk_set, Oset.mem_bool_true_iff in Hx.
    exact Hx.
  + intros [s [Hs Hx]].
    exists (variables_t s); split.
    * rewrite in_map_iff; exists s; split; trivial.
    * assert (IH := IHl _ Hs).
      rewrite Fset.equal_spec in IH.
      rewrite IH, Fset.mem_mk_set, Oset.mem_bool_true_iff.
      exact Hx.
Qed.

Hypothesis OF : Oset.Rcd symbol.

Fixpoint term_compare (t1 t2 : term) : comparison :=
  match t1, t2 with
    | Var v1, Var v2 => Oset.compare OX v1 v2
    | Var _, Term _ _ => Lt
    | Term _ _, Var _ => Gt
    | Term f1 l1, Term f2 l2 =>
      compareAB (Oset.compare OF) (comparelA term_compare) (f1,l1) (f2, l2)
  end.

Lemma term_eq_bool_ok :
  forall t1 t2, match term_compare t1 t2 with
             | Eq => t1 = t2
             | _ => t1 <> t2
           end.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2].
  + simpl.
    generalize (Oset.eq_bool_ok OX v1 v2).
    case (Oset.compare OX v1 v2).
    * apply f_equal.
    * intros Hv H; apply Hv; injection H; exact (fun h => h).
    * intros Hv H; apply Hv; injection H; exact (fun h => h).
  + simpl; discriminate.
- intros f1 l1 IH [v2 | f2 l2]; [simpl; discriminate | ].
  simpl.
  generalize (Oset.eq_bool_ok OF f1 f2).
  case (Oset.compare OF f1 f2).
  + intros Hf; subst f2.
    assert (Aux : match comparelA term_compare l1 l2 with
                    | Eq => l1 = l2
                    | _ => l1 <> l2
                  end).
    {
      refine (comparelA_eq_bool_ok _ _ _ _).
      do 4 intro; apply IH; assumption.
    }
    revert Aux.
    case (comparelA term_compare l1 l2).
    * apply f_equal.
    * intros Hl H; apply Hl; injection H; exact (fun h => h).
    * intros Hl H; apply Hl; injection H; exact (fun h => h).
  + intros Hf H; apply Hf; injection H; exact (fun _ h => h).
  + intros Hf H; apply Hf; injection H; exact (fun _ h => h).
Qed.

Lemma term_compare_lt_trans :
  forall t1 t2 t3, term_compare t1 t2 = Lt -> term_compare t2 t3 = Lt -> term_compare t1 t3 = Lt.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial)).
  apply Oset.compare_lt_trans.
- intros f1 l1 IH [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial)).
  case_eq (Oset.compare OF f1 f2); intro Hf12.
  + generalize (Oset.eq_bool_ok OF f1 f2); rewrite Hf12; intro; subst f2; clear Hf12.
    intros Hl1.
    case (Oset.compare OF f1 f3); trivial.
    revert Hl1; refine (comparelA_lt_trans _ _ _ _ _ _ _ _).
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a2 a3); rewrite Ha23; intro; subst a2.
      assumption.
    * do 6 intro; apply IH; trivial.
  + intros _; case_eq (Oset.compare OF f2 f3); intro Hf23.
    * rewrite (Oset.compare_lt_eq_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * rewrite (Oset.compare_lt_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * intro Abs; discriminate Abs.
  + intro Abs; discriminate Abs.
Qed.


Lemma term_compare_lt_gt :
  forall t1 t2, term_compare t1 t2 = CompOpp (term_compare t2 t1).
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2]; simpl; [ | trivial].
  apply Oset.compare_lt_gt.
- intros f1 l1 IH [v2 | f2 l2]; simpl; [trivial | ].
  rewrite (Oset.compare_lt_gt OF f2 f1).
  case (Oset.compare OF f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OT : Oset.Rcd term.
split with term_compare.
- apply term_eq_bool_ok.
- apply term_compare_lt_trans.
- apply term_compare_lt_gt.
Defined.

End Sec.

Arguments Var {dom} {symbol} x.
