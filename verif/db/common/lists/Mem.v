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

Require Import Bool List SetoidList.
Require Import ListFacts.

Section Sec.
Hypothesis A : Type.
Hypothesis eq_bool : A -> A -> bool.

Section Mem.

Fixpoint mem_bool (a : A) (l : list A) : bool :=
  match l with
  | nil => false
  | b :: k => eq_bool a b || mem_bool a k
  end.

Lemma mem_bool_unfold :
  forall a l, 
    mem_bool a l = match l with
                     | nil => false
                     | b :: k => eq_bool a b || mem_bool a k
                   end.
Proof.
intros a l; case l; intros; apply refl_equal.
Qed.

Lemma mem_bool_true_iff : 
  forall a l, mem_bool a l = true <-> (exists a', eq_bool a a' = true /\ In a' l).
Proof.
fix h 2.
intros a l; case l; clear l.
- split; intro H.
  + discriminate H.
  + destruct H as [a' [_ H]]; contradiction H.
- intros a1 l; rewrite mem_bool_unfold, Bool.orb_true_iff, h.
  split.
  + intros [Ha1 | [a' [Ha' H]]].
    * exists a1; split; [ | left]; trivial.
    * exists a'; split; [ | right]; trivial.
  + intros [a' [Ha' H]].
    simpl in H; destruct H as [H | H].
    * subst a'; left; trivial.
    * right; exists a'; split; trivial.
Qed.

Lemma mem_bool_InA :
  forall a l, mem_bool a l = true <-> InA (fun x y => eq_bool x y = true) a l.
Proof.
intros a l; induction l as [ | a1 l1]; simpl; split.
- intro Abs; discriminate Abs.
- intro Abs; inversion Abs.
- rewrite Bool.orb_true_iff; intros [H | H].
  + constructor 1; assumption.
  + constructor 2; apply IHl1; assumption.
- intro H; inversion H; clear H; subst.
  + rewrite Bool.orb_true_iff; left; assumption.
  + rewrite Bool.orb_true_iff; right; rewrite IHl1; assumption.
Qed.

Lemma mem_bool_app : forall a l1 l2, mem_bool a (l1 ++ l2) = mem_bool a l1 || mem_bool a l2.
Proof.
intro a; fix h 1; intro l1; case l1; clear l1.
intro l2; apply refl_equal.
intros a1 l1 l2; simpl; rewrite (h l1 l2), Bool.orb_assoc; apply refl_equal.
Qed.

Lemma mem_bool_flat_map :
forall (B : Type) a (f : B -> list A) (l : list B), 
  mem_bool a (flat_map f l) = existsb (fun b => mem_bool a (f b)) l.
Proof.
fix h 4.
intros B a f l; case l; clear l.
- apply refl_equal.
- intros b1 l; simpl; rewrite mem_bool_app, h.
  apply refl_equal.
Qed.

End Mem.

Section Remove.

Fixpoint remove_bool (a : A) (l : list A) : option (list A) :=
  match l with
    | nil => None
    | a1 :: l =>
      if eq_bool a a1 
      then Some l
      else 
        match remove_bool a l with
          | Some k => Some (a1 :: k)
          | None => None
        end
  end.

Lemma remove_bool_some_is_sound :
  forall a l l',
    remove_bool a l = Some l' ->
    {al1l2 : (A * list A * list A) | 
     match al1l2 with
       | (a', l1, l2) => eq_bool a a' = true /\ l = l1 ++ a' :: l2 /\ l' = l1 ++ l2
     end}.
Proof.
intros a.
fix h 1.
intros l l'; case l; clear l.
- intro H; simpl in H; discriminate H.
- intros a1 l; simpl.
  case_eq (eq_bool a a1); intro Ha.
  + intro H; injection H; clear H; intro; subst l'.
    exists (a1, nil, l); split; [ | split]; trivial.
  + case_eq (remove_bool a l).
    * intros k H K; injection K; clear K; intro; subst l'.
      case (h _ _ H).
      intros [[b l1] l2] [H1 [H2 H3]].
      subst l k.
      exists (b, (a1 :: l1), l2); split; [ | split]; trivial.
    * intros _ Abs; discriminate Abs.
Qed.

Lemma remove_bool_none_is_sound :
  forall a l,
    remove_bool a l = None ->
    forall b, In b l -> eq_bool a b = false.
Proof.
intros a.
fix h 1.
intros l; case l; clear l.
- intros _ b H; contradiction H.
- intros a1 l; simpl.
  case_eq (eq_bool a a1); intro Ha.
  + intro Abs; discriminate Abs.
  + case_eq (remove_bool a l).
    * intros k _ Abs; discriminate Abs.
    * {
        intros K _ b [Hb | Hb].
        - subst b; assumption.
        - apply (h _ K _ Hb).
      }
Qed.

End Remove.

Section AllDiff.

Fixpoint all_diff_bool l :=
  match l with
  | nil | _ :: nil => true
  | a1 :: l => negb (mem_bool a1 l) && (all_diff_bool l)
  end.

Lemma all_diff_bool_unfold : 
  forall a l, all_diff_bool (a :: l) = negb (mem_bool a l) && (all_diff_bool l).
Proof.
intros a l; case l; clear l; intros; trivial.
Qed.

Lemma all_diff_bool_app1 :
 forall l1 l2, all_diff_bool (l1 ++ l2) = true -> all_diff_bool l1 = true.
Proof.
fix h 1.
intros l1; case l1; clear l1; [ | intros x1 l1]; intros l2 H.
- apply refl_equal.
- simpl app in H; rewrite all_diff_bool_unfold, Bool.andb_true_iff in H.
  rewrite all_diff_bool_unfold, (h _ _ (proj2 H)).
  destruct H as [H _].
  rewrite mem_bool_app, negb_orb, Bool.andb_true_iff in H.
  rewrite (proj1 H).
  apply refl_equal.
Qed.

Lemma all_diff_bool_app2 :
 forall l1 l2, all_diff_bool (l1 ++ l2) = true -> all_diff_bool l2 = true.
Proof.
fix h 1.
intros l1; case l1; clear l1; [ | intros x1 l1]; intros l2 H.
- exact H.
- simpl app in H; rewrite all_diff_bool_unfold, Bool.andb_true_iff in H.
  apply (h _ _ (proj2 H)).
Qed.

End AllDiff.

Section Find.

Hypothesis B : Type.

Fixpoint find a (l : list (A * B)) :=
  match l with
    | nil => None
    | (a1, b1) :: l => if eq_bool a a1 then Some b1 else find a l
  end.

Lemma find_unfold :
  forall a l,
    find a l =  match l with
                  | nil => None
                  | (a1, b1) :: l => if eq_bool a a1 then Some b1 else find a l
                end.
Proof.
intros a l; case l; intros; apply refl_equal.
Qed.

Lemma find_app :
  forall a l1 l2,
    find a (l1 ++ l2) = match find a l1 with
                          | Some b => Some b
                          | None => find a l2
                        end.
Proof.
intros a; fix h 1.
intro l1; case l1; clear l1; [ | intros [a1 b1] l1]; intro l2.
- apply refl_equal.
- simpl app; rewrite 2 (find_unfold _ (_ :: _)).
  case (eq_bool a a1); [apply refl_equal | ].
  apply h.
Qed.
  
Lemma find_some :
  forall a l b, find a l = Some b -> 
                {a' : A | eq_bool a a' = true /\ In (a', b) l}.
Proof.
fix h 2.
intros a l b; case l; clear l.
- intro H; discriminate H.
- intros [a1 b1] l; rewrite find_unfold.
  case_eq (eq_bool a a1).
  + intros H K; exists a1; split; [assumption | ].
    injection K; clear K; intro K; left; apply f_equal; assumption.
  + intros _ K.
    apply h in K.
    destruct K as [a' [H1 H2]].
    exists a'; split; [assumption | ].
    right; assumption.
Qed.

Lemma find_none :
  forall a l, find a l = None ->
              forall a', eq_bool a a' = true -> forall b, In (a', b) l -> False.
Proof.
fix h 2.
intros a l; case l; clear l.
- intros _ a' _ b H; contradiction H.
- intros [a1 b1] l; rewrite find_unfold.
  case_eq (eq_bool a a1).
  + intros _ H; discriminate H.
  + intros Ha H a' Ha' b Hb.
    simpl in Hb; destruct Hb as [Hb | Hb].
    * injection Hb; clear Hb; do 2 intro; subst a1 b1.
      rewrite Ha' in Ha; discriminate Ha.
    * apply (h _ _ H _ Ha' _ Hb).
Qed.

End Find.

End Sec.

