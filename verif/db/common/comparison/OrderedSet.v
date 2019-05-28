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

Require Import Bool List String Ascii Sorted SetoidList.

Require Import BasicFacts ListFacts Mem NArith.

Lemma compare_eq_true :
  forall c, match c with Eq => true | _ => false end = true <-> c = Eq.
Proof.
intro c; case c; split; intro H.
- apply refl_equal.
- apply refl_equal.
- discriminate H.
- discriminate H.
- discriminate H.
- discriminate H.
Qed.

Lemma match_compare_eq :
  forall (A : Type) (a1 a2 a3 a1' a2' a3' : A) c1 c2, 
    a1 = a1' -> a2 = a2' -> a3 = a3' -> c1 = c2 ->
    match c1 with 
      | Eq => a1
      | Lt => a2
      | Gt => a3
    end =  
    match c2 with 
      | Eq => a1'
      | Lt => a2'
      | Gt => a3'
    end.
Proof.
intros; subst; trivial.
Qed.

Section BuildList.
Require Import List.

Hypothesis A : Type.
Hypothesis compareA : A -> A -> comparison.

(** How to build a lexicographic comparison function [comparelA] over the lists [(list A)] from a comparison function [compareA] over [A]. *)
Fixpoint comparelA l1 l2 :=
  match l1, l2 with
  | nil, nil => Eq
  | nil, _ :: _ => Lt
  | _ :: _, nil => Gt
  | a1 :: l1, a2 :: l2 => 
      match compareA a1 a2 with
      | Eq => comparelA l1 l2
      | Lt => Lt
      | Gt => Gt
      end
    end.

Lemma comparelA_unfold :
  forall l1 l2, comparelA l1 l2 =
  match l1, l2 with
  | nil, nil => Eq
  | nil, _ :: _ => Lt
  | _ :: _, nil => Gt
  | a1 :: l1, a2 :: l2 => 
      match compareA a1 a2 with
      | Eq => comparelA l1 l2
      | Lt => Lt
      | Gt => Gt
      end
    end.
Proof.
intros l1 l2; case l1; case l2; intros; apply refl_equal.
Qed.

Lemma comparelA_rev_eq :
  forall l1 l2, comparelA l1 l2 = Eq -> comparelA (rev l1) (rev l2) = Eq.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
- trivial.
- simpl in H.
  case_eq (compareA a1 a2); intro Ha; rewrite Ha in H; try discriminate H.
  assert (IH := IHl1 _ H).
  simpl.
  set (rl1 := rev l1) in *; clearbody rl1.
  set (rl2 := rev l2) in *; clearbody rl2.
  clear IHl1.
  revert rl2 IH; induction rl1 as [ | b1 rl1]; intros [ | b2 rl2] IH; simpl; try discriminate IH.
  + rewrite Ha; trivial.
  + simpl in IH.
    case_eq (compareA b1 b2); intro Hb; rewrite Hb in IH; try discriminate IH.
    apply IHrl1; assumption.
Qed.

Lemma comparelA_eq_bool_ok :
  forall l1 l2, (forall a1 a2, In a1 l1 -> In a2 l2 -> 
                               match compareA a1 a2 with
                                 | Eq => a1 = a2
                                 | _ => a1 <> a2
                               end) ->
   match comparelA l1 l2 with
   | Eq => l1 = l2
   | Lt => l1 <> l2
   | Gt => l1 <> l2
   end.
- intros l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] Hl; simpl.
  + apply refl_equal.
  + discriminate.
  + discriminate.
  + case_eq (compareA a1 a2); intro Ha.
    * generalize (Hl a1 a2 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))); 
      rewrite Ha; intro; subst a2.
      {
        generalize (IHl1 l2 (fun x y hx hy =>  Hl x y (or_intror _ hx) (or_intror _ hy))).
        case (comparelA l1 l2).
        - apply f_equal.
        - intros Kl H; apply Kl.
          injection H; exact (fun h => h).
        - intros Kl H; apply Kl.
          injection H; exact (fun h => h).
      }
    * generalize (Hl a1 a2 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))); 
      rewrite Ha; clear Ha; intro Ha.
      intro Kl; apply Ha.
      injection Kl; exact (fun _ h => h).
    * generalize (Hl a1 a2 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))); 
      rewrite Ha; clear Ha; intro Ha.
      intro Kl; apply Ha.
      injection Kl; exact (fun _ h => h).
Qed.

Lemma comparelA_eq_refl : 
  forall l, (forall a, In a l -> compareA a a = Eq) -> comparelA l l = Eq.
Proof.
intro l; induction l as [ | a l]; intros H; simpl.
apply refl_equal.
rewrite (H a (or_introl _ (refl_equal _))).
apply (IHl (fun s h => H s (or_intror _  h))).
Qed.

Lemma comparelA_eq_refl_alt : 
  forall l1, (forall a, In a l1 -> compareA a a = Eq) -> 
             forall l2, l1 = l2 -> comparelA l1 l2 = Eq.
Proof.
intros l1 Hl1 l2 H; subst l2; apply comparelA_eq_refl; assumption.
Qed.

Lemma comparelA_eq_app :
  forall l1 l1' l2 l2', 
    comparelA l1 l2 = Eq -> comparelA l1' l2' = Eq -> comparelA (l1 ++ l1') (l2 ++ l2') = Eq.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros l1' [ | a2 l2] l2' H H'; simpl in H; 
simpl; trivial; try discriminate.
revert H; case (compareA a1 a2); try discriminate.
intro; apply IHl1; trivial.
Qed.

Lemma comparelA_eq_filter :
  forall l1 l2 f, 
    (forall a1 a2, In a1 l1 -> compareA a1 a2 = Eq -> f a1 = f a2) -> 
    comparelA l1 l2 = Eq -> comparelA (filter f l1) (filter f l2) = Eq.
Proof.
intros l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] f Hf Hl;
  try discriminate Hl; trivial.
simpl in Hl.
case_eq (compareA a1 a2); intro Ha; rewrite Ha in Hl; try discriminate Hl.
simpl.
rewrite <- (Hf a1 a2 (or_introl _ (refl_equal _)) Ha).
case (f a1).
- simpl; rewrite Ha; apply IHl1; trivial.
  do 3 intro; apply Hf; right; assumption.
- apply IHl1; trivial.
  do 3 intro; apply Hf; right; assumption.
Qed.

Lemma comparelA_eq_trans : 
  forall l1 l2 l3, 
  (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
  comparelA l1 l2 = Eq -> comparelA l2 l3 = Eq -> comparelA l1 l3 = Eq.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] [ | a3 l3] H; simpl; trivial.
intro Abs; discriminate Abs.
generalize (H a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))).
case (compareA a1 a2).
case (compareA a2 a3).
intro Ha13; rewrite Ha13; trivial.
apply IHl1; do 6 intro; apply H; right; assumption.
intros _ _ Abs; discriminate Abs.
intros _ _ Abs; discriminate Abs.
intros _ Abs; discriminate Abs.
intros _ Abs; discriminate Abs.
Qed.

Lemma comparelA_le_lt_trans :
  forall l1 l2 l3, 
  (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
 (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
  comparelA l1 l2 = Eq -> comparelA l2 l3 = Lt -> comparelA l1 l3 = Lt.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] [ | a3 l3] H1 H2; simpl; trivial; try discriminate.
generalize (H1 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)))
(H2 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))).
case (compareA a1 a2).
case (compareA a2 a3).
intros Ha13 _; rewrite Ha13; trivial.
apply IHl1.
do 6 intro; apply H1; right; assumption.
do 6 intro; apply H2; right; assumption.
intros _ Ha13; rewrite Ha13; trivial.
intros _ _ _ Abs; discriminate Abs.
intros _ _ Abs; discriminate Abs.
intros _ _ Abs; discriminate Abs.
Qed.

Lemma comparelA_lt_le_trans :
  forall l1 l2 l3, 
  (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
 (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) ->
  comparelA l1 l2 = Lt -> comparelA l2 l3 = Eq -> comparelA l1 l3 = Lt.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] [ | a3 l3] H1 H2; simpl; trivial; try discriminate.
generalize (H1 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)))
(H2 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))).
case (compareA a1 a2).
case (compareA a2 a3).
intros Ha13 _; rewrite Ha13; trivial.
apply IHl1.
do 6 intro; apply H1; right; assumption.
do 6 intro; apply H2; right; assumption.
intros _ _ _ Abs; discriminate Abs.
intros _ _ _ Abs; discriminate Abs.
case (compareA a2 a3).
intros _ Ha13; rewrite Ha13; trivial.
intros _ _ _ Abs; discriminate Abs.
intros _ _ _ Abs; discriminate Abs.
intros _ _ Abs; discriminate Abs.
Qed.

Lemma comparelA_lt_trans :
  forall l1 l2 l3, 
  (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
  (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
 (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) ->
 (forall a1 a2 a3, In a1 l1 -> In a2 l2 -> In a3 l3 ->   
     compareA a1 a2 = Lt -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
  comparelA l1 l2 = Lt -> comparelA l2 l3 = Lt -> comparelA l1 l3 = Lt.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] [ | a3 l3] H1 H2 H3 H4; simpl; trivial; try discriminate.
generalize (H1 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)))
(H2 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)))
(H3 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)))
(H4 a1 a2 a3 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))).
case (compareA a1 a2).
case (compareA a2 a3).
intros Ha13 _ _ _; rewrite Ha13; trivial.
apply IHl1.
do 6 intro; apply H1; right; assumption.
do 6 intro; apply H2; right; assumption.
do 6 intro; apply H3; right; assumption.
do 6 intro; apply H4; right; assumption.
intros _ Ha13 _ _; rewrite Ha13; trivial.
intros _ _ _ _ _ Abs; discriminate Abs.
case (compareA a2 a3).
intros _ _ Ha13 _; rewrite Ha13; trivial.
intros _ _ _ Ha13; rewrite Ha13; trivial.
intros _ _ _ _ _ Abs; discriminate Abs.
intros _ _ _ _ Abs; discriminate Abs.
Qed.

Lemma comparelA_lt_gt : 
    forall l1 l2, (forall a1 a2, In a1 l1 -> In a2 l2 ->  compareA a1 a2 = CompOpp (compareA a2 a1)) ->
    comparelA l1 l2 = CompOpp (comparelA l2 l1).
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; simpl; try apply refl_equal.
rewrite (H a1 a2 (or_introl _ (refl_equal _)) (or_introl _ (refl_equal _))).
rewrite (IHl1 l2 (fun a1 a2 h1 h2 => H a1 a2 (or_intror _ h1) (or_intror _ h2))).
case (compareA a2 a1); simpl; apply refl_equal.
Qed.

Lemma comparelA_gt_eq_trans :
  forall l1 l2 l3, 
  (forall a1 a2 a3, In a1 l3 -> In a2 l2 -> In a3 l1 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
 (forall a1 a2 a3, In a1 l3 -> In a2 l2 -> In a3 l1 ->   
     compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
 (forall a1 a2 : A, In a1 l1 -> In a2 l3 -> compareA a1 a2 = CompOpp (compareA a2 a1)) ->
 (forall a1 a2 : A, In a1 l2 -> In a2 l3 -> compareA a1 a2 = CompOpp (compareA a2 a1)) ->
 (forall a1 a2 : A, In a1 l1 -> In a2 l2 -> compareA a1 a2 = CompOpp (compareA a2 a1)) ->
  comparelA l1 l2 = Gt -> comparelA l2 l3 = Eq -> comparelA l1 l3 = Gt.
Proof.
intros l1 l2 l3 H1 H2 H3 H4 H5.
rewrite (comparelA_lt_gt l1 l2), (comparelA_lt_gt l2 l3), (comparelA_lt_gt l1 l3), 3 CompOpp_iff.
- simpl.
  intros K1 K2; revert K2 K1.
  apply comparelA_le_lt_trans.
  + apply H1.
  + apply H2.
- assumption.
- assumption.
- assumption.
Qed.

Lemma comparelA_eq_length_eq :
  forall l1 l2, comparelA l1 l2 = Eq -> length l1 = length l2.
Proof.
intros l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try (trivial || discriminate H).
simpl; apply f_equal; apply IHl1.
simpl in H.
destruct (compareA a1 a2); try (trivial || discriminate H).
Qed.

End BuildList.

Lemma comparelA_comparelA_eq :
  forall (A : Type) (compareA : A -> A -> comparison) l1 l2,
    comparelA (comparelA compareA) l1 l2 = Eq ->
    comparelA compareA (flat_map (fun x : list A => x) l1) (flat_map (fun x : list A => x) l2) = Eq.
Proof.
intros A compareA l1; induction l1 as [ | x1 l1]; intros [ | x2 l2] H; simpl; try discriminate H; trivial.
simpl in H.
case_eq (comparelA compareA x1 x2); intro Hx; rewrite Hx in H; try discriminate H.
apply comparelA_eq_app; [ | apply IHl1]; assumption.
Qed.

Section BuildOption.

Hypothesis A : Type.
Hypothesis compareA : A -> A -> comparison.

Definition option_to_list (o : option A) :=
  match o with
  | Some x => x :: nil
  | None => nil
  end.

Definition compareoA o1 o2 := comparelA compareA (option_to_list o1) (option_to_list o2).

End BuildOption.

(** ** Equivalence *)

(** [compare] is a comparison function, which induces an equivalence relation thanks to [Eq]. This equivalence is compatible with the ordering induced by [Lt]. *)

Module Oeset.
Record Rcd (A : Type) : Type :=
  mk_R 
    {
      compare : A -> A -> comparison;
      compare_eq_trans : 
        forall a1 a2 a3, compare a1 a2 = Eq -> compare a2 a3 = Eq -> compare a1 a3 = Eq;
      compare_eq_lt_trans : 
        forall a1 a2 a3, compare a1 a2 = Eq -> compare a2 a3 = Lt -> compare a1 a3 = Lt;
      compare_lt_eq_trans : 
        forall a1 a2 a3, compare a1 a2 = Lt -> compare a2 a3 = Eq -> compare a1 a3 = Lt;
      compare_lt_trans : 
        forall a1 a2 a3, compare a1 a2 = Lt -> compare a2 a3 = Lt -> compare a1 a3 = Lt;
      compare_lt_gt : forall a1 a2, compare a1 a2 = CompOpp (compare a2 a1)
    }.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Rcd A.

Lemma compare_eq_refl :
  forall a, compare OA a a = Eq.
Proof.
intros a.
generalize (compare_lt_gt OA a a).
case (compare OA a a); try discriminate.
exact (fun _ => refl_equal _).
Qed.

Lemma compare_eq_refl_alt :
  forall a1 a2, a1 = a2 -> compare OA a1 a2 = Eq.
Proof.
intros a1 a2 H; subst a2.
apply compare_eq_refl.
Qed.

Lemma compare_eq_sym :
  forall a b, compare OA a b = Eq -> compare OA b a = Eq.
Proof.
intros a b H.
rewrite compare_lt_gt, H.
apply refl_equal.
Qed.

Lemma compare_eq_gt_trans :
  forall a b c, compare OA a b = Eq -> compare OA b c = Gt -> compare OA a c = Gt.
Proof.
intros a b c H1 H2.
rewrite compare_lt_gt, CompOpp_iff in H2.
rewrite compare_lt_gt, CompOpp_iff.
apply compare_lt_eq_trans with b; [apply H2 | ].
apply compare_eq_sym; assumption.
Qed.

Lemma compare_gt_eq_trans :
  forall a b c, compare OA a b = Gt -> compare OA b c = Eq -> compare OA a c = Gt.
Proof.
intros a b c H1 H2.
rewrite compare_lt_gt, CompOpp_iff in H1.
rewrite compare_lt_gt, CompOpp_iff.
apply compare_eq_lt_trans with b; [ | apply H1].
apply compare_eq_sym; assumption.
Qed. 

Lemma compare_gt_trans :
  forall a b c, compare OA a b = Gt -> compare OA b c = Gt -> compare OA a c = Gt.
Proof.
intros a b c H1 H2.
rewrite compare_lt_gt, CompOpp_iff in H1, H2.
rewrite compare_lt_gt, CompOpp_iff.
apply compare_lt_trans with b; [apply H2 | apply H1].
Qed.

Lemma compare_eq_1 :
  forall a1 a2 b, compare OA a1 a2 = Eq -> compare OA a1 b = compare OA a2 b.
Proof.
intros a1 a2 b Ha.
case_eq (compare OA a2 b); intro Hb.
- apply (compare_eq_trans OA _ _ _ Ha Hb).
- apply (compare_eq_lt_trans OA _ _ _ Ha Hb).
- apply (compare_eq_gt_trans _ _ _ Ha Hb).
Qed.

Lemma compare_eq_2 :
  forall a b1 b2, compare OA b1 b2 = Eq -> compare OA a b1 = compare OA a b2.
Proof.
intros a b1 b2 Hb; apply sym_eq.
case_eq (compare OA a b1); intro Ha.
- apply (compare_eq_trans OA _ _ _ Ha Hb).
- apply (compare_lt_eq_trans OA _ _ _ Ha Hb).
- apply (compare_gt_eq_trans _ _ _ Ha Hb).
Qed.

Definition eq_bool := (fun x y => match compare OA x y with Eq => true | _ => false end).

Lemma eq_bool_true_compare_eq :
  forall x y, eq_bool x y = true <-> compare OA x y = Eq.
Proof.
intros x y; split; unfold eq_bool.
destruct (compare OA x y); trivial; discriminate.
intro H; rewrite H; trivial.
Qed.

Lemma eq_bool_refl :
  forall x, eq_bool x x = true.
Proof.
intro x; unfold eq_bool; rewrite compare_eq_refl; apply refl_equal.
Qed.

Lemma Equivalence :
  RelationClasses.Equivalence (fun x y => eq_bool x y = true).
Proof.
unfold eq_bool; split.
- intro x; rewrite compare_eq_refl; apply refl_equal.
- intros x y H; rewrite compare_eq_true in H.
  rewrite compare_lt_gt, H; apply refl_equal.
- intros x y z; rewrite 3 compare_eq_true; apply compare_eq_trans.
Qed.

Definition mem_bool a l := Mem.mem_bool eq_bool a l.

Lemma mem_bool_unfold : 
  forall a l, 
    mem_bool a l = 
    match l with
      | nil => false
      | a1 :: l => match compare OA a a1 with Eq => true | _ => false end || mem_bool a l
    end.
Proof.
intros a l; case l.
- apply refl_equal.
- clear l; intros a1 l; simpl.
  apply refl_equal.
Qed.

Lemma in_mem_bool :
  forall a l, In a l -> mem_bool a l = true.
Proof.
intros a l H; induction l as [ | a1 l]; simpl in H; [contradiction H |  destruct H as [H | H]].
- subst a1; simpl; unfold eq_bool; rewrite compare_eq_refl; apply refl_equal.
- simpl; rewrite IHl, Bool.orb_true_r; trivial.
Qed.

Lemma mem_bool_eq_1 :
  forall a1 a2 l, compare OA a1 a2 = Eq -> mem_bool a1 l = mem_bool a2 l.
Proof.
fix h 3.
intros a1 a2 l Ha; case l; clear l.
- apply refl_equal.
- intros a l; rewrite (mem_bool_unfold a1), (mem_bool_unfold a2).
  apply f_equal2; [ | apply (h a1 a2 l Ha)].
  case_eq (compare OA a1 a); intro H.
  + assert (K := compare_eq_sym _ _ Ha).
    rewrite (compare_eq_trans _ _ _ _ K H).
    apply refl_equal.
  + assert (K := compare_eq_sym _ _ Ha).
    rewrite (compare_eq_lt_trans _ _ _ _ K H).
    apply refl_equal.
  + rewrite compare_lt_gt.
    rewrite compare_lt_gt, CompOpp_iff in H.
    rewrite (compare_lt_eq_trans _ _ _ _ H Ha).
    apply refl_equal.
Qed.

Lemma mem_bool_eq_2 :
  forall a l1 l2, comparelA (compare OA) l1 l2 = Eq -> mem_bool a l1 = mem_bool a l2.
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
- apply refl_equal.
- simpl in H.
  case_eq (compare OA a1 a2); intro Ha; rewrite Ha in H; try discriminate H.
  simpl; apply f_equal2; [ | apply IHl1; trivial].
  unfold eq_bool.
  case_eq (compare OA a a1); intro Ha1.
  + rewrite (compare_eq_trans _ _ _ _ Ha1 Ha); trivial.
  + rewrite (compare_lt_eq_trans _ _ _ _ Ha1 Ha); trivial.
  + rewrite (compare_gt_eq_trans _ _ _ Ha1 Ha); trivial.
Qed.    

Lemma mem_bool_true_iff : 
  forall a l, mem_bool a l = true <-> (exists a', compare OA a a' = Eq /\ In a' l).
Proof.
intros a l; unfold mem_bool, eq_bool; rewrite Mem.mem_bool_true_iff; 
split; intros [a' [H1 H2]].
- rewrite compare_eq_true in H1.
  exists a'; split; trivial.
- exists a'; rewrite compare_eq_true; split; trivial.
Qed.

Lemma mem_bool_filter :
  forall f l, (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
                  forall x, mem_bool x (filter f l) = andb (f x) (mem_bool x l).
Proof.
intros f l H x; induction l as [ | a1 l]; simpl.
- rewrite Bool.andb_false_r; apply refl_equal.
- case_eq (eq_bool x a1); intro Hx.
  + unfold eq_bool in Hx.
    rewrite compare_eq_true in Hx.
    assert (Kx : f x = f a1).
    {
      apply H; [ | assumption].
      rewrite mem_bool_unfold; rewrite Hx; apply refl_equal.
    }
    rewrite Kx; case_eq (f a1); intro Ha1.
    * rewrite mem_bool_unfold, Hx; apply refl_equal.
    * rewrite IHl, Kx, Ha1; [apply refl_equal | ].
      intros x1 x2 K; apply H.
      rewrite mem_bool_unfold, K, Bool.orb_true_r; apply refl_equal.
  + destruct (f a1); simpl.
    * rewrite Hx, IHl; [apply refl_equal | ].
      intros x1 x2 K; apply H.
      rewrite mem_bool_unfold, K, Bool.orb_true_r; apply refl_equal.
    * apply IHl; intros x1 x2 K; apply H.
      rewrite mem_bool_unfold, K, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma mem_bool_filter_eq_2 :
  forall f1 f2 l, (forall x, mem_bool x l = true -> f1 x = f2 x) ->
                  forall x, mem_bool x (filter f1 l) = mem_bool x (filter f2 l).
Proof.
intros f1 f2 l H x; induction l as [ | a1 l]; [apply refl_equal | simpl].
rewrite (H a1); 
  [ | simpl; rewrite Bool.orb_true_iff; left; 
      unfold eq_bool; rewrite compare_eq_refl; apply refl_equal].
destruct (f2 a1); [simpl; apply f_equal | ];
apply IHl; intros y Hy; apply H; simpl; rewrite Hy; apply Bool.orb_true_r.
Qed.

Lemma mem_bool_app :
forall a l1 l2, mem_bool a (l1 ++ l2) = mem_bool a l1 || mem_bool a l2.
Proof.
intros; apply Mem.mem_bool_app.
Qed.

Lemma mem_bool_rev :
  forall a l,  mem_bool a (rev l) = mem_bool a l.
Proof.
intros a l; induction l as [ | a1 l]; simpl; [apply refl_equal | ].
rewrite mem_bool_app, IHl, Bool.orb_comm; apply f_equal2; [ | apply refl_equal].
rewrite (mem_bool_unfold _ (_ :: _)), Bool.orb_false_r; apply refl_equal.
Qed.

Definition find (B : Type) a (l : list (A * B)) := Mem.find eq_bool a l.

Open Scope N.

Fixpoint nb_occ a l : N :=
  match l with
    | nil => 0
    | a1 :: l => (match compare OA a a1 with Eq => 1 | _ => 0 end) + nb_occ a l
  end.

Lemma nb_occ_unfold :
  forall a l, nb_occ a l = 
              match l with
                | nil => 0
                | a1 :: l => (match compare OA a a1 with Eq => 1 | _ => 0 end) + nb_occ a l
              end.                                                                                        
Proof.
intros a l; destruct l; apply refl_equal.
Qed.

Lemma nb_occ_non_neg :
  forall a l, 0 <= nb_occ a l.
Proof.
intros a l; induction l as [ | a1 l]; simpl.
- discriminate.
- apply N.add_nonneg_nonneg; [ | assumption].
  case (compare OA a a1); discriminate.
Qed.

Lemma nb_occ_diff_0_pos : forall a l, nb_occ a l <> 0 <-> 0 < nb_occ a l.
Proof.
intros a l; split; intro H.
- assert (K := nb_occ_non_neg a l).
  destruct (nb_occ a l).
  + apply False_rec; apply H; apply refl_equal.
  + apply refl_equal.
-  destruct (nb_occ a l).
   + discriminate H.
   + discriminate.
Qed.

Lemma nb_occ_id :
  forall l f, (forall x, mem_bool x l = true -> compare OA (f x) x = Eq) ->
                forall x, nb_occ x (map f l) = nb_occ x l.
Proof.
intro l; induction l as [ | a1 l]; intros f H x; simpl; [apply refl_equal | ].
apply f_equal2.
- assert (Ha1 : compare OA (f a1) a1 = Eq).
  {
    apply H; simpl; unfold eq_bool; rewrite compare_eq_refl.
    apply refl_equal.
  }
  rewrite compare_lt_gt, CompOpp_iff in Ha1.
  case_eq (compare OA x a1); intro H1.
  + rewrite (compare_eq_trans _ _ _ _ H1 Ha1); apply refl_equal.
  + rewrite (compare_lt_eq_trans _ _ _ _ H1 Ha1); apply refl_equal.
  + rewrite (compare_gt_eq_trans _ _ _ H1 Ha1); apply refl_equal.
- apply IHl; intros a Ha; apply H; simpl; rewrite Ha, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma mem_bool_id :
  forall l f, (forall x, mem_bool x l = true -> compare OA (f x) x = Eq) ->
                forall x, mem_bool x (map f l) = mem_bool x l.
Proof.
intro l; induction l as [ | a1 l]; intros f H x; simpl; [apply refl_equal | ].
apply f_equal2.
- assert (Ha1 : compare OA (f a1) a1 = Eq).
  {
    apply H; simpl; unfold eq_bool; rewrite compare_eq_refl.
    apply refl_equal.
  }
  rewrite compare_lt_gt, CompOpp_iff in Ha1.
  unfold eq_bool; case_eq (compare OA x a1); intro H1.
  + rewrite (compare_eq_trans _ _ _ _ H1 Ha1); apply refl_equal.
  + rewrite (compare_lt_eq_trans _ _ _ _ H1 Ha1); apply refl_equal.
  + rewrite (compare_gt_eq_trans _ _ _ H1 Ha1); apply refl_equal.
- apply IHl; intros a Ha; apply H; simpl; rewrite Ha, Bool.orb_true_r; apply refl_equal.
Qed.
  
Lemma nb_occ_eq_1 :
  forall a1 a2 l, compare OA a1 a2 = Eq -> nb_occ a1 l = nb_occ a2 l.
Proof.
intros a1 a2 l Ha; induction l as [ | a l]; [apply refl_equal | ].
rewrite 2 (nb_occ_unfold _ (a :: l)); apply f_equal2; [ | apply IHl].
case_eq (compare OA a2 a); intro Ka.
- rewrite (compare_eq_trans _ _ _ _ Ha Ka); apply refl_equal.
- rewrite (compare_eq_lt_trans _ _ _ _ Ha Ka); apply refl_equal.
- rewrite (compare_eq_gt_trans _ _ _ Ha Ka); apply refl_equal.
Qed.

Lemma nb_occ_eq_2 :
  forall a l1 l2, comparelA (compare OA) l1 l2 = Eq -> nb_occ a l1 = nb_occ a l2.
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
- apply refl_equal.
- simpl in H.
  case_eq (compare OA a1 a2); intro Ha; rewrite Ha in H; try discriminate H.
  simpl; apply f_equal2; [ | apply IHl1; trivial].
  rewrite (compare_eq_2 _ _ _ Ha); apply refl_equal.
Qed.

Lemma not_mem_nb_occ : forall a l, mem_bool a l = false -> nb_occ a l = 0.
Proof.
intros a l; induction l as [ | a1 l]; intro H; [apply refl_equal | ].
rewrite mem_bool_unfold, Bool.orb_false_iff in H; destruct H as [H1 H2].
rewrite nb_occ_unfold, (IHl H2).
case_eq (compare OA a a1); intro Ha; rewrite Ha in H1; (trivial || discriminate H1).
Qed.

Lemma mem_nb_occ : forall a l, mem_bool a l = true -> nb_occ a l <> 0.
Proof.
intros a l; induction l as [ | a1 l]; intro H; [discriminate | ].
rewrite mem_bool_unfold, Bool.orb_true_iff in H; destruct H as [H1 | H2].
- rewrite compare_eq_true in H1.
  rewrite nb_occ_unfold, H1; destruct (nb_occ a l); discriminate.
- rewrite nb_occ_unfold; generalize (IHl H2).
  case_eq (compare OA a a1); trivial.
  intros _; destruct (nb_occ a l); simpl; trivial.
  + intro; discriminate.
  + intros _; destruct p; discriminate.
Qed.

Lemma mem_nb_occ_pos : forall a l, mem_bool a l = true -> nb_occ a l > 0.
Proof.
intros a l Ha.
assert (Ka := mem_nb_occ a l Ha).
case_eq (nb_occ a l).
- intro H; rewrite H in Ka; apply False_rec; apply Ka; apply refl_equal.
- intros p _; apply refl_equal.
Qed.

Lemma nb_occ_mem : forall a l, nb_occ a l <> 0 -> mem_bool a l = true.
Proof.
intros a l H; generalize (not_mem_nb_occ a l).
case (mem_bool a l); [intros _; apply refl_equal | ].
intro K; rewrite (K (refl_equal _)) in H.
apply False_rec; apply H; apply refl_equal.
Qed.

Lemma nb_occ_not_mem : forall a l, nb_occ a l = 0 -> mem_bool a l = false.
Proof.
intros a l H; generalize (mem_nb_occ a l).
case (mem_bool a l); [ | intros _; apply refl_equal].
intro K; rewrite H in K; apply False_rec; apply (K (refl_equal _)).
apply refl_equal.
Qed.

Lemma In_nb_occ : forall a l, In a l -> nb_occ a l <> 0.
Proof.
intros a l H; apply mem_nb_occ.
rewrite mem_bool_true_iff.
exists a; split; [apply compare_eq_refl | assumption].
Qed.

Lemma nb_occ_list_size :
  forall a l, nb_occ a l = 
              N.of_nat (list_size 
                          (fun x => match compare OA a x with Eq => 1%nat | _ => 0%nat end) l).
Proof.
intros a l; induction l as [ | a1 l]; simpl; trivial.
rewrite Nat2N.inj_add; apply f_equal2; [ | apply IHl].
case (compare OA a a1); apply refl_equal.
Qed.

Lemma nb_occ_app :
  forall a l1 l2, nb_occ a (l1 ++ l2) = nb_occ a l1 + nb_occ a l2.
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros l2; simpl; [trivial | ].
rewrite IHl1, N.add_assoc; apply refl_equal.
Qed.

Lemma mem_filter :
  forall (f : A -> bool) l, 
    (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, mem_bool x (filter f l) = if f x then mem_bool x l else false.
Proof.
intros f l Hl x; induction l as [ | a1 l]; [destruct (f x); apply refl_equal | simpl].
unfold eq_bool.
case_eq (compare OA x a1); intro Hx.
- assert (Kx : f x = f a1).
  {
    apply Hl; [ | assumption].
    simpl; unfold eq_bool; rewrite Hx; apply refl_equal.
  }    
  rewrite Kx; case_eq (f a1); intro Ha1.
  + rewrite mem_bool_unfold, Hx; apply f_equal.
    rewrite IHl, Kx, Ha1; [apply refl_equal | ].
    intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
  + rewrite IHl, Kx, Ha1; [apply refl_equal | ].
    intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
- simpl; rewrite <- IHl.
  + destruct (f a1); simpl; try rewrite Hx; trivial.
    unfold eq_bool; rewrite Hx; apply refl_equal.
  + intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
- simpl; rewrite <- IHl.
  + destruct (f a1); simpl; try rewrite Hx; trivial.
    unfold eq_bool; rewrite Hx; apply refl_equal.
  + intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
Qed.

Lemma nb_occ_filter :
  forall (f : A -> bool) l, 
    (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, nb_occ x (filter f l) = if f x then nb_occ x l else 0%N.
Proof.
intros f l Hl x; induction l as [ | a1 l]; [destruct (f x); apply refl_equal | simpl].
case_eq (compare OA x a1); intro Hx.
- assert (Kx : f x = f a1).
  {
    apply Hl; [ | assumption].
    simpl; unfold eq_bool; rewrite Hx; apply refl_equal.
  }    
  rewrite Kx; case_eq (f a1); intro Ha1.
  + rewrite nb_occ_unfold, Hx; apply f_equal.
    rewrite IHl, Kx, Ha1; [apply refl_equal | ].
    intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
  + rewrite IHl, Kx, Ha1; [apply refl_equal | ].
    intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
- simpl; rewrite <- IHl.
  + destruct (f a1); simpl; try rewrite Hx; trivial.
  + intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
- simpl; rewrite <- IHl.
  + destruct (f a1); simpl; try rewrite Hx; trivial.
  + intros y1 y2 Hy; apply Hl; simpl.
    rewrite Hy; apply Bool.orb_true_r.
Qed.

Lemma nb_occ_filter_alt :
  forall (f : A -> bool) l, 
    (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, nb_occ x (filter f l) = (nb_occ x l) * (if f x then 1 else 0)%N.
Proof.
intros f l Hl x.
rewrite (nb_occ_filter _ _ Hl).
case (f x).
- rewrite N.mul_1_r; apply refl_equal.
- rewrite N.mul_0_r; apply refl_equal.
Qed.

Lemma nb_occ_filter_eq :
  forall f1 f2 s1 s2, 
    (forall x, nb_occ x s1 = nb_occ x s2) ->
    (forall x1 x2, nb_occ x1 s1 >= 1 -> compare OA x1 x2 = Eq -> f1 x1 = f2 x2) -> 
    forall x, nb_occ x (filter f1 s1) = nb_occ x (filter f2 s2).
Proof.
intros f1 f2 s1 s2 Hs Ks t.
rewrite 2 nb_occ_filter, <- Hs.
- case_eq (nb_occ t s1); [intro Ht | ].
  + case (f1 t); case (f2 t); trivial.
  + intros p Hp; apply if_eq; trivial.
    apply Ks.
    * rewrite Hp; destruct p; discriminate.
    * apply compare_eq_refl.
- intros e1 e2 He1 He.
  assert (Ke1 := mem_nb_occ _ _ He1).
  rewrite <- Hs in Ke1.
  case_eq (nb_occ e1 s1); [intro Je1 | intros p Hp].
  + rewrite Je1 in Ke1; apply False_rec; apply Ke1; apply refl_equal.
  + rewrite <- (Ks e1 e2).
    * apply sym_eq; apply Ks; [ | apply compare_eq_refl].
      rewrite Hp; destruct p; discriminate.
    * rewrite Hp; destruct p; discriminate.
    *  assumption.
- intros e1 e2 He1 He.
  assert (Ke1 := mem_nb_occ _ _ He1).
  case_eq (nb_occ e1 s1); [intro Je1 | intros p Hp].
  + rewrite Je1 in Ke1; apply False_rec; apply Ke1; apply refl_equal.
  + rewrite (Ks e1 e2).
    * apply sym_eq; apply Ks; [ | apply compare_eq_refl].
      rewrite <- (nb_occ_eq_1 _ _ _ He), Hp; destruct p; discriminate.
    * rewrite Hp; destruct p; discriminate.
    *  assumption.
Qed.

Lemma nb_occ_partition_1 :
  forall (f : A -> bool) l, 
    (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, nb_occ x (fst (partition f l)) = if f x then nb_occ x l else 0%N.
Proof.
intros f l Hf x; induction l as [ | a1 l]; [destruct (f x); apply refl_equal | ].
assert (IH : nb_occ x (fst (partition f l)) = (if f x then nb_occ x l else 0)).
{
  apply IHl.
  do 3 intro; apply Hf; simpl.
  rewrite Bool.orb_true_iff; right; assumption.
}
simpl.
destruct (partition f l) as [l1 l2]; simpl in IH; simpl.
case_eq (f a1); intro Ha1; simpl.
- case_eq (compare OA x a1); intro Hx.
  + rewrite IH, (Hf x a1), Ha1; trivial.
    rewrite mem_bool_unfold, Hx; apply refl_equal.
  + rewrite IH; apply refl_equal.
  + rewrite IH; apply refl_equal.
- rewrite IH; case_eq (compare OA x a1); intro Hx.
  + rewrite (Hf x a1), Ha1; trivial.
    rewrite mem_bool_unfold, Hx; apply refl_equal.
  + apply refl_equal.
  + apply refl_equal.
Qed.

Lemma nb_occ_partition_2 :
  forall (f : A -> bool) l, 
    (forall x1 x2, mem_bool x1 l = true -> compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, nb_occ x (snd (partition f l)) = if f x then 0%N else nb_occ x l.
Proof.
intros f l Hf x; induction l as [ | a1 l]; [destruct (f x); apply refl_equal | ].
assert (IH : nb_occ x (snd (partition f l)) = (if f x then 0 else nb_occ x l)).
{
  apply IHl.
  do 3 intro; apply Hf; simpl.
  rewrite Bool.orb_true_iff; right; assumption.
}
simpl.
destruct (partition f l) as [l1 l2]; simpl in IH; simpl.
case_eq (f a1); intro Ha1; simpl.
- case_eq (compare OA x a1); intro Hx.
  + rewrite IH, (Hf x a1), Ha1; trivial.
    rewrite mem_bool_unfold, Hx; apply refl_equal.
  + rewrite IH; apply refl_equal.
  + rewrite IH; apply refl_equal.
- rewrite IH; case_eq (compare OA x a1); intro Hx.
  + rewrite (Hf x a1), Ha1; trivial.
    rewrite mem_bool_unfold, Hx; apply refl_equal.
  + apply refl_equal.
  + apply refl_equal.
Qed.

Close Scope N.

End Sec.

Lemma mem_bool_flat_map :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B)  b (f : A -> list B) l, 
    mem_bool OB b (flat_map f l) = existsb (fun x => mem_bool OB b (f x)) l.
Proof.
intros A B OA OB b f.
fix h 1.
intro l; case l; clear l.
- apply refl_equal.
- intros a l; simpl.
  rewrite mem_bool_app; apply f_equal.
  apply mem_bool_flat_map.
Qed.

Lemma nb_occ_inj :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) f l, 
    (forall x1 x2, mem_bool OA x2 l = true -> 
                  (compare OA x1 x2 = Eq <-> compare OB (f x1) (f x2) = Eq)) -> 
    forall x, nb_occ OB (f x) (map f l) = nb_occ OA x l.
Proof.
intros A B OA OB f l; induction l as [ | a1 l];
intros Hl x; simpl; [apply refl_equal | ].
apply f_equal2.
- case_eq (compare OA x a1); intro Hx.
  + rewrite (Hl x a1) in Hx; [rewrite Hx; trivial | ].
    simpl; unfold eq_bool; rewrite compare_eq_refl; trivial.
  + case_eq (compare OB (f x) (f a1)); intro Hfx; trivial.
    rewrite <- (Hl x a1), Hx in Hfx; [discriminate Hfx | ].
    simpl; unfold eq_bool; rewrite compare_eq_refl; trivial.
  + case_eq (compare OB (f x) (f a1)); intro Hfx; trivial.
    rewrite <- (Hl x a1), Hx in Hfx; [discriminate Hfx | ].
    simpl; unfold eq_bool; rewrite compare_eq_refl; trivial.
- apply IHl.
  intros x1 x2 Hx2; apply Hl; simpl.
  rewrite Hx2, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma nb_occ_map_eq_weak :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f : A -> B) l1 l2,
    (forall x1 x2, mem_bool OA x1 l1 = true -> mem_bool OA x2 l2 = true ->
                   compare OA x1 x2 = Eq -> 
                   compare OB (f x1) (f x2) = Eq) ->
    (forall x, nb_occ OA x l1 = nb_occ OA x l2) -> 
    forall x, nb_occ OB (f x) (map f l1) = nb_occ OB (f x) (map f l2).
Proof.
intros A B OA OB f l1; induction l1 as [ | x1 l1]; intros l2 Hf H x.
- destruct l2 as [ | x2 l2]; [apply refl_equal | ].
  assert (Hx2 := H x2).
  simpl in Hx2; rewrite compare_eq_refl in Hx2.
  destruct (nb_occ OA x2 l2); discriminate Hx2.
- rewrite map_unfold, nb_occ_unfold.
  assert (Hx1 : mem_bool OA x1 l2 = true).
  {
    case_eq (mem_bool OA x1 l2); [intros _; apply refl_equal | ].
    intro Abs; generalize (not_mem_nb_occ OA _ _ Abs).
    rewrite <- H, nb_occ_unfold, compare_eq_refl.
    destruct (nb_occ OA x1 l1); discriminate.
  }
  rewrite mem_bool_true_iff in Hx1.
  destruct Hx1 as [x2 [Hx1 Hx2]].
  destruct (in_split _ _ Hx2) as [k1 [k2 Hk]].
  rewrite Hk, map_app, nb_occ_app.
  rewrite (map_unfold f (_ :: _)), (nb_occ_unfold _ _ (_ :: _)).
  assert (Hf' : forall x2 x3 : A, mem_bool OA x2 l1 = true -> mem_bool OA x3 (k1 ++ k2) = true ->
                                  compare OA x2 x3 = Eq -> compare OB (f x2) (f x3) = Eq).
  {
    intros y1 y2 Hy1 Hy2; apply Hf; simpl.
    - rewrite Hy1, Bool.orb_true_r; apply refl_equal. 
    - rewrite Hk; rewrite mem_bool_app, Bool.orb_true_iff in Hy2.
      destruct Hy2 as [Hy2 | Hy2].
      + rewrite mem_bool_app, Hy2; apply refl_equal.
      + rewrite mem_bool_app, (mem_bool_unfold _ _ (_ :: _)), Hy2.
        rewrite 2 Bool.orb_true_r; apply refl_equal.
  }
  assert (H' : forall x : A, nb_occ OA x l1 = nb_occ OA x (k1 ++ k2)).
  {
    intros y.
    generalize (H y); rewrite Hk, 2 nb_occ_app; simpl.
    case_eq (compare OA y x1); intro Hy.
    - rewrite (compare_eq_trans _ _ _ _ Hy Hx1); intro Ky.
      apply (Nplus_reg_l 1); rewrite Ky, N.add_comm, <- N.add_assoc; apply f_equal.
      apply N.add_comm.
    - rewrite (compare_lt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
    - rewrite (compare_gt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
  }
  assert (IH := IHl1 (k1 ++ k2) Hf' H' x).
  rewrite IH, map_app, nb_occ_app.
  rewrite N.add_comm, <- N.add_assoc; apply f_equal.
  rewrite N.add_comm; apply f_equal2; [ | apply refl_equal].
  assert (Kx1 : compare OB (f x) (f x1) = compare OB (f x) (f x2)).
  {
    assert (Kx1 : compare OB (f x1) (f x2) = Eq).
    {
      apply Hf.
      - rewrite mem_bool_unfold, compare_eq_refl; apply refl_equal.
      - case_eq (mem_bool OA x2 l2); [intros; trivial | ].
        intro _Hx2.
        assert (Kx2 := not_mem_nb_occ OA _ _ _Hx2).
        assert (Jx2 := H x2).
        rewrite Kx2, nb_occ_unfold, compare_lt_gt, Hx1 in Jx2.
        simpl in Jx2.
        destruct (nb_occ OA x2 l1); discriminate Jx2.
      - apply Hx1. 
    }
    apply sym_eq; case_eq (compare OB (f x) (f x1)); intro Jx1.
    - apply (compare_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_lt_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_gt_eq_trans _ _ _ _ Jx1 Kx1).
  }
  rewrite Kx1; apply refl_equal.
Qed.

Lemma nb_occ_map_eq_3 :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f : A -> B) l1 l2,
    (forall x1 x2, mem_bool OA x1 l1 = true -> mem_bool OA x2 l2 = true -> 
                   compare OA x1 x2 = Eq -> 
                   compare OB (f x1) (f x2) = Eq) ->
    (forall x, nb_occ OA x l1 = nb_occ OA x l2) -> 
    forall x, nb_occ OB x (map f l1) = nb_occ OB x (map f l2).
Proof.
intros A B OA OB f l1 l2 Hf H y.
case_eq (mem_bool OB y (map f l1)); [intros Hy | intros Hy].
- rewrite mem_bool_true_iff in Hy.
  destruct Hy as [fx [Hy Hfx]].
  rewrite in_map_iff in Hfx; destruct Hfx as [x [Hfx Hx]]; subst fx.
  rewrite 2 (nb_occ_eq_1 _ _ _ _ Hy).
  apply (nb_occ_map_eq_weak OA); trivial.
- case_eq (mem_bool OB y (map f l2)); [intros Hy' | intros Hy'].
  + rewrite mem_bool_true_iff in Hy'.
    destruct Hy' as [fx [Hy' Hfx]].
    rewrite in_map_iff in Hfx; destruct Hfx as [x [Hfx Hx]]; subst fx.
    rewrite 2 (nb_occ_eq_1 _ _ _ _ Hy').
    apply (nb_occ_map_eq_weak OA); trivial.
  + rewrite (not_mem_nb_occ OB _ _ Hy), (not_mem_nb_occ OB _ _ Hy').
    apply refl_equal.
Qed.

Lemma nb_occ_map_eq_2_3 :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f1 f2 : A -> B) l1 l2,
    (forall x1 x2, compare OA x1 x2 = Eq -> 
                   compare OB (f1 x1) (f2 x2) = Eq) ->
    (forall x, nb_occ OA x l1 = nb_occ OA x l2) -> 
    forall x, nb_occ OB x (map f1 l1) = nb_occ OB x (map f2 l2).
Proof.
intros A B OA OB f1 f2 l1; induction l1 as [ | x1 l1]; intros l2 Hf H x.
- destruct l2 as [ | x2 l2]; [trivial | ].
  apply False_rec.
  assert (Hx2 := H x2); simpl in Hx2.
  rewrite compare_eq_refl in Hx2; destruct (nb_occ OA x2 l2); discriminate Hx2.
- assert (Hx1 : mem_bool OA x1 l2 = true).
  {
    case_eq (mem_bool OA x1 l2); [intros _; apply refl_equal | ].
    intro Abs; generalize (not_mem_nb_occ OA _ _ Abs).
    rewrite <- H, nb_occ_unfold, compare_eq_refl.
    destruct (nb_occ OA x1 l1); discriminate.
  }
  rewrite mem_bool_true_iff in Hx1.
  destruct Hx1 as [x2 [Hx1 Hx2]].
  destruct (in_split _ _ Hx2) as [k1 [k2 Hk]].
  rewrite Hk, map_app, nb_occ_app.
  rewrite (map_unfold f1 (_ :: _)), (nb_occ_unfold _ _ (_ :: _)).
  assert (H' : forall x : A, nb_occ OA x l1 = nb_occ OA x (k1 ++ k2)).
  {
    intros y.
    generalize (H y); rewrite Hk, 2 nb_occ_app; simpl.
    case_eq (compare OA y x1); intro Hy.
    - rewrite (compare_eq_trans _ _ _ _ Hy Hx1); intro Ky.
      apply (Nplus_reg_l 1); rewrite Ky, N.add_comm, <- N.add_assoc; apply f_equal.
      apply N.add_comm.
    - rewrite (compare_lt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
    - rewrite (compare_gt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
  }
  assert (IH := IHl1 (k1 ++ k2) Hf H' x).
  rewrite IH, map_app, nb_occ_app.
  rewrite N.add_comm, <- N.add_assoc; apply f_equal.
  rewrite  (map_unfold _ (_ :: _)), (nb_occ_unfold _ _ (_ :: _)),
  N.add_comm; apply f_equal2; [ | apply refl_equal].
  assert (Kx1 : compare OB x (f1 x1) = compare OB x (f2 x2)).
  {
    assert (Kx1 : compare OB (f1 x1) (f2 x2) = Eq).
    {
      apply Hf; assumption.
    }
    apply sym_eq; case_eq (compare OB x (f1 x1)); intro Jx1.
    - apply (compare_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_lt_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_gt_eq_trans _ _ _ _ Jx1 Kx1).
  }
  rewrite Kx1; apply refl_equal.
Qed.

Lemma nb_occ_map_eq_2_3_alt :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f1 f2 : A -> B) l1 l2,
    (forall x1 x2, Oeset.mem_bool OA x1 l1 = true -> compare OA x1 x2 = Eq -> 
                   compare OB (f1 x1) (f2 x2) = Eq) ->
    (forall x, nb_occ OA x l1 = nb_occ OA x l2) -> 
    forall x, nb_occ OB x (map f1 l1) = nb_occ OB x (map f2 l2).
Proof.
intros A B OA OB f1 f2 l1; induction l1 as [ | x1 l1]; intros l2 Hf H x.
- destruct l2 as [ | x2 l2]; [trivial | ].
  apply False_rec.
  assert (Hx2 := H x2); simpl in Hx2.
  rewrite compare_eq_refl in Hx2; destruct (nb_occ OA x2 l2); discriminate Hx2.
- assert (Hx1 : mem_bool OA x1 l2 = true).
  {
    case_eq (mem_bool OA x1 l2); [intros _; apply refl_equal | ].
    intro Abs; generalize (not_mem_nb_occ OA _ _ Abs).
    rewrite <- H, nb_occ_unfold, compare_eq_refl.
    destruct (nb_occ OA x1 l1); discriminate.
  }
  rewrite mem_bool_true_iff in Hx1.
  destruct Hx1 as [x2 [Hx1 Hx2]].
  destruct (in_split _ _ Hx2) as [k1 [k2 Hk]].
  rewrite Hk, map_app, nb_occ_app.
  rewrite (map_unfold f1 (_ :: _)), (nb_occ_unfold _ _ (_ :: _)).
  assert (H' : forall x : A, nb_occ OA x l1 = nb_occ OA x (k1 ++ k2)).
  {
    intros y.
    generalize (H y); rewrite Hk, 2 nb_occ_app; simpl.
    case_eq (compare OA y x1); intro Hy.
    - rewrite (compare_eq_trans _ _ _ _ Hy Hx1); intro Ky.
      apply (Nplus_reg_l 1); rewrite Ky, N.add_comm, <- N.add_assoc; apply f_equal.
      apply N.add_comm.
    - rewrite (compare_lt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
    - rewrite (compare_gt_eq_trans _ _ _ _ Hy Hx1); intro Ky; apply Ky.
  }
  assert (Hf' : forall x1 x2 : A,
                  mem_bool OA x1 l1 = true ->
                  compare OA x1 x2 = Eq -> compare OB (f1 x1) (f2 x2) = Eq).
  {
    intros y1 y2 Hy1; apply Hf.
    rewrite mem_bool_unfold, Hy1, Bool.orb_true_r; trivial.
  }
  assert (IH := IHl1 (k1 ++ k2) Hf' H' x).
  rewrite IH, map_app, nb_occ_app.
  rewrite N.add_comm, <- N.add_assoc; apply f_equal.
  rewrite  (map_unfold _ (_ :: _)), (nb_occ_unfold _ _ (_ :: _)),
  N.add_comm; apply f_equal2; [ | apply refl_equal].
  assert (Kx1 : compare OB x (f1 x1) = compare OB x (f2 x2)).
  {
    assert (Kx1 : compare OB (f1 x1) (f2 x2) = Eq).
    {
      apply Hf; [ | assumption].
      rewrite mem_bool_unfold, compare_eq_refl; apply refl_equal.
    }
    apply sym_eq; case_eq (compare OB x (f1 x1)); intro Jx1.
    - apply (compare_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_lt_eq_trans _ _ _ _ Jx1 Kx1).
    - apply (compare_gt_eq_trans _ _ _ _ Jx1 Kx1).
  }
  rewrite Kx1; apply refl_equal.
Qed.

Lemma nb_occ_map_eq_2_alt :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f1 f2 : A -> B) l,
    (forall x1, In x1 l -> compare OB (f1 x1) (f2 x1) = Eq) ->
    forall x, nb_occ OB x (map f1 l) = nb_occ OB x (map f2 l).
Proof.
intros A B OA OB f1 f2; induction l as [ | a1 l]; intros Hf y.
- apply refl_equal.
- simpl; apply f_equal2; [ | apply IHl; intros; apply Hf; right; assumption].
  assert (Ha1 := Hf _ (or_introl _ (refl_equal _))).
  case_eq (compare OB y (f1 a1)); intro Hy.
  + rewrite (compare_eq_trans _ _ _ _ Hy Ha1); apply refl_equal.
  + rewrite (compare_lt_eq_trans _ _ _ _ Hy Ha1); apply refl_equal.
  + rewrite (compare_gt_eq_trans _ _ _ _ Hy Ha1); apply refl_equal.
Qed.

Lemma nb_occ_map_filter :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f : A -> bool) (g : A -> B) l,
    (forall x1 x2, 
       Oeset.mem_bool OA x1 l = true -> compare OB (g x1) (g x2) = Eq -> f x1 = f x2) ->
    forall a, nb_occ OB (g a) (map g (filter f l)) = 
              if (f a) then nb_occ OB (g a) (map g l) else 0%N.
Proof.
intros A B OA OB f g l Hl a; revert Hl a.
induction l as [ | a1 l]; intros Hl a; simpl; [case (f a); apply refl_equal | ].
case_eq (f a1); intro Ha1; simpl.
- case_eq (compare OB (g a) (g a1)); intro Ha.
  + rewrite IHl.
    rewrite <- (Hl a1 a), Ha1; trivial.
    * rewrite mem_bool_unfold, compare_eq_refl; apply refl_equal.
    * apply compare_eq_sym; assumption.
    * intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
  + case_eq (f a); intro Ka.
    * apply f_equal; rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
  + case_eq (f a); intro Ka.
    * apply f_equal; rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
- case_eq (compare OB (g a) (g a1)); intro Ha.
  + rewrite IHl.
    rewrite <- (Hl a1 a), Ha1; trivial.
    * rewrite mem_bool_unfold, compare_eq_refl; apply refl_equal.
    * apply compare_eq_sym; assumption.
    * intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
  + case_eq (f a); intro Ka.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
  + case_eq (f a); intro Ka.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
    * rewrite IHl, Ka; trivial.
      intros x1 x2 H; apply Hl; rewrite mem_bool_unfold, H, Bool.orb_true_r.
      apply refl_equal.
Qed.

Lemma map_filter_and :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (f1 f2 : A -> bool) (g : A -> B) l,
    (forall x1 x2, Oeset.mem_bool OA x1 l = true -> 
                   compare OB (g x1) (g x2) = Eq -> f1 x1 = f1 x2) ->
    (forall x1 x2, Oeset.mem_bool OA x1 l = true -> 
                   compare OB (g x1) (g x2) = Eq -> f2 x1 = f2 x2) ->
  forall x,
    Oeset.nb_occ OB x (map g (filter (fun x : A => f1 x && f2 x) l)) =
   N.min (Oeset.nb_occ OB x (map g (filter f1 l)))
         (Oeset.nb_occ OB x (map g (filter f2 l))).
Proof.
intros A B OA OB f1 f2 g l H1 H2 x.
case_eq (mem_bool OB x (map g l)).
- intros Hx; rewrite mem_bool_true_iff in Hx.
  destruct Hx as [b [Hx Hb]]; rewrite in_map_iff in Hb.
  destruct Hb as [a [Hb Ha]]; subst b.
  rewrite 3 (nb_occ_eq_1 _ _ _ _ Hx), 3 (nb_occ_map_filter OA); trivial.
  + case (f1 a); simpl.
    * {
        case (f2 a); simpl.
        - apply sym_eq; apply N.min_l.
          apply N.le_refl.
        - rewrite N.min_0_r; apply refl_equal.
      } 
    * rewrite N.min_0_l; apply refl_equal.
  + intros x1 x2 Hx1 _Hx; apply f_equal2; [apply H1 | apply H2]; trivial.
- intro Hx.
  apply trans_eq with 0%N.
  + case_eq (nb_occ OB x (map g (filter (fun x0 : A => f1 x0 && f2 x0) l))); [trivial | ].
    intros p Hp; rewrite <- not_true_iff_false in Hx.
    apply False_rec; apply Hx.
    generalize (not_mem_nb_occ OB x (map g (filter (fun x0 : A => f1 x0 && f2 x0) l))).
    rewrite Hp.
    case_eq (mem_bool OB x (map g (filter (fun x0 : A => f1 x0 && f2 x0) l))).
    * intros Hl _; rewrite mem_bool_true_iff in Hl.
      destruct Hl as [b [Hb Kb]].
      rewrite in_map_iff in Kb; destruct Kb as [a [Ha Ka]]; subst b.
      rewrite filter_In in Ka.
      rewrite mem_bool_true_iff; exists (g a); split; [assumption | ].
      rewrite in_map_iff; exists a; split; [trivial | apply (proj1 Ka)].
    * intros _ Abs; apply False_rec; generalize (Abs (refl_equal _)); discriminate.
  + case_eq (nb_occ OB x (map g (filter f1 l))); [rewrite N.min_0_l; trivial | ].
    intros p Hp; rewrite <- not_true_iff_false in Hx.
    apply False_rec; apply Hx.
    generalize (not_mem_nb_occ OB x (map g (filter f1 l))).
    rewrite Hp.
    case_eq (mem_bool OB x (map g (filter f1 l))).
    * intros Hl _; rewrite mem_bool_true_iff in Hl.
      destruct Hl as [b [Hb Kb]].
      rewrite in_map_iff in Kb; destruct Kb as [a [Ha Ka]]; subst b.
      rewrite filter_In in Ka.
      rewrite mem_bool_true_iff; exists (g a); split; [assumption | ].
      rewrite in_map_iff; exists a; split; [trivial | apply (proj1 Ka)].
    * intros _ Abs; apply False_rec; generalize (Abs (refl_equal _)); discriminate.
Qed.

End Oeset.

Lemma comparelA_map_eq_1 : 
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B) (f1 f2 : A -> B) l,
         (forall x, Oeset.compare OB (f1 x) (f2 x) = Eq) ->
         comparelA (Oeset.compare OB) (map f1 l) (map f2 l) = Eq.
Proof.
intros A B OA OB f1 f2 l; induction l as [ | x1 l]; intros Hf.
- apply refl_equal.
- simpl.
  rewrite Hf; apply IHl; assumption.
Qed.

Lemma comparelA_map_eq_2 : 
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B) (f : A -> B) l1 l2,
         (forall x1 x2, Oeset.compare OA x1 x2 = Eq -> Oeset.compare OB (f x1) (f x2) = Eq) ->
         comparelA (Oeset.compare OA) l1 l2 = Eq ->
         comparelA (Oeset.compare OB) (map f l1) (map f l2) = Eq.
Proof.
intros A B OA OB f l1; induction l1 as [ | x1 l1]; intros [ | x2 l2] Hf Hl; try discriminate Hl.
- apply refl_equal.
- simpl in Hl; simpl.
  case_eq (Oeset.compare OA x1 x2); intro Hx; rewrite Hx in Hl; try discriminate Hl.
  rewrite (Hf _ _ Hx); apply IHl1; trivial.
Qed.

Lemma comparelA_flat_map_eq_1 : 
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B) (f1 f2 : A -> list B) l,
         (forall x, comparelA (Oeset.compare OB) (f1 x) (f2 x) = Eq) ->
         comparelA (Oeset.compare OB) (flat_map f1 l) (flat_map f2 l) = Eq.
Proof.
intros A B OA OB f1 f2 l; induction l as [ | x1 l]; intros Hf.
- apply refl_equal.
- simpl; apply comparelA_eq_app; [ | apply IHl; trivial].
  apply Hf.
Qed.

Lemma comparelA_flat_map_eq_2 : 
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B) (f : A -> list B) l1 l2,
         (forall x1 x2, Oeset.compare OA x1 x2 = Eq -> comparelA (Oeset.compare OB) (f x1) (f x2) = Eq) ->
         comparelA (Oeset.compare OA) l1 l2 = Eq ->
         comparelA (Oeset.compare OB) (flat_map f l1) (flat_map f l2) = Eq.
Proof.
intros A B OA OB f l1; induction l1 as [ | x1 l1]; intros [ | x2 l2] Hf Hl; try discriminate Hl.
- apply refl_equal.
- simpl in Hl; simpl.
  case_eq (Oeset.compare OA x1 x2); intro Hx; rewrite Hx in Hl; try discriminate Hl.
  apply comparelA_eq_app; [apply (Hf _ _ Hx) | apply IHl1]; trivial.
Qed.

Lemma fold_left_rev_right_eq
      (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B)
      (f : B -> A -> A)
      (Hf : forall x1 x2 y1 y2, Oeset.compare OB x1 x2 = Eq -> Oeset.compare OA y1 y2 = Eq -> Oeset.compare OA (f x1 y1) (f x2 y2) = Eq) :
  forall l1 l2 acc1 acc2,
    Oeset.compare OA acc1 acc2 = Eq ->
    comparelA (Oeset.compare OB) l1 (rev l2) = Eq ->
    Oeset.compare OA (fold_left (fun a e => f e a) l1 acc2) (fold_right f acc1 l2) = Eq.
Proof.
  induction l1 as [ |x xs IHxs].
  - intros [ |y ys] acc1 acc2; simpl.
    + intros H _; now apply Oeset.compare_eq_sym.
    + case_eq (rev ys ++ y :: nil); try discriminate.
      intro H. elim (snoc_not_nil _ _ _ H).
  - intros l' acc1 acc2 Hacc. destruct (list_nil_snoc l') as [H1|[z [zs H1]]]; subst l'.
    + discriminate.
    + simpl. rewrite rev_app_distr. simpl.
      case_eq (Oeset.compare OB x z); try discriminate. intros Heq1 Heq2.
      rewrite fold_right_app. simpl.
      apply IHxs; trivial.
      apply Hf; trivial.
      now apply Oeset.compare_eq_sym.
Qed.



(** ** Equality *)
(** Same as above, but [compare] induces the Leibniz equality. *)

Module Oset.
Record Rcd (A : Type) : Type :=
  mk_R
    { 
      compare : A -> A -> comparison;
      eq_bool_ok : 
        forall a1 a2, match compare a1 a2 with Eq => a1 = a2 | _ => ~ a1 = a2 end;
      compare_lt_trans : 
        forall a1 a2 a3, compare a1 a2 = Lt -> compare a2 a3 = Lt -> compare a1 a3 = Lt;
      compare_lt_gt : forall a1 a2, compare a1 a2 = CompOpp (compare a2 a1)
}.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Rcd A.

Lemma compare_eq_refl :
  forall a, compare OA a a = Eq.
Proof.
intros a.
generalize (compare_lt_gt OA a a).
case (compare OA a a); try discriminate.
exact (fun _ => refl_equal _).
Qed.

Lemma compare_eq_sym :
  forall a b, compare OA a b = Eq -> compare OA b a = Eq.
Proof.
intros a b H.
rewrite compare_lt_gt, H.
apply refl_equal.
Qed.

Lemma compare_eq_trans : 
   forall a1 a2 a3, compare OA a1 a2 = Eq -> compare OA a2 a3 = Eq -> compare OA a1 a3 = Eq.
Proof.
intros a1 a2 a3 H1.
generalize (eq_bool_ok OA a1 a2); rewrite H1.
intro; subst a2; exact (fun h => h).
Qed.

Lemma  compare_eq_lt_trans : 
  forall a1 a2 a3, compare OA a1 a2 = Eq -> compare OA a2 a3 = Lt -> compare OA a1 a3 = Lt.
Proof.
intros a1 a2 a3 H1.
generalize (eq_bool_ok OA a1 a2); rewrite H1.
intro; subst a2; exact (fun h => h).
Qed.

Lemma  compare_lt_eq_trans : 
  forall a1 a2 a3, compare OA a1 a2 = Lt -> compare OA a2 a3 = Eq -> compare OA a1 a3 = Lt.
intros a1 a2 a3 H1 H2.
generalize (eq_bool_ok OA a2 a3); rewrite H2.
intro; subst a3; exact H1.
Qed.

Lemma compare_eq_gt_trans :
  forall a b c, compare OA a b = Eq -> compare OA b c = Gt -> compare OA a c = Gt.
Proof.
intros a b c H1 H2.
rewrite compare_lt_gt, CompOpp_iff in H2.
rewrite compare_lt_gt, CompOpp_iff.
apply compare_lt_eq_trans with b; [apply H2 | ].
apply compare_eq_sym; assumption.
Qed.

Lemma compare_gt_eq_trans :
  forall a b c, compare OA a b = Gt -> compare OA b c = Eq -> compare OA a c = Gt.
Proof.
intros a b c H1 H2.
rewrite compare_lt_gt, CompOpp_iff in H1.
rewrite compare_lt_gt, CompOpp_iff.
apply compare_eq_lt_trans with b; [ | apply H1].
apply compare_eq_sym; assumption.
Qed. 

Lemma compare_eq_iff :
  forall a1 a2, compare OA a1 a2 = Eq <-> a1 = a2.
Proof.
intros a1 a2; split; intro H.
- generalize (eq_bool_ok OA a1 a2); rewrite H.
  exact (fun h => h).
- subst a2; apply compare_eq_refl.
Qed.

Definition eq_bool := (fun x y => match compare OA x y with Eq => true | _ => false end).

Lemma eq_bool_refl : forall x, eq_bool x x = true.
Proof.
intro x; unfold eq_bool; rewrite compare_eq_refl; apply refl_equal.
Qed.

Lemma eq_bool_sym : forall x y, eq_bool x y = eq_bool y x.
Proof.
intros x y; unfold eq_bool; rewrite compare_lt_gt.
case (compare OA y x); apply refl_equal.
Qed.

Lemma eq_bool_true_iff :
  forall a1 a2, eq_bool a1 a2 = true <-> a1 = a2.
Proof.
intros a1 a2; unfold eq_bool.
rewrite compare_eq_true.
split; intro H.
- generalize (eq_bool_ok OA a1 a2); rewrite H.
  exact (fun h => h).
- subst a2; apply compare_eq_refl.
Qed.

Lemma Equivalence :
  RelationClasses.Equivalence (fun x y => eq_bool x y = true).
Proof.
unfold eq_bool; split.
- intro x; rewrite compare_eq_refl; apply refl_equal.
- intros x y H; rewrite compare_eq_true in H.
  rewrite compare_lt_gt, H; apply refl_equal.
- intros x y z; rewrite 3 compare_eq_true; apply compare_eq_trans.
Qed.

Lemma StrictOrder : RelationClasses.StrictOrder (fun x y => compare OA x y = Lt).
Proof.
split.
- intros x Hx.
  rewrite compare_eq_refl in Hx; discriminate Hx.
- intros x y z; apply compare_lt_trans.
Qed.

Lemma Compat :
  Morphisms.Proper
   (Morphisms.respectful (fun x y  => eq_bool x y = true)
      (Morphisms.respectful (fun x y => eq_bool x y = true) iff))
   (fun x y => compare OA x y = Lt).
Proof.
intros x1 y1 H1; rewrite eq_bool_true_iff in H1; subst y1.
intros x2 y2 H2; rewrite eq_bool_true_iff in H2; subst y2.
split; exact (fun h => h).
Qed.

Definition mem_bool a l := Mem.mem_bool eq_bool a l.

Lemma mem_bool_unfold : 
  forall a l, 
    mem_bool a l = 
    match l with
      | nil => false
      | a1 :: l => match compare OA a a1 with Eq => true | _ => false end || mem_bool a l
    end.
Proof.
intros a l; case l.
- apply refl_equal.
- clear l; intros a1 l; simpl.
  apply refl_equal.
Qed.

Lemma mem_bool_app : 
  forall a l1 l2, mem_bool a (l1 ++ l2) = mem_bool a l1 || mem_bool a l2.
Proof.
intros a l1 l2; apply Mem.mem_bool_app.                       
Qed.

Lemma mem_bool_true_iff : 
  forall a l, mem_bool a l = true <-> In a l.
Proof.
intros a l; unfold mem_bool, eq_bool; rewrite mem_bool_true_iff; split.
- intros [a' [Ha H]].
  generalize (eq_bool_ok OA a a').
  rewrite compare_eq_true in Ha; rewrite Ha.
  intro; subst a'; exact H.
- intro H; exists a; split; [ | assumption].
  rewrite compare_eq_refl; apply refl_equal.
Qed.

Open Scope N.

Fixpoint nb_occ a l : N :=
  match l with
    | nil => 0
    | a1 :: l => (match compare OA a a1 with Eq => 1 | _ => 0 end) + nb_occ a l
  end.

Lemma nb_occ_unfold :
  forall a l, nb_occ a l = 
              match l with
                | nil => 0
                | a1 :: l => (match compare OA a a1 with Eq => 1 | _ => 0 end) + nb_occ a l
              end.                                                                                        
Proof.
intros a l; destruct l; apply refl_equal.
Qed.

Definition all_diff_bool l := Mem.all_diff_bool eq_bool l.

Lemma all_diff_bool_unfold :
  forall a l, all_diff_bool (a :: l) = negb (mem_bool a l) && (all_diff_bool l).
Proof.
intros a l; unfold all_diff_bool, mem_bool.
apply Mem.all_diff_bool_unfold.
Qed.

Lemma all_diff_bool_ok : 
  forall l, all_diff l <-> all_diff_bool l = true.
Proof.
fix h 1.
intro l; case l; clear l.
- split; intro H; simpl; trivial.
- intros a1 l; split; rewrite all_diff_unfold, all_diff_bool_unfold, Bool.andb_true_iff; 
  intros [H1 H2]; split.
  + rewrite negb_true_iff, <- not_true_iff_false.
    intro K1; apply (H1 a1); [ | trivial].
    rewrite <- mem_bool_true_iff; apply K1.
  + rewrite <- h; apply H2.
  + rewrite negb_true_iff, <- not_true_iff_false in H1.
    intros a Ha Ka; subst a; apply H1.
    rewrite mem_bool_true_iff; apply Ha.
  + rewrite h; apply H2.
Qed.

Lemma all_diff_bool_app_1 :
  forall l1 l2, all_diff_bool (l1 ++ l2) = true -> all_diff_bool l1 = true.
Proof.
intros l1 l2; apply Mem.all_diff_bool_app1.
Qed.

Lemma all_diff_bool_app_2 :
  forall l1 l2, all_diff_bool (l1 ++ l2) = true -> all_diff_bool l2 = true.
Proof.
intros l1 l2; apply Mem.all_diff_bool_app2.
Qed.

Lemma all_diff_bool_app :
  forall l1 l2, all_diff_bool (l1 ++ l2) = true ->
   forall a, mem_bool a l1 = true -> mem_bool a l2 = true -> False.
Proof.
intros l1 l2 H a Ha Ka; rewrite <- all_diff_bool_ok in H.
apply (all_diff_app l1 l2 H a); rewrite <- mem_bool_true_iff; assumption.
Qed.

Lemma all_diff_bool_app_iff :
  forall l1 l2, 
    (all_diff_bool l1 = true /\ all_diff_bool l2 = true /\
     (forall a, mem_bool a l1 = true -> mem_bool a l2 = true -> False)) <->
     all_diff_bool (l1 ++ l2) = true.
Proof.
intros l1 l2.
rewrite <- 3 all_diff_bool_ok, <- all_diff_app_iff; split.
- intros [H1 [H2 H]]; repeat split; trivial.
  intros a Ha Ka; apply (H a); rewrite mem_bool_true_iff; trivial.
- intros [H1 [H2 H]]; repeat split; trivial.
  intros a Ha Ka; apply (H a); rewrite <- mem_bool_true_iff; trivial.
Qed.

Lemma all_diff_bool_fst :
  forall (B : Type) (l : list (A * B)), 
    all_diff_bool (List.map (@fst _ _) l) = true ->
    forall a b1 b2, List.In (a, b1) l -> List.In (a, b2) l -> b1 = b2.
Proof.
intros B l Hl a b1 b2 H1 H2.
destruct (in_split _ _ H1) as [l1 [l2 K1]].
rewrite K1 in H2.
destruct (in_app_or _ _ _ H2) as [K2 | K2].
- destruct (in_split _ _ K2) as [k1 [k2 K3]].
  apply False_rec.
  rewrite K1, map_app in Hl.
  apply (all_diff_bool_app _ _ Hl a).
  + rewrite K3, map_app.
    simpl; rewrite mem_bool_app; simpl.
    unfold eq_bool; rewrite compare_eq_refl, Bool.orb_true_r.
    apply refl_equal.
  + simpl.
    unfold eq_bool; rewrite compare_eq_refl.
    apply refl_equal.
- simpl in K2; destruct K2 as [K2 | K2]; [injection K2; trivial | ].
  destruct (in_split _ _ K2) as [k1 [k2 K3]].
  apply False_rec.
  rewrite K1, map_app in Hl.
  generalize (all_diff_bool_app_2 _ _ Hl); clear Hl; intro Hl.
  simpl map in Hl; rewrite K3, map_app in Hl.
  apply False_rec.
  apply (all_diff_bool_app (a :: map (fst (B := B)) k1) (map (fst (B := B)) ((a, b2) :: k2)) Hl a).
  + simpl; unfold eq_bool.
    rewrite compare_eq_refl; apply refl_equal.
  + simpl; unfold eq_bool.
    rewrite compare_eq_refl; apply refl_equal.
Qed.

Lemma all_diff_bool_mapI_rec :
  forall (B : Type) f l n, (forall i1 i2, f i1 = f i2 -> i1 = i2) -> 
                all_diff_bool (mapI_rec (A := B) (fun i x => f i) n l) = true.
Proof.
intros B f l n H; revert n.
induction l as [ | x1 l]; intro n; simpl; [trivial | ].
case_eq (mapI_rec (fun (i : N) (_ : B) => f i) (n + 1) l); [trivial | ].
intros x k Hn; rewrite <- Hn, IHl, Bool.andb_true_r, negb_true_iff, <- not_true_iff_false.
intro K; rewrite mem_bool_true_iff, in_mapI_rec_iff in K.
destruct K as [i [bi [Hi [Ki K]]]].
assert (J := H _ _ K).
apply (N.lt_irrefl n).
rewrite J at 2.
apply N.lt_le_trans with (n + 1)%N.
- rewrite N.add_1_r, N.lt_succ_r; apply N.le_refl.
- apply N.le_add_r.
Qed.

Section Find.

Hypothesis B : Type.

Definition find a (l : list (A * B)) := Mem.find eq_bool a l.

Lemma find_eq :
  forall a l1 l2, l1 = l2 -> find a l1 = find a l2.
Proof.
intros a l1 l2 H; apply f_equal; assumption.
Qed.

Lemma find_app :
  forall a l1 l2, 
    find a (l1 ++ l2) = match find a l1 with Some b1 => Some b1 | _ => find a l2 end.
Proof.
intros a l1 l2.
unfold find.
apply Mem.find_app.
Qed.

Lemma not_mem_find_none :
  forall a l, mem_bool a (map (@fst _ _) l) = false -> find a l = None.
Proof.
intros a l; induction l as [ | [a1 b1] l]; intro H; [trivial | ].
rewrite map_unfold, mem_bool_unfold, Bool.orb_false_iff in H; simpl in H; destruct H as [H1 H2].
simpl; unfold eq_bool; rewrite H1.
apply IHl; apply H2.
Qed.

Lemma all_diff_bool_fst_find :
  forall (l : list (A * B)), all_diff_bool (map (@fst _ _) l) = true ->
     forall a b, In (a, b) l -> find a l = Some b.
Proof.
intros l H a b Ha.
case_eq (find a l).
- intros b' Ha'; apply f_equal.
  rewrite <- all_diff_bool_ok in H.
  apply (all_diff_fst _ H a); [ | assumption].
  destruct (Mem.find_some _ _ _ Ha') as [_a [H1 H2]].
  rewrite eq_bool_true_iff in H1; subst _a.
  apply H2.
- intro K; apply False_rec.
  refine (Mem.find_none _ _ _ K a _ b Ha).
  rewrite eq_bool_true_iff; apply refl_equal.
Qed.

Lemma find_some :
  forall a l b, find a l = Some b -> In (a, b) l.
Proof.
intros a l b H.
destruct (Mem.find_some _ _ _ H) as [_a [H1 H2]].
rewrite eq_bool_true_iff in H1; subst _a; assumption.
Qed.

Lemma find_none :
  forall a l, find a l = None -> forall b, In (a, b) l -> False.
Proof.
intros a l H1 b H2.
assert (H3 : eq_bool a a = true).
{
  rewrite eq_bool_true_iff; apply refl_equal.
}
apply (Mem.find_none _ _ l H1 a H3 _ H2).
Qed.

Lemma find_none_alt : forall a l, find a l = None -> In a (map (@fst _ _) l) -> False.
Proof.
intros a l H1 H2.
rewrite in_map_iff in H2.
destruct H2 as [[_a b] [H2 H3]]; simpl in H2; subst _a.
apply (find_none _ _ H1 _ H3). 
Qed.

(* Lemma find_map2 :
  forall (C : Type) (f : C -> A) (g : C -> B) l a, 
    (forall a1 a2, List.In a1 l -> List.In a2 l -> f a1 = f a2 -> a1 = a2) ->
    In a l -> find (f a) (map (fun x => (f x, g x)) l) = Some (g a).
Proof.
intros C f g l a; 
induction l as [ | a1 l];
intros H Ha.
- contradiction Ha.
- simpl.
  case_eq (eq_bool (f a) (f a1)); intro Ja.
  + rewrite eq_bool_true_iff in Ja.
    do 2 apply f_equal; apply sym_eq; apply (H _ _ Ha (or_introl _ (refl_equal _)) Ja).
  + simpl in Ha; destruct Ha as [Ha | Ha].
    * subst a1; unfold eq_bool in Ja; rewrite compare_eq_refl in Ja; discriminate Ja.
    * apply IHl; [ | assumption].
      do 4 intro; apply H; right; assumption.
Qed.
*)

End Find.  

End Sec.

Section Sec2.

Hypotheses A B : Type.
Hypothesis OA : Rcd A.
Hypothesis OB : Rcd B.

Definition one_to_one_bool sa (rho : A -> B) :=
  forallb 
    (fun a1 => 
          forallb
            (fun a2 => match compare OB (rho a1) (rho a2) with 
                            | Eq => 
                              match compare OA a1 a2 with
                                | Eq => true
                                | Lt | Gt => false
                              end
                            | Lt | Gt => true
                          end) sa)
    sa.

Lemma one_to_one_bool_ok :
  forall sa rho, one_to_one sa rho <-> one_to_one_bool sa rho = true.
Proof.
intros fa rho.
unfold one_to_one, one_to_one_bool.
rewrite forallb_forall; split.
- (* 1/2 *)
  intros H a1 Ha1; rewrite forallb_forall.
  intros a2 Ha2.
  generalize (eq_bool_ok OB (rho a1) (rho a2)).
  case (compare OB (rho a1) (rho a2)); 
    [ intro Ha
    | exact (fun _ => refl_equal _) 
    | exact (fun _ => refl_equal _) ].
  rewrite (H a1 a2 Ha1 Ha2 Ha), compare_eq_refl.
  apply refl_equal.
- (* 1/1 *)
  intros H a1 a2 Ha1 Ha2 Ha.
  assert (IHa1 := H _ Ha1).
  rewrite forallb_forall in IHa1.
  assert (IH := IHa1 _ Ha2).
  rewrite Ha, compare_eq_refl, compare_eq_true in IH.
  generalize (eq_bool_ok OA a1 a2); rewrite IH.
  exact (fun h => h).
Qed.

Lemma all_diff_bool_map :
  forall (f : A -> B) l, 
    all_diff_bool OA l = true -> (forall x1 x2, In x1 l -> f x1 = f x2 -> x1 = x2) -> 
    all_diff_bool OB (map f l) = true.
Proof.
intros f l; induction l as [ | a1 l]; intros H1 H2;  [trivial | ].
rewrite all_diff_bool_unfold, Bool.andb_true_iff in H1.
rewrite map_unfold, all_diff_bool_unfold.
rewrite IHl, Bool.andb_true_r.
- rewrite negb_true_iff, <- not_true_iff_false in H1.
  rewrite negb_true_iff, <- not_true_iff_false.
  intro H; apply H1.
  rewrite mem_bool_true_iff, in_map_iff in H.
  destruct H as [x [H Hx]].
  rewrite (H2 a1 x (or_introl _ (refl_equal _)) (sym_eq H)).
  rewrite mem_bool_true_iff; assumption.
- apply (proj2 H1).
- do 3 intro; apply H2; right; assumption.
Qed.

Lemma all_diff_bool_snd :
  forall (l : list (A * B)), 
    all_diff_bool OB (List.map (@snd _ _) l) = true ->
    forall a1 a2 b, List.In (a1, b) l -> List.In (a2, b) l -> a1 = a2.
Proof.
intros l H a1 a2 b Ha1 Ha2.
apply (all_diff_bool_fst OB (map (fun x => match x with (a, b) => (b, a) end) l)) with b.
- rewrite map_map, <- H; apply f_equal.
  rewrite <- map_eq; intros x _; destruct x; trivial.
- rewrite in_map_iff; exists (a1, b); split; trivial.
- rewrite in_map_iff; exists (a2, b); split; trivial.
Qed.

(** Merging two compatible substitutions *)
Fixpoint merge (partial_res l : list (A * B)) {struct l} : option (list (A * B)) :=
  match l with
  | nil => Some partial_res
  | (x, t) as p :: l => 
       match find OA x partial_res with
       | Some t' => if eq_bool OB t t' then merge partial_res l else None
       | None => merge (p :: partial_res) l
       end
   end.

Lemma merge_correct :
   forall l1 l2,
     match merge l1 l2 with
       | Some l => 
         (forall a b, find OA a l1 = Some b -> find OA a l = Some b) /\
         (forall a b, find OA a l2 = Some b -> 
                      (exists b', find OA a l = Some b' /\ eq_bool OB b b' = true)) /\
         (forall a b, find OA a l = Some b -> 
                      (find OA a l1 = Some b \/ (find OA a l1 = None /\ find OA a l2 = Some b)))
       | None => exists a, 
                   exists a', 
                     exists b, 
                       exists b', 
                         (find OA a l1 = Some b \/ In (a, b) l2) /\ In (a',  b') l2 /\
                         eq_bool OA a a' = true /\ eq_bool OB b' b = false
     end.
Proof.
fix h 2.
intros l1 l2; case l2; clear l2; simpl.
- (* 1/2 l2 = [] *)
  repeat split.
  + exact (fun _ _ h => h).
  + intros a b H; discriminate H.
  + intros a b H; left; exact H.
- (* 1/1 l2 = _ :: _ *)
  intros [a2 b2] l2.
  case_eq (find OA a2 l1).
  + (* 1/2 find a2 l1 = Some _ *)
    intros b Hb; case_eq (eq_bool OB b2 b).
    * (* 1/3 b2 = b *)
      intro b2_eq_b; rewrite eq_bool_true_iff in b2_eq_b; subst b2.
      {
        generalize (h l1 l2); case (merge l1 l2).
        - (* 1/4 merge l1 l2 = Some l *)
          intros l H; case H; clear H.
          intros H1 H; case H; clear H.
          intros H2 H3.
          repeat split.
          + (* 1/6 *)
            assumption.
          + (* 1/5 *)
            intros a b'; case_eq (eq_bool OA a a2).
            * intros a_eq_a2 H; injection H; clear H; intro H; subst b'.
              rewrite eq_bool_true_iff in a_eq_a2; subst a2.
              {
                exists b; split.
                - apply H1; assumption.
                - rewrite eq_bool_true_iff; apply refl_equal.
              }
            * intros a_diff_a2 F'; apply H2; assumption.
          + (* 1/4 *)
            intros a b' F'; case_eq (eq_bool OA a a2).
            * intros a_eq_a2.
              rewrite eq_bool_true_iff in a_eq_a2; subst a2.
              destruct (H3 _ _ F') as [K3 | K3]; [left; assumption | ].
              rewrite (proj1 K3) in Hb; discriminate Hb.
            * intro a_diff_a2; apply H3; assumption.
        - (* 1/3 merge l1 l2 = None *)
          intros [a [a' [b1 [b1' [[F' | F'] [F'' [a_eq_a' b1_diff_b1']]]]]]];
          exists a; exists a'; exists b1; exists b1'; repeat split.
          + left; assumption.
          + right; assumption.
          + assumption.
          + assumption.
          + do 2 right; assumption.
          + right; assumption.
          + assumption.
          + assumption.
      }
    * (* 1/2 b2 <> b *)
      intro b2_diff_b.
      {
        exists a2; exists a2; exists b; exists b2; repeat split.
        - left; assumption.
        - left; reflexivity.
        - rewrite eq_bool_true_iff; apply refl_equal.
        - assumption.
      }
  + (* 1/1 find a2 l1 = None *)
    intro F.
    generalize (h ((a2, b2) :: l1) l2).
    case (merge ((a2, b2) :: l1) l2); simpl.
    * (* 1/2 merge ((a2,b2) :: l1) l2 = Some l *)
      intros l H; case H; clear H.
      intros H1 H; case H; clear H.
      intros H2 H3.
      {
        repeat split.
        - (* 1/4 *)
          intros a b F'; generalize (H1 a b); case_eq (eq_bool OA a a2).
          + intro a_eq_a2; rewrite eq_bool_true_iff in a_eq_a2; subst a2.
            rewrite F' in F; discriminate F.
          + intros _ H1a; apply H1a; assumption.
        - (* 1/3 *)
          intros a b'; case_eq (eq_bool OA a a2).
          intros a_eq_a2 H; injection H; clear H; intro H; subst b'.
          rewrite eq_bool_true_iff in a_eq_a2; subst a2.
          exists b2; split.
          + apply (H1 a b2); rewrite eq_bool_refl; apply refl_equal.
          + apply eq_bool_refl.
          + intros a_diff_a2 F'; exact (H2 a b' F').
        - (* 1/2 *)
          intros a b F'; generalize (H3 a b F'); case_eq (eq_bool OA a a2).
          + intros a_eq_a2; rewrite eq_bool_true_iff in a_eq_a2; subst a2.
            intros [F'' | FF].
            * right; split; trivial.
            * destruct FF as [FF _]; discriminate FF.
          + intros _ H; exact H.
      } 
    * (* 1/1 *)
      intros [a [a' [b1 [b1' [[F' | F'] [F'' [a_eq_a' b1_diff_b1']]]]]]].
      rewrite eq_bool_true_iff in a_eq_a'; subst a'.
      {
        case_eq (eq_bool OA a a2).
        - intros a_eq_a2; rewrite a_eq_a2 in F'; injection F'; clear F'; intro; subst b2.
          rewrite eq_bool_true_iff in a_eq_a2; subst a2.
          exists a; exists a; exists b1'; exists b1; repeat split.
          + do 2 right; assumption.
          + left; trivial.
          + apply eq_bool_refl.
          + rewrite eq_bool_sym; assumption.
        - intros a_diff_a2; rewrite a_diff_a2 in F'.
          exists a; exists a; exists b1; exists b1'; repeat split.
          + left; assumption.
          + right; assumption.
          + apply eq_bool_refl.
          + assumption.
      } 
      {
        exists a; exists a'; exists b1; exists b1'; repeat split.
        - do 2 right; assumption.
        - right; assumption.
        - assumption.
        - assumption.
      }
Qed.

Lemma merge_inv :
  forall (l1 l2 : list (A * B)), 
    (forall a1 a1' b1 c1, In (a1,b1) l1 -> In (a1',c1) l1 -> eq_bool OA a1 a1' = true -> 
                          eq_bool OB b1 c1 =true) ->
       (forall a2 a2' b2 c2, In (a2,b2) l2 -> In (a2',c2) l2 -> eq_bool OA a2 a2' = true -> 
                             eq_bool OB b2 c2 = true) ->
       match merge l1 l2 with
       | Some l => (forall a a' b c, In (a,b) l -> In (a',c) l -> eq_bool OA a a' = true -> 
                                     eq_bool OB b c = true) 
       | None => True
       end.
Proof.
fix h 2.
intros l1 l2; case l2; clear l2.
- (* 1/2 l2 = [] *)
  intros Inv1 _; exact Inv1.
- (* 1/1 l2 = _ :: _ *)
  intros p l2; case p; clear p; simpl.
  intros a2 b2 Inv1 Inv2.
  case_eq (Oset.find OA a2 l1).
  + (* 1/2 find eqA a2 l1 = Some b *)
    intros b H; case_eq (Oset.eq_bool OB b2 b); [intro b2_eq_b | intro b2_diff_b].
    * (* 1/3 b = b2 *)
      apply h.
      exact Inv1.
      {
        intros a a' b' c ab_in_l2 ac_in_l2; apply (Inv2 a a' b' c).
        - right; assumption.
        - right; assumption.
      }
    * (* b <> b2 *)
      exact I.
  + (* 1/1 find eqA a2 l1 = None *)
    intro H; apply h; simpl.
    * {
        intros a a' b' c [H1 | ab_in_l1] [H2 | ac_in_l1].
        - injection H1; injection H2; intros; subst a a' b' c.
          apply eq_bool_refl.
        - rewrite eq_bool_true_iff; intro; subst a'.
          injection H1; clear H1; do 2 intro; subst a2 b2.
          apply False_rec.
          apply (find_none _ _ _ H _ ac_in_l1).
        - rewrite eq_bool_true_iff; intro; subst a'.
          injection H2; clear H2; do 2 intro; subst a2 b2.
          apply False_rec.
          apply (find_none _ _ _ H _ ab_in_l1).
        - apply Inv1; trivial.
      }
    * do 6 intro; apply Inv2; right; assumption.
Qed.

End Sec2.

Lemma find_map :
  forall (A : Type) (OA : Rcd A) (B : Type) (f : A -> B) l a, 
    In a l -> find OA a (map (fun x => (x, f x)) l) = Some (f a).
Proof.
intros A OA B f l a; induction l as [ | a1 l]; intro Ha.
- contradiction Ha.
- simpl in Ha; simpl.
  case_eq (eq_bool OA a a1); intro Ka.
  + rewrite eq_bool_true_iff in Ka; subst a1; apply refl_equal.
  + destruct Ha as [Ha | Ha]; [subst a1; rewrite eq_bool_refl in Ka; discriminate Ka | ].
    apply IHl; assumption.
Qed.

Lemma find_some_map :
  forall (A : Type) (OA : Rcd A) (B C : Type) (f : B -> C) l a b, 
    find OA a l = Some b -> 
    find OA a (map (fun xy => match xy with (x, y) => (x, f y) end) l) = Some (f b).
Proof.
intros A OA B C f l a b; induction l as [ | [a1 b1] l]; intro Ha.
- discriminate Ha.
- simpl in Ha; simpl.
  case_eq (eq_bool OA a a1); intro Ka.
  + rewrite Ka in Ha; injection Ha; clear Ha; intro; subst b1; trivial.
  + rewrite Ka in Ha; apply IHl; assumption.
Qed.

Lemma find_none_map :
  forall (A : Type) (OA : Rcd A) (B C : Type) (f : B -> C) l a, 
    find OA a l = None ->
    find OA a (map (fun xy => match xy with (x, y) => (x, f y) end) l) = None.
Proof.
intros A OA B C f l a; induction l as [ | [a1 b1] l]; intro Ha.
- apply refl_equal.
- simpl in Ha; simpl.
  case_eq (eq_bool OA a a1); intro Ka; rewrite Ka in Ha.
  + discriminate Ha.
  + apply IHl; assumption.
Qed.

(*
Lemma find_map_3 :
  forall (A : Type) (OA : Rcd A) (B1 B2 C D : Type) 
         (f : C -> A) (g1 : C -> B1) (g2 : C -> B2) (h1 : B1 -> D) (h2 : B2 -> D) l a d, 
    (forall a1, List.In a1 l -> h1 (g1 a1) = h2 (g2 a1)) ->
    match find OA (f a) (map (fun x => (f x, g1 x)) l) with
      | Some x => h1 x 
      | None => d
    end = 
    match find OA (f a) (map (fun x => (f x, g2 x)) l) with
      | Some x => h2 x 
      | None => d
    end.
Proof.
intros A OA B1 B2 C D f g1 g2 h1 h2 l a d; 
induction l as [ | a1 l]; intro H.
- apply refl_equal.
- simpl.
  case_eq (eq_bool OA (f a) (f a1)); intro Ka.
  + apply H; left; apply refl_equal.
  + apply IHl; do 2 intro; apply H; right; assumption.
Qed.

Lemma find_map4 :
  forall (A B : Type) (OA : Rcd A) (OB : Rcd B) (C : Type) (f : A -> B) a (l : list (A * C)) l',
    (forall a1 a2, In a1 (map (@fst _ _) l) -> f a1 = f a2 -> a1 = a2) ->
    l' = map (fun x => match x with (x1, x2) => (f x1, x2) end) l ->
    find OA a l = find OB (f a) l'.
Proof.
intros A B OA OB C f a l l' H Hl'; subst l'.
induction l as [ | [a1 b1] l]; [apply refl_equal | simpl].
case_eq (eq_bool OA a a1); intro Ha.
- rewrite eq_bool_true_iff in Ha; subst a1.
  unfold eq_bool; rewrite compare_eq_refl; apply refl_equal.
- case_eq (eq_bool OB (f a) (f a1)); intro Hb.
  + rewrite eq_bool_true_iff in Hb.
    assert (Ka := H a1 a (or_introl _ (refl_equal _)) (sym_eq Hb)); subst a1.
    unfold eq_bool in Ha; rewrite compare_eq_refl in Ha; discriminate Ha.
  + apply IHl.
    do 3 intro; apply H; right; assumption.
Qed.
*)

End Oset.

Definition oeset_of_oset (A : Type) (OA : Oset.Rcd A) : Oeset.Rcd A.
Proof.
apply Oeset.mk_R with (Oset.compare OA).
- do 3 intro; apply Oset.compare_eq_trans.
- do 3 intro; apply Oset.compare_eq_lt_trans.
- do 3 intro; apply Oset.compare_lt_eq_trans.
- do 3 intro; apply Oset.compare_lt_trans.
- do 2 intro; apply Oset.compare_lt_gt.
Defined.

Lemma mem_bool_oeset_of_oset :
  forall (A : Type) (OA : Oset.Rcd A) a l,
    Oeset.mem_bool (oeset_of_oset OA) a l = Oset.mem_bool OA a l.
Proof.
intros A OA a l.
apply refl_equal.
Qed.

Section BuildPair.

Hypothesis A B : Type.
Hypothesis compareA : A -> A -> comparison.
Hypothesis compareB : B -> B -> comparison.

(** How to build a comparison function [compareAB] over the pairs [(A * B)] from a comparison function [compareA] over [A], and a comparison function [compareB] over [B]. *)
Definition compareAB (ab1 ab2 : A * B) : comparison :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) =>
     match compareA a1 a2 with
     | Eq => compareB b1 b2
     | Lt => Lt
     | Gt => Gt
     end
  end.

Lemma compareAB_unfold :
  forall ab1 ab2, compareAB ab1 ab2 =
  match ab1, ab2 with
  | (a1, b1), (a2, b2) =>
     match compareA a1 a2 with
     | Eq => compareB b1 b2
     | Lt => Lt
     | Gt => Gt
     end
  end.
Proof.
intros ab1 ab2; case ab1; case ab2; intros; apply refl_equal.
Qed.

Lemma compareAB_eq_bool_ok :
  forall a1 b1 a2 b2, 
    match compareA a1 a2 with Eq => a1 = a2 | _ => ~ a1 = a2 end ->
    match compareB b1 b2 with Eq => b1 = b2 | _ => ~ b1 = b2 end ->
    match compareAB (a1, b1) (a2, b2) with 
      | Eq => (a1, b1) = (a2, b2) 
      | _ => ~ (a1, b1) = (a2, b2) 
    end.
Proof.
intros a1 b1 a2 b2; unfold compareAB.
case (compareA a1 a2).
intro; subst a2.
case (compareB b1 b2).
intro; subst b2; apply refl_equal.
intros Hb H; apply Hb; injection H; exact (fun h => h).
intros Hb H; apply Hb; injection H; exact (fun h => h).
intros Ha _ H; apply Ha; injection H; exact (fun _ h => h).
intros Ha _ H; apply Ha; injection H; exact (fun _ h => h).
Qed.

Lemma compareAB_eq_refl : forall a b, compareA a a = Eq -> compareB b b = Eq -> compareAB (a, b) (a, b) = Eq.
Proof.
intros a b Ha Hb; unfold compareAB; rewrite Ha, Hb; apply refl_equal.
Qed.

Lemma compareAB_eq_sym : 
  forall a1 b1 a2 b2, 
    (compareA a1 a2 = Eq -> compareA a2 a1 = Eq) ->
    (compareB b1 b2 = Eq -> compareB b2 b1 = Eq) ->
    compareAB (a1, b1) (a2, b2) = Eq -> compareAB (a2, b2) (a1, b1) = Eq.
Proof.
intros a1 b1 a2 b2; unfold compareAB.
case (compareA a1 a2).
intro HA; rewrite HA; [ | apply refl_equal].
exact (fun h => h).
intros _ _ Abs; discriminate Abs.
intros _ _ Abs; discriminate Abs.
Qed.

Lemma compareAB_eq_trans : 
  forall a1 b1 a2 b2 a3 b3,
   (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
  (compareB b1 b2 = Eq -> compareB b2 b3 = Eq -> compareB b1 b3 = Eq) ->
  compareAB (a1, b1) (a2, b2) = Eq -> compareAB (a2, b2) (a3, b3) = Eq -> compareAB (a1, b1) (a3, b3) = Eq.
Proof.
intros a1 b1 a2 b2 a3 b3 HA HB; simpl.
case_eq (compareA a1 a2); intro A12; [ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
intro B23; rewrite (HA A12 A23), (HB B12 B23); apply refl_equal.
Qed.

Lemma compareAB_le_lt_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) -> 
    (compareB b1 b2 = Eq -> compareB b2 b3 = Lt -> compareB b1 b3 = Lt) -> 
    compareAB (a1, b1) (a2, b2) = Eq -> compareAB (a2, b2) (a3, b3) = Lt -> compareAB (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA HB; simpl.
case_eq (compareA a1 a2); intro A12; [ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
intro B23; rewrite (HA A12 A23), (HB B12 B23); apply refl_equal.
intros _; rewrite (KA A12 A23); apply refl_equal.
Qed.

Lemma compareAB_lt_le_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) -> 
    (compareB b1 b2 = Lt -> compareB b2 b3 = Eq -> compareB b1 b3 = Lt) -> 
    compareAB (a1, b1) (a2, b2) = Lt -> compareAB (a2, b2) (a3, b3) = Eq -> compareAB (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA HB; simpl.
case_eq (compareA a1 a2); intro A12; [ | | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ | intro Abs; discriminate Abs  | intro Abs; discriminate Abs].
intro B23; rewrite (HA A12 A23), (HB B12 B23); apply refl_equal.
intros _; case_eq (compareA a2 a3); intro A23; [ | intro Abs; discriminate Abs  | intro Abs; discriminate Abs].
intro B23; rewrite (KA A12 A23); apply refl_equal.
Qed.

Lemma compareAB_lt_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) -> 
    (compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) -> 
    (compareA a1 a2 = Lt -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) -> 
    (compareB b1 b2 = Lt -> compareB b2 b3 = Lt -> compareB b1 b3 = Lt) -> 
    compareAB (a1, b1) (a2, b2) = Lt -> compareAB (a2, b2) (a3, b3) = Lt -> compareAB (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA JA LA HB; simpl.
case_eq (compareA a1 a2); intro A12; [ | | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
intro B23; rewrite (HA A12 A23), (HB B12 B23); apply refl_equal.
intros _; rewrite (KA A12 A23); apply refl_equal.
intros _; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
intro B23; rewrite (JA A12 A23); apply refl_equal.
intros _; rewrite (LA A12 A23); apply refl_equal.
Qed.

Lemma compareAB_lt_gt : 
    forall a1 b1 a2 b2, 
    (compareA a1 a2 = CompOpp (compareA a2 a1)) ->
    (compareB b1 b2 = CompOpp (compareB b2 b1)) ->
    compareAB (a1, b1) (a2, b2) = CompOpp (compareAB (a2, b2) (a1, b1)).
Proof.
intros a1 b1 a2 b2 HA HB; unfold compareAB.
rewrite HA, HB.
case (compareA a2 a1); simpl; apply refl_equal.
Qed.

End BuildPair.


Section BuildPairLeft.

Hypothesis A B : Type.
Hypothesis compareA : A -> A -> comparison.

(** How to build a comparison function [compareAl] over the pairs [(A * B)] from a comparison function [compareA] over [A]. *)
Definition compareAl (ab1 ab2 : A * B) : comparison :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) => compareA a1 a2
  end.

Lemma compareAl_eq_refl : forall a b, compareA a a = Eq -> compareAl (a, b) (a, b) = Eq.
Proof.
intros a b Ha; unfold compareAl; rewrite Ha; apply refl_equal.
Qed.

Lemma compareAl_eq_sym :
  forall a1 b1 a2 b2,
    (compareA a1 a2 = Eq -> compareA a2 a1 = Eq) ->
    compareAl (a1, b1) (a2, b2) = Eq -> compareAl (a2, b2) (a1, b1) = Eq.
Proof.
intros a1 b1 a2 b2; unfold compareAl.
case (compareA a1 a2).
intro HA; rewrite HA; [ | apply refl_equal].
exact (fun h => h).
discriminate.
discriminate.
Qed.

Lemma compareAl_eq_trans :
  forall a1 b1 a2 b2 a3 b3,
   (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
  compareAl (a1, b1) (a2, b2) = Eq -> compareAl (a2, b2) (a3, b3) = Eq -> compareAl (a1, b1) (a3, b3) = Eq.
Proof.
intros a1 b1 a2 b2 a3 b3 HA HB; simpl.
case_eq (compareA a1 a2); intro A12; auto.
Qed.

Lemma compareAl_le_lt_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
    compareAl (a1, b1) (a2, b2) = Eq -> compareAl (a2, b2) (a3, b3) = Lt -> compareAl (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA; simpl.
case_eq (compareA a1 a2); intro A12; [ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
discriminate.
intros _; rewrite (KA A12 A23); apply refl_equal.
Qed.

Lemma compareAl_lt_le_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) ->
    compareAl (a1, b1) (a2, b2) = Lt -> compareAl (a2, b2) (a3, b3) = Eq -> compareAl (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA; simpl.
case_eq (compareA a1 a2); intro A12; [ | | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ | intro Abs; discriminate Abs  | intro Abs; discriminate Abs].
discriminate.
intros _; case_eq (compareA a2 a3); intro A23; [ | intro Abs; discriminate Abs  | intro Abs; discriminate Abs].
intro B23; rewrite (KA A12 A23); apply refl_equal.
Qed.

Lemma compareAl_lt_trans :
    forall a1 b1 a2 b2 a3 b3,
    (compareA a1 a2 = Eq -> compareA a2 a3 = Eq -> compareA a1 a3 = Eq) ->
    (compareA a1 a2 = Eq -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
    (compareA a1 a2 = Lt -> compareA a2 a3 = Eq -> compareA a1 a3 = Lt) ->
    (compareA a1 a2 = Lt -> compareA a2 a3 = Lt -> compareA a1 a3 = Lt) ->
    compareAl (a1, b1) (a2, b2) = Lt -> compareAl (a2, b2) (a3, b3) = Lt -> compareAl (a1, b1) (a3, b3) = Lt.
Proof.
intros a1 b1 a2 b2 a3 b3 HA KA JA LA; simpl.
case_eq (compareA a1 a2); intro A12; [ | | intro Abs; discriminate Abs].
intro B12; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
discriminate.
intros _; rewrite (KA A12 A23); apply refl_equal.
intros _; case_eq (compareA a2 a3); intro A23; [ |  | intro Abs; discriminate Abs].
intro B23; rewrite (JA A12 A23); apply refl_equal.
intros _; rewrite (LA A12 A23); apply refl_equal.
Qed.

Lemma compareAl_lt_gt :
    forall a1 b1 a2 b2,
    (compareA a1 a2 = CompOpp (compareA a2 a1)) ->
    compareAl (a1, b1) (a2, b2) = CompOpp (compareAl (a2, b2) (a1, b1)).
Proof.
intros a1 b1 a2 b2 HA; unfold compareAl.
rewrite HA.
case (compareA a2 a1); simpl; apply refl_equal.
Qed.

End BuildPairLeft.


Definition mk_opairs (A B : Type) (OA : Oset.Rcd A) (SB : Oset.Rcd B) : Oset.Rcd (A * B).
Proof.
split with (compareAB (Oset.compare OA) (Oset.compare SB)).
- intros [a1 b1] [a2 b2]; apply compareAB_eq_bool_ok.
  + intros; apply Oset.eq_bool_ok.
  + intros; apply Oset.eq_bool_ok.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAB_lt_trans.
  + apply Oset.compare_eq_trans.
  + apply Oset.compare_eq_lt_trans.
  + apply Oset.compare_lt_eq_trans.
  + apply Oset.compare_lt_trans.
  + apply Oset.compare_lt_trans.
- intros [a1 b1] [a2 b2]; apply compareAB_lt_gt.
  + apply Oset.compare_lt_gt.
  + apply Oset.compare_lt_gt.
Defined.

Definition mk_oepairs (A B : Type) (OA : Oeset.Rcd A) (SB : Oeset.Rcd B) : Oeset.Rcd (A * B).
Proof.
split with (compareAB (Oeset.compare OA) (Oeset.compare SB)).
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAB_eq_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_eq_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAB_le_lt_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_eq_lt_trans.
  + apply Oeset.compare_eq_lt_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAB_lt_le_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_lt_eq_trans.
  + apply Oeset.compare_lt_eq_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAB_lt_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_eq_lt_trans.
  + apply Oeset.compare_lt_eq_trans.
  + apply Oeset.compare_lt_trans.
  + apply Oeset.compare_lt_trans.
- intros [a1 b1] [a2 b2]; apply compareAB_lt_gt.
  + apply Oeset.compare_lt_gt.
  + apply Oeset.compare_lt_gt.
Defined.

Definition mk_oepairsleft (A B : Type) (OA : Oeset.Rcd A) : Oeset.Rcd (A * B).
Proof.
split with (compareAl (Oeset.compare OA)).
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAl_eq_trans.
  apply Oeset.compare_eq_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAl_le_lt_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_eq_lt_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAl_lt_le_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_lt_eq_trans.
- intros [a1 b1] [a2 b2] [a3 b3]; apply compareAl_lt_trans.
  + apply Oeset.compare_eq_trans.
  + apply Oeset.compare_eq_lt_trans.
  + apply Oeset.compare_lt_eq_trans.
  + apply Oeset.compare_lt_trans.
- intros [a1 b1] [a2 b2]; apply compareAl_lt_gt.
  apply Oeset.compare_lt_gt.
Defined.


Definition mk_olists (A : Type) (OA : Oset.Rcd A) : Oset.Rcd (list A).
Proof.
split with (comparelA (Oset.compare OA)).
- intros l1 l2; apply (comparelA_eq_bool_ok (Oset.compare OA) l1 l2).
  intros; apply Oset.eq_bool_ok.
- intros l1 l2 l3; apply comparelA_lt_trans.
  + do 6 intro; apply Oset.compare_eq_trans.
  + do 6 intro; apply Oset.compare_eq_lt_trans.
  + do 6 intro; apply Oset.compare_lt_eq_trans.
  + do 6 intro; apply Oset.compare_lt_trans.
- intros l1 l2; apply comparelA_lt_gt.
  do 4 intro; apply Oset.compare_lt_gt.
Defined.

Definition mk_oelists (A : Type) (OA : Oeset.Rcd A) : Oeset.Rcd (list A).
Proof.
split with (comparelA (Oeset.compare OA)).
- intros l1 l2 l3; apply comparelA_eq_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
- intros l1 l2 l3; apply comparelA_le_lt_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_eq_lt_trans.
- intros l1 l2 l3; apply comparelA_lt_le_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_lt_eq_trans.
- intros l1 l2 l3; apply comparelA_lt_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_eq_lt_trans.
  + do 6 intro; apply Oeset.compare_lt_eq_trans.
  + do 6 intro; apply Oeset.compare_lt_trans.
- intros l1 l2; apply comparelA_lt_gt.
  do 4 intro; apply Oeset.compare_lt_gt.
Defined.

Definition mk_ooption (A : Type) (OA : Oset.Rcd A) : Oset.Rcd (option A).
Proof.
split with (compareoA (Oset.compare OA)).
- intros a1 a2; unfold compareoA, option_to_list.
  destruct a1 as [a1 | ]; destruct a2 as [a2 | ]; simpl; try discriminate; trivial.
  case_eq (Oset.compare OA a1 a2); intro Ha.
  + apply f_equal; assert (H := Oset.eq_bool_ok OA a1 a2); rewrite Ha in H; apply H.
  + intro H; injection H; clear H; intro H; rewrite H, Oset.compare_eq_refl in Ha;
      discriminate Ha.
  + intro H; injection H; clear H; intro H; rewrite H, Oset.compare_eq_refl in Ha;
      discriminate Ha.
- do 3 intro; unfold compareoA, option_to_list; apply comparelA_lt_trans.
  + do 6 intro; apply Oset.compare_eq_trans.
  + do 6 intro; apply Oset.compare_eq_lt_trans.
  + do 6 intro; apply Oset.compare_lt_eq_trans.
  + do 6 intro; apply Oset.compare_lt_trans.
- do 2 intro; unfold compareoA, option_to_list; apply comparelA_lt_gt.
  do 4 intro; apply Oset.compare_lt_gt.
Defined.

Definition mk_oeoption (A : Type) (OA : Oeset.Rcd A) : Oeset.Rcd (option A).
Proof.
split with (compareoA (Oeset.compare OA)).
- do 3 intro; unfold compareoA, option_to_list; apply comparelA_eq_trans.
  do 6 intro; apply Oeset.compare_eq_trans.
- do 3 intro; unfold compareoA, option_to_list; apply comparelA_le_lt_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_eq_lt_trans.
- do 3 intro; unfold compareoA, option_to_list; apply comparelA_lt_le_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_lt_eq_trans.
- do 3 intro; unfold compareoA, option_to_list; apply comparelA_lt_trans.
  + do 6 intro; apply Oeset.compare_eq_trans.
  + do 6 intro; apply Oeset.compare_eq_lt_trans.
  + do 6 intro; apply Oeset.compare_lt_eq_trans.
  + do 6 intro; apply Oeset.compare_lt_trans.
- do 2 intro; unfold compareoA, option_to_list; apply comparelA_lt_gt.
  do 4 intro; apply Oeset.compare_lt_gt.
Defined.


Section Group.

Hypothesis (A B : Type).
Hypothesis OA : Oeset.Rcd A.
Hypothesis (proj : B -> A).

Fixpoint group x ls :=
  match ls with
  | nil => (proj x, x :: nil) :: nil
  | (k, lk) :: ls =>
    match Oeset.compare OA k (proj x) with
    | Eq => (k, x :: lk) :: ls
    | _ => (k, lk) :: group x ls
    end
  end.

Lemma group_unfold :
  forall x ls,
    group x ls =
  match ls with
  | nil => (proj x, x :: nil) :: nil
  | (k, lk) :: ls =>
    match Oeset.compare OA k (proj x) with
    | Eq => (k, x :: lk) :: ls
    | _ => (k, lk) :: group x ls
    end
  end.
Proof.
intros x ls.
case_eq ls; intros; apply refl_equal.
Qed.

Lemma keys_of_group : 
  forall x ls,
    map fst (group x ls) =
    if Oeset.mem_bool OA (proj x) (map fst ls) then map fst ls else  map fst ls ++ (proj x) :: nil.
Proof.
intros x ls; induction ls as [ | [k1 lk1] ls]; simpl; [apply refl_equal | ].
- unfold Oeset.eq_bool; rewrite Oeset.compare_lt_gt.
  case (Oeset.compare OA (proj x) k1); simpl; trivial.
  + destruct (Oeset.mem_bool OA (proj x) (map fst ls)); rewrite IHls; trivial.
  + destruct (Oeset.mem_bool OA (proj x) (map fst ls)); rewrite IHls; trivial.
Qed.

Lemma all_diff_keys_of_group :
  forall x lg, all_diff_bool (Oeset.eq_bool OA) (map fst lg) = true ->
               all_diff_bool (Oeset.eq_bool OA) (map fst (group x lg)) = true.
Proof.
intros x lg H.
rewrite keys_of_group.
case_eq (Oeset.mem_bool OA (proj x) (map fst lg)); intro K; [assumption | ].
set (lk := (map fst lg)) in *; clearbody lk; clear lg.
induction lk as [ | k1 lk]; simpl; trivial.
rewrite all_diff_bool_unfold, Bool.andb_true_iff, negb_true_iff in H.
rewrite Oeset.mem_bool_unfold, Bool.orb_false_iff in K.
assert (IH := IHlk (proj2 H) (proj2 K)).
rewrite IH, Bool.andb_true_r.
rewrite Mem.mem_bool_app; simpl.
rewrite (proj1 H), Bool.orb_false_l, Bool.orb_false_r.
unfold Oeset.eq_bool.
rewrite Oeset.compare_lt_gt.
destruct (Oeset.compare OA (proj x) k1).
- destruct K as [K _]; discriminate K.
- simpl; destruct (lk ++ proj x :: nil); trivial.
- simpl; destruct (lk ++ proj x :: nil); trivial.
Qed.

Lemma group_app :
  forall x ls1 ls2,
    group x (ls1 ++ ls2) =
    if Oeset.mem_bool OA (proj x) (map fst ls1) 
    then (group x ls1) ++ ls2 else  ls1 ++ (group x ls2).
Proof.
intros x ls1; induction ls1 as [ | [k1 lk1] ls1]; intros ls2; simpl; [trivial | ].
assert (IH := IHls1 ls2).
unfold Oeset.eq_bool.
rewrite (Oeset.compare_lt_gt OA (proj x)).
case (Oeset.compare OA k1 (proj x)); simpl; [trivial | | ].
+ destruct (Oeset.mem_bool OA (proj x) (map fst ls1)); rewrite IH; trivial.
+ destruct (Oeset.mem_bool OA (proj x) (map fst ls1)); rewrite IH; trivial.
Qed.

Lemma insert_in_groups :
  forall t lg, all_diff_bool (Oeset.eq_bool OA) (map fst lg) = true ->
               group t lg =
               if Oeset.mem_bool OA (proj t) (map fst lg)
               then map (fun x => match x with 
                                    (k, lk) => 
                                    if Oeset.eq_bool OA (proj t) k
                                    then (k, t :: lk)
                                    else (k, lk)
                                  end) lg
               else lg ++ (proj t, t :: nil) :: nil.
Proof.
intros t lg; induction lg as [ | [k1 lk1] lg]; intros H.
- apply refl_equal.
- rewrite group_unfold, (map_unfold _ (_ :: _)), (Oeset.mem_bool_unfold _ _ (_ :: _)).
  simpl fst.
  rewrite Oeset.compare_lt_gt; simpl; unfold Oeset.eq_bool.
  case_eq (Oeset.compare OA (proj t) k1); intro Ht; simpl.
  + apply f_equal.
    assert (Hg : forall g, In g lg -> Oeset.eq_bool OA (proj t) (fst g) = false).
    {
      intros [k lk] Hk; simpl.
      simpl map in H; rewrite all_diff_bool_unfold, Bool.andb_true_iff in H.
      rewrite negb_true_iff in H.
      unfold Oeset.eq_bool; rewrite (Oeset.compare_eq_1 _ _ _ _ Ht).
      case_eq (Oeset.compare OA k1 k); intro Kk; trivial.
      rewrite <- (proj1 H); apply sym_eq.
      rewrite (Oeset.mem_bool_true_iff OA k1 (map fst lg)).
      exists k; split; [assumption | ].
      rewrite in_map_iff; eexists; split; [ | apply Hk]; trivial.
      }
    clear IHlg H; induction lg as [ | [k lk] lg]; [trivial | ].
    simpl; rewrite <- IHlg.
    * assert (H1 := Hg _ (or_introl _ (refl_equal _))); unfold Oeset.eq_bool in H1; simpl in H1.
      destruct (Oeset.compare OA (proj t) k); trivial.
      discriminate H1.
    * intros; apply Hg; right; trivial.
  + rewrite IHlg.
    * case_eq (Oeset.mem_bool OA (proj t) (map fst lg)); intro Kt; apply refl_equal.
    * simpl map in H; rewrite all_diff_bool_unfold, Bool.andb_true_iff in H.
      apply (proj2 H).
  + rewrite IHlg.
    * case_eq (Oeset.mem_bool OA (proj t) (map fst lg)); intro Kt; apply refl_equal.
    * simpl map in H; rewrite all_diff_bool_unfold, Bool.andb_true_iff in H.
      apply (proj2 H).
Qed.

Lemma insert_in_groups_weak :
  forall t lg, Oeset.mem_bool OA (proj t) (map fst lg) = false ->
               group t lg = lg ++ (proj t, t :: nil) :: nil.
Proof.
intros t lg; induction lg as [ | [k1 lk1] lg]; intros H.
- apply refl_equal.
- rewrite (map_unfold _ (_ :: _)), (Oeset.mem_bool_unfold _ _ (_ :: _)), Bool.orb_false_iff in H.
  destruct H as [H1 H2]; simpl fst in H1.
  rewrite group_unfold, Oeset.compare_lt_gt.
  destruct (Oeset.compare OA (proj t) k1); try discriminate H1; simpl;
    rewrite (IHlg H2); trivial.
Qed.

Lemma insert_in_one_group :
  forall t lg, Oeset.mem_bool OA (proj t) (map fst lg) = true ->
               exists lg1, exists lg2, exists k, exists lk,
                     lg = lg1 ++ (k, lk) :: lg2 /\
                     Oeset.mem_bool OA (proj t) (map fst lg1) = false /\
                     Oeset.eq_bool OA (proj t) k = true /\
                     group t lg = lg1 ++ (k, t :: lk) :: lg2.
Proof.
intros t lg Ht.
induction lg as [ | [k1 lk1] lg]; [discriminate Ht | ].
rewrite map_unfold, Oeset.mem_bool_unfold in Ht; simpl fst in Ht.
case_eq (Oeset.compare OA (proj t) k1); intro Kt.
- exists nil; exists lg; exists k1; exists lk1.
  split; [apply refl_equal | ].
  split; [apply refl_equal | ].
  split; [unfold Oeset.eq_bool; rewrite Kt; trivial | ].
  rewrite group_unfold, Oeset.compare_lt_gt, Kt; apply refl_equal.
- rewrite Kt in Ht; simpl in Ht.
  destruct (IHlg Ht) as [lg1 [lg2 [k [lk [H1 [H2 [H3 H4]]]]]]].
  exists ((k1, lk1) :: lg1); exists lg2; exists k; exists lk.
  split; [rewrite H1; simpl; apply refl_equal | ].
  split; [simpl; unfold Oeset.eq_bool; rewrite Kt, H2; trivial | ].
  split; [assumption | ].
  rewrite group_unfold, Oeset.compare_lt_gt, Kt, H1.
  simpl; rewrite H1 in H4; rewrite H4; trivial.
- rewrite Kt in Ht; simpl in Ht.
  destruct (IHlg Ht) as [lg1 [lg2 [k [lk [H1 [H2 [H3 H4]]]]]]].
  exists ((k1, lk1) :: lg1); exists lg2; exists k; exists lk.
  split; [rewrite H1; simpl; apply refl_equal | ].
  split; [simpl; unfold Oeset.eq_bool; rewrite Kt, H2; trivial | ].
  split; [assumption | ].
  rewrite group_unfold, Oeset.compare_lt_gt, Kt, H1.
  simpl; rewrite H1 in H4; rewrite H4; trivial.
Qed.

Lemma insert_in_one_group_alt :
  forall t lg1 lg2 k lk,  Oeset.mem_bool OA (proj t) (map fst lg1) = false ->
                          Oeset.eq_bool OA (proj t) k = true ->
                          group t (lg1 ++ (k, lk) :: lg2) = lg1 ++ (k, t :: lk) :: lg2.
Proof.
intros t lg1; induction lg1 as [ | [k1 lk1] lg1]; intros lg2 k lk H1 H2. 
- unfold Oeset.eq_bool in H2; rewrite compare_eq_true in H2; simpl.
  rewrite Oeset.compare_lt_gt, H2; apply refl_equal.
- rewrite map_unfold, Oeset.mem_bool_unfold, Bool.orb_false_iff in H1.
  destruct H1 as [H1 K1]; simpl in H1; simpl.
  rewrite Oeset.compare_lt_gt.
  destruct (Oeset.compare OA (proj t) k1); [discriminate H1 | | ]; simpl; 
    apply f_equal; apply IHlg1; trivial.
Qed.

Lemma group_eq_1 : 
  forall (OB : Oeset.Rcd B),
    (forall b1 b2, Oeset.compare OB b1 b2 = Eq -> Oeset.compare OA (proj b1) (proj b2) = Eq) ->
    forall x1 x2 lg, 
    Oeset.compare OB x1 x2 = Eq ->
    comparelA (compareAB (Oeset.compare OA) (comparelA (Oeset.compare OB)))
              (group x1 lg) (group x2 lg) = Eq.
Proof.
intros OB proj_eq x1 x2 lg Hx.
induction lg as [ | [k1 lk1] lg]; simpl.
- rewrite Hx, (proj_eq _ _ Hx); trivial.
- rewrite <- (Oeset.compare_eq_2 _ _ _ _ (proj_eq _ _ Hx)).
  case (Oeset.compare OA k1 (proj x1)).
  + simpl.
    rewrite Oeset.compare_eq_refl, Hx.
    rewrite 2 comparelA_eq_refl; trivial.
    * intros [k lk] _; apply compareAB_eq_refl; [apply Oeset.compare_eq_refl | ].
      apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl.
    * intros; apply Oeset.compare_eq_refl.
  + simpl; rewrite Oeset.compare_eq_refl, comparelA_eq_refl;
      [ | intros; apply Oeset.compare_eq_refl].
    apply IHlg.
  + simpl; rewrite Oeset.compare_eq_refl, comparelA_eq_refl;
      [ | intros; apply Oeset.compare_eq_refl].
    apply IHlg.
Qed.

End Group.

Lemma group_eq_0 :
  forall (A B : Type) (OA : Oeset.Rcd A) (proj1 proj2 : B -> A), 
    (forall t, proj1 t = proj2 t) ->
    forall x s, group OA proj1 x s = group OA proj2 x s.
Proof.
intros A B OA proj1 proj2 H x s; induction s as [ | [k1 lk1] s]; simpl.
- rewrite H; trivial.
- rewrite H, IHs; trivial.
Qed.

Lemma comparelA_Eq :
  forall (A : Type) (OA : Oeset.Rcd A),
  let ltA := fun x y => Oeset.compare OA x y = Lt in
  forall l1 l2, (forall e, Oeset.mem_bool OA e l1 = Oeset.mem_bool OA e l2) ->
    Sorted ltA l1 -> Sorted ltA l2 ->
    comparelA (Oeset.compare OA) l1 l2 = Eq.
Proof.
intros A OA ltA l1; induction l1 as [ | a1 l1]; intros [ | a2 l2].
- intros _ _ _; apply refl_equal.
- intros H; apply False_rec; generalize (H a2); simpl; unfold Oeset.eq_bool.
  rewrite Oeset.compare_eq_refl; discriminate.
- intros H; apply False_rec; generalize (H a1); simpl; unfold Oeset.eq_bool.
  rewrite Oeset.compare_eq_refl; discriminate.
- intros H Sl1 Sl2; simpl.
  assert (Aux : Oeset.compare OA a1 a2 = Eq).
  {
    generalize (H a1) (H a2); simpl; unfold Oeset.eq_bool; rewrite 2 Oeset.compare_eq_refl; simpl.
    case_eq (Oeset.compare OA a1 a2); intro Ha12; simpl.
    - exact (fun _ _ => refl_equal _).
    - rewrite Oeset.compare_lt_gt, Ha12; simpl.
      intros H1 H2; generalize (sym_eq H1); clear H1; intro H1.
      rewrite Oeset.mem_bool_true_iff in H1.
      destruct H1 as [e' [H1 J1]].
      generalize (Sorted_extends (Oeset.compare_lt_trans OA) Sl2).
      rewrite Forall_forall.
      intro L; assert (L1 := L e' J1).
      assert (Abs : Oeset.compare OA a1 a1 = Lt).
      {
        apply Oeset.compare_lt_trans with a2; [assumption | ].
        apply Oeset.compare_lt_eq_trans with e'; [assumption | ].
        rewrite Oeset.compare_lt_gt, H1; apply refl_equal.
      }
      generalize (Oeset.compare_lt_gt OA a1 a1); rewrite Abs; discriminate.
    - rewrite Oeset.compare_lt_gt, Ha12; simpl.
      intros H1 H2; generalize (sym_eq H1); clear H1; intro H1.
      rewrite Oeset.mem_bool_true_iff in H2.
      destruct H2 as [e' [H2 J2]].
      generalize (Sorted_extends (Oeset.compare_lt_trans OA) Sl1).
      rewrite Forall_forall.
      intro L; assert (L2 := L e' J2).
      assert (Abs : Oeset.compare OA a2 a2 = Lt).
      {
        rewrite Oeset.compare_lt_gt, CompOpp_iff in Ha12; simpl in Ha12.
        apply Oeset.compare_lt_trans with a1; [assumption | ].
        apply Oeset.compare_lt_eq_trans with e'; [assumption | ].
        simpl in H2; rewrite Oeset.compare_lt_gt, H2; apply refl_equal.
      }
      generalize (Oeset.compare_lt_gt OA a2 a2); rewrite Abs; discriminate.
  }
  rewrite Aux; apply IHl1.
  + intros e; generalize (H e); simpl.
    case_eq (Oeset.compare OA e a1); intro He.
    * intros _.
      {
        case_eq (Oeset.mem_bool OA e l1); intro H1.
        - apply False_rec.
          rewrite (Oeset.mem_bool_eq_1 _ _ _ _ He), Oeset.mem_bool_true_iff in H1.
          destruct H1 as [e' [H1 J1]].
          generalize (Sorted_extends (Oeset.compare_lt_trans OA) Sl1).
          rewrite Forall_forall.
          intro L; assert (L1 := L e' J1).
          assert (Abs : Oeset.compare OA a1 a1 = Lt).
          {
            apply Oeset.compare_lt_eq_trans with e'; [assumption | ].
            simpl in H1; rewrite Oeset.compare_lt_gt, H1; apply refl_equal.
          }
          generalize (Oeset.compare_lt_gt OA a1 a1); rewrite Abs; discriminate.
        - case_eq (Oeset.mem_bool OA e l2); intro H2.
          + apply False_rec.
            rewrite (Oeset.mem_bool_eq_1 _ _ _ _ He), Oeset.mem_bool_true_iff in H2.
            destruct H2 as [e' [H2 J2]].
            generalize (Sorted_extends (Oeset.compare_lt_trans OA) Sl2).
            rewrite Forall_forall.
            intro L; assert (L2 := L e' J2).
            assert (Abs : Oeset.compare OA a2 a2 = Lt).
            {
              apply Oeset.compare_lt_eq_trans with e'; [assumption | ].
              refine (Oeset.compare_eq_trans _ _ _ _ _ Aux).
              rewrite Oeset.compare_lt_gt, H2; apply refl_equal.
            }
            rewrite Oeset.compare_eq_refl in Abs; discriminate Abs.
          + apply refl_equal.
      }
    * unfold Oeset.eq_bool; rewrite He, (Oeset.compare_lt_eq_trans _ _ _ _ He Aux). 
      exact (fun h => h).
    * unfold Oeset.eq_bool; rewrite He, (Oeset.compare_gt_eq_trans _ _ _ _ He Aux). 
      exact (fun h => h).
  + inversion Sl1; assumption.
  + inversion Sl2; assumption.
Qed.


Lemma comparelA_fold_left_eq
      (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B)
      (f : A -> B -> A)
      (Hf : forall x1 x2 y1 y2, Oeset.compare OA x1 x2 = Eq -> Oeset.compare OB y1 y2 = Eq -> Oeset.compare OA (f x1 y1) (f x2 y2) = Eq)
      l1 l2 acc
      (Hl : comparelA (Oeset.compare OB) l1 l2 = Eq) :
  Oeset.compare OA (fold_left f l1 acc) (fold_left f l2 acc) = Eq.
Proof.
  apply (Oeset.compare_eq_trans _ _ (fold_right (fun b a => f a b) acc (rev l1))).
  - apply (fold_left_rev_right_eq _ OB).
    + intros; now apply Hf.
    + now apply Oeset.compare_eq_refl.
    + rewrite rev_involutive. apply comparelA_eq_refl. intros; now apply Oeset.compare_eq_refl.
  - apply Oeset.compare_eq_sym. apply (fold_left_rev_right_eq _ OB).
    + intros; now apply Hf.
    + now apply Oeset.compare_eq_refl.
    + rewrite rev_involutive. now apply (Oeset.compare_eq_sym (mk_oelists OB)).
Qed.


    (** Some concrete ordered sets. *)
Require Import Arith NArith.

Definition Ounit : Oset.Rcd unit.
split with (fun _ _ => Eq).
- intros a1 a2; destruct a1; destruct a2; apply refl_equal.
- intros; discriminate.
- intros; apply refl_equal.
Defined.

Definition bool_compare b1 b2 :=
  match b1, b2 with
    | true, true => Eq
    | true, false => Lt
    | false, true => Gt
    | false, false => Eq
  end.

Definition Obool : Oset.Rcd bool.
split with bool_compare.
- intros [ | ] [ | ]; simpl; trivial; discriminate.
- intros [ | ] [ | ] [ | ]; simpl; trivial; discriminate.
- intros [ | ] [ | ]; simpl; trivial.
Defined.

Definition Onat : Oset.Rcd nat.
split with nat_compare.
(* 1/3 *)
intros a1 a2; case_eq (nat_compare a1 a2); intro H12.
rewrite (nat_compare_eq _ _ H12); apply refl_equal.
rewrite <- nat_compare_lt in H12.
intro; subst a2; apply False_rec; apply (lt_irrefl _ H12).
rewrite <- nat_compare_gt in H12.
intro; subst a2; apply False_rec; apply (lt_irrefl _ H12).
(* 1/2 *)
intros n1 n2 n3.
case_eq (nat_compare n1 n2); intro H12; [ intro Abs; discriminate Abs | | intro Abs; discriminate Abs].
intros _; case_eq (nat_compare n2 n3); intro H23; [ intro Abs; discriminate Abs | | intro Abs; discriminate Abs].
intros _.
rewrite <- nat_compare_lt in H12, H23.
rewrite <- nat_compare_lt; apply lt_trans with n2; assumption.
(* 1/1 *)
intros a1 a2; case_eq (nat_compare a1 a2); intro H12.
rewrite nat_compare_eq_iff in H12; subst a2.
generalize (refl_equal a1); rewrite <- nat_compare_eq_iff; intro Hn; rewrite Hn; apply refl_equal.
rewrite <- nat_compare_lt in H12.
assert (H21 : a2 > a1); [apply H12 | ].
rewrite nat_compare_gt in H21; rewrite H21; apply refl_equal.
rewrite <- nat_compare_gt in H12.
assert (H21 : a2 < a1); [apply H12 | ].
rewrite nat_compare_lt in H21; rewrite H21; apply refl_equal.
Defined.

Definition ON : Oset.Rcd N.
split with Ncompare.
- (* 1/3 *)
  intros a1 a2; case_eq (Ncompare a1 a2); intro H12.
  + rewrite (Ncompare_Eq_eq _ _ H12); apply refl_equal.
  + intro H; subst a2; rewrite Ncompare_refl in H12; discriminate H12.
  + intro H; subst a2; rewrite Ncompare_refl in H12; discriminate H12.
- (* 1/2 *)
  intros n1 n2 n3; rewrite 3 nat_of_Ncompare, <- 3 nat_compare_lt; apply lt_trans.
- (* 1/1 *)
  intros n1 n2; case_eq (Ncompare n1 n2); intro A12; rewrite <- Ncompare_antisym, A12; simpl; apply refl_equal.
Defined.

Require compcert.lib.Integers.
Section ptrofs. 
  
  Import compcert.lib.Integers.

  Definition ptrofs_compare (x y : ptrofs) : Datatypes.comparison :=
    if Ptrofs.eq_dec x y then Eq else if Ptrofs.lt x y then Lt else Gt.

  Lemma ptrofs_compare_lt x y : ptrofs_compare x y = Lt <-> Ptrofs.lt x y = true.
    unfold ptrofs_compare; destruct Ptrofs.eq_dec; case_eq (Ptrofs.lt x y); intro h; try easy.
    subst x. unfold Ptrofs.lt, Coqlib.zlt in h.
    destruct ZArith_dec.Z_lt_dec. apply BinInt.Z.lt_irrefl in l. easy. easy.
  Qed.

  Lemma ptrofs_compare_eq x y : ptrofs_compare x y = Eq <-> x = y.
    unfold ptrofs_compare; destruct Ptrofs.eq_dec; case_eq (Ptrofs.lt x y); easy.
  Qed.

  Definition Optrofs : Oset.Rcd ptrofs.
    split with ptrofs_compare.
    - intros a1 a2; case_eq (ptrofs_compare a1 a2); rewrite <- ptrofs_compare_eq; try easy; intros h ne; rewrite h in ne; easy.
    - intros. rewrite ptrofs_compare_lt in *. unfold Ptrofs.lt in *.
      destruct Coqlib.zlt, Coqlib.zlt, Coqlib.zlt; try easy.
      pose proof (BinInt.Z.lt_trans _ _ _ l l0). easy.
    - intros. 
      unfold ptrofs_compare. destruct Ptrofs.eq_dec, Ptrofs.eq_dec; try easy.
      symmetry in e. easy. symmetry in e. easy.
      case_eq (Ptrofs.lt a1 a2); intro h; case_eq (Ptrofs.lt a2 a1); intro g.
      rewrite Ptrofs.lt_not in g. apply andb_prop in g. rewrite negb_true_iff in g. destruct g.
      rewrite h in H. easy. easy. easy. rewrite Ptrofs.lt_not, andb_false_iff in g.
      destruct g; rewrite negb_false_iff in H. rewrite h in H. easy. apply Ptrofs.eq_false in n. rewrite n in H. easy.
  Defined.

End ptrofs.

Require Import ZArith.

Definition OZ : Oset.Rcd Z.
split with Zcompare.
(* 1/3 *)
intros a1 a2; case_eq (Zcompare a1 a2); intro H12.
rewrite (Zcompare_Eq_eq _ _ H12); apply refl_equal.
intro H; subst a2; rewrite Zcompare_refl in H12; discriminate H12.
intro H; subst a2; rewrite Zcompare_refl in H12; discriminate H12.
(* 1/2 *)
intros n1 n2 n3 H12 H23; apply (Zcompare_Lt_trans _ _ _ H12 H23).
(* 1/1 *)
intros n1 n2; case_eq (Zcompare n1 n2); intro H12.
rewrite (Zcompare_Eq_eq _ _ H12), Zcompare_refl; apply refl_equal.
rewrite <- Zcompare_Gt_Lt_antisym in H12; rewrite H12; apply refl_equal.
rewrite Zcompare_Gt_Lt_antisym in H12; rewrite H12; apply refl_equal.
Defined.

Section NEmbedding.

Hypothesis A : Type.
Hypothesis N_of_A : A -> N.
Hypothesis N_of_A_inj : forall a1 a2, N_of_A a1 = N_of_A a2 -> a1 = a2.

Definition Oemb : Oset.Rcd A.
set (compare := fun a1 a2 => Ncompare (N_of_A a1) (N_of_A a2)).
split with compare.
(* 1/3 *)
intros a1 a2; unfold compare; simpl.
generalize (Ncompare_eq_correct (N_of_A a1) (N_of_A a2)).
case (Ncompare (N_of_A a1) (N_of_A a2)); intro H.
apply N_of_A_inj; rewrite <- H; apply refl_equal.
intro Abs; subst a2; generalize (refl_equal (N_of_A a1)); rewrite <- H; discriminate.
intro Abs; subst a2; generalize (refl_equal (N_of_A a1)); rewrite <- H; discriminate.
(* 1/2 *)
intros n1 n2 n3; unfold compare; simpl; rewrite 3 nat_of_Ncompare, <- 3 nat_compare_lt; apply lt_trans.
(* 1/1 *)
intros n1 n2; unfold compare; simpl.
case_eq (Ncompare (N_of_A n1) (N_of_A n2)); intro A12;
rewrite <- Ncompare_antisym, A12; apply refl_equal.
Defined.

End NEmbedding.

Fixpoint string_compare s1 s2 : comparison :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _ => Lt
  | String _ _, EmptyString => Gt
  | String a1 s1, String a2 s2 =>
       match Ncompare (N_of_ascii a1) (N_of_ascii a2) with
       | Eq => string_compare s1 s2
       | Lt => Lt
       | Gt => Gt 
       end
  end.

Definition Ostring : Oset.Rcd string.
split with string_compare.
(* 1/3 *)
intro s1; induction s1 as [ | a1 s1]; intros [ | a2 s2]; simpl.
apply refl_equal.
discriminate.
discriminate.
case_eq (Ncompare (N_of_ascii a1) (N_of_ascii a2)); intro A12.
generalize (IHs1 s2); case (string_compare s1 s2); intro S12.
apply f_equal2; [ | apply S12].
rewrite <- (ascii_N_embedding a1), <- (ascii_N_embedding a2); apply f_equal; apply Ncompare_Eq_eq; apply A12.
intro H12; apply S12; injection H12; intros; subst; apply refl_equal.
intro H12; apply S12; injection H12; intros; subst; apply refl_equal.
intro H12; injection H12; intros; subst; rewrite Ncompare_refl in A12; discriminate A12.
intro H12; injection H12; intros; subst; rewrite Ncompare_refl in A12; discriminate A12.
(* 1/2 *)
intro s1; induction s1 as [ | a1 s1]; intros [ | a2 s2]; simpl.
intros s3 Abs; discriminate Abs.
intros [ | a3 s3].
intros _ Abs; discriminate Abs.
exact (fun _ _ => refl_equal _).
intros s3 Abs; discriminate Abs.
intros [ | a3 s3].
intros _ Abs; discriminate Abs.
case_eq (Ncompare (N_of_ascii a1) (N_of_ascii a2)); intro A12.
rewrite (Ncompare_Eq_eq _ _ A12).
intro S12; case_eq (Ncompare (N_of_ascii a2) (N_of_ascii a3)); intro A23.
apply IHs1; assumption.
exact (fun h => h).
exact (fun h => h).
intros _; case_eq (Ncompare (N_of_ascii a2) (N_of_ascii a3)); intro A23.
rewrite <- (Ncompare_Eq_eq _ _ A23), A12.
exact (fun _ => refl_equal _).
rewrite nat_of_Ncompare, <- nat_compare_lt in A12.
rewrite nat_of_Ncompare, <- nat_compare_lt in A23.
assert (A13 := lt_trans _ _ _ A12 A23).
rewrite nat_compare_lt, <- nat_of_Ncompare in A13; rewrite A13.
exact (fun _ => refl_equal _).
intros Abs; discriminate Abs.
intros Abs; discriminate Abs.
(* 1/1 *)
intro s1; induction s1 as [ | a1 s1]; intros [ | a2 s2]; simpl.
apply refl_equal.
apply refl_equal.
apply refl_equal.
case_eq (Ncompare (N_of_ascii a1) (N_of_ascii a2)); intro A12;
rewrite <- Ncompare_antisym, A12; simpl.
apply IHs1.
apply refl_equal.
apply refl_equal.
Defined.

Ltac oset_compare_tac :=
  match goal with
    | |- Oset.compare ?OS ?a1 ?a2 = Eq -> 
         Oset.compare ?OS ?a2 ?a3 = Eq ->
         Oset.compare ?OS ?a1 ?a3 = Eq =>
      apply Oset.compare_eq_trans
    | |- Oset.compare ?OS ?a1 ?a2 = Eq -> 
         Oset.compare ?OS ?a2 ?a3 = Lt ->
         Oset.compare ?OS ?a1 ?a3 = Lt =>
      apply Oset.compare_eq_lt_trans
    | |- Oset.compare ?OS ?a1 ?a2 = Lt -> 
         Oset.compare ?OS ?a2 ?a3 = Eq ->
         Oset.compare ?OS ?a1 ?a3 = Lt =>
      apply Oset.compare_lt_eq_trans
    | |- Oset.compare ?OS ?a1 ?a2 = Lt -> 
         Oset.compare ?OS ?a2 ?a3 = Lt ->
         Oset.compare ?OS ?a1 ?a3 = Lt =>
      apply Oset.compare_lt_trans
    | |- Oset.compare ?OS ?a1 ?a2 = CompOpp (Oset.compare ?OS ?a2 ?a1) =>
      apply Oset.compare_lt_gt

    | H : Oset.eq_bool ?OS ?x1 ?x2 = true |- ?x1 = ?x2  =>
      rewrite Oset.eq_bool_true_iff in H; apply H
    | H : match Oset.compare ?OS ?x1 ?x2 with
           | Eq => true
           | Lt => false
           | Gt => false
         end = true |- ?x1 = ?x2  =>
      revert H;
        generalize (Oset.eq_bool_ok OS x1 x2);
        case (Oset.compare OS x1 x2);
        [ exact (fun h _ => h) 
        | let Abs := fresh "Abs" in intros _ Abs; discriminate Abs
        | let Abs := fresh "Abs" in intros _ Abs; discriminate Abs]
    | |- match Oset.compare ?OS ?x1 ?x2 with
           | Eq => true
           | Lt => false
           | Gt => false
         end = true -> ?x1 = ?x2 =>
       generalize (Oset.eq_bool_ok OS x1 x2);
         case (Oset.compare OS x1 x2);
         [ exact (fun h _ => h) 
         | let Abs := fresh "Abs" in intros _ Abs; discriminate Abs
         | let Abs := fresh "Abs" in intros _ Abs; discriminate Abs]
    | |- match Oset.compare ?OS ?x1 ?x2 with
           | Eq => ?x1 = ?x2
           | Lt => ?x1 <> ?x2
           | Gt => ?x1 <> ?x2
         end =>
      apply (Oset.eq_bool_ok OS x1 x2)
    | |- match Oset.compare ?OS ?x1 ?x2 with
           | Eq => ?f ?x1 = ?f ?x2
           | Lt => ?f ?x1 <> ?f ?x2
           | Gt => ?f ?x1 <> ?f ?x2
         end =>
      generalize (Oset.eq_bool_ok OS x1 x2);
        case (Oset.compare OS x1 x2);
        [apply f_equal 
        | let H1 := fresh in 
          let H2 := fresh in
          intros H1 H2;
            apply H1; injection H2; exact (fun h => h)
        | let H1 := fresh in 
          let H2 := fresh in
          intros H1 H2;
            apply H1; injection H2; exact (fun h => h)]
    | |- match Oset.compare ?OS ?x1 ?x2 with
           | Eq => ?f2 (?f1 ?x1) = ?f2 (?f1 ?x2)
           | Lt => ?f2 (?f1 ?x1) <> ?f2 (?f1 ?x2)
           | Gt => ?f2 (?f1 ?x1) <> ?f2 (?f1 ?x2)
         end =>
      generalize (Oset.eq_bool_ok OS x1 x2);
        case (Oset.compare OS x1 x2);
        [apply (f_equal (fun x => f2 (f1 x)))
        | let H1 := fresh in 
          let H2 := fresh in
          intros H1 H2;
            apply H1; injection H2; exact (fun h => h)
        | let H1 := fresh in 
          let H2 := fresh in
          intros H1 H2;
            apply H1; injection H2; exact (fun h => h)]
  end.

Ltac oeset_compare_tac :=
  match goal with
    | |- Oeset.compare ?OS ?a1 ?a1 = Eq => apply Oeset.compare_eq_refl
    | h1 : Oeset.compare ?OS ?a1 ?a2 = Eq, 
      h2 : Oeset.compare ?OS ?a2 ?a3 = Eq
      |- Oeset.compare ?OS ?a1 ?a3 = Eq => apply (Oeset.compare_eq_trans _ _ _ _ h1 h2)
    | |- Oeset.compare ?OS ?a1 ?a2 = Eq -> 
         Oeset.compare ?OS ?a2 ?a3 = Eq -> 
         Oeset.compare ?OS ?a1 ?a3 = Eq => apply Oeset.compare_eq_trans
    | h1 : Oeset.compare ?OS ?a1 ?a2 = Eq,
      h2 : Oeset.compare ?OS ?a2 ?a3 = Lt 
      |- Oeset.compare ?OS ?a1 ?a3 = Lt => apply (Oeset.compare_eq_lt_trans _ _ _ _ h1 h2)
    | |- Oeset.compare ?OS ?a1 ?a2 = Eq -> 
         Oeset.compare ?OS ?a2 ?a3 = Lt ->
         Oeset.compare ?OS ?a1 ?a3 = Lt => apply Oeset.compare_eq_lt_trans
    | h1 : Oeset.compare ?OS ?a1 ?a2 = Lt,
      h2 : Oeset.compare ?OS ?a2 ?a3 = Eq 
      |- Oeset.compare ?OS ?a1 ?a3 = Lt => apply (Oeset.compare_lt_eq_trans _ _ _ _ h1 h2)
    | |- Oeset.compare ?OS ?a1 ?a2 = Lt -> 
         Oeset.compare ?OS ?a2 ?a3 = Eq ->
         Oeset.compare ?OS ?a1 ?a3 = Lt => apply Oeset.compare_lt_eq_trans
    | h1 : Oeset.compare ?OS ?a1 ?a2 = Lt,
      h2 : Oeset.compare ?OS ?a2 ?a3 = Lt 
      |- Oeset.compare ?OS ?a1 ?a3 = Lt => apply (Oeset.compare_lt_trans _ _ _ _ h1 h2)
    | |- Oeset.compare ?OS ?a1 ?a2 = Lt -> 
         Oeset.compare ?OS ?a2 ?a3 = Lt ->
         Oeset.compare ?OS ?a1 ?a3 = Lt => apply Oeset.compare_lt_trans
    | |- Oeset.compare ?OS ?a1 ?a2 = CompOpp (Oeset.compare ?OS ?a2 ?a1) =>
      apply Oeset.compare_lt_gt
  end.

Ltac comparelA_tac :=
  match goal with
    | |- comparelA ?comp ?a1 ?a2 = Eq ->
         comparelA ?comp ?a2 ?a3 = Eq ->
         comparelA ?comp ?a1 ?a3 = Eq =>
      apply comparelA_eq_trans; do 6 intro
    | |- comparelA ?comp ?a1 ?a2 = Eq ->
         comparelA ?comp ?a2 ?a3 = Lt ->
         comparelA ?comp ?a1 ?a3 = Lt =>
      apply comparelA_le_lt_trans; do 6 intro
    | |- comparelA ?comp ?a1 ?a2 = Lt ->
         comparelA ?comp ?a2 ?a3 = Eq ->
         comparelA ?comp ?a1 ?a3 = Lt =>
      apply comparelA_lt_le_trans; do 6 intro
    | |- comparelA ?comp ?a1 ?a2 = Lt ->
         comparelA ?comp ?a2 ?a3 = Lt ->
         comparelA ?comp ?a1 ?a3 = Lt =>
      apply comparelA_lt_trans; do 6 intro
    | |- comparelA ?comp ?a1 ?a2 = CompOpp (comparelA ?comp ?a2 ?a1) =>
      apply comparelA_lt_gt; do 4 intro
  end.

Ltac comparelA_eq_bool_ok_tac :=
  match goal with
    | |- match comparelA ?comp ?x1 ?x2 with
           | Eq => ?f ?x1 = ?f ?x2
           | Lt => ?f ?x1 <> ?f ?x2
           | Gt => ?f ?x1 <> ?f ?x2
         end =>
      let Aux := fresh "Aux" in
      assert (Aux : forall a1 a2,
                      List.In a1 x1 ->
                      List.In a2 x2 ->
                      match comp a1 a2 with
                        | Eq => a1 = a2
                        | Lt => a1 <> a2
                        | Gt => a1 <> a2
                      end); 
        [do 4 intro 
        | generalize (comparelA_eq_bool_ok _ x1 x2 Aux);
          case (comparelA comp x1 x2);
          [apply f_equal
          | let H1 := fresh in
            let H2 := fresh in
            intros H1 H2; apply H1; injection H2; exact (fun h => h)
          | let H1 := fresh in
            let H2 := fresh in
            intros H1 H2; apply H1; injection H2; exact (fun h => h)]]
  end.

Ltac compareAB_tac :=
  match goal with
    | |- compareAB (Oset.compare ?OA) ?cB (?a,?b1) (?a,?b2) = Eq => 
         unfold compareAB; rewrite (Oset.compare_eq_refl OA)
      
    | |- compareAB ?OS1 ?OS2 (?a1,?b1) (?a2,?b2) = Eq ->
         compareAB ?OS1 ?OS2 (?a2,?b2) (?a3,?b3) = Eq ->
         compareAB ?OS1 ?OS2 (?a1,?b1) (?a3,?b3) = Eq =>
      apply compareAB_eq_trans

    | |- compareAB ?OS1 ?OS2 ?x1 ?x2 = Eq ->
         compareAB ?OS1 ?OS2 ?x2 ?x3 = Eq ->
         compareAB ?OS1 ?OS2 ?x1 ?x3 = Eq =>
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let a3 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      let b3 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        destruct x3 as [a3 b3];
        apply compareAB_eq_trans

    | |- compareAB ?OS1 ?OS2 (?a1,?b1) (?a2,?b2) = Eq ->
         compareAB ?OS1 ?OS2 (?a2,?b2) (?a3,?b3) = Lt ->
         compareAB ?OS1 ?OS2 (?a1,?b1) (?a3,?b3) = Lt =>
      apply compareAB_le_lt_trans

    | |- compareAB ?OS1 ?OS2 ?x1 ?x2 = Eq ->
         compareAB ?OS1 ?OS2 ?x2 ?x3 = Lt ->
         compareAB ?OS1 ?OS2 ?x1 ?x3 = Lt =>
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let a3 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      let b3 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        destruct x3 as [a3 b3];
        apply compareAB_le_lt_trans

    | |- compareAB ?OS1 ?OS2 (?a1,?b1) (?a2,?b2) = Lt ->
         compareAB ?OS1 ?OS2 (?a2,?b2) (?a3,?b3) = Eq ->
         compareAB ?OS1 ?OS2 (?a1,?b1) (?a3,?b3) = Lt =>
      apply compareAB_lt_le_trans

    | |- compareAB ?OS1 ?OS2 ?x1 ?x2 = Lt ->
         compareAB ?OS1 ?OS2 ?x2 ?x3 = Eq ->
         compareAB ?OS1 ?OS2 ?x1 ?x3 = Lt =>
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let a3 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      let b3 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        destruct x3 as [a3 b3];
        apply compareAB_lt_le_trans

    | |- compareAB ?OS1 ?OS2 (?a1,?b1) (?a2,?b2) = Lt ->
         compareAB ?OS1 ?OS2 (?a2,?b2) (?a3,?b3) = Lt ->
         compareAB ?OS1 ?OS2 (?a1,?b1) (?a3,?b3) = Lt =>
      apply compareAB_lt_trans

    | |- compareAB ?OS1 ?OS2 ?x1 ?x2 = Lt ->
         compareAB ?OS1 ?OS2 ?x2 ?x3 = Lt ->
         compareAB ?OS1 ?OS2 ?x1 ?x3 = Lt =>
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let a3 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      let b3 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        destruct x3 as [a3 b3];
        apply compareAB_lt_trans

    | |- compareAB ?OS1 ?OS2 (?a1,?b1) (?a2,?b2) = 
         CompOpp (compareAB ?OS1 ?OS2 (?a2,?b2) (?a1,?b1)) =>
      apply compareAB_lt_gt

    | |- compareAB ?OS1 ?OS2 ?x1 ?x2 = CompOpp (compareAB ?OS1 ?OS2 ?x2 ?x1) =>
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        apply compareAB_lt_gt
  end.


Ltac compareAB_eq_bool_ok_tac :=
  match goal with
    | |- match compareAB ?comp1 ?comp2 (?a1,?b1) (?a2,?b2) with
           | Eq => ?f (?a1,?b1) = ?f (?a2,?b1)
           | Lt => ?f (?a1,?b1) <> ?f (?a2,?b1)
           | Gt => ?f (?a1,?b1) <> ?f (?a2,?b1)
         end => idtac
    | |- match compareAB ?comp1 ?comp2 ?x1 ?x2 with
           | Eq => ?f ?x1 = ?f ?x2
           | Lt => ?f ?x1 <> ?f ?x2
           | Gt => ?f ?x1 <> ?f ?x2
         end => 
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2]
    | |- match compareAB ?comp1 ?comp2 (?a1,?b1) (?a2,?b2) with
           | Eq => (?a1,?b1) = (?a2,?b1)
           | Lt => (?a1,?b1) <> (?a2,?b1)
           | Gt => (?a1,?b1) <> (?a2,?b1)
         end => apply compareAB_eq_bool_ok
    | |- match compareAB ?comp1 ?comp2 ?x1 ?x2 with
           | Eq => ?x1 = ?x2
           | Lt => ?x1 <> ?x2
           | Gt => ?x1 <> ?x2
         end => 
      let a1 := fresh "a" in
      let a2 := fresh "a" in
      let b1 := fresh "b" in
      let b2 := fresh "b" in
      destruct x1 as [a1 b1];
        destruct x2 as [a2 b2];
        apply compareAB_eq_bool_ok
  end.
