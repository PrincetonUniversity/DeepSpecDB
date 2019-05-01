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

Require Import Bool List Sorted SetoidList NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet FiniteSet. 

Open Scope N_scope.

Module Febag.
Record Rcd (elt : Type) (Elt : Oeset.Rcd elt) : Type :=
  mk_R
    {
      bag : Type;
      nb_occ : elt -> bag -> N;
      add : elt -> bag -> bag;
      nb_occ_add : forall s a e, nb_occ e (add a s) = 
                               (if Oeset.eq_bool Elt e a then 1 else 0) + nb_occ e s;
      singleton : elt -> bag;
      nb_occ_singleton : 
        forall x y : elt, nb_occ y (singleton x) = if Oeset.eq_bool Elt y x then 1 else 0;
      union : bag -> bag -> bag;
      nb_occ_union : 
        forall (s s' : bag) (x : elt), nb_occ x (union s s') = nb_occ x s + nb_occ x s';
      union_max : bag -> bag -> bag;
      nb_occ_union_max : 
        forall (s s' : bag) (x : elt), 
          nb_occ x (union_max s s') = N.max (nb_occ x s) (nb_occ x s');
      inter : bag -> bag -> bag;
      nb_occ_inter : 
        forall (s s' : bag) (x : elt), nb_occ x (inter s s') = N.min (nb_occ x s) (nb_occ x s');
      diff : bag -> bag -> bag;
      nb_occ_diff : 
        forall (s s' : bag) (x : elt), nb_occ x (diff s s') = (nb_occ x s) - (nb_occ x s');
      equal : bag -> bag -> bool;
      nb_occ_equal : forall s1 s2, equal s1 s2 = true <-> (forall e, nb_occ e s1 = nb_occ e s2);
      subbag : bag -> bag -> bool;
      subbag_spec : 
        forall s1 s2, subbag s1 s2 = true <-> (forall e, nb_occ e s1 <= nb_occ e s2);
      empty : bag;     
      nb_occ_empty : forall e, nb_occ e empty = 0;
      is_empty : bag -> bool;
      is_empty_spec : forall s, is_empty s = equal s empty;
      elements : bag -> list elt;
      elements_empty : elements empty = nil;
      elements_spec1 : 
        forall s s', equal s s' = true -> 
                     comparelA (Oeset.compare Elt) (elements s) (elements s') = Eq;      
      nb_occ_elements : forall e s, nb_occ e s = Oeset.nb_occ Elt e (elements s);
      elements_spec3 : forall s, Sorted (fun x y => Oeset.compare Elt x y <> Gt) (elements s);
      choose : bag -> option elt;
      choose_spec1 : forall s e, choose s = Some e -> nb_occ e s >= 1;
      choose_spec2 : forall s, choose s = None -> is_empty s = true;
      choose_spec3 : forall s1 s2, equal s1 s2 = true ->
                                   match choose s1 with
                                     | None => choose s2 = None
                                     | Some e1 => match choose s2 with
                                                    | None => False
                                                    | Some e2 => Oeset.compare Elt e1 e2 = Eq
                                                  end
                                   end;
      filter : (elt -> bool) -> bag -> bag;
      nb_occ_filter : 
        forall (s : bag) (f : elt -> bool),
          (forall e e', nb_occ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          forall (x : elt), nb_occ x (filter f s) = nb_occ x s * (if f x then 1 else 0);
      filter_spec_weak : 
        forall (s : bag) (f : elt -> bool) (x : elt),
          nb_occ x (filter f s) >= 1 -> nb_occ x s >= 1;
      partition : (elt -> bool) -> bag -> (bag * bag);
      partition_spec1 : 
        forall (s : bag) (x : elt) (f : elt -> bool),
          (forall e e', nb_occ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          nb_occ x (fst (partition f s)) = nb_occ x s * (if f x then 1 else 0);
      partition_spec2 : 
        forall (s : bag) (x : elt) (f : elt -> bool),
          (forall e e', nb_occ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          nb_occ x (snd (partition f s)) = nb_occ x s * if (f x) then 0 else 1;
      for_all : (elt -> bool) -> bag -> bool;
      for_all_spec : forall (s : bag) (f : elt -> bool), for_all f s = forallb f (elements s);
      exists_ : (elt -> bool) -> bag -> bool;
      exists_spec : forall (s : bag) (f : elt -> bool), exists_ f s = existsb f (elements s);
      fold : forall (A : Type), (elt -> A -> A) -> bag -> A -> A;
      fold_spec : forall (s : bag) (A : Type) a0 (f : elt -> A -> A),
          fold f s a0 = fold_left (fun (a : A) (e : elt) => f e a) (elements s) a0;
      compare : bag -> bag -> comparison;
      compare_spec : forall s1 s2, compare s1 s2 = Eq <-> equal s1 s2 = true;
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

Section Build.

Hypothesis elt : Type.
Hypothesis Elt : Oeset.Rcd elt.

Definition bag_ := @list elt.

Definition nb_occ_ e s := Oeset.nb_occ Elt e s.

Definition add_ (e : elt) (s : bag_) := e :: s.
Lemma add_spec_ : 
  forall s a e, nb_occ_ e (add_ a s) = (if Oeset.eq_bool Elt e a then 1 else 0) + nb_occ_ e s.
Proof.
intros s a e; simpl; unfold Oeset.eq_bool; case (Oeset.compare Elt e a); apply refl_equal.
Qed.

Definition singleton_ (e : elt) := e :: nil.

Lemma singleton_spec_ :
  forall x y : elt, nb_occ_ y (singleton_ x) = if Oeset.eq_bool Elt y x then 1 else 0.
Proof.
intros a e; simpl; unfold Oeset.eq_bool; case (Oeset.compare Elt e a); apply refl_equal.
Qed.

Definition union_ (s1 s2 : bag_) := s1 ++ s2.
Lemma nb_occ_union_ : forall (s s' : bag_) (x : elt), nb_occ_ x (union_ s s') = nb_occ_ x s + nb_occ_ x s'.
Proof.
intros s1 s2 e; apply Oeset.nb_occ_app.
Qed.

Fixpoint remove_dup_rec acc l :=
  match l with
    | nil => acc
    | a1 :: l => 
      if Oeset.mem_bool Elt a1 acc 
      then remove_dup_rec acc l 
      else remove_dup_rec (a1 :: acc) l
  end.

Fixpoint mk_dup_list n (a : elt) :=
  match n with
    | O => nil
    | S n => a :: mk_dup_list n a
  end.

Definition union_max_ (s1 s2 : bag_) :=
  flat_map (fun a => mk_dup_list (N.to_nat (Nmax (nb_occ_ a s1) (nb_occ_ a s2))) a) 
           (remove_dup_rec nil (s1 ++ s2)).

Lemma remove_dup_rec_remove_dup :
  forall acc l, (forall x, Oeset.nb_occ Elt x acc <= 1) ->
                forall x, Oeset.nb_occ Elt x (remove_dup_rec acc l) <= 1.
Proof.
intros acc l; revert acc; induction l as [ | a1 l]; intros acc H x; simpl.
- apply H.
- case_eq (Oeset.mem_bool Elt a1 acc); intro Ha1.
  + apply IHl; apply H.
  + apply IHl.
    intros a; simpl.
    case_eq (Oeset.compare Elt a a1); intro Ha.
    * rewrite (Oeset.nb_occ_eq_1 _ _ _ _ Ha), (Oeset.not_mem_nb_occ _ _ _ Ha1).
      apply N.le_refl.
    * apply H.
    * apply H.
Qed.

(* begin hide *)
Lemma nb_occ_remove_dup_rec :
  forall acc l x,
    Oeset.nb_occ Elt x (remove_dup_rec acc l) =
    N.max (Oeset.nb_occ Elt x acc) (if Oeset.mem_bool Elt x l then 1 else 0).
Proof.
intros acc l; revert acc; induction l as [ | a1 l]; intros acc x; simpl.
- rewrite N.max_0_r; apply refl_equal.
- case_eq (Oeset.mem_bool Elt a1 acc); intro Ha1.
  + rewrite IHl.
    case_eq (Oeset.eq_bool Elt x a1); intro Hx; [ | apply refl_equal].
    unfold Oeset.eq_bool in Hx; rewrite compare_eq_true in Hx.
    rewrite <- (Oeset.mem_bool_eq_1 _ _ _ _ Hx) in Ha1; simpl.
    assert (Aux :  1 <= Oeset.nb_occ Elt x acc).
    {
      generalize (Oeset.mem_nb_occ _ _ _ Ha1).
      destruct (Oeset.nb_occ Elt x acc).
      - intro Abs; apply False_rec; apply Abs; apply refl_equal.
      - intros _; unfold N.le; destruct p; simpl; discriminate.
    }
    rewrite 2 N.max_l; trivial.
    refine (N.le_trans _ _ _ _ Aux).
    destruct (Oeset.mem_bool Elt x l); discriminate.
  + rewrite IHl.
    rewrite Oeset.nb_occ_unfold; unfold Oeset.eq_bool.
    case_eq (Oeset.compare Elt x a1); intro Hx.
    * rewrite <- (Oeset.mem_bool_eq_1 _ _ _ _ Hx) in Ha1.
      rewrite (Oeset.not_mem_nb_occ _ _ _ Ha1); simpl.
      {
        rewrite N.max_l, N.max_r; trivial.
        - discriminate.
        - destruct (Oeset.mem_bool Elt x l); discriminate.
      } 
    * apply refl_equal.
    * apply refl_equal.
Qed.
(* end hide *)

Lemma in_remove_dup_rec :
  forall acc l x, 
    Oeset.mem_bool Elt x l || Oeset.mem_bool Elt x acc = 
    Oeset.mem_bool Elt x (remove_dup_rec acc l).
Proof.
intros acc l; revert acc; induction l as [ | a1 l]; intros acc x; simpl.
- apply refl_equal.
- case_eq (Oeset.mem_bool Elt a1 acc); intro Ha1; rewrite <- IHl.
  + case_eq ( Oeset.eq_bool Elt x a1); intro Hx; [ | apply refl_equal].
    unfold Oeset.eq_bool in Hx; rewrite compare_eq_true in Hx.
    rewrite <- (Oeset.mem_bool_eq_1 _ _ _ _ Hx) in Ha1; rewrite Ha1, 2 Bool.orb_true_r.
    apply refl_equal.
  + simpl; rewrite eq_bool_iff, 4 Bool.orb_true_iff; intuition.
Qed.


Lemma nb_occ_dup_list_1 :
  forall n a a', Oeset.compare Elt a' a = Eq -> 
                 Oeset.nb_occ Elt a' (mk_dup_list n a) = (N.of_nat n).
Proof.
intro n; induction n as [ | n]; intros a a' H; [apply refl_equal | ].
simpl mk_dup_list; rewrite Oeset.nb_occ_unfold, H, (IHn _ _ H).
assert (K := Nat2N.inj_add 1 n); simpl in K; simpl; rewrite <- K; apply refl_equal.
Qed.

Lemma nb_occ_dup_list_2 :
  forall n a a', Oeset.compare Elt a' a <> Eq -> 
                 Oeset.nb_occ Elt a' (mk_dup_list n a) = 0.
Proof.
intro n; induction n as [ | n]; intros a a' H; [apply refl_equal | ].
simpl mk_dup_list; rewrite Oeset.nb_occ_unfold, (IHn _ _ H).
destruct (Oeset.compare Elt a' a); trivial.
apply False_rec; apply H; apply refl_equal.
Qed.

Lemma union_max_spec_ : 
  forall (s s' : bag_) (x : elt), nb_occ_ x (union_max_ s s') = Nmax (nb_occ_ x s) (nb_occ_ x s').
Proof.
intros s1 s2 e.
unfold union_max_.
assert (H1 : forall x, Oeset.nb_occ Elt x (remove_dup_rec nil (s1 ++ s2)) <= 1).
{
  apply remove_dup_rec_remove_dup.
  intro; simpl; apply N.le_0_l.
}
assert (H2 : forall x, Oeset.mem_bool Elt x (remove_dup_rec nil (s1 ++ s2)) =
                      Oeset.mem_bool Elt x (s1 ++ s2)).
{
  intro x; rewrite <- in_remove_dup_rec; simpl.
  rewrite Bool.orb_false_r; apply refl_equal.
}
set (l := remove_dup_rec nil (s1 ++ s2)) in *; clearbody l.
unfold nb_occ_; generalize (H1 e) (H2 e); clear H1 H2.
revert s1 s2; induction l as [ | a1 l]; intros s1 s2 H1 H2; simpl.
- generalize (sym_eq H2); rewrite Oeset.mem_bool_app; simpl.
  rewrite Bool.orb_false_iff; intros [K1 K2].
  rewrite (Oeset.not_mem_nb_occ _ _ _ K1), (Oeset.not_mem_nb_occ _ _ _ K2).
  apply refl_equal.
- rewrite Oeset.nb_occ_app.
    assert (Aux : forall l, Oeset.nb_occ Elt e l = 0 ->
                            Oeset.nb_occ Elt e
     (flat_map
        (fun a : elt =>
         mk_dup_list
           (N.to_nat (N.max (Oeset.nb_occ Elt a s1) (Oeset.nb_occ Elt a s2)))
           a) l) = 0).
    {
      clear l IHl H1 H2; intros l Aux; induction l as [ | a l]; simpl; [trivial | ].
      rewrite Oeset.nb_occ_app, IHl, nb_occ_dup_list_2.
      - apply refl_equal.
      - simpl in Aux.
        destruct (Oeset.compare Elt e a).
        + destruct (Oeset.nb_occ Elt e l); discriminate Aux.
        + discriminate.
        + discriminate.
      - simpl in Aux.
        destruct (Oeset.nb_occ Elt e l); [trivial | ].
        destruct (Oeset.compare Elt e a); try discriminate Aux.
    }
  case_eq (Oeset.compare Elt e a1); intro He.
  + rewrite nb_occ_dup_list_1; [ | assumption].
    rewrite N2Nat.id.
    rewrite Aux, N.add_0_r.
    * rewrite 2 (Oeset.nb_occ_eq_1 _ _ _ _ He).
      apply refl_equal.
    * generalize H1; simpl; rewrite He.
      rewrite N.le_1_r.
      destruct (Oeset.nb_occ Elt e l); [trivial | ].
      intros [Abs | Abs]; [ | destruct p]; discriminate Abs.
  + rewrite nb_occ_dup_list_2, IHl.
    * apply refl_equal.
    * refine (N.le_trans _ _ _ _ H1). 
      simpl.
      destruct (Oeset.compare Elt e a1); try apply N.le_refl.
      rewrite N.add_comm; apply N.le_add_r.
    * rewrite <- H2; simpl; unfold Oeset.eq_bool; rewrite He.
      apply refl_equal.
    * rewrite He; discriminate.
  + rewrite nb_occ_dup_list_2, IHl.
    * apply refl_equal.
    * refine (N.le_trans _ _ _ _ H1). 
      simpl.
      destruct (Oeset.compare Elt e a1); try apply N.le_refl.
      rewrite N.add_comm; apply N.le_add_r.
    * rewrite <- H2; simpl; unfold Oeset.eq_bool; rewrite He.
      apply refl_equal.
    * rewrite He; discriminate.
Qed.

Function inter_bag b b12 {measure (fun x => plus (length (fst x)) (length (snd x))) b12} :=
  match b12 with
    | (nil, _) => b
    | (x1 :: b1, nil) => b
    | (x1 :: b1, x2 :: b2) => 
          match Oeset.compare Elt x1 x2 with
            | Eq => inter_bag (x1 :: b) (b1, b2)
            | Lt => inter_bag b (b1, x2 :: b2)
            | Gt => inter_bag b (x1 :: b1, b2)
          end
  end.
Proof.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
Defined.

Definition inter_ l1 l2 := inter_bag nil (quicksort Elt l1, quicksort Elt l2).

Lemma nb_occ_inter_aux :
  forall x l1 l2 l, 
    Oeset.nb_occ Elt x (inter_bag l (l1, l2)) = 
    Oeset.nb_occ Elt x l + Oeset.nb_occ Elt x (inter_bag nil (l1, l2)).
Proof.
intros x l1 l2.
set (n := plus (length l1) (length l2)).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert x l1 l2 Hn; induction n as [ | n].
- intros x [ | a1 l1] l2 Hn l; [ | inversion Hn].
  rewrite 2 inter_bag_equation, (Oeset.nb_occ_unfold _ _ nil), N.add_0_r.
  apply refl_equal.
- intros x [ | a1 l1] l2 Hn l.
  + rewrite 2 inter_bag_equation, (Oeset.nb_occ_unfold _ _ nil), N.add_0_r.
    apply refl_equal.
  + destruct l2 as [ | a2 l2].
    * rewrite 2 inter_bag_equation, (Oeset.nb_occ_unfold _ _ nil), N.add_0_r.
      apply refl_equal.
    * rewrite 2 (inter_bag_equation _ (_ :: _, _ :: _)).
      {
        case_eq (Oeset.compare Elt a1 a2); intro Ha.
        - assert (Kn : (length l1 + length l2 <= n)%nat).
          {
            simpl in Hn; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply Plus.plus_le_compat_l; apply le_S; apply le_n.
          }
          rewrite 2 (IHn x l1 l2 Kn (a1 :: _)), 2 (Oeset.nb_occ_unfold _ _ (a1 :: _)).
          rewrite (Oeset.nb_occ_unfold Elt x nil).
          ring.
        - rewrite IHn; trivial.
          simpl in Hn; apply (le_S_n _ _ Hn).
        - rewrite IHn; trivial.
          simpl in Hn; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
          simpl; rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
      }
Qed.

Lemma nb_occ_inter_ : 
  forall (s s' : bag_) (x : elt), nb_occ_ x (inter_ s s') = Nmin (nb_occ_ x s) (nb_occ_ x s').
Proof.
intros s1 s2 x.
unfold inter_, nb_occ_.
assert (H1 := quick_sorted Elt s1).
assert (H2 := quick_sorted Elt s2).
rewrite <- (nb_occ_quicksort Elt x s1), <- (nb_occ_quicksort Elt x s2).
set (l1 := quicksort Elt s1) in *; clearbody l1; clear s1.
set (l2 := quicksort Elt s2) in *; clearbody l2; clear s2.
set (m := plus (length l1) (length l2)).
assert (Hm := le_n m); unfold m at 1 in Hm; clearbody m.
revert l1 H1 l2 H2 Hm; induction m as [ | m];
intros l1 H1 l2 H2 Hm.
- destruct l1; [ | inversion Hm].
  destruct l2; [ | inversion Hm].
  rewrite inter_bag_equation; simpl.
  rewrite N.min_0_r; apply refl_equal.
- destruct l1 as [ | a1 l1]; [simpl | rewrite inter_bag_equation].
  + rewrite N.min_0_l; apply refl_equal.
  + rewrite (Oeset.nb_occ_unfold Elt x (a1 :: _)); case_eq (Oeset.compare Elt x a1); intro Hx.
    * destruct l2 as [ | a2 l2]; [rewrite N.min_0_r; apply refl_equal | ].
      {
        case_eq (Oeset.compare Elt a1 a2); intro Ha.
        - rewrite nb_occ_inter_aux, IHm, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)), Hx.
          + rewrite (Oeset.compare_eq_trans _ _ _ _ Hx Ha), N.add_min_distr_l.
            rewrite (Oeset.nb_occ_unfold Elt x nil); ring.
          + apply (sorted_tl_sorted H1).
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            apply Plus.plus_le_compat_l; apply le_S; apply le_n.
        - rewrite IHm, (nb_occ_sorted (l := a2 :: l2) x (a := a2)), 2 N.min_0_r; trivial.
          + apply (Oeset.compare_eq_lt_trans _ _ _ _ Hx Ha).
          + constructor 3; [ | assumption].
            rewrite Oeset.compare_eq_refl; discriminate.
          + apply (sorted_tl_sorted H1).
          + simpl in Hm; simpl; apply (le_S_n _ _ Hm).
        - rewrite IHm, (Oeset.nb_occ_unfold Elt x (a1 :: _)), Hx; trivial.
          + rewrite (Oeset.nb_occ_unfold Elt x (a2 :: _)), 
            (Oeset.compare_eq_gt_trans _ _ _ _ Hx Ha).
            apply refl_equal.
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            simpl; rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
      }
    * destruct l2 as [ | a2 l2]; [rewrite N.min_0_r; apply refl_equal | ].
      {
        case_eq (Oeset.compare Elt a1 a2); intro Ha.
        - rewrite nb_occ_inter_aux, IHm, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)), Hx.
          + rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Hx Ha), N.add_min_distr_l.
            rewrite (Oeset.nb_occ_unfold Elt x nil); ring.
          + apply (sorted_tl_sorted H1).
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            apply Plus.plus_le_compat_l; apply le_S; apply le_n.
        - rewrite IHm, (nb_occ_sorted (l := a2 :: l2) x (a := a2)), 2 N.min_0_r; trivial.
          + apply (Oeset.compare_lt_trans _ _ _ _ Hx Ha).
          + constructor 3; [ | assumption].
            rewrite Oeset.compare_eq_refl; discriminate.
          + apply (sorted_tl_sorted H1).
          + simpl in Hm; simpl; apply (le_S_n _ _ Hm).
        - rewrite IHm, (Oeset.nb_occ_unfold Elt x (a1 :: _)), Hx; trivial.
          + rewrite (Oeset.nb_occ_unfold Elt x (a2 :: _)).
            case_eq (Oeset.compare Elt x a2); intro Kx; trivial.
            rewrite (nb_occ_sorted (l := l1) x (a := a1)), 2 N.min_0_l; trivial.
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            simpl; rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
      }
    * destruct l2 as [ | a2 l2]; [rewrite N.min_0_r; apply refl_equal | ].
      {
        case_eq (Oeset.compare Elt a1 a2); intro Ha.
        - rewrite nb_occ_inter_aux, IHm, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)), Hx.
          + rewrite (Oeset.compare_gt_eq_trans _ _ _ _ Hx Ha), N.add_min_distr_l.
            rewrite (Oeset.nb_occ_unfold Elt x nil); ring.
          + apply (sorted_tl_sorted H1).
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            apply Plus.plus_le_compat_l; apply le_S; apply le_n.
        - rewrite IHm; trivial.
          + apply (sorted_tl_sorted H1).
          + simpl in Hm; simpl; apply (le_S_n _ _ Hm).
        - rewrite IHm, (Oeset.nb_occ_unfold Elt x (a1 :: _)), Hx; trivial.
          + rewrite (Oeset.nb_occ_unfold Elt x (a2 :: _)).
            rewrite (Oeset.compare_gt_trans _ _ _ _ Hx Ha); apply refl_equal.
          + apply (sorted_tl_sorted H2).
          + simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
            simpl; rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
      }
Qed.

Function diff_bag b b12 {measure (fun x => plus (length (fst x)) (length (snd x))) b12} :=
  match b12 with
    | (nil, _) => b
    | (x1 :: b1, nil) => b ++ (x1 :: b1)
    | (x1 :: b1, x2 :: b2) => 
          match Oeset.compare Elt x1 x2 with
            | Eq => diff_bag b (b1, b2)
            | Lt => diff_bag (x1 :: b) (b1, x2 :: b2)
            | Gt => diff_bag b (x1 :: b1, b2)
          end
  end.
Proof.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
- intros _ [b1 b2] l1 l2 x1 k1 H1 x2 k2 H2 H _; simpl; auto with arith.
Defined.

Definition diff_ l1 l2 := diff_bag nil (quicksort Elt l1, quicksort Elt l2).

Lemma diff_spec_aux :
  forall x l1 l2 l, 
    Oeset.nb_occ Elt x (diff_bag l (l1, l2)) = 
    Oeset.nb_occ Elt x l + Oeset.nb_occ Elt x (diff_bag nil (l1, l2)).
Proof.
intros x l1 l2.
set (n := plus (length l1) (length l2)).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert x l1 l2 Hn; induction n as [ | n].
- intros x [ | a1 l1] l2 Hn l; [ | inversion Hn].
  rewrite 2 diff_bag_equation, (Oeset.nb_occ_unfold _ _ nil), N.add_0_r.
  apply refl_equal.
- intros x [ | a1 l1] l2 Hn l.
  + rewrite 2 diff_bag_equation, (Oeset.nb_occ_unfold _ _ nil), N.add_0_r.
    apply refl_equal.
  + destruct l2 as [ | a2 l2].
    * rewrite 2 diff_bag_equation, Oeset.nb_occ_app; apply refl_equal.
    * rewrite 2 (diff_bag_equation _ (_ :: _, _ :: _)).
      {
        case_eq (Oeset.compare Elt a1 a2); intro Ha.
        - rewrite IHn; trivial.
          simpl in Hn; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
          rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_S; apply le_n.
        - assert (Kn : (length l1 + length (a2 :: l2) <= n)%nat).
          {
            simpl in Hn; apply (le_S_n _ _ Hn).
          }
          rewrite 2 (IHn x l1 (a2 :: l2) Kn (a1 :: _)), 2 (Oeset.nb_occ_unfold _ _ (a1 :: _)).
          rewrite (Oeset.nb_occ_unfold Elt x nil).
          ring.
        - rewrite IHn; trivial.
          simpl in Hn; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
          rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
      }
Qed.

Lemma diff_spec_ : 
  forall (s s' : bag_) (x : elt), nb_occ_ x (diff_ s s') = (nb_occ_ x s) - (nb_occ_ x s').
Proof.
intros s1 s2 x.
unfold nb_occ_, diff_.
assert (H1 := quick_sorted Elt s1).
assert (H2 := quick_sorted Elt s2).
rewrite <- (nb_occ_quicksort Elt x s1), <- (nb_occ_quicksort Elt x s2).
set (l1 := quicksort Elt s1) in *; clearbody l1; clear s1.
set (l2 := quicksort Elt s2) in *; clearbody l2; clear s2.
set (m := plus (length l1) (length l2)).
assert (Hm := le_n m); unfold m at 1 in Hm; clearbody m.
revert l1 H1 l2 H2 Hm; induction m as [ | m];
intros l1 H1 l2 H2 Hm.
- destruct l1; [ | inversion Hm].
  destruct l2; [ | inversion Hm].
  rewrite diff_bag_equation; simpl; apply refl_equal.
- destruct l1 as [ | a1 l1]; [simpl; apply refl_equal | rewrite diff_bag_equation].
  destruct l2 as [ | a2 l2]; [rewrite N.sub_0_r; apply refl_equal | ].
  case_eq (Oeset.compare Elt a1 a2); intro Ha.
  + rewrite IHm, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)).
    case_eq (Oeset.compare Elt x a1); intro Hx.
    * rewrite (Oeset.compare_eq_trans _ _ _ _ Hx Ha).
      {
        case_eq (Ncompare (Oeset.nb_occ Elt x l1) (Oeset.nb_occ Elt x l2)); intro H.
        - rewrite N.compare_eq_iff in H; rewrite <- H, 2 N.sub_diag.
          apply refl_equal.
        - rewrite N.compare_lt_iff in H; generalize (N.lt_le_incl _ _ H); clear H; intro H.
          rewrite <- N.sub_0_le in H; rewrite H; apply sym_eq; rewrite N.sub_0_le.
          rewrite <- N.add_le_mono_l, <- N.sub_0_le; apply H.
        - rewrite N.compare_gt_iff in H.
          rewrite <- N.add_sub_assoc, (N.add_comm 1 (Oeset.nb_occ _ _ _)), N.sub_add_distr.
          + rewrite N.add_sub_assoc, N.add_comm, N.add_sub; trivial.
            apply N.le_add_le_sub_r.
            rewrite <- N.le_succ_l, <- N.add_1_l in H; apply H.
          + rewrite <- N.le_succ_l, <- N.add_1_l in H; apply H.
      }
    * rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Hx Ha); apply refl_equal.
    * rewrite (Oeset.compare_gt_eq_trans _ _ _ _ Hx Ha); apply refl_equal.
    * apply (sorted_tl_sorted H1).
    * apply (sorted_tl_sorted H2).
    * simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
      apply Plus.plus_le_compat_l; apply le_S; apply le_n.
  + rewrite diff_spec_aux, IHm, 2 (Oeset.nb_occ_unfold Elt x (a1 :: _)), 
    (Oeset.nb_occ_unfold Elt x nil).
    * case_eq (Oeset.compare Elt x a1); intro Hx; trivial.
      { 
        rewrite (nb_occ_sorted (l := a2 :: l2) x (a := a2)), 2 N.sub_0_r; trivial.
        - apply (Oeset.compare_eq_lt_trans _ _ _ _ Hx Ha).
        - constructor 3; [ | assumption].
          rewrite Oeset.compare_eq_refl; discriminate.
      } 
    * apply (sorted_tl_sorted H1).
    * assumption.
    * simpl in Hm; simpl; apply (le_S_n _ _ Hm).
  + rewrite IHm, (Oeset.nb_occ_unfold Elt x (a2 :: _)).
    * case_eq (Oeset.compare Elt x a2); intro Hx; trivial.
      {
        rewrite (nb_occ_sorted (l := a1 :: l1) x (a := a1)), 2 N.sub_0_l; trivial.
        - rewrite Oeset.compare_lt_gt, CompOpp_iff in Ha.
          apply (Oeset.compare_eq_lt_trans _ _ _ _ Hx Ha).
        - constructor 3; [ | assumption].
          rewrite Oeset.compare_eq_refl; discriminate.
      } 
    * assumption.
    * apply (sorted_tl_sorted H2).
    * simpl in Hm; refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hm)).
      simpl; rewrite (Plus.plus_comm _ (S _)); simpl; rewrite Plus.plus_comm; apply le_n.
Qed.

Definition equal_ (s1 s2 : bag_) := _permut_bool (Oeset.eq_bool Elt) s1 s2.

Lemma nb_occ_equal_ : 
  forall s1 s2, equal_ s1 s2 = true <-> (forall e, nb_occ_ e s1 = nb_occ_ e s2).
Proof.
unfold equal_, nb_occ_.
intros l1 l2; split.
- do 2 intro; apply permut_nb_occ.
  assert (H' := _permut_bool_true_is_sound _ _ _ H).
  refine (_permut_incl _ _ H').
  intros a b K; unfold Oeset.eq_bool in K; rewrite compare_eq_true in K; apply K.
- revert l2; induction l1 as [ | a1 l1]; intro l2; simpl; trivial.
  + intro H; destruct l2 as [ | a2 l2]; [trivial | ].
    generalize (H a2); rewrite Oeset.nb_occ_unfold, Oeset.compare_eq_refl.
    destruct (Oeset.nb_occ Elt a2 l2); discriminate.
  + intro H; case_eq (Mem.remove_bool (Oeset.eq_bool Elt) a1 l2). 
    * intros k2 Hl2.
      destruct (Mem.remove_bool_some_is_sound _ _ _ Hl2) as [[[_a1 l21] l22] [Ha1 [Kl2 Kk2]]].
      apply IHl1; intro x; assert (Hx := H x).
      rewrite Kl2, Oeset.nb_occ_app, (Oeset.nb_occ_unfold _ _ (_ :: _)) in Hx.
      rewrite Kk2, Oeset.nb_occ_app.
      unfold Oeset.eq_bool in Ha1; rewrite compare_eq_true in Ha1.
      {
        case_eq (Oeset.compare Elt x a1); intro Kx.
        - rewrite Kx, (Oeset.compare_eq_trans _ _ _ _ Kx Ha1) in Hx.
          apply Nplus_reg_l with 1; rewrite Hx; ring.
        - rewrite Kx, (Oeset.compare_lt_eq_trans _ _ _ _ Kx Ha1) in Hx; apply Hx.
        - rewrite Kx, (Oeset.compare_gt_eq_trans _ _ _ _ Kx Ha1) in Hx; apply Hx.
      } 
    * intro Hl2; apply False_rec.
      generalize (H a1); rewrite Oeset.compare_eq_refl.
      assert (H2 : Oeset.nb_occ Elt a1 l2 = 0).
      {
        clear H; induction l2 as [ | b2 l2]; simpl; trivial.
        simpl in Hl2.
        case_eq (Oeset.eq_bool Elt a1 b2); intro Hb; rewrite Hb in Hl2.
        - discriminate Hl2.
        - rewrite IHl2.
          + revert Hb; unfold Oeset.eq_bool.
            destruct (Oeset.compare Elt a1 b2); trivial.
            intro Abs; discriminate Abs.
          + destruct (Mem.remove_bool (Oeset.eq_bool Elt) a1 l2); [discriminate Hl2 | trivial].
      }
      rewrite H2; destruct (Oeset.nb_occ Elt a1 l1); discriminate.
Qed.

Definition subbag_ l1 l2 :=
  forallb (fun x => match Ncompare (Oeset.nb_occ Elt x l1) (Oeset.nb_occ Elt x l2) with
                      | Eq | Lt => true 
                      | Gt => false 
                    end) l1.

Lemma subbag_spec_ : 
  forall s1 s2, subbag_ s1 s2 = true <-> (forall e, nb_occ_ e s1 <= nb_occ_ e s2).
Proof.
intros l1 l2; unfold subbag_, nb_occ_.
rewrite forallb_forall; split; intro H.
- intros x.
  case_eq (Oeset.mem_bool Elt x l1); intro Hx.
  + rewrite Oeset.mem_bool_true_iff in Hx.
    destruct Hx as [a [Hx Ha]].
    rewrite 2 (Oeset.nb_occ_eq_1 _ _ _ _ Hx).
    assert (Ka := H _ Ha).
    case_eq (Ncompare (Oeset.nb_occ Elt a l1) (Oeset.nb_occ Elt a l2)); 
      intro Ja; rewrite Ja in Ka. 
    * rewrite N.compare_eq_iff in Ja; rewrite Ja; apply N.le_refl.
    * rewrite N.compare_lt_iff in Ja; apply N.lt_le_incl; apply Ja.
    * discriminate Ka.
  + rewrite (Oeset.not_mem_nb_occ _ _ _ Hx).
    apply N.le_0_l.
- intros x _; generalize (H x); unfold N.le.
  case (Ncompare (Oeset.nb_occ Elt x l1) (Oeset.nb_occ Elt x l2)); trivial.
  intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Definition empty_ := @nil elt.

Lemma empty_spec_ : forall e, nb_occ_ e empty_ = 0.
Proof.
intro e; apply refl_equal.
Qed.

Definition is_empty_ (s : bag_) := match s with nil => true | _ :: _ => false end.

Lemma is_empty_spec_ : forall s, is_empty_ s = equal_ s empty_.
Proof.
intro s; destruct s; apply refl_equal.
Qed.

Definition elements_ (s : bag_) := quicksort Elt s.

Lemma elements_empty_ : elements_ empty_ = nil.
Proof.
apply refl_equal.
Qed.

Lemma elements_spec1_ : 
  forall s s', equal_ s s' = true -> 
               comparelA (Oeset.compare Elt) (elements_ s) (elements_ s') = Eq.
Proof.
intros l1 l2 H.
apply (sort_is_unique (OA := Elt) (quick_sorted _ _) (quick_sorted _ _)).
apply permut_trans with l1.
- apply permut_sym; apply quick_permut.
- apply permut_trans with l2.
  + refine (_permut_incl _ _ (_permut_bool_true_is_sound _ _ _ H)).
    intros x y K; unfold Oeset.eq_bool in K; rewrite compare_eq_true in K; apply K.
  + apply quick_permut.
Qed.

Lemma mem_elements_ : 
  forall e s, nb_occ_ e s = Oeset.nb_occ Elt e (elements_ s).
Proof.
intros a l; rewrite nb_occ_quicksort; apply refl_equal.
Qed.

Lemma elements_spec3_ :
  forall s, Sorted (fun x y => Oeset.compare Elt x y <> Gt) (elements_ s).
Proof.
intro l; rewrite <- is_sorted_Sorted; apply quick_sorted.
Qed.

Definition choose_ (s : bag_) :=
  match quicksort Elt s with
    | nil => None
    | x :: _ => Some x
  end.

Lemma choose_spec1_ : forall s e, choose_ s = Some e -> nb_occ_ e s >= 1.
Proof.
unfold choose_, nb_occ_.
intros l e H; case_eq (quicksort Elt l); [intro K; rewrite K in H; discriminate H | ].
intros a k K; rewrite K in H; injection H; clear H; intro H; subst e.
rewrite <- nb_occ_quicksort, K, Oeset.nb_occ_unfold, Oeset.compare_eq_refl, N.ge_le_iff.
apply N.le_add_r.
Qed.

Lemma choose_spec2_ : forall s, choose_ s = None -> is_empty_ s = true.
Proof.
unfold choose_, is_empty_.
intros l H; case_eq (quicksort Elt l); [ | intros a k K; rewrite K in H; discriminate H].
clear H; intro H.
case_eq l; [intros _; apply refl_equal | ].
intros a k K; rewrite K, quicksort_equation in H.
destruct (ListSort.partition Elt a k) as [k1 k2]; 
  destruct (quicksort Elt k1); discriminate H.
Qed.

Lemma choose_spec3_ : 
  forall s1 s2, equal_ s1 s2 = true ->
                match choose_ s1 with
                  | None => choose_ s2 = None
                  | Some e1 => match choose_ s2 with
                                 | None => False
                                 | Some e2 => Oeset.compare Elt e1 e2 = Eq
                               end
                end.
Proof.
unfold equal_, choose_.
intros l1 l2 H; rewrite nb_occ_equal_ in H.
assert (K : Oeset.compare (mk_oelists Elt) (quicksort Elt l1) (quicksort Elt l2) = Eq).
{
  apply (sort_is_unique (OA := Elt) (quick_sorted Elt l1) (quick_sorted Elt l2)).
  refine (@_permut_incl 
            _ _ (fun x y => Oeset.eq_bool Elt x y = true) 
            _ _ _ _ (_permut_bool_true_is_sound _ _ _ _)).
  + intros a b K; unfold Oeset.eq_bool in K; rewrite compare_eq_true in K; apply K.
  + rewrite nb_occ_equal_; intro x.
    rewrite 2 (nb_occ_quicksort Elt); apply H.
}
destruct (quicksort Elt l1) as [ | a1 k1]; destruct (quicksort Elt l2) as [ | a2 k2];
try discriminate K; trivial.
simpl in K.
destruct (Oeset.compare Elt a1 a2); try discriminate K; trivial.
Qed.

Definition filter_ f (s : bag_) : bag_ := List.filter f s.

Lemma filter_spec_:
  forall (s : bag_) (f : elt -> bool),
    (forall e e', nb_occ_ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    forall (x : elt), nb_occ_ x (filter_ f s) = nb_occ_ x s * (if f x then 1 else 0).
Proof.
unfold nb_occ_, filter_.
intros l f H x; induction l as [ | a l]; simpl; [trivial | ].
assert (H' : forall e e' : elt, Oeset.nb_occ Elt e  l >= 1 ->
                                Oeset.compare Elt e e' = Eq -> f e = f e').
{
  intros a1 a2 K; apply H.
  rewrite Oeset.nb_occ_unfold, N.ge_le_iff.
  rewrite N.ge_le_iff in K; refine (N.le_trans _ _ _ K _).
  rewrite N.add_comm; apply N.le_add_r.
}   
case_eq (f a); intro Hfa.
- rewrite Oeset.nb_occ_unfold.
  case_eq (Oeset.compare Elt x a); intro Hx.
  + rewrite IHl, (H x a), Hfa, 2 N.mul_1_r; trivial.
    rewrite Oeset.nb_occ_unfold, Hx, N.ge_le_iff.
    apply N.le_add_r.
  + apply IHl; trivial.
  + apply IHl; trivial.
- case_eq (Oeset.compare Elt x a); intro Hx.
  + rewrite IHl, (H x a), Hfa, 2 N.mul_0_r; trivial.
    rewrite Oeset.nb_occ_unfold, Hx, N.ge_le_iff.
    apply N.le_add_r.
  + apply IHl; trivial.
  + apply IHl; trivial.
Qed.

Lemma filter_spec_weak_ : 
  forall (s : bag_) (f : elt -> bool)  (x : elt), 
    nb_occ_ x (filter_ f s) >= 1 -> nb_occ_ x s >= 1.
Proof.
unfold filter_; intro l; induction l as [ | x1 l]; intros f x H; simpl.
- simpl in H; apply H.
- simpl in H.
  case_eq (f x1); intro Hfx1; rewrite Hfx1 in H.
  + unfold nb_occ_ in H; rewrite Oeset.nb_occ_unfold in H.
    case_eq ( Oeset.compare Elt x x1); intro Hx; rewrite Hx in H.
    * unfold N.ge; destruct (nb_occ_ x l); simpl; [discriminate | ].
      destruct p; discriminate.
    * simpl; apply (IHl f x); apply H.
    * simpl; apply (IHl f x); apply H.
  + case_eq ( Oeset.compare Elt x x1); intro Hx.
    * unfold N.ge; destruct (nb_occ_ x l); simpl; [discriminate | ].
      destruct p; discriminate.
    * simpl; apply (IHl f x); apply H.
    * simpl; apply (IHl f x); apply H.
Qed.

Definition partition_ f (s : bag_) := List.partition f s.

Lemma partition_spec1_ : 
  forall (s : bag_) (x : elt) (f : elt -> bool),
    (forall e e', nb_occ_ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    nb_occ_ x (fst (partition_ f s)) = nb_occ_ x s * (if f x then 1 else 0).
Proof.
unfold partition_, nb_occ_.
intro l; induction l as [ | a1 l]; intros x f H; simpl; [apply refl_equal | ].
case_eq (List.partition f l); intros l1 l2 Hl.
assert (H' : forall e e' : elt, Oeset.nb_occ Elt e l >= 1 ->
                                Oeset.compare Elt e e' = Eq -> f e = f e').
{
intros x1 x2 K; apply H.  
rewrite Oeset.nb_occ_unfold.
rewrite N.ge_le_iff in K; rewrite N.ge_le_iff.
refine (N.le_trans _ _ _ K _); rewrite N.add_comm; apply N.le_add_r.
}
assert (IH := IHl x _ H'); rewrite Hl in IH; simpl fst in IH.
case_eq (Oeset.compare Elt x a1); intro Hx.
- assert (Hf : f x = f a1).
  {
    apply H; [ | assumption].
    rewrite Oeset.nb_occ_unfold, Hx, N.ge_le_iff.
    apply N.le_add_r.
  }
  rewrite Hf.
  case_eq (f a1); intro Hfa1; simpl fst.
  + rewrite Oeset.nb_occ_unfold, Hx, IH, Hf, Hfa1, 2 N.mul_1_r; apply refl_equal.
  + rewrite IH, Hf, Hfa1, 2 N.mul_0_r; apply refl_equal.
- case_eq (f a1); intro Hfa1; simpl fst.
  + rewrite Oeset.nb_occ_unfold, Hx, IH; apply refl_equal.
  + rewrite IH; apply refl_equal.
- case_eq (f a1); intro Hfa1; simpl fst.
  + rewrite Oeset.nb_occ_unfold, Hx, IH; apply refl_equal.
  + rewrite IH; apply refl_equal.
Qed.

Lemma partition_spec2_ : 
  forall (s : bag_) (x : elt) (f : elt -> bool),
    (forall e e', nb_occ_ e s >= 1 -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    nb_occ_ x (snd (partition_ f s)) = nb_occ_ x s * if (f x) then 0 else 1.
Proof.
unfold partition_, nb_occ_.
intro l; induction l as [ | a1 l]; intros x f H; simpl; [apply refl_equal | ].
case_eq (List.partition f l); intros l1 l2 Hl.
assert (H' : forall e e' : elt, Oeset.nb_occ Elt e l >= 1 ->
                                Oeset.compare Elt e e' = Eq -> f e = f e').
{
intros x1 x2 K; apply H.  
rewrite Oeset.nb_occ_unfold.
rewrite N.ge_le_iff in K; rewrite N.ge_le_iff.
refine (N.le_trans _ _ _ K _); rewrite N.add_comm; apply N.le_add_r.
}
assert (IH := IHl x _ H'); rewrite Hl in IH; simpl snd in IH.
case_eq (Oeset.compare Elt x a1); intro Hx.
- assert (Hf : f x = f a1).
  {
    apply H; [ | assumption].
    rewrite Oeset.nb_occ_unfold, Hx, N.ge_le_iff.
    apply N.le_add_r.
  }
  rewrite Hf.
  case_eq (f a1); intro Hfa1; simpl snd.
  + rewrite IH, Hf, Hfa1, 2 N.mul_0_r; apply refl_equal.
  + rewrite Oeset.nb_occ_unfold, Hx, IH, Hf, Hfa1, 2 N.mul_1_r; apply refl_equal.
- case_eq (f a1); intro Hfa1; simpl snd.
  + rewrite IH; apply refl_equal.
  + rewrite Oeset.nb_occ_unfold, Hx, IH; apply refl_equal.
- case_eq (f a1); intro Hfa1; simpl snd.
  + rewrite IH; apply refl_equal.
  + rewrite Oeset.nb_occ_unfold, Hx, IH; apply refl_equal.
Qed.

Definition for_all_ f (s : bag_) := forallb f s.

Lemma for_all_spec_ : forall (s : bag_) (f : elt -> bool), for_all_ f s = forallb f (elements_ s).
Proof.
unfold for_all_, elements_.
intros l f; rewrite eq_bool_iff, 2 forallb_forall; split; intros H x Hx; apply H.
- rewrite <- In_quicksort in Hx; assumption.
- rewrite <- In_quicksort; assumption.
Qed.

Definition exists__ f (s : bag_) := existsb f s.

Lemma exists_spec_ : forall (s : bag_) (f : elt -> bool), exists__ f s = existsb f (elements_ s).
Proof.
unfold exists__, elements_.
intros l f; rewrite eq_bool_iff, 2 existsb_exists; split.
- intros [x [Hx Kx]]; exists x; split; [ | assumption].
  rewrite <- In_quicksort; assumption.
- intros [x [Hx Kx]]; exists x; split; [ | assumption].
  rewrite <- In_quicksort in Hx; assumption.
Qed.

Definition fold_ (A : Type) (f : elt -> A -> A) (s : bag_) (a : A) := 
  fold_left (fun (a : A) (e : elt) => f e a) (elements_ s) a.

Definition fold_spec_ : 
  forall (s : bag_) (A : Type) a0 (f : elt -> A -> A),
    fold_ f s a0 = fold_left (fun (a : A) (e : elt) => f e a) (elements_ s) a0.
Proof.
intros; apply refl_equal.
Qed.

Definition compare_ (s1 s2 : bag_) := 
  Oeset.compare (mk_oelists Elt) (elements_ s1) (elements_ s2).

Lemma compare_spec_ : forall s1 s2, compare_ s1 s2 = Eq <-> equal_ s1 s2 = true.
Proof.
intros s1 s2; split; intro H.
- rewrite nb_occ_equal_; unfold nb_occ_.
  intro; apply permut_nb_occ.
  apply permut_trans with (quicksort Elt s1); [apply quick_permut | ].
  apply permut_trans with (quicksort Elt s2); [ | apply permut_sym; apply quick_permut].
  unfold compare_, elements_ in H.
  set (l1 := quicksort Elt s1) in *; clearbody l1; clear s1.
  set (l2 := quicksort Elt s2) in *; clearbody l2; clear s2.
  revert l2 H; induction l1 as [ | a1 l1]; intros [ | a2 l2]; simpl.
  + intros _; apply Pnil.
  + intro Abs; discriminate Abs.
  + intro Abs; discriminate Abs.
  + case_eq (Oeset.compare Elt a1 a2); intros Ha H; try discriminate H.
    apply permut_cons; [ | apply IHl1]; assumption.
- unfold equal_ in H; unfold compare_.
  apply sort_is_unique.
  + apply quick_sorted.
  + apply quick_sorted.
  + apply permut_trans with s2;  [ | apply quick_permut].
    apply permut_trans with s1; [apply permut_sym; apply quick_permut | ].
    refine (_permut_incl _ _ (_permut_bool_true_is_sound (Oeset.eq_bool Elt) _ _ _)).  
    * unfold Oeset.eq_bool; intros a b K; rewrite compare_eq_true in K; apply K.
    * assumption.
Qed.

Lemma compare_eq_trans_ : 
  forall a1 a2 a3, compare_ a1 a2 = Eq -> compare_ a2 a3 = Eq -> compare_ a1 a3 = Eq.
Proof.
do 3 intro; apply Oeset.compare_eq_trans.
Qed.

Lemma compare_eq_lt_trans_ : 
  forall a1 a2 a3, compare_ a1 a2 = Eq -> compare_ a2 a3 = Lt -> compare_ a1 a3 = Lt.
Proof.
do 3 intro; apply Oeset.compare_eq_lt_trans.
Qed.

Lemma compare_lt_eq_trans_ : 
  forall a1 a2 a3, compare_ a1 a2 = Lt -> compare_ a2 a3 = Eq -> compare_ a1 a3 = Lt.
Proof.
do 3 intro; apply Oeset.compare_lt_eq_trans.
Qed.

Lemma compare_lt_trans_ : 
  forall a1 a2 a3, compare_ a1 a2 = Lt -> compare_ a2 a3 = Lt -> compare_ a1 a3 = Lt.
Proof.
do 3 intro; apply Oeset.compare_lt_trans.
Qed.

Lemma compare_lt_gt_ : forall a1 a2, compare_ a1 a2 = CompOpp (compare_ a2 a1).
Proof.
do 2 intro; apply Oeset.compare_lt_gt.
Qed.


Definition build : Rcd Elt :=
  mk_R Elt
      (bag := bag_)
      (Oeset.nb_occ Elt)
      add_
      add_spec_
      singleton_
      singleton_spec_
      union_
      nb_occ_union_
      union_max_
      union_max_spec_
      inter_
      nb_occ_inter_
      diff_
      diff_spec_
      equal_
      nb_occ_equal_
      subbag_
      subbag_spec_
      empty_
      empty_spec_
      is_empty_
      is_empty_spec_
      elements_
      elements_empty_
      elements_spec1_
      mem_elements_
      elements_spec3_
      choose_
      choose_spec1_
      choose_spec2_
      choose_spec3_
      filter_
      filter_spec_ filter_spec_weak_
      partition_
      partition_spec1_
      partition_spec2_
      for_all_
      for_all_spec_
      exists__
      exists_spec_
      fold_
      fold_spec_
      compare_
      compare_spec_
      compare_eq_trans_
      compare_eq_lt_trans_ 
      compare_lt_eq_trans_
      compare_lt_trans_ 
      compare_lt_gt_.

End Build.

Section Facts.

Hypothesis A : Type.
Hypothesis EA : Oeset.Rcd A.
Hypothesis BA : Rcd EA.

Lemma nb_occ_eq_2 :
  forall s1 s2, equal BA s1 s2 = true -> forall x, nb_occ BA x s1 = nb_occ BA x s2.
Proof.
intros s1 s2 Hs x.
rewrite nb_occ_equal in Hs; apply Hs.
Qed.

Lemma equal_eq_1 : 
  forall s1 s2 s1', equal BA s1 s1' = true -> equal BA s1 s2 = equal BA s1' s2.
Proof.
intros s1 s2 s1' H1.
rewrite nb_occ_equal in H1.
rewrite eq_bool_iff, 2 nb_occ_equal.
split; intros H e; [rewrite <- H1 | rewrite H1]; apply H.
Qed.

Lemma equal_eq_2 : 
  forall s1 s2 s2', equal BA s2 s2' = true -> equal BA s1 s2 = equal BA s1 s2'.
Proof.
intros s1 s2 s2' H2.
rewrite nb_occ_equal in H2.
rewrite eq_bool_iff, 2 nb_occ_equal.
split; intros H e; [rewrite <- H2 | rewrite H2]; apply H.
Qed.

Lemma equal_trans : 
  forall s1 s2 s3, equal BA s1 s2 = true -> equal BA s2 s3 = true -> equal BA s1 s3 = true.
Proof.
intros s1 s2 s3 H1 H2.
rewrite nb_occ_equal in H1, H2; rewrite nb_occ_equal; intro x; rewrite H1; apply H2.
Qed.

Lemma equal_sym : 
  forall s1 s2, equal BA s1 s2 = true -> equal BA s2 s1 = true.
Proof.
intros s1 s2 H1.
rewrite nb_occ_equal in H1; rewrite nb_occ_equal; intro x; rewrite H1; apply refl_equal.
Qed.

Definition mem a s := Oeset.mem_bool EA a (elements BA s).

Lemma mem_unfold : forall a s, mem a s = Oeset.mem_bool EA a (elements BA s).
Proof.
intros; apply refl_equal.
Qed.

Lemma mem_nb_occ :
  forall a s, mem a s = match Ncompare (nb_occ BA a s) 0 with
    | Lt | Eq => false
    | Gt => true
  end.
Proof.
intros a s; unfold mem.
rewrite nb_occ_elements.
generalize (Oeset.mem_nb_occ EA a (elements BA s)) (Oeset.not_mem_nb_occ EA a (elements BA s)).
case (Oeset.mem_bool EA a (elements BA s)).
- intros H _; generalize (H (refl_equal _)).
  destruct (Oeset.nb_occ EA a (elements BA s)).
  + intro Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros; apply refl_equal.
- intros _ H; rewrite (H (refl_equal _)); apply refl_equal.
Qed.

Lemma nb_occ_mem : forall a s, nb_occ BA a s <> 0%N -> mem a s = true.
Proof.
intros a s H; unfold mem.
apply Oeset.nb_occ_mem.
rewrite <- nb_occ_elements; assumption.
Qed.

Lemma not_mem_nb_occ :
  forall a s, mem a s = false -> nb_occ BA a s = 0%N.
Proof.
intros a s; rewrite mem_nb_occ.
case_eq (nb_occ BA a s); trivial.
intros p _ Hp; discriminate Hp.
Qed.

Lemma mem_eq_1 :
  forall s x1 x2, Oeset.compare EA x1 x2 = Eq -> mem x1 s = mem x2 s.
Proof.
intros s x1 x2 H.
rewrite eq_bool_iff; split; intro Hx; apply nb_occ_mem; intro Kx.
- rewrite nb_occ_elements in Kx.
  rewrite mem_nb_occ, nb_occ_elements, (Oeset.nb_occ_eq_1 _ _ _ _ H), Kx in Hx.
  discriminate Hx.
- rewrite nb_occ_elements in Kx.
  rewrite mem_nb_occ, nb_occ_elements, <- (Oeset.nb_occ_eq_1 _ _ _ _ H), Kx in Hx.
  discriminate Hx.
Qed.

Lemma mem_eq_2 :
  forall s1 s2, equal BA s1 s2 = true -> forall x, mem x s1 = mem x s2.
Proof.
intros s1 s2 H x.
rewrite nb_occ_equal in H.
rewrite eq_bool_iff; split; intro Hx; apply nb_occ_mem; intro Kx.
- rewrite mem_nb_occ, H, Kx in Hx; discriminate Hx.
- rewrite mem_nb_occ, <- H, Kx in Hx; discriminate Hx.
Qed.

Lemma mem_eq :
  forall s1 s2 x1 x2, equal BA s1 s2 = true -> Oeset.compare EA x1 x2 = Eq ->
                      mem x1 s1 = mem x2 s2.
Proof.
intros s1 s2 x1 x2 Hs Hx.
rewrite (mem_eq_1 _ _ _ Hx).
apply mem_eq_2; assumption.
Qed.

Lemma mem_union :
  forall a s1 s2, mem a (union BA s1 s2) = orb (mem a s1) (mem a s2).
Proof.
intros a s1 s2; rewrite 3 mem_nb_occ, nb_occ_union.
destruct (nb_occ BA a s1); simpl; [apply refl_equal | ].
destruct (nb_occ BA a s2); trivial.
Qed.

Lemma mem_inter :
  forall a s1 s2, mem a (inter BA s1 s2) = andb (mem a s1) (mem a s2).
Proof.
intros a s1 s2; rewrite 3 mem_nb_occ, nb_occ_inter.
destruct (nb_occ BA a s1); [simpl; rewrite N.min_0_l; apply refl_equal | ].
destruct (nb_occ BA a s2); simpl; trivial.
unfold N.min; simpl; destruct ((p ?= p0)%positive); trivial.
Qed.

Lemma diff_spec_weak :
  forall a s1 s2, mem a (diff BA s1 s2) = true -> mem a s1 = true.
Proof.
intros a s1 s2; rewrite 2 mem_nb_occ, nb_occ_diff.
case_eq (nb_occ BA a s1 - nb_occ BA a s2 ?= 0); try discriminate.
intros H _.
case_eq (nb_occ BA a s1 ?= 0); trivial.
- intro K; rewrite N.compare_eq_iff in K; rewrite K in H.
  destruct (nb_occ BA a s2); simpl in H; discriminate H.
- intro K; destruct (nb_occ BA a s1); simpl in K; discriminate K.
Qed.

Lemma empty_spec_weak : forall a, mem a (empty BA) = false.
Proof.
intro a; rewrite mem_nb_occ, nb_occ_empty; simpl; apply refl_equal.
Qed.

Lemma in_elements_mem :
  forall x b, In x (elements BA b) -> mem x b = true.
Proof.
intros x b H.
unfold mem; rewrite Oeset.mem_bool_true_iff.
exists x; split; [apply Oeset.compare_eq_refl | assumption].
Qed.

Fixpoint mk_bag (l : list A) :=
  match l with
    | nil => empty BA
    | a1 :: l => add _ a1 (mk_bag l)
  end.

Lemma mk_bag_unfold :
  forall l, mk_bag l = 
  match l with
    | nil => empty BA
    | a1 :: l => add _ a1 (mk_bag l)
  end.
Proof.
intro l; case l; intros; apply refl_equal.
Qed.

Lemma mem_mk_bag : 
  forall a l, mem a (mk_bag l) = Oeset.mem_bool EA a l.
Proof.
intros a l; rewrite mem_nb_occ.
induction l as [ | a1 l]; simpl.
- rewrite nb_occ_empty; simpl; apply refl_equal.
- rewrite nb_occ_add.
  destruct (Oeset.eq_bool EA a a1); simpl.
  + destruct (nb_occ BA a (mk_bag l)); trivial.
  + apply IHl.
Qed.

Lemma nb_occ_mk_bag :
  forall a l, nb_occ BA a (mk_bag l) = Oeset.nb_occ EA a l.
Proof.
intros a l; induction l as [ | a1 l]; simpl.
- rewrite nb_occ_empty; apply refl_equal.
- rewrite nb_occ_add; unfold Oeset.eq_bool; rewrite IHl.
  case (Oeset.compare EA a a1); apply refl_equal.
Qed.

Lemma elements_mk_bag :
  forall b, equal BA (mk_bag (elements BA b)) b = true.
Proof.
intro b; rewrite nb_occ_equal; intro; rewrite nb_occ_mk_bag, nb_occ_elements.
apply refl_equal.
Qed.

Definition interp_set_op o b1 b2 :=
  match o with
    | UnionMax => union_max BA b1 b2
    | Union => union BA b1 b2
    | Inter => inter BA b1 b2
    | Diff => diff BA b1 b2
  end.

Fixpoint Union l : bag BA :=
  match l with
    | nil => empty _
    | a :: l => union _ a (Union l)
  end.

Lemma elements_singleton :
  forall x, exists x', (Oeset.compare EA x x' = Eq) /\ elements BA (singleton BA x) = x' :: nil.
Proof.
intros x.
assert (H := nb_occ_singleton BA x x).
unfold Oeset.eq_bool in H; rewrite Oeset.compare_eq_refl in H.
rewrite nb_occ_elements in H.
assert (K : mem x (singleton BA x) = true).
{
  unfold mem.
  generalize (Oeset.not_mem_nb_occ EA x (elements BA (singleton BA x))).
  case (Oeset.mem_bool EA x (elements BA (singleton BA x))); trivial.
  intro Abs; rewrite (Abs (refl_equal _)) in H; discriminate H.
}
unfold mem in K.
rewrite Oeset.mem_bool_true_iff in K.
destruct K as [x' [Hx' K]].
exists x'; split; [assumption | ].
set (l1 := elements BA (singleton BA x)).
assert (Hl1 : forall x2, In x2 l1 -> Oeset.compare EA x2 x = Eq).
{
  intros x2 Hx2.
  destruct (in_split _ _ Hx2) as [l2 [l3 L]]; subst l1.  
  assert (K' := nb_occ_singleton BA x x2).
  rewrite nb_occ_elements, L, Oeset.nb_occ_app, 
  (Oeset.nb_occ_unfold _ _ (_ :: _)), Oeset.compare_eq_refl in K'.
  unfold Oeset.eq_bool in K'.
  case_eq (Oeset.compare EA x2 x); intro Kx2; rewrite Kx2 in K'.
  - apply refl_equal.
  - destruct (Oeset.nb_occ EA x2 l2); destruct (Oeset.nb_occ EA x2 l3); discriminate K'.
  - destruct (Oeset.nb_occ EA x2 l2); destruct (Oeset.nb_occ EA x2 l3); discriminate K'.
}
subst l1.
case_eq (elements BA (singleton BA x)); [intro J | intros x1 l1 J];
rewrite J in K.
- contradiction K.
- assert (Kl1 : l1 = nil).
  {
    destruct l1 as [ | x2 l1]; [apply refl_equal | ].
    assert (L := nb_occ_singleton BA x x2).
    rewrite nb_occ_elements, J in L.
    unfold Oeset.eq_bool in L.
    rewrite J in Hl1.
    assert (Hx1 := Hl1 x1 (or_introl _ (refl_equal _))).
    assert (Hx2 := Hl1 x2 (or_intror _ (or_introl _ (refl_equal _)))).
    rewrite 2 Oeset.nb_occ_unfold, Oeset.compare_eq_refl, Hx2 in L.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in Hx1.
    rewrite (Oeset.compare_eq_trans _ _ _ _ Hx2 Hx1) in L.
    destruct (Oeset.nb_occ EA x2 l1); try discriminate L.
    destruct p; discriminate L.
  }
  apply f_equal2; [ | assumption].
  subst l1; simpl in K; destruct K as [K | K]; [assumption | contradiction K].
Qed.

Lemma filter_eq :
  forall f1 f2 s1 s2, 
    equal BA s1 s2 = true -> 
    (forall x1 x2, nb_occ BA x1 s1 >= 1 -> Oeset.compare EA x1 x2 = Eq -> f1 x1 = f2 x2) -> 
    equal BA (filter BA f1 s1) (filter BA f2 s2) = true.
Proof.
intros f1 f2 s1 s2 Hs Ks.
rewrite nb_occ_equal in Hs.
rewrite nb_occ_equal; intro t.
rewrite 2 nb_occ_filter, <- Hs.
- case_eq (nb_occ BA t s1).
  + intros; rewrite 2 N.mul_0_l; apply refl_equal.
  + intros p Hp; apply f_equal.
    apply if_eq; trivial.
    apply Ks.
    * rewrite Hp; destruct p; discriminate.
    * apply Oeset.compare_eq_refl.
- intros e1 e2 He1 He.
  rewrite <- Hs in He1.
  rewrite <- (Ks _ _ He1 He); apply sym_eq.
  apply Ks; trivial.
  apply Oeset.compare_eq_refl.
- intros e1 e2 He1 He.
  rewrite (Ks _ _ He1 He); apply sym_eq.
  apply Ks.
  + rewrite nb_occ_elements, <- (Oeset.nb_occ_eq_1 _ _ _ _ He), <- nb_occ_elements.
    assumption.
  + apply Oeset.compare_eq_refl.
Qed.

Lemma filter_eq_2 :
  forall f s1 s2, 
    equal BA s1 s2 = true -> 
    (forall x1 x2, nb_occ BA x1 s1 >= 1 -> Oeset.compare EA x1 x2 = Eq -> f x1 = f x2) -> 
    equal BA (filter BA f s1) (filter BA f s2) = true.
Proof.
intros f s1 s2 Hs Ks.
apply filter_eq; trivial.
Qed.

Lemma filter_true :
  forall b, equal BA (filter BA (fun _ => true) b) b = true.
Proof.
intro b; rewrite nb_occ_equal.
intros a; rewrite nb_occ_filter; [ | intros; trivial].
rewrite N.mul_1_r; apply refl_equal.
Qed.

Lemma mk_bag_filter :
  forall f s, 
    (forall x1 x2, nb_occ BA x1 s >= 1 -> Oeset.compare EA x1 x2 = Eq -> f x1 = f x2) -> 
    equal BA (filter BA f s) (mk_bag (List.filter f (elements BA s))) = true.
Proof.
intros f s H.
rewrite nb_occ_equal.
intro t.
rewrite nb_occ_filter; [ | trivial].
rewrite nb_occ_mk_bag, Oeset.nb_occ_filter, nb_occ_elements.
- case (f t).
  + rewrite N.mul_1_r; apply refl_equal.
  + rewrite N.mul_0_r; apply refl_equal.
- intros x1 x2 Hx; apply H.
  rewrite nb_occ_elements.
  generalize (Oeset.mem_nb_occ _ _ _ Hx).
  destruct (Oeset.nb_occ EA x1 (elements BA s)).
  + intro Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros _; destruct p; discriminate.
Qed.

Definition OBag : Oeset.Rcd (bag BA).
split with (compare BA).
- apply compare_eq_trans.
- apply compare_eq_lt_trans.
- apply compare_lt_eq_trans.
- apply compare_lt_trans.
- apply compare_lt_gt.
Defined.

Lemma mem_union_max :
  forall x b1 b2, mem x (union_max BA b1 b2) = mem x b1 || mem x b2.
Proof.
  intros x b1 b2; unfold mem.
  assert (H := nb_occ_union_max BA b1 b2 x).
  rewrite 3 nb_occ_elements in H.
  case_eq (Oeset.mem_bool EA x (elements BA (union_max BA b1 b2))); intro K.
  - case_eq (Oeset.mem_bool EA x (elements BA b1)); intro K1; [trivial | ].
    case_eq (Oeset.mem_bool EA x (elements BA b2)); intro K2; [trivial | ].
    rewrite (Oeset.not_mem_nb_occ _ _ _ K1), (Oeset.not_mem_nb_occ _ _ _ K2) in H.
    generalize (Oeset.mem_nb_occ _ _ _ K).
    rewrite H; intro Abs; apply False_rec; apply Abs; apply refl_equal.
  - case_eq (Oeset.mem_bool EA x (elements BA b1)); intro K1.
    + rewrite (Oeset.not_mem_nb_occ _ _ _ K) in H.
      generalize (Oeset.mem_nb_occ _ _ _ K1).
      destruct (Oeset.nb_occ EA x (elements BA b1)).
      * intro Abs; apply False_rec; apply Abs; apply refl_equal.
      * destruct (Oeset.nb_occ EA x (elements BA b2)); simpl in H; try discriminate H.
        unfold N.max in H.
        destruct (N.pos p ?= N.pos p0); discriminate H.
    + case_eq (Oeset.mem_bool EA x (elements BA b2)); intro K2; [ | apply refl_equal].
      rewrite (Oeset.not_mem_nb_occ _ _ _ K), (Oeset.not_mem_nb_occ _ _ _ K1) in H.
      rewrite N.max_0_l in H.
      generalize (Oeset.mem_nb_occ _ _ _ K2); rewrite <- H.
      intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma mem_filter :
  forall f c,
    (forall x1 x2, mem x1 c = true -> Oeset.compare EA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, mem x (filter BA f c) = andb (mem x c) (f x).
Proof.
intros f b H x; simpl.
unfold mem.
assert (H' : forall e e' : A,
                 (nb_occ BA e b >= 1)%N -> Oeset.compare EA e e' = Eq -> f e = f e').
{
  intros x1 x2 Hx; apply H.
  simpl; unfold mem.
  generalize (Oeset.not_mem_nb_occ EA x1 (Febag.elements BA b)).
  destruct (Oeset.mem_bool EA x1 (Febag.elements BA b)); trivial.
  intro Abs; rewrite nb_occ_elements, (Abs (refl_equal _)) in Hx.
  unfold N.ge in Hx; apply False_rec; apply Hx; apply refl_equal.
}
assert (K := nb_occ_filter BA b f H' x).
rewrite 2 nb_occ_elements in K.
case_eq (Oeset.mem_bool EA x (elements BA (Febag.filter BA f b))); intro H1;
case_eq ((Oeset.mem_bool EA x (elements BA b) && f x)%bool); intro H2; trivial.
+ rewrite Bool.andb_false_iff in H2.
  destruct H2 as [H2 | H2].
  * rewrite (Oeset.not_mem_nb_occ _ _ _ H2), N.mul_0_l in K.
    generalize (Oeset.mem_nb_occ _ _ _ H1); rewrite K.
    intro Abs; apply False_rec; apply Abs; apply refl_equal.
  * rewrite H2, N.mul_0_r in K.
    generalize (Oeset.mem_nb_occ _ _ _ H1); rewrite K.
    intro Abs; apply False_rec; apply Abs; apply refl_equal.
+ rewrite Bool.andb_true_iff in H2.
  rewrite (Oeset.not_mem_nb_occ _ _ _ H1), (proj2 H2), N.mul_1_r in K.
  generalize (Oeset.mem_nb_occ _ _ _ (proj1 H2)); rewrite <- K.
  intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma diff_set :
  forall c1 c2, 
    (forall x, mem x c1 = true <-> nb_occ BA x c1 = 1) -> 
    (forall x, mem x c2 = true <-> nb_occ BA x c2 = 1) ->
    ((forall x, mem x (diff BA c1 c2) = true <-> nb_occ BA x (diff BA c1 c2) = 1) /\
    (forall x, nb_occ BA x (diff BA c1 c2) = 1 <-> (mem x c1 = true /\ mem x c2 = false))).
Proof.
intros c1 c2 H1 H2; split; (intro x; split).
- intro H.
  case_eq (nb_occ BA x (diff BA c1 c2)).
  + intro Hp; rewrite mem_nb_occ, Hp in H; discriminate H.
  + intros p Hp.
    rewrite nb_occ_diff in Hp.
    case_eq (nb_occ BA x c1).
    * intro Hp1; rewrite Hp1 in Hp; discriminate Hp.
    * intros p1 Hp1.
      {
        case_eq (mem x c1); intro Hx1.
        - rewrite H1 in Hx1; rewrite Hx1 in Hp1, Hp.
          destruct p1; try discriminate Hp1.
          case_eq (nb_occ BA x c2).
          + intro Hp2; rewrite Hp2 in Hp; apply sym_eq; apply Hp.
          + intros p2 Hp2; rewrite Hp2 in Hp.
            destruct p2; discriminate Hp.
        - rewrite mem_nb_occ, Hp1 in Hx1; discriminate Hx1.
      } 
- intro H; rewrite mem_nb_occ, H; apply refl_equal.
- rewrite nb_occ_diff; intro H.
  case_eq (mem x c1); intro Hx1.
  + split; [apply refl_equal | ].
    rewrite H1 in Hx1; rewrite Hx1 in H.
    case_eq (nb_occ BA x c2); [intro Hx2 | intros p2 Hx2].
    * case_eq (mem x c2); intro Kx2; [ | apply refl_equal].
      rewrite H2 in Kx2; rewrite Kx2 in Hx2; discriminate Hx2.
    * rewrite Hx2 in H.
      destruct p2; discriminate H.
  + rewrite mem_nb_occ in Hx1.
    destruct (nb_occ BA x c1) as [ | p1]; [discriminate H | ].
    discriminate Hx1.
- intros [Hx1 Hx2]; rewrite nb_occ_diff.
  rewrite H1 in Hx1; rewrite Hx1.
  rewrite (not_mem_nb_occ _ _ Hx2); apply refl_equal.
Qed.

End Facts.

Section Facts2.

Hypothesis A B : Type.
Hypothesis EA : Oeset.Rcd A.
Hypothesis BA : Rcd EA.
Hypothesis EB : Oeset.Rcd B.
Hypothesis BB : Rcd EB.

Definition map f (b : bag BA) := mk_bag BB (List.map f (elements BA b)).

Lemma map_unfold :
  forall f b, map f b = mk_bag BB (List.map f (elements BA b)).
Proof.
intros; apply refl_equal.
Qed.

Lemma mem_map :
  forall (f : A -> B) (c : bag BA) b,
    mem BB b (map f c) = true <-> 
    (exists a, Oeset.compare EB b (f a) = Eq /\ In a (elements BA c)).
Proof.
intros f c b; unfold map; rewrite mem_mk_bag, Oeset.mem_bool_true_iff; split.
- intros [fa [Hb Hfa]]; rewrite in_map_iff in Hfa.
  destruct Hfa as [a [Hfa Ha]]; subst fa.
  exists a; split; assumption.
- intros [a [Hb Ha]]; exists (f a); split; [assumption | ].
  rewrite in_map_iff; exists a; split; trivial.
Qed.

Lemma map_filter_and :
  forall (g : A -> B) (f1 f2 : A -> bool) (c : bag BA),
    (forall x1 x2, mem BA x1 c = true -> Oeset.compare EA x1 x2 = Eq -> 
                   Oeset.compare EB (g x1) (g x2) = Eq) ->
    (forall e e', nb_occ BA e c >= 1 -> Oeset.compare EB (g e) (g e') = Eq -> f1 e = f1 e') ->
    (forall e e', nb_occ BA e c >= 1 -> Oeset.compare EB (g e) (g e') = Eq -> f2 e = f2 e') ->
    equal BB (map g (filter BA (fun x => f1 x && f2 x) c)) 
          (inter BB (map g (filter BA f1 c)) (map g (filter BA f2 c))) = true.
Proof.
intros g f1 f2 c H H1 H2; rewrite nb_occ_equal; intros x.
rewrite nb_occ_inter; unfold map.
rewrite 3 nb_occ_mk_bag.
apply trans_eq with
  (Oeset.nb_occ EB x (List.map g (List.filter (fun x0 : A => f1 x0 && f2 x0) (elements BA c)))).
- apply permut_nb_occ.
  apply _permut_map with (fun x1 x2 => Oeset.compare EA x1 x2 = Eq).
  + intros x1 x2 Hx1 _; apply H.
    generalize (in_elements_mem _ _ _ Hx1); clear Hx1; intro Hx1.
    rewrite mem_nb_occ, nb_occ_filter in Hx1.
    * rewrite (mem_nb_occ BA x1 c).
      {
        case_eq ( nb_occ BA x1 c).
        - intro Kx1; rewrite Kx1, N.mul_0_l in Hx1; discriminate Hx1.
        - intros p _; apply refl_equal.
      } 
      * {
          intros y1 y2 Hy Ky; apply f_equal2.
          - apply H1; trivial.
            apply H; trivial.
            rewrite mem_nb_occ.
            destruct (nb_occ BA y1 c); trivial.
            apply False_rec; apply Hy; apply refl_equal.
          - apply H2; trivial.
            apply H; trivial.
            rewrite mem_nb_occ.
            destruct (nb_occ BA y1 c); trivial.
            apply False_rec; apply Hy; apply refl_equal.
      }
  + apply nb_occ_permut; clear x; intro x.
    rewrite <- nb_occ_elements, nb_occ_filter, Oeset.nb_occ_filter.
    * case (f1 x && f2 x); 
      [rewrite N.mul_1_r; rewrite nb_occ_elements | rewrite N.mul_0_r]; apply refl_equal.
    * {
        intros y1 y2 Hy Ky; apply f_equal2.
        - apply H1; trivial.
          + rewrite nb_occ_elements.
            generalize (Oeset.mem_nb_occ EA _ _ Hy).
            destruct (Oeset.nb_occ EA y1 (elements BA c)).
            * intro Abs; apply False_rec; apply Abs; apply refl_equal.
            * intros _; destruct p; discriminate.
          +  apply H; trivial.
        - apply H2; trivial.
          + rewrite nb_occ_elements.
            generalize (Oeset.mem_nb_occ EA _ _ Hy).
            destruct (Oeset.nb_occ EA y1 (elements BA c)).
            * intro Abs; apply False_rec; apply Abs; apply refl_equal.
            *  intros _; destruct p; discriminate.
          + apply H; trivial.
      } 
    * {
        intros y1 y2 Hy Ky; apply f_equal2.
        - apply H1; trivial.
          apply H; trivial.
          rewrite mem_nb_occ.
          destruct (nb_occ BA y1 c); trivial.
          apply False_rec; apply Hy; apply refl_equal.
        - apply H2; trivial.
          apply H; trivial.
          rewrite mem_nb_occ.
          destruct (nb_occ BA y1 c); trivial.
          apply False_rec; apply Hy; apply refl_equal.
      } 
- rewrite (Oeset.map_filter_and EA).
  apply f_equal2.
  + apply permut_nb_occ.
    apply _permut_map with (fun x1 x2 => Oeset.compare EA x1 x2 = Eq).
    * intros x1 x2 Hx1 _; apply H.
      rewrite filter_In in Hx1.
      apply (in_elements_mem _ _ _ (proj1 Hx1)).
    * apply nb_occ_permut; clear x; intro x.
      {
        rewrite <- nb_occ_elements, nb_occ_filter, Oeset.nb_occ_filter.
        - case (f1 x); 
          [rewrite N.mul_1_r; rewrite nb_occ_elements | rewrite N.mul_0_r]; 
          apply refl_equal.
        - intros y1 y2 Hy Ky; apply H1; trivial.
          + rewrite nb_occ_elements.
            generalize (Oeset.mem_nb_occ EA _ _ Hy).
            destruct (Oeset.nb_occ EA y1 (elements BA c)).
            * intro Abs; apply False_rec; apply Abs; apply refl_equal.
            * intros _; destruct p; discriminate.
          + apply H; trivial.
        - intros y1 y2 Hy Ky; apply H1; trivial.
          apply H; trivial.
          rewrite mem_nb_occ.
          destruct (nb_occ BA y1 c); trivial.
          apply False_rec; apply Hy; apply refl_equal.
      } 
  + apply permut_nb_occ.
    apply _permut_map with (fun x1 x2 => Oeset.compare EA x1 x2 = Eq).
    * intros x1 x2 Hx1 _; apply H.
      rewrite filter_In in Hx1.
      apply (in_elements_mem _ _ _ (proj1 Hx1)).
    * apply nb_occ_permut; clear x; intro x.
      {
        rewrite <- nb_occ_elements, nb_occ_filter, Oeset.nb_occ_filter.
        - case (f2 x); 
          [rewrite N.mul_1_r; rewrite nb_occ_elements | rewrite N.mul_0_r]; 
          apply refl_equal.
        - intros y1 y2 Hy Ky; apply H2; trivial.
          + rewrite nb_occ_elements.
            generalize (Oeset.mem_nb_occ EA _ _ Hy).
            destruct (Oeset.nb_occ EA y1 (elements BA c)).
            * intro Abs; apply False_rec; apply Abs; apply refl_equal.
            * intros _; destruct p; discriminate.
          + apply H; trivial.
        - intros y1 y2 Hy Ky; apply H2; trivial.
          apply H; trivial.
          rewrite mem_nb_occ.
          destruct (nb_occ BA y1 c); trivial.
          apply False_rec; apply Hy; apply refl_equal.
      } 
  + intros y1 y2 Hy Ky; apply H1; trivial.
    rewrite nb_occ_elements.
    generalize (Oeset.mem_nb_occ EA _ _ Hy).
    destruct (Oeset.nb_occ EA y1 (elements BA c)).
    * intro Abs; apply False_rec; apply Abs; apply refl_equal.
    * intros _; destruct p; discriminate.
  + intros y1 y2 Hy Ky; apply H2; trivial.
    rewrite nb_occ_elements.
    generalize (Oeset.mem_nb_occ EA _ _ Hy).
    destruct (Oeset.nb_occ EA y1 (elements BA c)).
    * intro Abs; apply False_rec; apply Abs; apply refl_equal.
    * intros _; destruct p; discriminate.
Qed.

End Facts2.

End Febag.

Close Scope N_scope.

Notation "a 'inBE' V" := (Febag.mem _ a V = true) (at level 70, no associativity).
Notation "a 'inBE?' V" := (Febag.mem _ a V) (at level 70, no associativity).
Notation "s1 '=BE=' s2" := (Febag.equal _ s1 s2 = true) (at level 70, no associativity).
Notation "s1 '=BE?=' s2" := (Febag.equal _ s1 s2) (at level 70, no associativity).
Notation "s1 'unionBE' s2" := (Febag.union _ s1 s2) (at level 70, no associativity).
Notation "s1 'interBE' s2" := (Febag.inter _ s1 s2) (at level 70, no associativity).
Notation "'emptysetBE'" := (Febag.empty _) (at level 70, no associativity).
Notation "a 'addBE' s" := (Febag.add _ a s) (at level 70, no associativity).
