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

(** Finite sets as records, in order to have them compatible with the section mechanism of Coq. #<br>#
    This file is simply an adaptation of the finite sets of Letouzey, from the standard library of Coq. *)

Set Implicit Arguments.

Require Import Bool List Sorted SetoidList Arith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet FiniteSetImpl. 

Inductive set_op : Type :=
  | Union
  | UnionMax
  | Inter
  | Diff.

Module Feset.
Record Rcd (elt : Type) (Elt : Oeset.Rcd elt) : Type :=
  mk_R
    {
      set : Type;
      mem : elt -> set -> bool;
      add : elt -> set -> set;
      add_spec : forall s a e, mem e (add a s) = Oeset.eq_bool Elt e a || mem e s;
      singleton : elt -> set;
      singleton_spec : 
        forall x y : elt, mem y (singleton x) = Oeset.eq_bool Elt y x;
      union : set -> set -> set;
      mem_union : forall (s s' : set) (x : elt), mem x (union s s') = mem x s || mem x s';
      inter : set -> set -> set;
      mem_inter : forall (s s' : set) (x : elt), mem x (inter s s') = mem x s && mem x s';
      diff : set -> set -> set;
      mem_diff : forall (s s' : set) (x : elt), mem x (diff s s') = mem x s && negb (mem x s');
      equal : set -> set -> bool;
      equal_spec : forall s1 s2, equal s1 s2 = true <-> (forall e, mem e s1 = mem e s2);
      subset : set -> set -> bool;
      subset_spec : 
        forall s1 s2, subset s1 s2 = true <-> (forall e, mem e s1 = true -> mem e s2 = true);
      empty : set;     
      empty_spec : forall e, mem e empty = false;
      is_empty : set -> bool;
      is_empty_spec : forall s, is_empty s = equal s empty;
      elements : set -> list elt;
      elements_empty : elements empty = nil;
      elements_spec1 : 
        forall s s', equal s s' = true -> 
                     comparelA (Oeset.compare Elt) (elements s) (elements s') = Eq;      
      mem_elements : forall e s, mem e s = Oeset.mem_bool Elt e (elements s);
      elements_spec3 : forall s, Sorted (fun x y => Oeset.compare Elt x y = Lt) (elements s);
      choose : set -> option elt;
      choose_spec1 : forall s e, choose s = Some e -> mem e s = true;
      choose_spec2 : forall s, choose s = None -> is_empty s = true;
      choose_spec3 : forall s1 s2, equal s1 s2 = true ->
                                   match choose s1 with
                                     | None => choose s2 = None
                                     | Some e1 => match choose s2 with
                                                    | None => False
                                                    | Some e2 => Oeset.compare Elt e1 e2 = Eq
                                                  end
                                   end;
      cardinal : set -> nat;
      filter : (elt -> bool) -> set -> set;
      filter_spec : 
        forall (s : set) (x : elt) (f : elt -> bool),
          (forall e e', mem e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          mem x (filter f s) = mem x s && f x;
      filter_spec_weak : 
        forall (s : set) (x : elt) (f : elt -> bool),
          mem x (filter f s) = true -> mem x s = true;
      partition : (elt -> bool) -> set -> (set * set);
      partition_spec1 : 
        forall (s : set) (f : elt -> bool),
          (forall e e', mem e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          forall (x : elt), mem x (fst (partition f s)) = mem x s && f x;
      partition_spec2 : 
        forall (s : set) (f : elt -> bool),
          (forall e e', mem e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
          forall (x : elt), mem x (snd (partition f s)) = mem x s && negb (f x);
      for_all : (elt -> bool) -> set -> bool;
      for_all_spec : forall (s : set) (f : elt -> bool), for_all f s = forallb f (elements s);
      exists_ : (elt -> bool) -> set -> bool;
      exists_spec : forall (s : set) (f : elt -> bool), exists_ f s = existsb f (elements s);
      fold : forall (A : Type), (elt -> A -> A) -> set -> A -> A;
      fold_spec : forall (s : set) (A : Type) a0 (f : elt -> A -> A),
          fold f s a0 = fold_left (fun (a : A) (e : elt) => f e a) (elements s) a0;
      compare : set -> set -> comparison;
      compare_spec : forall s1 s2, compare s1 s2 = Eq <-> equal s1 s2 = true;
      compare_eq_trans : 
        forall a1 a2 a3, compare a1 a2 = Eq -> compare a2 a3 = Eq -> compare a1 a3 = Eq;
      compare_eq_lt_trans : 
        forall a1 a2 a3, compare a1 a2 = Eq -> compare a2 a3 = Lt -> compare a1 a3 = Lt;
      compare_lt_eq_trans : 
        forall a1 a2 a3, compare a1 a2 = Lt -> compare a2 a3 = Eq -> compare a1 a3 = Lt;
      compare_lt_trans : 
        forall a1 a2 a3, compare a1 a2 = Lt -> compare a2 a3 = Lt -> compare a1 a3 = Lt;
      compare_lt_gt : forall a1 a2, compare a1 a2 = CompOpp (compare a2 a1);
      cardinal_spec : forall s, cardinal s = List.length (elements s)
    }.

Definition build elt (Elt : Oeset.Rcd elt) := 
  mk_R 
    Elt (set := FiniteSetImpl.set Elt) (@mem_ _ Elt) 
    (@add_ _ Elt) (@add_spec_ _ Elt)(* remove_ *) 
    (@singleton_ _ Elt) (@singleton_spec_ _ Elt)
    (@union_ _ Elt) (@union_spec_ _ Elt)
    (@inter_ _ Elt) (@inter_spec_ _ Elt)
    (@diff_ _ Elt) (@diff_spec_ _ Elt)
    (@equal_ _ Elt) (@equal_spec_ _ Elt)
    (@subset_ _ Elt) (@subset_spec_ _ Elt)
    (@empty_ _ Elt) (@empty_spec_ _ Elt)
    (@is_empty_ _ Elt) (@is_empty_spec_ _ Elt)
    (@elements_ _ Elt) (@elements_empty_ _ Elt) 
    (@elements_spec1_ _ Elt) (@elements_spec2_ _ Elt) (@elements_spec3_ _ Elt) 
    (@choose_ _ Elt) (@choose_spec1_ _ Elt) (@choose_spec2_ _ Elt) (@choose_spec3__ _ Elt) 
    (* fold_ *) (@cardinal_ _ _)
    (@filter_ _ Elt) (@filter_spec_ _ Elt) (@filter_spec_weak_ _ Elt)
    (@partition_ _ Elt) 
    (fun s f h x => @partition_spec1__ _ Elt s x f h)
    (fun s f h x => @partition_spec2__ _ Elt s x f h)
    (@for_all_ _ Elt) (@for_all_spec_ _ Elt)
    (@exists__ _ Elt) (@exists_spec_ _ Elt) (@fold_ _ Elt) (@fold_spec_ _ Elt)
    (@compare_ _ Elt) (@compare_spec_ _ Elt)
    (@compare_eq_trans_ _ Elt) (@compare_eq_lt_trans_ _ Elt) (@compare_lt_eq_trans_ _ Elt) 
    (@compare_lt_trans_ _ Elt) (@compare_lt_gt_ _ Elt) 
(* 
    eq_equiv_ *)  (* subset_spec_ *) (* elements_spec3_ *)
     (* remove_spec_  *)
     (* mem_diff_ fold_spec_*) 
     (@cardinal_spec_ _ _)
(* cardinal_subset_ filter_spec2_ filter_spec3_ filter_true_ filter_and_ filter_or_ filter_not_*).

Section Sec.

Hypothesis A : Type.
Hypothesis Elt : Oeset.Rcd A.
Hypothesis FA : Rcd Elt.

Lemma equal_refl : forall s, equal FA s s = true.
Proof.
intro s; rewrite equal_spec; intro e; apply refl_equal.
Qed.

Definition nb_occ e s := Oeset.nb_occ Elt e (elements FA s).

Lemma nb_occ_unfold : forall e s, nb_occ e s = Oeset.nb_occ Elt e (elements FA s).
Proof.
intros e s; apply refl_equal.
Qed.

Lemma nb_occ_alt : forall e s, nb_occ e s = if mem FA e s then 1%N else 0%N.
Proof.
intros e s; unfold nb_occ.
rewrite mem_elements.
assert (_H := elements_spec3 _ s).
set (l := elements FA s) in *; clearbody l; clear s.
assert (H : StronglySorted (fun x y : A => Oeset.compare Elt x y = Lt) l).
{
  apply Sorted_StronglySorted; [ | assumption].
  intros x1 x2 x3; apply Oeset.compare_lt_trans.
}
clear _H.
induction l as [ | a1 l]; [apply refl_equal | ].
inversion H; clear H; subst.
rewrite Oeset.mem_bool_unfold, Oeset.nb_occ_unfold.
case_eq (Oeset.compare Elt e a1); intro He; [ | apply IHl; assumption | apply IHl; assumption].
assert (H : Oeset.nb_occ Elt e l = 0%N).
{
  apply Oeset.not_mem_nb_occ.
  case_eq (Oeset.mem_bool Elt e l); [ | intros; trivial].
  intro H; apply False_rec.
  rewrite Oeset.mem_bool_true_iff in H; destruct H as [e' [Ke He']].
  rewrite Forall_forall in H3.
  generalize (H3 _ He').
  rewrite (Oeset.compare_eq_trans _ _ _ _ (Oeset.compare_eq_sym _ _ _ He) Ke).
  discriminate.
}
rewrite H, N.add_0_r.
apply refl_equal.
Qed.

Fixpoint mk_set (l : list A) :=
  match l with
    | nil => empty FA
    | a1 :: l => add _ a1 (mk_set l)
  end.

Lemma mk_set_unfold :
  forall l, mk_set l = match l with
                         | nil => empty _
                         | a1 :: l => add _ a1 (mk_set l)
                       end.
Proof.
intros l; case l; intros; apply refl_equal.
Qed.

Lemma mem_mk_set :
  forall a l, mem _ a (mk_set l) = Oeset.mem_bool Elt a l.
Proof.
intros a l; induction l as [ | a1 l].
- rewrite mk_set_unfold, empty_spec; apply refl_equal.
- rewrite mk_set_unfold, add_spec, IHl.
  apply refl_equal.
Qed.

Lemma mk_set_eq :
  forall l1 l2, (forall t, Oeset.mem_bool Elt t l1 = Oeset.mem_bool Elt t l2) ->
                equal _ (mk_set l1) (mk_set l2) = true.
Proof.
intros l1 l2 H; rewrite equal_spec; intro t.
rewrite 2 mem_mk_set; apply H.
Qed.

Lemma mk_set_eq_weak :
  forall l1 l2, (forall t, Oeset.nb_occ Elt t l1 = Oeset.nb_occ Elt t l2) ->
                equal _ (mk_set l1) (mk_set l2) = true.
Proof.
intros l1 l2 H; rewrite equal_spec; intro t.
rewrite 2 mem_mk_set, eq_bool_iff; split; intro Ht.
- apply Oeset.nb_occ_mem; rewrite <- H; apply Oeset.mem_nb_occ; assumption.
- apply Oeset.nb_occ_mem; rewrite H; apply Oeset.mem_nb_occ; assumption.
Qed.

Lemma elements_mk_set_elements :
  forall s, 
    comparelA (Oeset.compare Elt) (elements FA (mk_set (elements FA s))) (elements FA s) = Eq.
Proof.
intro s; apply elements_spec1; rewrite equal_spec.
intro x; rewrite mem_mk_set, <- mem_elements.
apply refl_equal.
Qed.

Fixpoint Union l : set FA :=
  match l with
    | nil => empty _
    | a :: l => union _ a (Union l)
  end.

Lemma Union_unfold :
  forall l, Union l = match l with
                        | nil => empty _
                        | a :: l => union _ a (Union l)
                      end.
Proof.
intros l; case l; intros; apply refl_equal.
Qed.

Lemma mem_Union :
  forall a l, mem FA a (Union l) = true <-> 
              (exists s, List.In s l /\  mem FA a s = true).
Proof.
intros a l; induction l as [ | s1 l].
- rewrite Union_unfold, empty_spec.
  split; intro H.
  + discriminate H.
  + destruct H as [s [H _]]; contradiction H.
- rewrite Union_unfold, mem_union, Bool.orb_true_iff, IHl.
  split; intro H.
  + destruct H as [H | [s [Hs H]]].
    * exists s1; split; [left | ]; trivial.
    * exists s; split; [right | ]; trivial.
  + destruct H as [s [Hs H]].
    simpl in Hs; destruct Hs as [Hs | Hs].
    * subst s; left; assumption.
    * right; exists s; split; assumption.
Qed.

Lemma singleton_eq :
  forall a1 a2, 
    Oeset.compare Elt a1 a2 = Eq -> equal FA (singleton FA a1) (singleton FA a2) = true.
Proof.
intros a1 a2 H; rewrite equal_spec; intro a.
rewrite 2 singleton_spec, eq_bool_iff; unfold Oeset.eq_bool; rewrite 2 compare_eq_true; 
split; intro K.
- apply (Oeset.compare_eq_trans _ _ _ _ K H).
- apply (Oeset.compare_eq_trans _ _ _ _ K (Oeset.compare_eq_sym _ _ _ H)).
Qed.

Lemma choose_singleton :
 forall a1, exists a2, 
   (choose FA (singleton FA a1) = Some a2 /\ Oeset.compare Elt a1 a2 = Eq).
Proof.
intro a1.
case_eq (choose FA (singleton FA a1)).
- intros a Ha; exists a; split; [apply refl_equal | ].
  assert (Ka := choose_spec1 _ _ Ha).
  rewrite singleton_spec in Ka.
  unfold Oeset.eq_bool in Ka; rewrite compare_eq_true in Ka.
  apply Oeset.compare_eq_sym; apply Ka.
- intro H; assert (K := choose_spec2 _ _ H).
  rewrite is_empty_spec, equal_spec in K.
  assert (Ka1 := K a1).
  rewrite singleton_spec, empty_spec in Ka1.
  unfold Oeset.eq_bool in Ka1; rewrite Oeset.compare_eq_refl in Ka1.
  discriminate Ka1.
Qed.

Lemma mem_eq_2 :
  forall s1 s2, equal FA s1 s2 = true -> forall x, mem FA x s1 = mem FA x s2.
Proof.
intros s1 s2 Hs x; rewrite equal_spec in Hs; apply Hs.
Qed.

Lemma in_elements_mem :
  forall a s, List.In a (elements FA s) -> mem _ a s = true.
Proof.
intros a s H.
rewrite mem_elements, Oeset.mem_bool_true_iff.
exists a; split; [ | assumption].
apply Oeset.compare_eq_refl.
Qed.

Lemma mem_eq_1 :
  forall a a' s, Oeset.compare Elt a a' = Eq -> mem FA a s = mem FA a' s.
Proof.
intros a a' s Ha.
rewrite 2 mem_elements, eq_bool_iff, 2 Oeset.mem_bool_true_iff; split.
- intros [a1 [Ha1 Ka1]].
  exists a1; split; [ | assumption].
  refine (Oeset.compare_eq_trans _ _ _ _ _ Ha1).
  rewrite Oeset.compare_lt_gt, Ha; apply refl_equal.
- intros [a1 [Ha1 Ka1]].
  exists a1; split; [ | assumption].
  refine (Oeset.compare_eq_trans _ _ _ _ Ha Ha1).
Qed.

Lemma mem_fold2 :
 forall (fb : A -> A -> bool) (ff : A -> A -> A) x s0 l0 s1 s2, 
   (forall x, mem FA x s0 = Oeset.mem_bool Elt x l0) ->
  mem FA x (fold FA
       (fun t1 acc =>
           fold FA
           (fun t2 acc => if fb t1 t2 then add _ (ff t1 t2) acc else acc)
         s2 acc)
     s1 s0) =
     Oeset.mem_bool Elt x (fold_left
       (fun acc t1 =>
           fold_left
           (fun acc t2 => if fb t1 t2 then (ff t1 t2 :: acc) else acc)
         (elements FA s2) acc)
     (elements FA s1) l0).
Proof.
intros fb ff x s0 l0 s1 s2.
rewrite mem_elements, fold_spec.
set (l1 := elements FA s1) in *; clearbody l1; clear s1.
revert s0 l0 s2; 
  induction l1 as [ | t1 l1]; 
  simpl; intros s0 l0 s2 H0;
  [rewrite <- mem_elements, H0; apply refl_equal | ].
set (s0' := fold 
              FA
              (fun (t2 : A) (acc : set FA) =>
                 if fb t1 t2 then add FA (ff t1 t2) acc else acc) s2 s0).
set (l0' := fold_left
              (fun (acc : list A) (t2 : A) =>
                 if fb t1 t2 then ff t1 t2 :: acc else acc) 
              (elements FA s2) l0).
assert (IH := IHl1 s0' l0' s2); simpl in IH; rewrite IH;
 [apply refl_equal | clear IH IHl1].
subst s0' l0'.
intros y; rewrite fold_spec.
set (l2 := elements FA s2); clearbody l2; clear s2.
revert s0 l0 H0; induction l2 as [ | t2 l2]; intros s0 l0 H0; simpl.
apply H0.
apply IHl2.
intros z; case (fb t1 t2); [ | apply H0].
rewrite add_spec; simpl; rewrite H0.
case (Oeset.compare Elt z (ff t1 t2)); apply refl_equal.
Qed.

Definition interp_set_op o :=
  fun (s1 s2 : set FA) => match o with
                            | Inter => inter _ s1 s2
                            | Diff => diff _ s1 s2
                            | _ => union _ s1 s2
                          end.

Lemma interp_set_op_eq :
  forall o (s1 s2 s1' s2' : set FA),
    equal _ s1 s1' = true -> equal _ s2 s2' = true -> 
    equal _ (interp_set_op o s1 s2) (interp_set_op o s1' s2') = true.
Proof.
intros o s1 s2 s1' s2' H H';
  rewrite equal_spec in H, H'; rewrite equal_spec.
intros a; destruct o; unfold interp_set_op.  
- rewrite 2 mem_union, H, H'; apply refl_equal.
- rewrite 2 mem_union, H, H'; apply refl_equal.
- rewrite 2 mem_inter, H, H'; apply refl_equal.
- rewrite 2 mem_diff, H, H'; apply refl_equal.
Qed.

Lemma fold_inter_is_inter_cardinal_ :
 forall s1 s2, cardinal FA (inter FA s1 s2) = 
               length (fold_inter_ Elt nil (elements FA s1) (elements FA s2)).
Proof.
intros s1 s2.
rewrite Feset.cardinal_spec.
apply comparelA_eq_length_eq with (Oeset.compare Elt).
apply comparelA_Eq.
- intro e; rewrite <- (fold_inter_is_inter_list Elt e (elements _ s1) (elements _ s2)).
  rewrite <- mem_elements, mem_inter, 2 mem_elements, Bool.orb_false_r.
  apply refl_equal.
- apply elements_spec3.
- apply fold_inter_is_sorted_; apply elements_spec3.
Qed.

Lemma fold_union_is_union_cardinal_ :
 forall s1 s2, cardinal FA (union FA s1 s2) = 
               length (fold_union_ Elt (elements FA s1) (elements FA s2)).
Proof.
intros s1 s2.
rewrite cardinal_spec.
apply comparelA_eq_length_eq with (Oeset.compare Elt).
apply comparelA_Eq.
- intro e; rewrite <- (fold_union_is_union_list Elt e (elements _ s1) (elements _ s2)).
  rewrite <- mem_elements, mem_union, 2 mem_elements.
  apply refl_equal.
- apply Feset.elements_spec3.
- apply fold_union_is_sorted_; apply Feset.elements_spec3.
Qed.

Lemma cardinal_union_ :
  forall s1 s2, 
    (cardinal FA (union FA s1 s2) + cardinal FA (inter FA s1 s2) = 
     cardinal FA s1 + cardinal FA s2)%nat.
Proof.
intros s1 s2.
rewrite fold_inter_is_inter_cardinal_, fold_union_is_union_cardinal_, 2 (cardinal_spec FA).
generalize (elements_spec3 FA s2).
set  (l1 := elements FA s1); clearbody l1; clear s1.
set  (l2 := elements FA s2); clearbody l2; clear s2.
revert l1; induction l2 as [ | a2 l2]; intros l1 Sl2; simpl.
- (* 1/2 *)
  apply refl_equal.
- (* 1/1 *)
  inversion Sl2; subst.
  case_eq (Oeset.mem_bool Elt a2 l1); intro Ha2.
  + (* 1/2 *)
    rewrite length_fold_inter_; simpl.
    assert (IH := IHl2 l1 H1).
    rewrite 2 (plus_comm _ (S _)); simpl; rewrite plus_comm, IH, plus_comm; apply refl_equal.
  + (* 1/1 *)
    apply sym_eq.
    generalize (sym_eq (IHl2 (insert_ Elt a2 l1) H1)).
    rewrite length_insert_.
    simpl; rewrite (plus_comm _ (S _)); simpl; rewrite plus_comm.
    intro IH; rewrite IH; apply f_equal.
    clear IHl2 Sl2 IH.
    revert a2 l1 H1 H2 Ha2; induction l2 as [ | a2 l2]; intros a l1 H1 H2 Ha; simpl.
    * apply refl_equal.
    * rewrite mem_insert_.
      inversion H2; subst.
      rewrite Oeset.compare_lt_gt, H0; simpl.
      {
        case (Oeset.mem_bool Elt a2 l1).
        - rewrite 2 (length_fold_inter_ Elt (a2 :: nil)), IHl2.
          + apply refl_equal.
          + inversion H1; assumption.
          + destruct l2 as [ | x l2].
            * constructor 1.
            * constructor 2.
              {
                apply Oeset.compare_lt_trans with a2.
                - inversion H2; assumption.
                - inversion H1; subst.
                  inversion H5; assumption.
              }
          + assumption.
        - apply IHl2.
          + inversion H1; assumption.
          + destruct l2 as [ | x l2].
            * constructor 1.
            * {
                constructor 2.
                apply Oeset.compare_lt_trans with a2.
                - inversion H2; assumption.
                - inversion H1; subst.
                  + inversion H5; assumption.
              }
          + assumption.
      }
Qed.

Lemma cardinal_singleton :
  forall e, cardinal FA (singleton FA e) = 1.
Proof.
intro e; rewrite cardinal_spec.
case_eq (elements FA (singleton FA e)).
- intro H.
  assert (Aux := singleton_spec FA e e).
  unfold Oeset.eq_bool in Aux; rewrite Oeset.compare_eq_refl, Feset.mem_elements, H in Aux.
  discriminate Aux.
- intros a1 [ | a2 l] H; [apply refl_equal | ].
  assert (Ha1 : mem FA a1 (singleton FA e) = true).
  {
    rewrite mem_elements, H; simpl; unfold Oeset.eq_bool;
    rewrite Oeset.compare_eq_refl; apply refl_equal.
  } 
  assert (Ha2 : mem FA a2 (singleton FA e) = true).
  {
    rewrite mem_elements, H; simpl; unfold Oeset.eq_bool;
    rewrite Oeset.compare_eq_refl, Bool.orb_true_r; apply refl_equal.
  }
  rewrite singleton_spec in Ha1, Ha2.
  assert (Aux := elements_spec3 FA (singleton FA e)).
  rewrite H in Aux.
  inversion Aux; clear Aux.
  inversion H3; clear H3; subst.
  unfold Oeset.eq_bool in Ha1, Ha2.
  case_eq (Oeset.compare Elt a1 e); intro Ka1; rewrite Ka1 in Ha1; try discriminate Ha1.
  case_eq (Oeset.compare Elt a2 e); intro Ka2; rewrite Ka2 in Ha2; try discriminate Ha2.
  rewrite (Oeset.compare_eq_1 _ _ _ _ Ka1), (Oeset.compare_eq_2 _ _ _ _ Ka2) in H5.
  rewrite Oeset.compare_eq_refl in H5; discriminate H5.
Qed.

Lemma cardinal_subset : 
  forall s1 s2, subset FA s1 s2 = true -> (cardinal _ s1 <= cardinal _ s2)%nat.
Proof.
intros s1 s2 Hs.
rewrite 2 cardinal_spec.
apply (cardinal_subset_list Elt).
- apply (elements_spec3 FA).
- apply (elements_spec3 FA).
- intros x Hx; rewrite subset_spec in Hs.
  unfold Oeset.mem_bool, Oeset.eq_bool in *; simpl in Hx; simpl.
  assert (Kx := Hs x).
  rewrite 2 (mem_elements FA) in Kx.
  unfold Oset.mem_bool, Oset.eq_bool in Kx; apply Kx; assumption.
Qed.

Lemma cardinal_strict_subset :
 forall s1 s2 e, 
   subset FA s1 s2 = true -> mem FA e s1 = false -> mem FA e s2 = true -> 
   cardinal FA s1 < cardinal FA s2.
Proof.
intros s1 s2 e H H1 H2.
apply lt_le_trans with (cardinal FA (union _ (singleton FA e) s1)).
- assert (K := cardinal_union_ (singleton FA e) s1).
  assert (J : cardinal FA (inter FA (singleton FA e) s1) = 0).
  {
    assert (J : equal FA (inter FA (singleton FA e) s1) (empty FA) = true).
    {
      rewrite equal_spec; intro x.
      rewrite mem_inter, singleton_spec, 2 mem_elements, elements_empty.
      rewrite Bool.andb_false_iff.
      case_eq (Oeset.eq_bool Elt x e); intro Hx.
      - right; rewrite Oeset.eq_bool_true_compare_eq in Hx.
        rewrite (Oeset.mem_bool_eq_1 Elt x e _ Hx), <- mem_elements; assumption.
      - left; apply refl_equal.
    } 
    rewrite cardinal_spec, (comparelA_eq_length_eq _ _ _ (elements_spec1 _ _ _ J)), elements_empty.
    apply refl_equal.
  }
  rewrite J, <- plus_n_O in K.
  rewrite K.
  rewrite cardinal_singleton; apply le_n.
- apply cardinal_subset.
  rewrite subset_spec; intros x Hx; rewrite subset_spec in H.
  rewrite mem_union, Bool.orb_true_iff, singleton_spec in Hx.
  destruct Hx as [Hx | Hx].
  + rewrite Oeset.eq_bool_true_compare_eq in Hx.
    rewrite mem_elements, (Oeset.mem_bool_eq_1 _ _ _ _ Hx), <- mem_elements; assumption.
  + apply H; assumption.
Qed.

End Sec.

Section Sec2.

Hypotheses A B : Type.
Hypotheses EltA : Oeset.Rcd A.
Hypotheses EltB : Oeset.Rcd B.
Hypothesis FA : Rcd EltA.
Hypothesis FB : Rcd EltB.

Definition map (f : A -> B) s := mk_set FB (List.map f (elements FA s)).

Lemma map_unfold : forall f s, map f s = mk_set FB (List.map f (elements FA s)).
Proof.
intros f s; apply refl_equal.
Qed.

Lemma mem_map :
  forall f s b, mem _ b (map f s) = true <-> 
                (exists a, Oeset.compare EltB b (f a) = Eq /\ List.In a (elements _ s)).
Proof.
intros f s b; rewrite map_unfold, mem_mk_set; split.
- rewrite Oeset.mem_bool_true_iff; intros [b' [Hb' H]].
  rewrite in_map_iff in H.
  destruct H as [a [H Ha]]; subst b'.
  exists a; split; trivial.
- intros [a [H Ha]].
  rewrite Oeset.mem_bool_true_iff; exists (f a); split; [assumption | ].
  rewrite in_map_iff; exists a; split; trivial.
Qed.

Lemma map_eq_s :
  forall f s1 s2, 
    (forall x1 x2, mem _ x1 s1 = true -> Oeset.compare EltA x1 x2 = Eq -> 
                   Oeset.compare EltB (f x1) (f x2) = Eq) ->
    equal _ s1 s2 = true -> equal _ (map f s1) (map f s2) = true.
Proof.
intros f s1 s2 Hf Hs.
rewrite equal_spec in Hs.
rewrite equal_spec; intro b.
rewrite eq_bool_iff, 2 mem_map; split.
- intros [a [Hb Ha]].
  assert (Ka := in_elements_mem _ _ _ Ha).
  rewrite Hs, mem_elements, Oeset.mem_bool_true_iff in Ka.
  destruct Ka as [a' [Ka Ha']].
  exists a'; split; [ | assumption].
  refine (Oeset.compare_eq_trans _ _ _ _ Hb _).
  apply Hf.
  + apply (in_elements_mem _ _ _ Ha).
  + assumption.
- intros [a [Hb Ha]].
  assert (Ka := in_elements_mem _ _ _ Ha).
  rewrite <- Hs, mem_elements, Oeset.mem_bool_true_iff in Ka.
  destruct Ka as [a' [Ka Ha']].
  exists a'; split; [ | assumption].
  refine (Oeset.compare_eq_trans _ _ _ _ Hb _).
  apply Hf.
  + rewrite (mem_eq_1 _ _ _ _ Ka).
    apply (in_elements_mem _ _ _ Ha').
  + assumption.
Qed.

End Sec2.

Lemma map_id :
  forall (A : Type) (EltA : Oeset.Rcd A) (FA : Rcd EltA) (f : A -> A) fa,
    (forall a, mem FA a fa = true -> Oeset.compare EltA (f a) a = Eq) ->
    equal _ (map FA FA f fa) fa = true.
Proof.
intros A EltA FA f fa H.
rewrite Feset.equal_spec; intro a.
unfold map.
rewrite eq_bool_iff, mem_mk_set, Oeset.mem_bool_true_iff.
rewrite mem_elements, Oeset.mem_bool_true_iff.
split; intros [a1 [Ha Ha1]].
- rewrite in_map_iff in Ha1.
  destruct Ha1 as [a2 [Ha1 Ha2]].
  exists a2; split; [ | assumption].
  refine (Oeset.compare_eq_trans _ _ _ _ Ha _).
  rewrite <- Ha1.
  apply H.
  apply (in_elements_mem _ _ _ Ha2).
- exists (f a1); split; [ | rewrite in_map_iff; exists a1; split; trivial].
  refine (Oeset.compare_eq_trans _ _ _ _ Ha _).
  rewrite Oeset.compare_lt_gt, H; [apply refl_equal | ].
  apply (in_elements_mem _ _ _ Ha1).
Qed.

End Feset.

Module Fset.

Record Rcd (elt : Type) (Elt : Oset.Rcd elt) : Type :=
  mk_R
    {
      set : Type;
      mem : elt -> set -> bool;
      add : elt -> set -> set;
      add_spec : forall s a e, mem e (add a s) = Oset.eq_bool Elt e a || mem e s;
      singleton : elt -> set;
      singleton_spec : 
        forall x y : elt, mem y (singleton x) = Oset.eq_bool Elt y x;
      union : set -> set -> set;
      mem_union : forall (s s' : set) (x : elt), mem x (union s s') = mem x s || mem x s';
      inter : set -> set -> set;
      mem_inter : forall (s s' : set) (x : elt), mem x (inter s s') = mem x s && mem x s';
      diff : set -> set -> set;
      mem_diff : forall (s s' : set) (x : elt), mem x (diff s s') = mem x s && negb (mem x s');
      equal : set -> set -> bool;
      equal_spec : forall s1 s2, equal s1 s2 = true <-> (forall e, mem e s1 = mem e s2);
      subset : set -> set -> bool;
      subset_spec : 
        forall s1 s2, subset s1 s2 = true <-> (forall e, mem e s1 = true -> mem e s2 = true);
      empty : set;
      empty_spec : forall e, mem e empty = false;
      is_empty : set -> bool;
      is_empty_spec : forall s, is_empty s = equal s empty;
      elements : set -> list elt;
      elements_empty : elements empty = nil;
      elements_spec1 : 
        forall s s', equal s s' = true -> elements s = elements s';
      mem_elements : forall e s, mem e s = Oset.mem_bool Elt e (elements s);
      elements_spec3 : forall s, Sorted (fun x y => Oset.compare Elt x y = Lt) (elements s);
      cardinal : set -> nat;
      cardinal_spec : forall s, cardinal s = List.length (elements s);
      choose : set -> option elt;
      choose_spec1 : forall s e, choose s = Some e -> mem e s = true;
      choose_spec2 : forall s, choose s = None -> is_empty s = true;
      choose_spec3 : forall s1 s2, equal s1 s2 = true -> choose s1 = choose s2;
      filter : (elt -> bool) -> set -> set;
      mem_filter : 
        forall (s : set) (x : elt) (f : elt -> bool),
          mem x (filter f s) = mem x s && f x;
      partition : (elt -> bool) -> set -> (set * set);
      partition_spec1 : 
        forall (s : set) (f : elt -> bool) (x : elt),
          mem x (fst (partition f s)) = mem x s && f x;
      partition_spec2 : 
        forall (s : set) (f : elt -> bool) (x : elt),
          mem x (snd (partition f s)) = mem x s && negb (f x);
      for_all : (elt -> bool) -> set -> bool;
      for_all_spec : forall f s, for_all f s = forallb f (elements s);
      exists_ : (elt -> bool) -> set -> bool;
      exists_spec : forall f s, exists_ f s = true <-> (exists e, mem e s = true /\ f e = true);
      fold : forall (A : Type), (elt -> A -> A) -> set -> A -> A;
      fold_spec : forall (s : set) (A : Type) a0 (f : elt -> A -> A),
          fold f s a0 = fold_left (fun (a : A) (e : elt) => f e a) (elements s) a0;
      compare : set -> set -> comparison;
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

Definition build elt (Elt : Oset.Rcd elt) :=
  mk_R Elt
    (set := FiniteSetImpl.set (Elt_ Elt)) 
    (@mem_ _ _) 
    (@add_ _ _) (@add_spec_ _ _)
    (@singleton_ _ _) (@singleton_spec_ _ _)
    (@union_ _ _) (@union_spec_ _ _) 
    (@inter_ _ _) (@inter_spec_ _ _) 
    (@diff_ _ _) (@diff_spec_ _ _) 
    (@equal_ _ _) (@equal_spec_ _ _)
    (@subset_ _ _) (@subset_spec_ _ _)
    (@empty_ _ _) (@empty_spec_ _ _) 
    (@is_empty_ _ _) (@is_empty_spec_ _ _)
    (@elements_ _ _) (@elements_empty_ _ _)
    (@elements_spec1__ _ _) (@elements_spec2_ _ _) (@elements_spec3_ _ _)
    (@cardinal_ _ _) (@cardinal_spec_ _ _)
    (@choose_ _ _) (@choose_spec1_ _ _) (@choose_spec2_ _ _) (@choose_spec3___ _ _)
    (@filter_ _ _) (@filter_spec__ _ _)
    (@partition_ _ _) 
    (fun s f x => @partition_spec1___ _ _ s x f) 
    (fun s f x => @partition_spec2___ _ _ s x f) 
    (@for_all_ _ _) (fun f s => @for_all_spec_ _ _ s f) 
    (@exists__ _ _) (@exists_spec__ _ _)
    (@fold_ _ _) (@fold_spec_ _ _)
    (@compare_ _ _) (@compare_spec_ _ _) 
    (@compare_eq_trans_ _ _) (@compare_eq_lt_trans_ _ _) (@compare_lt_eq_trans_ _ _) 
    (@compare_lt_trans_ _ _) (@compare_lt_gt_ _ _).

Section Sec.

Hypothesis A : Type.
Hypothesis Elt : Oset.Rcd A.
Hypothesis FA : Rcd Elt.

Fixpoint mk_set (l : list A) :=
  match l with
    | nil => empty FA
    | a1 :: l => add _ a1 (mk_set l)
  end.

Lemma mk_set_unfold :
  forall l, mk_set l = match l with
                         | nil => empty _
                         | a1 :: l => add _ a1 (mk_set l)
                       end.
Proof.
intros l; case l; intros; apply refl_equal.
Qed.

Lemma mem_mk_set :
  forall l a, mem _ a (mk_set l) = Oset.mem_bool Elt a l.
Proof.
intros l a.
induction l as [ | a1 l]; rewrite mk_set_unfold.
- rewrite empty_spec; apply refl_equal.
- rewrite add_spec, IHl; apply refl_equal.
Qed.

Lemma mem_mk_set_app :
  forall l1 l2 a, mem _ a (mk_set (l1 ++ l2)) = mem _ a (mk_set l1) || mem _ a (mk_set l2).
Proof.
intros l1 l2 a; rewrite 3 mem_mk_set, Oset.mem_bool_app.
apply refl_equal.
Qed.

Lemma mk_set_idem :
  forall s, equal _ (mk_set (elements FA s)) s = true.
Proof.
intros s.
rewrite equal_spec; intro a.
rewrite (mem_mk_set (elements _ _)).
rewrite <- mem_elements.
apply refl_equal.
Qed.

Fixpoint Union l : set FA :=
  match l with
    | nil => empty _
    | a :: l => union _ a (Union l)
  end.

Lemma Union_unfold :
  forall l, Union l = match l with
                        | nil => empty _
                        | a :: l => union _ a (Union l)
                      end.
Proof.
intros l; case l; intros; apply refl_equal.
Qed.

Lemma Union_map_eq :
  forall (B : Type) (f1 f2 : B -> set FA) (l : list B),
    (forall x, List.In x l -> equal FA (f1 x) (f2 x) = true) ->
    equal _ (Union (map f1 l)) (Union (map f2 l)) = true.
Proof.
intros B f1 f2 l; induction l as [ | b1 l]; intros Hl; rewrite equal_spec; intro b.
- apply refl_equal.
- simpl; rewrite 2 mem_union; apply f_equal2.
  + revert b; rewrite <- equal_spec; apply Hl; left; apply refl_equal.
  + revert b; rewrite <- equal_spec; apply IHl; intros; apply Hl; right; assumption.
Qed.

Lemma mem_Union :
  forall a l, mem FA a (Union l) = true <-> (exists s, List.In s l /\  mem FA a s = true).
Proof.
intros a l; induction l as [ | s1 l].
- rewrite Union_unfold, empty_spec.
  split; intro H.
  + discriminate H.
  + destruct H as [s [H _]]; contradiction H.
- rewrite Union_unfold, mem_union, Bool.orb_true_iff, IHl.
  split; intro H.
  + destruct H as [H | [s [Hs H]]].
    * exists s1; split; [left | ]; trivial.
    * exists s; split; [right | ]; trivial.
  + destruct H as [s [Hs H]].
    simpl in Hs; destruct Hs as [Hs | Hs].
    * subst s; left; assumption.
    * right; exists s; split; assumption.
Qed.

Lemma mem_Union_app :
  forall a l1 l2, mem FA a (Union (l1 ++ l2)) = orb (mem FA a (Union l1)) (mem FA a (Union l2)).
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros l2; simpl.
- rewrite empty_spec; apply refl_equal.
- rewrite 2 mem_union, IHl1.
  apply orb_assoc.
Qed.

Lemma for_all_spec_alt : 
        forall f s, for_all FA f s = true <-> (forall e, mem FA e s = true -> f e = true).
Proof.
intros f s; rewrite for_all_spec, forallb_forall; split; intro H.
- intros e He; apply (H e).
  rewrite mem_elements, Oset.mem_bool_true_iff in He; apply He.
- intros e He; apply (H e).
  rewrite mem_elements, Oset.mem_bool_true_iff; apply He.
Qed.

Lemma equal_refl :
 forall s, equal FA s s = true.
Proof.
intros s.
rewrite equal_spec; intro; apply refl_equal.
Qed.

Lemma equal_refl_alt :
  forall s1 s2, s1 = s2 -> equal FA s1 s2 = true.
Proof.
intros s1 s2 Hs; subst s2; apply equal_refl.
Qed.

Lemma subset_refl :
  forall s, subset FA s s = true.
Proof.
intros s; rewrite subset_spec; exact (fun _ h => h).
Qed.

Lemma subset_trans :
  forall s1 s2 s3, subset FA s1 s2 = true -> subset FA s2 s3 = true -> subset FA s1 s3 = true.
Proof.
intros s1 s2 s3; rewrite 3 subset_spec; intros H1 H2 x Hx.
apply H2; apply H1; apply Hx.
Qed.

Lemma in_elements_mem :
  forall a s, List.In a (elements FA s) -> mem FA a s = true.
Proof.
intros a s H.
rewrite mem_elements, Oset.mem_bool_true_iff.
assumption.
Qed.

Lemma mem_in_elements :
  forall a s, mem FA a s = true -> List.In a (elements FA s).
Proof.
intros a s Ha.
rewrite mem_elements, Oset.mem_bool_true_iff in Ha; apply Ha.
Qed.

Lemma mem_eq_1 :
  forall a a' s,
    Oset.eq_bool Elt a a' = true -> mem FA a s = mem FA a' s.
Proof.
intros a a' s Ha.
rewrite Oset.eq_bool_true_iff in Ha; subst a'; apply refl_equal.
Qed.

Lemma mem_eq_2 :
  forall s1 s2, equal FA s1 s2 = true -> forall x, mem FA x s1 = mem FA x s2.
Proof.
intros s1 s2 H x; rewrite equal_spec in H; apply H.
Qed.

Lemma Union_map_singleton_equal :
  forall s, equal FA (Union (map (fun x => singleton FA x) (elements FA s))) s = true.
Proof.
intro s; rewrite equal_spec; intro x.
rewrite eq_bool_iff, mem_Union; split.
- intros [sx [Hsx Hx]].
  rewrite in_map_iff in Hsx.
  destruct Hsx as [_x [Hsx _Hx]]; subst sx.
  rewrite singleton_spec, Oset.eq_bool_true_iff in Hx; subst _x.
  apply in_elements_mem; assumption.
- intro Hx.
  exists (singleton _ x); split.
  + rewrite in_map_iff; exists x; split; [trivial | ].
    rewrite mem_elements, Oset.mem_bool_true_iff in Hx.
    assumption.
  + rewrite singleton_spec, Oset.eq_bool_true_iff; apply refl_equal.
Qed.

Lemma inter_idem :
  forall s, equal FA (inter _ s s) s = true.
Proof.
intro s; rewrite Fset.equal_spec; intro a.
rewrite Fset.mem_inter, Bool.andb_diag.
apply refl_equal.
Qed.

Lemma inter_comm :
  forall s1 s2, equal FA (inter _ s1 s2) (inter _ s2 s1) = true.
Proof.
intros s1 s2; rewrite equal_spec; intro a.
rewrite 2 mem_inter; apply Bool.andb_comm.
Qed.

Lemma inter_assoc :
  forall s1 s2 s3, equal FA (inter _ s1 (inter _ s2 s3)) (inter _ (inter _ s1 s2) s3) = true.
Proof.
intros s1 s2 s3; rewrite equal_spec; intro x.
rewrite 4 mem_inter, Bool.andb_assoc; apply refl_equal.
Qed.

Lemma union_idem :
  forall s, equal FA (union _ s s) s = true.
Proof.
intro s; rewrite Fset.equal_spec; intro a.
rewrite Fset.mem_union, Bool.orb_diag.
apply refl_equal.
Qed.

Lemma union_comm :
  forall s1 s2, equal FA (union _ s1 s2) (union _ s2 s1) = true.
Proof.
intros s1 s2; rewrite equal_spec; intro a.
rewrite 2 mem_union; apply Bool.orb_comm.
Qed.

Lemma union_assoc :
  forall s1 s2 s3, equal FA (union _ s1 (union _ s2 s3)) (union _ (union _ s1 s2) s3) = true.
Proof.
intros s1 s2 s3; rewrite equal_spec; intro x.
rewrite 4 mem_union, Bool.orb_assoc; apply refl_equal.
Qed.

Lemma union_empty_r :
  forall s, equal FA (union _ s (empty _)) s = true.
Proof.
intro s; rewrite equal_spec; intro a.
rewrite mem_union, empty_spec, Bool.orb_false_r.
apply refl_equal.
Qed.

Lemma inter_empty :
  forall s1 s2, equal FA (inter _ s1 s2) (empty _) = true -> 
                  forall x , mem _ x s1 = true -> mem _ x s2 = true -> False.
Proof.
intros s1 s2 Hs x H1 H2.
rewrite equal_spec in Hs.
generalize (Hs x); rewrite mem_inter, empty_spec, H1, H2.
discriminate.
Qed.

Lemma subset_eq_1 :
  forall s1 s2 s, equal FA s1 s2 = true -> subset FA s1 s = subset FA s2 s.
Proof.
intros s1 s2 s H.
rewrite equal_spec in H.
rewrite eq_bool_iff, 2 subset_spec; split; intros K x Hx; apply K.
- rewrite H; assumption.
- rewrite <- H; assumption.
Qed.

Lemma subset_eq_2 :
  forall s1 s2 s, equal FA s1 s2 = true -> subset FA s s1 = subset FA s s2.
Proof.
intros s1 s2 s H.
rewrite equal_spec in H.
rewrite eq_bool_iff, 2 subset_spec; split; intros K x Hx.
- rewrite <- H; apply K; assumption.
- rewrite H; apply K; assumption.
Qed.

Lemma compare_eq_refl :
  forall s, compare FA s s = Eq.
Proof.
intro s; rewrite compare_spec; apply equal_refl.
Qed.

Lemma equal_eq_1 :
  forall s1 s2 s1', 
    equal FA s1 s1' = true -> equal FA s1 s2 = equal FA s1' s2.
Proof.
intros s1 s2 s1' H1.
rewrite equal_spec in H1.
rewrite eq_bool_iff; split; 
intro H; rewrite equal_spec in H; rewrite equal_spec; intro x.
- rewrite <- H1; apply H.
- rewrite H1; apply H.
Qed.

Lemma equal_eq_2 :
  forall s1 s2 s2', 
    equal FA s2 s2' = true -> equal FA s1 s2 = equal FA s1 s2'.
Proof.
intros s1 s2 s2' H2.
rewrite equal_spec in H2.
rewrite eq_bool_iff; split; 
intro H; rewrite equal_spec in H; rewrite equal_spec; intro x.
- rewrite <- H2; apply H.
- rewrite H2; apply H.
Qed.

Lemma union_eq_1 :
  forall s1 s1' s2, equal FA s1 s1' = true -> equal FA (union FA s1 s2) (union FA s1' s2) = true.
Proof.
intros s1 s1' s2 H1; rewrite equal_spec in H1; rewrite equal_spec; intro x.
rewrite 2 mem_union, H1; apply refl_equal.
Qed.

Lemma union_eq_2 :
  forall s1 s2 s2', equal FA s2 s2' = true -> equal FA (union FA s1 s2) (union FA s1 s2') = true.
Proof.
intros s1 s2 s2' H2; rewrite equal_spec in H2; rewrite equal_spec; intro x.
rewrite 2 mem_union, H2; apply refl_equal.
Qed.

Lemma union_eq :
  forall s1 s1' s2 s2', equal FA s1 s1' = true -> equal FA s2 s2' = true -> 
                        equal FA (union FA s1 s2) (union FA s1' s2') = true.
Proof.
intros s1 s1' s2 s2' H1 H2; rewrite equal_spec in H1, H2; rewrite equal_spec; intro x.
rewrite 2 mem_union, H1, H2; apply refl_equal.
Qed.

Lemma inter_eq_1 :
  forall s1 s1' s2, equal FA s1 s1' = true -> equal FA (inter FA s1 s2) (inter FA s1' s2) = true.
Proof.
intros s1 s1' s2 H1; rewrite equal_spec in H1; rewrite equal_spec; intro x.
rewrite 2 mem_inter, H1; apply refl_equal.
Qed.

Lemma inter_eq_2 :
  forall s1 s2 s2', equal FA s2 s2' = true -> equal FA (inter FA s1 s2) (inter FA s1 s2') = true.
Proof.
intros s1 s2 s2' H2; rewrite equal_spec in H2; rewrite equal_spec; intro x.
rewrite 2 mem_inter, H2; apply refl_equal.
Qed.

Lemma inter_eq :
  forall s1 s1' s2 s2', equal FA s1 s1' = true -> equal FA s2 s2' = true -> 
                        equal FA (inter FA s1 s2) (inter FA s1' s2') = true.
Proof.
intros s1 s1' s2 s2' H1 H2; rewrite equal_spec in H1, H2; rewrite equal_spec; intro x.
rewrite 2 mem_inter, H1, H2; apply refl_equal.
Qed.

Lemma filter_union :
  forall f s1 s2,
    equal FA (filter _ f (union _ s1 s2)) (union FA (filter _ f s1) (filter _ f s2)) = true.
Proof.
intros f s1 s2.
rewrite equal_spec; intro a.
rewrite mem_union, 3 mem_filter, mem_union.
case (f a); [ | rewrite 3 Bool.andb_false_r; apply refl_equal].
rewrite 3 Bool.andb_true_r; apply refl_equal.
Qed.

Lemma elements_empty_strong :
  forall s, elements FA s = nil <-> equal _ s (empty _) = true.
Proof.
intro s; split; intro H.
- rewrite equal_spec.
  intros a; rewrite mem_elements, H, empty_spec.
  apply refl_equal.
- case_eq (elements FA s); [intros; apply refl_equal | ].
  intros a1 l Hs.
  assert (Aux := mem_elements FA a1 s).
  rewrite Hs, Oset.mem_bool_unfold, Oset.compare_eq_refl in Aux.
  rewrite equal_spec in H.
  rewrite H, empty_spec in Aux.
  discriminate Aux.
Qed.

Lemma elements_add_1 :
  forall s a, mem FA a s = true -> elements FA (add FA a s) = elements FA s.
Proof.
intros s a Ha.
apply elements_spec1.
rewrite equal_spec; intro x.
rewrite add_spec.
case_eq (Oset.eq_bool Elt x a); intro Hx.
- rewrite Oset.eq_bool_true_iff in Hx.
  rewrite Hx, Ha.
  apply refl_equal.
- apply refl_equal.
Qed.

Lemma elements_add_2 :
  forall s a, mem FA a s = false ->
    exists l1, 
      exists l2, elements FA s = (l1 ++ l2) /\
                 elements FA (add FA a s) = l1 ++ a :: l2.
Proof.
intros s a Ha.
rewrite mem_elements, <- Bool.not_true_iff_false, Oset.mem_bool_true_iff in Ha.
assert (Aux : equal _ (add _ a s) (mk_set (a :: elements FA s)) = true).
{
  rewrite equal_spec; intro x.
  rewrite add_spec, mem_mk_set, Oset.mem_bool_unfold.
  apply f_equal.  
  rewrite <- mem_elements.
  apply refl_equal.
} 
rewrite (elements_spec1 _ _ _ Aux).
clear Aux.
exists (List.filter (fun x => match Oset.compare Elt x a with Lt => true | _ => false end) (elements FA s)).
exists (List.filter (fun x => match Oset.compare Elt a x with Lt => true | _ => false end) (elements FA s)).
split.
- apply (sorted_list_eq Elt).
  + intros e; rewrite eq_bool_iff, Oset.mem_bool_app, Bool.orb_true_iff, 3 Oset.mem_bool_true_iff.
    rewrite 2 filter_In; split.
    * intro He.
      {
        case_eq (Oset.compare Elt e a); intro H.
        - apply False_rec; apply Ha.
          generalize (Oset.eq_bool_ok Elt e a); rewrite H.
          intro; subst; apply He.
        - left; split; trivial.
        - right.
          rewrite Oset.compare_lt_gt, H; split; trivial.
      }
    * intros [[He _] | [He _]]; exact He.
  + apply elements_spec3.
  + apply SortA_app with (fun x y => Oset.eq_bool Elt x y = true); try apply Oset.StrictOrder.
    * apply Oset.Equivalence.
    (* * apply Oset.StrictOrder. *)
    * {
        apply (filter_sort (Oset.Equivalence Elt)).
        - apply Oset.StrictOrder.
        - intros a1 a2 Ka b1 b2 Kb.
          rewrite Oset.eq_bool_true_iff in Ka, Kb; subst a2 b2.
          split; exact (fun h => h).
        - apply elements_spec3.
      }
    * {
        apply (filter_sort (Oset.Equivalence Elt)).
        - apply Oset.StrictOrder.
        - intros a1 a2 Ka b1 b2 Kb.
          rewrite Oset.eq_bool_true_iff in Ka, Kb; subst a2 b2.
          split; exact (fun h => h).
        - apply elements_spec3.
      }
    * intros x y Hx Hy.
      rewrite InA_alt in Hx; destruct Hx as [x' [H Hx]].
      rewrite Oset.eq_bool_true_iff in H; subst x'.
      rewrite InA_alt in Hy.
      destruct Hy as [y' [H Hy]].
      rewrite Oset.eq_bool_true_iff in H; subst y'.
      rewrite filter_In in Hx, Hy.
      destruct Hx as [_ Hx]; destruct Hy as [_ Hy].
      {
        apply Oset.compare_lt_trans with a.
        - destruct (Oset.compare Elt x a); trivial; discriminate Hx.
        - destruct (Oset.compare Elt a y); trivial; discriminate Hy.
      } 
- apply (sorted_list_eq Elt).
  + intros e; rewrite eq_bool_iff, Oset.mem_bool_app, Bool.orb_true_iff, 3 Oset.mem_bool_true_iff.
    simpl List.In; rewrite 2 filter_In; split.
    * intro He.
      {
        rewrite <- (Oset.mem_bool_true_iff Elt), <- mem_elements in He.
        rewrite add_spec, Bool.orb_true_iff in He.
        destruct He as [He | He].
        + rewrite Oset.eq_bool_true_iff in He.
          right; left; apply sym_eq; assumption.
        + rewrite mem_mk_set, (Oset.mem_bool_true_iff Elt) in He.
          case_eq (Oset.compare Elt e a); intro H.
        - apply False_rec; apply Ha.
          generalize (Oset.eq_bool_ok Elt e a); rewrite H.
          intro; subst; apply He.
        - left; split; trivial.
        - do 2 right.
          rewrite Oset.compare_lt_gt, H; split; trivial.
      }
    * intro He; rewrite <- (Oset.mem_bool_true_iff Elt), <- mem_elements.
      rewrite add_spec, Bool.orb_true_iff, Oset.eq_bool_true_iff.
      rewrite mem_mk_set, Oset.mem_bool_true_iff.
      destruct He as [[He _] | [He | [He _]]]; [right | left; subst | right]; trivial.
  + apply elements_spec3.
  + apply SortA_app with (fun x y => Oset.eq_bool Elt x y = true); try apply Oset.StrictOrder.
    * apply Oset.Equivalence.
    (* * apply Oset.StrictOrder. *)
    * {
        apply (filter_sort (Oset.Equivalence Elt)).
        - apply Oset.StrictOrder.
        - intros a1 a2 Ka b1 b2 Kb.
          rewrite Oset.eq_bool_true_iff in Ka, Kb; subst a2 b2.
          split; exact (fun h => h).
        - apply elements_spec3.
      }
    * {
        constructor 2.
        - apply (filter_sort (Oset.Equivalence Elt)).
          + apply Oset.StrictOrder.
          + intros a1 a2 Ka b1 b2 Kb.
            rewrite Oset.eq_bool_true_iff in Ka, Kb; subst a2 b2.
            split; exact (fun h => h).
          + apply elements_spec3.
        - case_eq (List.filter
                     (fun x : A =>
                        match Oset.compare Elt a x with
                          | Eq => false
                          | Lt => true
                          | Gt => false
                        end) (elements _ s)).
          + intros _; constructor 1.
          + intros a1 l Hs.
            constructor 2.
            assert (Ha1 : List.In a1 (a1 :: l)); [left; apply refl_equal | ].
            rewrite <- Hs, filter_In in Ha1.
            destruct Ha1 as [_ Ha1].
            destruct (Oset.compare Elt a a1); trivial; discriminate Ha1.
      }
    * intros x y Hx Hy.
      rewrite InA_alt in Hx; destruct Hx as [x' [H Hx]].
      rewrite Oset.eq_bool_true_iff in H; subst x'.
      rewrite InA_alt in Hy.
      destruct Hy as [y' [H Hy]].
      rewrite Oset.eq_bool_true_iff in H; subst y'.
      rewrite filter_In in Hx.
      destruct Hx as [_ Hx].
      destruct Hy as [Hy | Hy]; 
        [subst y; destruct (Oset.compare Elt x a); trivial; discriminate Hx | ].
      rewrite filter_In in Hy; destruct Hy as [_ Hy].
      {
        apply Oset.compare_lt_trans with a.
        - destruct (Oset.compare Elt x a); trivial; discriminate Hx.
        - destruct (Oset.compare Elt a y); trivial; discriminate Hy.
      } 
Qed.

Lemma elements_singleton :
  forall a, elements _ (singleton FA a) = a :: nil.
Proof.
intros a.
apply (sorted_list_eq Elt).
- intros e; rewrite <- mem_elements, singleton_spec, 2 Oset.mem_bool_unfold.
  rewrite Bool.orb_false_r; apply refl_equal.
- apply elements_spec3.
- constructor 2; constructor.
Qed.
 
Lemma elements_singleton_strong :
  forall s a, elements _ s = a :: nil <-> equal FA s (singleton _ a) = true.
Proof.
intros s a; split; intro H.
- rewrite equal_spec; intro x.
  rewrite mem_elements, H, singleton_spec.
  rewrite 2 Oset.mem_bool_unfold, Bool.orb_false_r.
  apply refl_equal.
- rewrite (elements_spec1 _ _ _ H).
  rewrite elements_singleton.
  apply refl_equal.
Qed.

Lemma all_elements_equal :
  forall a s, (forall x, mem FA x s = true -> x = a) ->
              equal _ s (empty _) = true \/ equal _ s (singleton _ a) = true.
Proof.
intros a s H.
assert (H' : forall x, List.In x (elements _ s) -> x = a).
{
  intros x Ha; apply H.
  rewrite mem_elements, Oset.mem_bool_true_iff.
  assumption.
}
destruct (all_elements_equal Elt H' (elements_spec3 _ s)) as [K | K].
- left; rewrite equal_spec; intro x.
  rewrite mem_elements, K, empty_spec; apply refl_equal.
- right; rewrite equal_spec; intro x.
  rewrite mem_elements, K, singleton_spec, 2 Oset.mem_bool_unfold, Bool.orb_false_r.
  apply refl_equal.
Qed.

Lemma equal_union_singleton :
  forall a s1 s2, 
    equal FA (union _ s1 s2) (singleton _ a) = true <->
    ((equal _ s1 (singleton _ a) = true /\ equal _ s2 (singleton _ a) = true) \/
     (equal _ s1 (singleton _ a) = true /\ equal _ s2 (empty _) = true) \/
     (equal _ s1 (empty _) = true /\ equal _ s2 (singleton _ a) = true)).
Proof.
intros a s1 s2; split.
- intro H.
  assert (H1 : forall x, mem FA x s1 = true -> x = a).
  {
    intros x Hx.
    assert (Kx : mem _ x (union _ s1 s2) = true).
    {
      rewrite mem_union, Hx; apply refl_equal.
    }
    rewrite equal_spec in H; rewrite H, singleton_spec, Oset.eq_bool_true_iff in Kx.
    assumption.
  }
  assert (H2 : forall x, mem FA x s2 = true -> x = a).
  {
    intros x Hx.
    assert (Kx : mem _ x (union _ s1 s2) = true).
    {
      rewrite mem_union, Hx, Bool.orb_true_r; apply refl_equal.
    }
    rewrite equal_spec in H; rewrite H, singleton_spec, Oset.eq_bool_true_iff in Kx.
    assumption.
  }
  destruct (all_elements_equal _ H1) as [K1 | K1];
    destruct (all_elements_equal _ H2) as [K2 | K2].
  + apply False_rec.
    rewrite equal_spec in H, K1, K2.
    assert (K := H a).
    rewrite mem_union, K1, K2, empty_spec, singleton_spec in K.
    unfold Oset.eq_bool in K; rewrite Oset.compare_eq_refl in K.
    discriminate K.
  + right; right; split; assumption.
  + right; left; split; assumption.
  + left; split; assumption.
- intros [[H1 H2] | [[H1 H2] | [H1 H2]]];
  rewrite equal_spec in H1, H2;
  rewrite equal_spec; intro x; rewrite mem_union, H1, H2, singleton_spec.
  + apply Bool.orb_diag.
  + rewrite empty_spec, Bool.orb_false_r; apply refl_equal.
  + rewrite empty_spec, Bool.orb_false_l; apply refl_equal.
Qed.

Lemma mem_fold2 :
 forall (fb : A -> A -> bool) (ff : A -> A -> A) x s0 l0 s1 s2, 
   (forall x, mem FA x s0 = Oset.mem_bool Elt x l0) ->
  mem FA x (fold FA
       (fun t1 acc =>
           fold FA
           (fun t2 acc => if fb t1 t2 then add _ (ff t1 t2) acc else acc)
         s2 acc)
     s1 s0) =
     Oset.mem_bool Elt x (fold_left
       (fun acc t1 =>
           fold_left
           (fun acc t2 => if fb t1 t2 then (ff t1 t2 :: acc) else acc)
         (elements FA s2) acc)
     (elements FA s1) l0).
Proof.
intros fb ff x s0 l0 s1 s2.
rewrite mem_elements, fold_spec.
set (l1 := elements FA s1) in *; clearbody l1; clear s1.
revert s0 l0 s2; 
  induction l1 as [ | t1 l1]; 
  simpl; intros s0 l0 s2 H0;
  [rewrite <- mem_elements, H0; apply refl_equal | ].
set (s0' := fold 
              FA
              (fun (t2 : A) (acc : set FA) =>
                 if fb t1 t2 then add FA (ff t1 t2) acc else acc) s2 s0).
set (l0' := fold_left
              (fun (acc : list A) (t2 : A) =>
                 if fb t1 t2 then ff t1 t2 :: acc else acc) 
              (elements FA s2) l0).
assert (IH := IHl1 s0' l0' s2); simpl in IH; rewrite IH;
 [apply refl_equal | clear IH IHl1].
subst s0' l0'.
intros y; rewrite fold_spec.
set (l2 := elements FA s2); clearbody l2; clear s2.
revert s0 l0 H0; induction l2 as [ | t2 l2]; intros s0 l0 H0; simpl.
apply H0.
apply IHl2.
intros z; case (fb t1 t2); [ | apply H0].
rewrite add_spec; simpl; rewrite H0.
case (Oset.compare Elt z (ff t1 t2)); apply refl_equal.
Qed.

Definition interp_set_op (o : set_op) :=
  fun (s1 s2 : set FA) => match o with
                            | Inter => inter _ s1 s2 
                            | Diff => diff _ s1 s2 
                            | _ => union _ s1 s2
                          end.
                                            
Lemma interp_set_op_eq :
  forall o (s1 s2 s1' s2' : set FA),
    equal _ s1 s1' = true -> equal _ s2 s2' = true -> 
    equal _ (interp_set_op o s1 s2) (interp_set_op o s1' s2') = true.
Proof.
intros o s1 s2 s1' s2' H H';
  rewrite equal_spec in H, H'; rewrite equal_spec.
intros a; destruct o; unfold interp_set_op.  
- rewrite 2 mem_union, H, H'; apply refl_equal.
- rewrite 2 mem_union, H, H'; apply refl_equal.
- rewrite 2 mem_inter, H, H'; apply refl_equal.
- rewrite 2 mem_diff, H, H'; apply refl_equal.
Qed.

Lemma elements_inter :
  forall s1 s2 a, List.In a (elements FA (inter _ s1 s2)) <-> 
                  List.In a (elements _ s1) /\ List.In a (elements _ s2).
Proof.
intros s1 s2 a.
rewrite <- (Oset.mem_bool_true_iff Elt), <- mem_elements, mem_inter, 
Bool.andb_true_iff, 2 mem_elements, 2 Oset.mem_bool_true_iff.
split; exact (fun h => h).
Qed.

Lemma elements_union :
  forall s1 s2 a, List.In a (elements FA (union _ s1 s2)) <-> 
                  List.In a (elements _ s1) \/ List.In a (elements _ s2).
Proof.
intros s1 s2 a.
rewrite <- (Oset.mem_bool_true_iff Elt), <- mem_elements, mem_union, 
Bool.orb_true_iff, 2 mem_elements, 2 Oset.mem_bool_true_iff.
split; exact (fun h => h).
Qed.

Lemma cardinal_cardinal :
  let FA' := Feset.build (oeset_of_oset Elt) in
  forall s, cardinal FA s = Feset.cardinal FA' (Feset.mk_set FA' (elements FA s)).
Proof.
intros FA' s; rewrite cardinal_spec, Feset.cardinal_spec.
apply (comparelA_eq_length_eq (Oeset.compare (oeset_of_oset Elt))).
apply comparelA_Eq.
- intro x; rewrite <- Feset.mem_elements, Feset.mem_mk_set; apply refl_equal.
- unfold oeset_of_oset; simpl Oeset.compare.
  apply elements_spec3.
- apply Feset.elements_spec3.
Qed.

Lemma cardinal_subset : 
  forall s1 s2, subset FA s1 s2 = true -> (cardinal _ s1 <= cardinal _ s2)%nat.
Proof.
intros s1 s2 Hs.
rewrite 2 cardinal_cardinal.
apply Feset.cardinal_subset.
rewrite Feset.subset_spec.
intros x; rewrite Fset.subset_spec in Hs; generalize (Hs x).
rewrite 2 mem_elements, 2 Feset.mem_mk_set.
unfold oeset_of_oset, Oset.mem_bool, Oeset.mem_bool, Oset.eq_bool, Oeset.eq_bool; 
  simpl Oeset.compare.
exact (fun h => h).
Qed.

Lemma cardinal_strict_subset :
 forall s1 s2 e, subset FA s1 s2 = true -> mem FA e s1 = false -> mem FA e s2 = true -> 
   cardinal FA s1 < cardinal FA s2.
Proof.
intros s1 s2 e Hs H1 H2.
rewrite 2 cardinal_cardinal.
apply Feset.cardinal_strict_subset with e.
- rewrite Feset.subset_spec.
  intros x; rewrite Fset.subset_spec in Hs; generalize (Hs x).
  rewrite 2 mem_elements, 2 Feset.mem_mk_set.
  unfold oeset_of_oset, Oset.mem_bool, Oeset.mem_bool, Oset.eq_bool, Oeset.eq_bool; 
  simpl Oeset.compare.
  exact (fun h => h).
- rewrite <- H1, mem_elements, Feset.mem_mk_set.
  unfold oeset_of_oset, Oset.mem_bool, Oeset.mem_bool, Oset.eq_bool, Oeset.eq_bool; 
  simpl Oeset.compare; apply refl_equal.
- rewrite <- H2, mem_elements, Feset.mem_mk_set.
  unfold oeset_of_oset, Oset.mem_bool, Oeset.mem_bool, Oset.eq_bool, Oeset.eq_bool; 
  simpl Oeset.compare; apply refl_equal.
Qed.

End Sec.

Section Sec2.

Hypotheses A B : Type.
Hypothesis EltA : Oset.Rcd A.
Hypothesis EltB : Oset.Rcd B.
Hypothesis FA : Rcd EltA.
Hypothesis FB : Rcd EltB.

Definition map (f : A -> B) fa := mk_set FB (List.map f (elements FA fa)).

Lemma mem_map :
  forall (f : A -> B) s b, mem _ b (map f s) = true <-> (exists a, f a = b /\ mem _ a s = true).
Proof.
intros f s b.
unfold map.
rewrite mem_mk_set.
rewrite Oset.mem_bool_true_iff.
rewrite in_map_iff.
split; intros [a [H1 H2]]; exists a; split; trivial.
rewrite mem_elements, Oset.mem_bool_true_iff; assumption.
rewrite mem_elements, Oset.mem_bool_true_iff in H2; assumption.
Qed.

Lemma map_eq_s :
  forall f s1 s2, equal _ s1 s2 = true -> equal _ (map f s1) (map f s2) = true.
Proof.
intros f s1 s2 Hs.
rewrite equal_spec in Hs.
rewrite equal_spec; intro b.
rewrite eq_bool_iff, 2 mem_map; split.
- intros [a [Hb Ha]]; subst b.
  exists a; split; [apply refl_equal | rewrite <- Hs; assumption].
- intros [a [Hb Ha]]; subst b.
  exists a; split; [apply refl_equal | rewrite Hs; assumption].
Qed.

Lemma map_union : 
  forall f s1 s2, equal _ (map f (union _ s1 s2)) (union _ (map f s1) (map f s2)) = true.
Proof.
intros f s1 s2.
rewrite equal_spec.
intro b; rewrite mem_union, eq_bool_iff, mem_map; split.
- intros [a [Hb Ha]]; subst b.
  rewrite Fset.mem_union, Bool.orb_true_iff in Ha; rewrite Bool.orb_true_iff.
  destruct Ha as [Ha | Ha]; [left | right]; rewrite mem_map; exists a; split; trivial.
- rewrite Bool.orb_true_iff, 2 mem_map.
  intros [[a [Hb Ha]] | [a [Hb Ha]]]; exists a; rewrite Fset.mem_union, Ha; split; trivial.
  rewrite Bool.orb_true_r.
  apply refl_equal.
Qed.

Lemma all_diff_bool_elements :
 forall s, Oset.all_diff_bool EltA (elements FA s) = true.
Proof.
intros s.
assert (Aux : NoDupA (fun x y : A => Oset.eq_bool EltA x y = true) (elements FA s)).
{
  apply (SortA_NoDupA (Oset.Equivalence EltA) (Oset.StrictOrder EltA)).
  - intros a1 a2 Ha b1 b2 Hb.
    rewrite Oset.eq_bool_true_iff in Ha, Hb; subst a2 b2.
    split; exact (fun h => h).
  - apply  (elements_spec3 FA s).
}    
set (l := elements FA s) in *; clearbody l.
induction l as [ | a1 l].
- apply refl_equal.
- inversion Aux; clear Aux; subst. 
  simpl.
  destruct l as [ | a2 l]; [apply refl_equal | ].
  rewrite (IHl H2), Bool.andb_true_r; clear IHl H2.
  revert H1.
  generalize (a2 :: l); clear a2 l; intro l.
  rewrite negb_true_iff, <- not_true_iff_false.
  intros H K; apply H.
  rewrite Mem.mem_bool_true_iff in K.
  rewrite InA_alt; apply K.
Qed.

End Sec2.

End Fset.

Notation "a 'inS' s" := (Fset.mem _ a s = true) (at level 70, no associativity).
Notation "a 'inS?' s" := (Fset.mem _ a s) (at level 70, no associativity).
Notation "s1 '=S=' s2" := (Fset.equal _ s1 s2 = true) (at level 70, no associativity).
Notation "s1 '=S?=' s2" := (Fset.equal _ s1 s2) (at level 70, no associativity).
Notation "s1 'unionS' s2" := (Fset.union _ s1 s2) (at level 70, no associativity).
Notation "s1 'interS' s2" := (Fset.inter _ s1 s2) (at level 70, no associativity).
Notation "s1 'subS?' s2" := (Fset.subset _ s1 s2) (at level 70, no associativity).
Notation "s1 'subS' s2" := (Fset.subset _ s1 s2 = true) (at level 70, no associativity).
Notation "'emptysetS'" := (Fset.empty _) (at level 70, no associativity).
Notation "a 'addS' s" := (Fset.add _ a s) (at level 70, no associativity).
Notation "'{{{' s '}}}'" := (Fset.elements _ s) (at level 70, no associativity).
Notation "'{{' e '}}'" := (Fset.singleton _ e) (at level 70, no associativity).

Notation "a 'inSE' V" := (Feset.mem _ a V = true) (at level 70, no associativity).
Notation "a 'inSE?' V" := (Feset.mem _ a V) (at level 70, no associativity).
Notation "s1 '=SE=' s2" := (Feset.equal _ s1 s2 = true) (at level 70, no associativity).
Notation "s1 '=SE?=' s2" := (Feset.equal _ s1 s2) (at level 70, no associativity).
Notation "s1 'unionSE' s2" := (Feset.union _ s1 s2) (at level 70, no associativity).
Notation "s1 'interSE' s2" := (Feset.inter _ s1 s2) (at level 70, no associativity).
Notation "s1 'subSE?' s2" := (Feset.subset _ s1 s2) (at level 70, no associativity).
Notation "s1 'subSE' s2" := (Feset.subset _ s1 s2 = true) (at level 70, no associativity).
Notation "'emptysetSE'" := (Feset.empty _) (at level 70, no associativity).
Notation "a 'addSE' s" := (Feset.add _ a s) (at level 70, no associativity).


