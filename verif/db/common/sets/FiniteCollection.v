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

Require Import List NArith Bool BasicFacts ListFacts ListPermut OrderedSet FiniteSet FiniteBag.

Inductive flag : Type :=
  | FlagSet
  | FlagBag.

Module Fecol.

Record Rcd (elt : Type) (Elt : Oeset.Rcd elt) : Type :=
  mk_R
    {
      CSet : Feset.Rcd Elt;
      CBag : Febag.Rcd Elt
    }.


Section Sec.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.
Hypothesis CA : Rcd OA.

Notation FA := (CSet CA).
Notation BA := (CBag CA).

Inductive collection : Type :=
  | Fset : forall (s : Feset.set FA), collection
  | Fbag : forall (s : Febag.bag BA), collection.


Definition flag c :=
  match c with
      | Fset _ => FlagSet
      | Fbag _ => FlagBag
  end.

Definition to_set c :=
  match c with
    | Fset s => s
    | Fbag b => Feset.mk_set FA (Febag.elements BA b)
  end.

Definition to_bag c :=
  match c with
    | Fset s => Febag.mk_bag BA (Feset.elements FA s)
    | Fbag b => b
  end.

Definition mem a c :=
  match c with 
    | Fset s => Feset.mem _ a s
    | Fbag b => Febag.mem _ a b
  end.

Lemma mem_eq_1 :
  forall a1 a2 c, Oeset.compare OA a1 a2 = Eq -> mem a1 c = mem a2 c.
Proof.
intros a1 a [s | b] Ha; simpl.
- apply Feset.mem_eq_1; assumption.
- unfold Febag.mem.
  apply Oeset.mem_bool_eq_1; assumption.
Qed.

Lemma mem_mem_set :
  forall x c, mem x c = Feset.mem FA x (to_set c).
Proof.
intros x [s | b]; [apply refl_equal | simpl].
rewrite Febag.mem_nb_occ.
rewrite Febag.nb_occ_elements, Feset.mem_mk_set.
generalize (Oeset.mem_nb_occ OA x (Febag.elements BA b));
generalize (Oeset.not_mem_nb_occ OA x (Febag.elements BA b)).
destruct (Oeset.mem_bool OA x (Febag.elements BA b)).
- intros _ H; generalize (H (refl_equal _)); clear H; intro H.
  destruct (Oeset.nb_occ OA x (Febag.elements BA b)).
  + apply False_rec; apply H; apply refl_equal.
  + apply refl_equal.
- intros H _; rewrite (H (refl_equal _)); apply refl_equal.
Qed.

Lemma mem_mem_bag :
  forall x c, mem x c = Febag.mem BA x (to_bag c).
Proof.
intros x [s | b]; simpl; [ | trivial].
rewrite Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
Qed.

Definition add a c :=
  match c with
    | Fset s => Fset (Feset.add _ a s)
    | Fbag b => Fbag (Febag.add _ a b)
  end.

Definition singleton f a :=
  match f with
    | FlagSet => Fset (Feset.singleton FA a)
    | _ => Fbag (Febag.singleton BA a)
  end.

Definition equal c1 c2 :=
  match c1, c2 with
    | Fset s1, Fset s2 => Feset.equal _ s1 s2
    | Fbag b1, Fbag b2 => Febag.equal _ b1 b2
    | _, _ => false
  end.

Definition empty f :=
  match f with
    | FlagSet => Fset (Feset.empty FA)
    | _ => Fbag (Febag.empty BA)
  end.

Definition is_empty c :=
  match c with
    | Fset s => Feset.is_empty _ s
    | Fbag b => Febag.is_empty _ b
  end.

Definition elements c :=
  match c with
    | Fset s => Feset.elements _ s
    | Fbag b => Febag.elements _ b
  end.

Definition nb_occ a c := Oeset.nb_occ OA a (elements c).

Definition choose c :=
  match c with
    | Fset s => Feset.choose _ s
    | Fbag b => Febag.choose _ b
  end.

Definition partition f c :=
  match c with
    | Fset s => match Feset.partition _ f s with (s1, s2) => (Fset s1, Fset s2) end
    | Fbag b => match Febag.partition _ f b with (b1, b2) => (Fbag b1, Fbag b2) end
  end.

Definition fold (B : Type) (f : A -> B -> B) c b0 :=
  match c with
    | Fset s => Feset.fold FA f s b0
    | Fbag b => Febag.fold BA f b b0
  end.

Definition app_col f fs fb c :=
  match f, c with
    | FlagSet, _ => Fset (fs (to_set c))
    | FlagBag, _ => Fbag (fb (to_bag c))
  end.

Definition app_col2 f fs fb c1 c2 :=
  match f, c1, c2 with
    | FlagSet, _, _ => Fset (fs (to_set c1) (to_set c2))
    | FlagBag, _, _ => Fbag (fb (to_bag c1) (to_bag c2))
  end.

Definition union f c1 c2 := app_col2 f (Feset.union FA) (Febag.union BA) c1 c2.

Definition union_max f c1 c2 := app_col2 f (Feset.union FA) (Febag.union_max BA) c1 c2.

Definition inter f c1 c2 := app_col2 f (Feset.inter FA) (Febag.inter BA) c1 c2.

Definition diff f c1 c2 := app_col2 f (Feset.diff FA) (Febag.diff BA) c1 c2.

Lemma mem_union :
  forall f c1 c2 t, mem t (union f c1 c2) = orb (mem t c1) (mem t c2).
Proof.
intros f [s1 | b1] [s2 | b2] t; destruct f; simpl.
- apply Feset.mem_union.
- rewrite Febag.mem_union, 2 Febag.mem_mk_bag, 2 Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_union, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_union, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, 2 Feset.mem_mk_set; apply refl_equal.
- apply Febag.mem_union; apply refl_equal.
Qed.

Lemma mem_inter :
  forall f c1 c2 t, mem t (inter f c1 c2) = andb (mem t c1) (mem t c2).
Proof.
intros f [s1 | b1] [s2 | b2] t; destruct f; simpl.
- apply Feset.mem_inter.
- rewrite Febag.mem_inter, 2 Febag.mem_mk_bag, 2 Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_inter, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_inter, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_inter, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_inter, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_inter, 2 Feset.mem_mk_set; apply refl_equal.
- apply Febag.mem_inter; apply refl_equal.
Qed.

Lemma nb_occ_inter_set :
  forall c1 c2 t, 
    nb_occ t (inter FlagSet c1 c2) = if (andb (mem t c1) (mem t c2)) then 1%N else 0%N.
Proof.
intros c1 c2 t; unfold nb_occ, elements, inter; simpl.
rewrite <- Feset.nb_occ_unfold, Feset.nb_occ_alt, Feset.mem_inter, 2 mem_mem_set.
apply refl_equal.
Qed.

Lemma nb_occ_inter_bag :
  forall c1 c2 t, nb_occ t (inter FlagBag c1 c2) = N.min (nb_occ t c1) (nb_occ t c2).
Proof.
intros c1 c2 t.
unfold nb_occ at 1, elements; simpl.
rewrite <- Febag.nb_occ_elements, Febag.nb_occ_inter.
apply f_equal2.
- unfold nb_occ; destruct c1; simpl.
  + rewrite Febag.nb_occ_mk_bag; apply refl_equal.
  + apply Febag.nb_occ_elements.
- unfold nb_occ; destruct c2; simpl.
  + rewrite Febag.nb_occ_mk_bag; apply refl_equal.
  + apply Febag.nb_occ_elements.
Qed.

Lemma mem_union_max :
  forall f c1 c2 t, mem t (union_max f c1 c2) = orb (mem t c1) (mem t c2).
Proof.
intros f [s1 | b1] [s2 | b2] t; destruct f; simpl.
- apply Feset.mem_union.
- rewrite Febag.mem_union_max, 2 Febag.mem_mk_bag, 2 Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_union_max, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, Feset.mem_mk_set; apply refl_equal.
- rewrite Febag.mem_union_max, Febag.mem_mk_bag, Feset.mem_elements; apply refl_equal.
- rewrite Feset.mem_union, 2 Feset.mem_mk_set; apply refl_equal.
- apply Febag.mem_union_max; apply refl_equal.
Qed.

Lemma nb_occ_union_max_bag :
  forall c1 c2 t, nb_occ t (union_max FlagBag c1 c2) = N.max (nb_occ t c1) (nb_occ t c2).
Proof.
intros c1 c2 t; simpl; unfold nb_occ, elements.
rewrite <- Febag.nb_occ_elements, Febag.nb_occ_union_max; apply f_equal2.
- destruct c1 as [s1 | b1]; simpl.
  + rewrite Febag.nb_occ_mk_bag; apply refl_equal.
  + apply Febag.nb_occ_elements.
- destruct c2 as [s2 | b2]; simpl.
  + rewrite Febag.nb_occ_mk_bag; apply refl_equal.
  + apply Febag.nb_occ_elements.
Qed.

Lemma diff_spec_weak :
  forall f c1 c2 t, mem t (diff f c1 c2) = true -> mem t c1 = true.
Proof.
intros f [s1 | b1] [s2 | b2] t; destruct f; simpl;
try (rewrite Feset.mem_diff, Bool.andb_true_iff; apply proj1);
try (apply Febag.diff_spec_weak);
try (intro H; assert (K := Febag.diff_spec_weak _ _ _ _ H);
              rewrite Febag.mem_mk_bag, <- Feset.mem_elements in K; apply K);
try (rewrite Feset.mem_diff, Bool.andb_true_iff, Feset.mem_mk_set; apply proj1).
Qed.

Lemma equal_spec : 
  forall s1 s2, equal s1 s2 = true <-> (flag s1 = flag s2 /\ forall e, nb_occ e s1 = nb_occ e s2).
Proof.
intros [s1 | b1] [s2 | b2]; split; simpl; intro H; try discriminate.
- split; [apply refl_equal | ].
  rewrite Feset.equal_spec in H; intro x; unfold nb_occ, elements.
  assert (K := Feset.nb_occ_alt FA x); unfold Feset.nb_occ in K.
  rewrite 2 K, H; apply refl_equal.
- assert (K := Feset.nb_occ_alt FA); unfold Feset.nb_occ in K.
  rewrite Feset.equal_spec; intro x.
  generalize (proj2 H x).
  unfold nb_occ, elements.
  rewrite 2 K.
  destruct (x inSE? s1); destruct (x inSE? s2); trivial; discriminate.
- assert (H1 := proj1 H); discriminate H1.
- assert (H1 := proj1 H); discriminate H1.
- split; [apply refl_equal | ].
  rewrite Febag.nb_occ_equal in H; intro x.
  unfold nb_occ, elements; rewrite <- 2 Febag.nb_occ_elements.
  rewrite H; apply refl_equal.
- rewrite Febag.nb_occ_equal; intro x.
  unfold nb_occ, elements.
  destruct H as [_ H]; assert (Hx := H x).
  unfold nb_occ, elements in Hx; rewrite <- 2 Febag.nb_occ_elements in Hx.
  apply Hx.  
Qed.

Lemma equal_trans :
  forall s1 s2 s3, equal s1 s2 = true -> equal s2 s3 = true -> equal s1 s3 = true.
Proof.
intros s1 s2 s3; rewrite 3 equal_spec.
intros [H1 H2] [K1 K2]; split.
- rewrite H1; apply K1.
- intros e; rewrite H2; apply K2.
Qed.

Lemma equal_sym : forall s1 s2, equal s1 s2 = equal s2 s1.
Proof.
intros s1 s2; rewrite eq_bool_iff.
rewrite 2 equal_spec; split; intros [H1 H2]; split.
- apply sym_eq; apply H1.
- intros e; apply sym_eq; apply H2.
- apply sym_eq; apply H1.
- intros e; apply sym_eq; apply H2.
Qed.

Lemma equal_eq_1 : forall s1 s1' s2, equal s1 s1' = true -> equal s1 s2 = equal s1' s2.
Proof.
intros s1 s1' s2 H.
rewrite equal_spec in H.
rewrite eq_bool_iff, 2 equal_spec; split.
- intros [H1 H2]; split.
  + rewrite <- (proj1 H); assumption.
  + intro s; rewrite <- (proj2 H); apply H2.
- intros [H1 H2]; split.
  + rewrite (proj1 H); assumption.
  + intro s; rewrite (proj2 H); apply H2.
Qed.

Lemma equal_eq_2 : forall s1 s2 s2', equal s2 s2' = true -> equal s1 s2 = equal s1 s2'.
Proof.
intros s1 s2 s2' H.
rewrite 2 (equal_sym s1).
apply equal_eq_1; assumption.
Qed.

Lemma mem_empty : forall f x, mem x (empty f) = false.
Proof.
intros f x; destruct f; simpl.
- rewrite Feset.empty_spec; apply refl_equal.
- rewrite Febag.mem_nb_occ, Febag.nb_occ_empty; apply refl_equal.
Qed.

Lemma nb_occ_set :
  forall x c, flag c = FlagSet -> nb_occ x c = Feset.nb_occ _ x (to_set c).
Proof.
intros x c H; destruct c; try discriminate.
unfold to_set; simpl.
 apply refl_equal.
Qed.

Lemma nb_occ_bag :
  forall x c, nb_occ x c = Febag.nb_occ _ x (to_bag c).
Proof.
intros x c; destruct c as [c | c].
- simpl; rewrite Febag.nb_occ_mk_bag; unfold nb_occ.
  apply refl_equal.
- unfold to_bag; rewrite Febag.nb_occ_elements.
  apply refl_equal.
Qed.

Lemma nb_occ_unfold :
  forall x c, nb_occ x c = match flag c with
                             | FlagSet => (if Feset.mem _ x (to_set c) then 1 else 0)%N
                             | _ =>  Febag.nb_occ _ x (to_bag c)
                           end.
Proof.
intros x c; destruct c; unfold nb_occ.
- rewrite <- Feset.nb_occ_alt; unfold Feset.nb_occ.
  apply refl_equal.
- simpl; rewrite <- Febag.nb_occ_elements.
  apply refl_equal.
Qed.

Lemma nb_occ_empty : forall f x, nb_occ x (empty f) = 0%N.
Proof.
intros f x; unfold nb_occ; destruct f; simpl.
- rewrite Feset.elements_empty; apply refl_equal.
- rewrite Febag.elements_empty; apply refl_equal.
Qed.


Lemma is_empty_spec : forall s, is_empty s = equal s (empty (flag s)).
Proof.
intros [s | b]; simpl.
- apply Feset.is_empty_spec.
- apply Febag.is_empty_spec.
Qed.

Lemma mem_singleton : forall f x y, mem x (singleton f y) = true -> Oeset.compare OA x y = Eq.
Proof.
intros f x y H; destruct f; unfold singleton, mem in H.
- rewrite Feset.singleton_spec in H; unfold Oeset.eq_bool in H.
  rewrite compare_eq_true in H; assumption.
- rewrite Febag.mem_nb_occ, Febag.nb_occ_singleton in H; unfold Oeset.eq_bool in H.
  case_eq (Oeset.compare OA x y); intro Hx; rewrite Hx in H; try discriminate H.
  apply refl_equal.
Qed.

Lemma elements_spec1 :
  forall c1 c2, equal c1 c2 = true -> 
  comparelA (Oeset.compare OA) (elements c1) (elements c2) = Eq.
Proof.
intros [s1 | s1] [s2 | s2] H; try discriminate H; simpl in H.
- apply Feset.elements_spec1; assumption.
- apply Febag.elements_spec1; assumption.
Qed.

Lemma mem_elements :
  forall x c, mem x c = Oeset.mem_bool OA x (elements c).
Proof.
intros x [s | b].
- apply Feset.mem_elements.
- apply refl_equal.
Qed.

Lemma elements_set :
  forall c, flag c = FlagSet -> elements c = Feset.elements _ (to_set c).
Proof.
intros c Hc; destruct c; try discriminate Hc; apply refl_equal.
Qed.

Lemma elements_bag :
  forall c, flag c = FlagBag -> elements c = Febag.elements _ (to_bag c).
Proof.
intros c Hc; destruct c; try discriminate Hc; apply refl_equal.
Qed.

Lemma in_elements_mem :
  forall x c, In x (elements c) -> mem x c = true.
Proof.
intros x [s | b] H; simpl.
- apply Feset.in_elements_mem; assumption.
- unfold Febag.mem; rewrite Oeset.mem_bool_true_iff.
  exists x; split; [apply Oeset.compare_eq_refl | assumption].
Qed.

Lemma nb_occ_eq_1 :
  forall c x1 x2, Oeset.compare OA x1 x2 = Eq -> nb_occ x1 c = nb_occ x2 c.
Proof.
intros c x1 x2 Hx; unfold nb_occ.
rewrite (Oeset.nb_occ_eq_1 _ _ _ _ Hx).
apply refl_equal.
Qed.

Lemma nb_occ_eq_2 :
  forall c1 c2, equal c1 c2 = true -> forall x, nb_occ x c1 = nb_occ x c2.
Proof.
intros c1 c2 H x; rewrite equal_spec in H.
apply (proj2 H).
Qed.

Lemma mem_bool_elements_eq_2 :
  forall c1 c2, 
    equal c1 c2 = true ->
    forall x, Oeset.mem_bool OA x (elements c1) = Oeset.mem_bool OA x (elements c2).
Proof.
intros c1 c2 H x.
assert (K := elements_spec1 _ _ H).
set (l1 := elements c1) in *; clearbody l1.
set (l2 := elements c2) in *; clearbody l2.
revert l2 K; induction l1 as [ | t1 l1]; intros [ | t2 l2] K; try discriminate K.
- apply refl_equal.
- simpl in K; simpl.
  case_eq (Oeset.compare OA t1 t2); intro Ht; rewrite Ht in K; try discriminate K.
  rewrite (IHl1 l2 K); apply f_equal2; [ | apply refl_equal].
  unfold Oeset.eq_bool.
  case_eq (Oeset.compare OA x t1); intro Ht1.
  + rewrite (Oeset.compare_eq_trans OA _ _ _ Ht1 Ht); apply refl_equal.
  + rewrite (Oeset.compare_lt_eq_trans OA _ _ _ Ht1 Ht); apply refl_equal.
  + rewrite (Oeset.compare_gt_eq_trans OA _ _ _ Ht1 Ht); apply refl_equal.
Qed.

Lemma mem_eq_2 :
  forall c1 c2, equal c1 c2 = true -> forall x, mem x c1 = mem x c2.
Proof.
intros c1 c2 H x.
rewrite 2 mem_elements; apply mem_bool_elements_eq_2.
assumption.
Qed.

Lemma nb_occ_eq_mem_eq :
  forall c1 c2 x1 x2, nb_occ x1 c1 = nb_occ x2 c2 -> mem x1 c1 = mem x2 c2.
Proof.
intros c1 c2 x1 x2 H.
unfold nb_occ in H.
case_eq (Oeset.nb_occ OA x2 (elements c2)); [intro Hx | intros p Hx].
- unfold mem; destruct c2 as [s2 | b2]; simpl in Hx.
  + rewrite Feset.mem_elements.
    generalize (Oeset.mem_nb_occ OA x2 (Feset.elements FA s2)); rewrite Hx.
    case (Oeset.mem_bool OA x2 (Feset.elements FA s2));
      [intro Abs; apply False_rec; apply Abs; trivial | ].
    intros _; simpl in H; rewrite Hx in H.
    destruct c1 as [s1 | b1]; simpl in H.
    * rewrite Feset.mem_elements.
      generalize (Oeset.mem_nb_occ OA x1 (Feset.elements FA s1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Feset.elements FA s1));
        [intro Abs; apply False_rec; apply Abs; trivial | ].
      trivial.
    * unfold Febag.mem.
      generalize (Oeset.mem_nb_occ OA x1 (Febag.elements BA b1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Febag.elements BA b1));
        [intro Abs; apply False_rec; apply Abs; trivial | ].
      trivial.
  + unfold Febag.mem.
    generalize (Oeset.mem_nb_occ OA x2 (Febag.elements BA b2)); rewrite Hx.
    case (Oeset.mem_bool OA x2 (Febag.elements BA b2));
      [intro Abs; apply False_rec; apply Abs; trivial | ].
    intros _; simpl in H; rewrite Hx in H.
    destruct c1 as [s1 | b1]; simpl in H.
    * rewrite Feset.mem_elements.
      generalize (Oeset.mem_nb_occ OA x1 (Feset.elements FA s1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Feset.elements FA s1));
        [intro Abs; apply False_rec; apply Abs; trivial | ].
      trivial.
    * unfold Febag.mem.
      generalize (Oeset.mem_nb_occ OA x1 (Febag.elements BA b1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Febag.elements BA b1));
        [intro Abs; apply False_rec; apply Abs; trivial | ].
      trivial.
- unfold mem; destruct c2 as [s2 | b2]; simpl in Hx.
  + rewrite Feset.mem_elements.
    generalize (Oeset.not_mem_nb_occ OA x2 (Feset.elements FA s2)); rewrite Hx.
    case (Oeset.mem_bool OA x2 (Feset.elements FA s2));
      [ | intro Abs; apply False_rec; discriminate Abs; trivial].
    intros _; simpl in H; rewrite Hx in H.
    destruct c1 as [s1 | b1]; simpl in H.
    * rewrite Feset.mem_elements.
      generalize (Oeset.not_mem_nb_occ OA x1 (Feset.elements FA s1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Feset.elements FA s1));
        [ | intro Abs; apply False_rec; discriminate Abs; trivial].
      trivial.
    * unfold Febag.mem.
      generalize (Oeset.not_mem_nb_occ OA x1 (Febag.elements BA b1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Febag.elements BA b1));
        [ | intro Abs; apply False_rec; discriminate Abs; trivial].
      trivial.
  + unfold Febag.mem.
    generalize (Oeset.not_mem_nb_occ OA x2 (Febag.elements BA b2)); rewrite Hx.
    case (Oeset.mem_bool OA x2 (Febag.elements BA b2));
      [ | intro Abs; apply False_rec; discriminate Abs; trivial].
    intros _; simpl in H; rewrite Hx in H.
    destruct c1 as [s1 | b1]; simpl in H.
    * rewrite Feset.mem_elements.
      generalize (Oeset.not_mem_nb_occ OA x1 (Feset.elements FA s1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Feset.elements FA s1));
        [ | intro Abs; apply False_rec; discriminate Abs; trivial].
      trivial.
    * unfold Febag.mem.
      generalize (Oeset.not_mem_nb_occ OA x1 (Febag.elements BA b1)); rewrite H.
      case (Oeset.mem_bool OA x1 (Febag.elements BA b1));
        [ | intro Abs; apply False_rec; discriminate Abs; trivial].
      trivial.
Qed.

Lemma mem_nb_occ :
  forall x c, mem x c = true -> nb_occ x c <> 0%N.
Proof.
intros x c; destruct c as [c | c]; simpl; unfold nb_occ, elements;
intro H; apply Oeset.mem_nb_occ.
- rewrite <- Feset.mem_elements; assumption.
- unfold Febag.mem in H; assumption.
Qed.

Lemma nb_occ_mem :
  forall x c, nb_occ x c <> 0%N -> mem x c = true.
Proof.
intros x c; destruct c as [c | c]; simpl; unfold nb_occ, elements;
intro H.
- rewrite Feset.mem_elements; apply Oeset.nb_occ_mem; assumption.
- unfold Febag.mem; apply Oeset.nb_occ_mem; assumption.
Qed.

Lemma not_mem_nb_occ : 
  forall x c, mem x c = false -> nb_occ x c = 0%N.
Proof.
intros x c; destruct c as [c | c]; simpl; unfold nb_occ, elements;
intro H; apply Oeset.not_mem_nb_occ.
- rewrite <- Feset.mem_elements; assumption.
- unfold Febag.mem in H; assumption.
Qed.

Lemma nb_occ_not_mem :
  forall x c, nb_occ x c = 0%N -> mem x c = false.
Proof.
intros x c; destruct c as [c | c]; simpl; unfold nb_occ, elements;
intro H.
- rewrite <- not_true_iff_false, Feset.mem_elements, not_true_iff_false; 
  apply Oeset.nb_occ_not_mem; assumption.
- unfold Febag.mem; apply Oeset.nb_occ_not_mem; assumption.
Qed.

Lemma inter_eq_1 :
  forall flg c1 c1' c2, equal c1 c1' = true -> equal (inter flg c1 c2) (inter flg c1' c2) = true.
Proof.
intros flg c1 c1' c2 H.
rewrite equal_spec in H; rewrite equal_spec; split; [destruct flg; trivial | ].
intros e; rewrite 2 nb_occ_unfold; destruct flg; simpl.
- rewrite 2 Feset.mem_inter, <- 3 mem_mem_set.
  case_eq (mem e c1); intro He.
  + rewrite (nb_occ_mem e c1'); [apply refl_equal | ].
    rewrite <- (proj2 H).
    apply mem_nb_occ; assumption.
  + rewrite (nb_occ_not_mem e c1'); [apply refl_equal | ].
    rewrite <- (proj2 H).
    apply not_mem_nb_occ; assumption.
- rewrite 2 Febag.nb_occ_inter.
  apply f_equal2; [ | apply refl_equal].
  rewrite <- 2 nb_occ_bag.
  apply (proj2 H).
Qed.

Lemma inter_eq_2 :
  forall flg c1 c2 c2', equal c2 c2' = true -> equal (inter flg c1 c2) (inter flg c1 c2') = true.
Proof.
intros flg c1 c2 c2' H.
rewrite equal_spec in H; rewrite equal_spec; split; [destruct flg; trivial | ].
intros e; rewrite 2 nb_occ_unfold; destruct flg; simpl.
- rewrite 2 Feset.mem_inter, <- 3 mem_mem_set.
  case_eq (mem e c2); intro He.
  + rewrite (nb_occ_mem e c2'); [apply refl_equal | ].
    rewrite <- (proj2 H).
    apply mem_nb_occ; assumption.
  + rewrite (nb_occ_not_mem e c2'); [apply refl_equal | ].
    rewrite <- (proj2 H).
    apply not_mem_nb_occ; assumption.
- rewrite 2 Febag.nb_occ_inter.
  apply f_equal2; [apply refl_equal | ].
  rewrite <- 2 nb_occ_bag.
  apply (proj2 H).
Qed.


Lemma choose_spec3 :
  forall s1 s2, equal s1 s2 = true ->
                match choose s1 with
                  | None => choose s2 = None
                  | Some e1 => match choose s2 with
                                 | None => False
                                 | Some e2 => Oeset.compare OA e1 e2 = Eq
                               end
                end.
Proof.
intros [s1 | s1] [s2 | s2] H; simpl in H; try discriminate H; simpl; simpl in H.
- apply Feset.choose_spec3; assumption.
- apply Febag.choose_spec3; assumption.
Qed.

Lemma partition_spec1 : 
  forall c f,
    (forall e e', mem e c = true -> Oeset.compare OA e e' = Eq -> f e = f e') -> 
    forall x, nb_occ x (fst (partition f c)) = (nb_occ x c * (if f x then 1 else 0))%N.
Proof.
intros [s | b] f H x; simpl.
- generalize (Feset.partition_spec1 FA s f H x).
  case (Feset.partition FA f s); intros s1 s2; simpl fst; simpl.
  rewrite 2 nb_occ_unfold; simpl; intro Hx; rewrite Hx.
  case (x inSE? s); case (f x); apply refl_equal. 
- assert (H' : forall e e' : A,
                 (Febag.nb_occ BA e b >= 1)%N -> Oeset.compare OA e e' = Eq -> f e = f e').
  {
    intros x1 x2 Hx; apply H; simpl.
    rewrite Febag.mem_nb_occ; destruct (Febag.nb_occ BA x1 b); trivial.
    apply False_rec; apply Hx; apply refl_equal.
  }
  generalize (Febag.partition_spec1 BA b x f H').
  case (Febag.partition BA f b); intros b1 b2; simpl fst.
  rewrite 2 nb_occ_unfold; simpl.
  exact (fun h => h).
Qed.

Lemma partition_spec2 : 
  forall s f,
    (forall e e', mem e s = true -> Oeset.compare OA e e' = Eq -> f e = f e') -> 
    forall x, nb_occ x (snd (partition f s)) = (nb_occ x s * if (f x) then 0 else 1)%N.
Proof.
intros [s | b] f H x; simpl.
- generalize (Feset.partition_spec2 FA s f H x).
  case (Feset.partition FA f s); intros s1 s2; simpl fst; simpl.
  rewrite 2 nb_occ_unfold; simpl; intro Hx; rewrite Hx.
  case (x inSE? s); case (f x); apply refl_equal. 
- assert (H' : forall e e' : A,
                 (Febag.nb_occ BA e b >= 1)%N -> Oeset.compare OA e e' = Eq -> f e = f e').
  {
    intros x1 x2 Hx; apply H; simpl.
    rewrite Febag.mem_nb_occ; destruct (Febag.nb_occ BA x1 b); trivial.
    apply False_rec; apply Hx; apply refl_equal.
  }
  generalize (Febag.partition_spec2 BA b x f H').
  case (Febag.partition BA f b); intros b1 b2; simpl fst.
  rewrite 2 nb_occ_unfold; simpl.
  exact (fun h => h).
Qed.

Definition interp_set_op o f c1 c2 :=
  match o with
    | UnionMax => union_max f c1 c2
    | Union => union f c1 c2
    | Inter => inter f c1 c2
    | Diff => diff f c1 c2
  end.

Fixpoint Union f lc :=
  match lc with
    | nil => empty f
    | a :: lc => union f a (Union f lc)
  end.

Lemma Union_unfold :
  forall f lc, Union f lc = match lc with nil => empty f | a :: lc => union f a (Union f lc) end.
Proof.
intros f lc; destruct lc; apply refl_equal.
Qed.

Lemma flag_Union : 
  forall c lc, flag (Union (flag c) lc) = (flag c). 
Proof.
intros c lc; destruct c; destruct lc; simpl; trivial.
Qed.

Definition mk_col f l :=
  match f with
    | FlagSet => Fset (Feset.mk_set _ l)
    | _ => Fbag (Febag.mk_bag _ l)
  end.

Lemma mem_mk_col :
  forall f l t, mem t (mk_col f l) = Oeset.mem_bool OA t l.
Proof.
intros f l t; destruct f; unfold mem, mk_col.
- apply Feset.mem_mk_set.
- apply Febag.mem_mk_bag.
Qed.

Lemma nb_occ_mk_col :
  forall f l t, nb_occ t (mk_col f l) = 
                (match f with 
                   | FlagSet => 1
                   | _ => Oeset.nb_occ OA t l
                 end * (if Oeset.mem_bool OA t l then 1 else 0))%N.
Proof.
intros f l t; destruct f; rewrite nb_occ_unfold; simpl.
- rewrite Feset.mem_mk_set; destruct (Oeset.mem_bool OA t l); apply refl_equal.
- rewrite Febag.nb_occ_mk_bag.
  generalize (Oeset.not_mem_nb_occ OA t l).
  case (Oeset.mem_bool OA t l).
  + intros _; rewrite N.mul_1_r; apply refl_equal.
  + intro H; rewrite (H (refl_equal _)); apply refl_equal.
Qed.

Lemma nb_occ_mk_col_flagbag :
  forall f l t, f = FlagBag -> nb_occ t (mk_col f l) = Oeset.nb_occ OA t l.
Proof.
intros f l t Hf; subst f; rewrite nb_occ_mk_col.
generalize (Oeset.not_mem_nb_occ OA t l).
case (Oeset.mem_bool OA t l).
- intros _; rewrite N.mul_1_r; apply refl_equal.
- intro H; rewrite (H (refl_equal _)); apply refl_equal.
Qed.

Lemma nb_occ_elements :
  forall c t, nb_occ t c = Oeset.nb_occ OA t (elements c).
Proof.
intros c t; unfold nb_occ; apply refl_equal.
Qed.

Lemma nb_occ_mk_col_eq :
  forall f1 f2 l1 l2 t, f1 = f2 -> Oeset.nb_occ OA t l1 = Oeset.nb_occ OA t l2 ->
                        nb_occ t (mk_col f1 l1) = nb_occ t (mk_col f2 l2).
Proof.
intros f1 f2 l1 l2 t Hf Hl; subst f2.
rewrite 2 nb_occ_mk_col, Hl; apply f_equal.
case_eq (Oeset.mem_bool OA t l1); intro H1.
- case_eq (Oeset.mem_bool OA t l2); intro H2; [apply refl_equal | ].
  rewrite (Oeset.not_mem_nb_occ _ _ _ H2) in Hl.
  generalize (Oeset.mem_nb_occ _ _ _ H1); rewrite Hl; intro Abs.
  apply False_rec; apply Abs; apply refl_equal.
- rewrite (Oeset.not_mem_nb_occ _ _ _ H1) in Hl.
  case_eq (Oeset.mem_bool OA t l2); intro H2; [ | apply refl_equal].
  generalize (Oeset.mem_nb_occ _ _ _ H2); rewrite Hl; intro Abs.
  apply False_rec; apply Abs; apply refl_equal.
Qed.

Definition filter f c :=
  match c with
    | Fset s => Fset (Feset.filter _ f s)
    | Fbag b => Fbag (Febag.filter _ f b)
  end.

Lemma flag_filter :
  forall f c, flag (filter f c) = flag c.
Proof.
intros f c; destruct c; trivial.
Qed.

Lemma mem_filter :
  forall f c,
    (forall x1 x2, mem x1 c = true -> Oeset.compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, mem x (filter f c) = andb (mem x c) (f x).
Proof.
intros f [s | b] H x; simpl.
- rewrite Feset.filter_spec; [apply refl_equal | apply H].
- apply Febag.mem_filter; assumption.
Qed.

Lemma nb_occ_filter :
  forall f c, 
    (forall x1 x2, mem x1 c = true -> Oeset.compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall x, nb_occ x (filter f c) = (nb_occ x c * (if f x then 1 else 0))%N.
Proof.
intros f [s | b] H x; unfold filter.
- assert (Hx := Feset.nb_occ_alt FA x); unfold Feset.nb_occ in Hx.
  rewrite 2 nb_occ_elements; unfold filter, elements; rewrite 2 Hx, Feset.filter_spec.
  + destruct (x inSE? s); destruct (f x); trivial.
  + intros x1 x2 Kx; apply H; unfold mem; assumption.
- assert (Hx := @Febag.nb_occ_filter _ _ BA b f).
  rewrite nb_occ_unfold; simpl flag; simpl to_bag; cbv iota; rewrite Hx.
  + rewrite nb_occ_unfold; simpl flag; simpl to_bag; cbv iota.
    apply refl_equal.
  + intros x1 x2 Kx; apply H.
    simpl; unfold Febag.mem.
    generalize (Oeset.not_mem_nb_occ OA x1 (Febag.elements BA b)).
    destruct (Oeset.mem_bool OA x1 (Febag.elements BA b)); trivial.
    intro Abs; rewrite Febag.nb_occ_elements, (Abs (refl_equal _)) in Kx.
    unfold N.ge in Kx; apply False_rec; apply Kx; apply refl_equal.
Qed.

Lemma elements_filter :
  forall f c, (forall x1 x2, mem x1 c = true -> Oeset.compare OA x1 x2 = Eq -> f x1 = f x2) ->
              _permut (fun x y => Oeset.compare OA x y = Eq) 
                      (elements (filter f c)) (List.filter f (elements c)).
Proof.
intros f c H; apply nb_occ_permut.
intros x.
assert (K := nb_occ_filter _ _ H x).
unfold nb_occ in K; rewrite K.
rewrite Oeset.nb_occ_filter.
- case (f x).
  + rewrite N.mul_1_r; apply refl_equal.
  + rewrite N.mul_0_r; apply refl_equal.
- do 3 intro; apply H.
  unfold mem; destruct c.
  + rewrite Feset.mem_elements; apply H0.
  + apply H0.
Qed.

Lemma nb_occ_mk_col_filter :
  forall flg f l, 
    (forall x1 x2, Oeset.mem_bool OA x1 l = true -> Oeset.compare OA x1 x2 = Eq -> f x1 = f x2) ->
    forall t,
      nb_occ t (mk_col flg (List.filter f l)) = (nb_occ t (mk_col flg l) * (if f t then 1 else 0))%N.
Proof.
intros flg f l Hl t.
rewrite 2 nb_occ_mk_col, (Oeset.nb_occ_filter _ _ _ Hl), (Oeset.mem_bool_filter _ _ _ Hl).
destruct flg; destruct (f t); destruct (Oeset.mem_bool OA t l); 
repeat rewrite N.mul_1_r; repeat rewrite N.mul_0_r; trivial.
Qed.


End Sec.

Arguments Fset {_} {_} {_} s.
Arguments Fbag {_} {_} {_} s.

Definition map (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) (f : A -> B) (c : collection CA) :=
  match c with
    | Fset s => Fset (CA:=CB) (Feset.map (CSet CA) (CSet CB) f s)
    | Fbag b => Fbag (CA:=CB) (Febag.map (CBag CA) (CBag CB) f b)
  end.

Lemma map_unfold :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) (f : A -> B) (c : collection CA),
    (map CB f c) = (mk_col CB (flag c) (List.map f (elements c))).
Proof.
intros A B OA CA OB CB f c; destruct c; simpl.
- unfold Feset.map; apply refl_equal.
- unfold Febag.map; apply refl_equal.
Qed.

Lemma mem_map :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) 
         (f : A -> B) (c : collection CA) b,
    mem b (map CB f c) = true <-> 
    (exists a, Oeset.compare OB b (f a) = Eq /\ In a (elements c)).
Proof.
intros A B OA CA OB CB f c b; destruct c as [s | s]; unfold map; simpl.
- rewrite Feset.mem_map; split; exact (fun h => h).
- rewrite Febag.mem_map; split; exact (fun h => h).
Qed.

Lemma nb_occ_bag_map_eq :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) 
         (f : A -> B) (c1 c2 : collection CA), flag c1 = FlagBag -> flag c2 = FlagBag ->
    (forall x1 x2, mem x1 c1 = true -> mem x2 c2 = true -> Oeset.compare OA x1 x2 = Eq ->
                   Oeset.compare OB (f x1) (f x2) = Eq) ->
    (forall x, nb_occ x c1 = nb_occ x c2) ->
    forall x, nb_occ x (map CB f c1) = nb_occ x (map CB f c2).
Proof.
intros A B OA CA OB CB f c1 c2 Fc1 Fc2 Hf H y.
unfold nb_occ in *.
destruct c1 as [s1 | b1]; try discriminate Fc1.
destruct c2 as [s2 | b2]; try discriminate Fc2.
unfold map, Febag.map, elements.
rewrite <- 2 Febag.nb_occ_elements, 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_3 OA).
- intros x1 x2 Hx; apply Hf.
  unfold mem, Febag.mem; apply Hx.
- intro x; apply (H x).
Qed.

Lemma nb_occ_map_eq :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) 
         (f : A -> B) (c1 c2 : collection CA), 
    (forall x1 x2, mem x1 c1 = true -> mem x2 c2 = true -> Oeset.compare OA x1 x2 = Eq ->
                   Oeset.compare OB (f x1) (f x2) = Eq) ->
    equal c1 c2 = true ->
    forall t, nb_occ t (map CB f c1) = nb_occ t (map CB f c2).
Proof.
intros A B OA CA OB CB f c1 c2 Hf Hc t.
rewrite equal_spec in Hc; destruct Hc as [H1 H2].
destruct c1 as [s1 | b1]; destruct c2 as [s2 | b2]; try discriminate H1.
- unfold map, nb_occ.
  unfold Feset.map, elements.
  assert (Aux := Feset.nb_occ_alt (CSet CB) t); unfold Feset.nb_occ in Aux.
  rewrite 2 Aux; clear Aux.
  assert (Aux : t inSE? Feset.mk_set (CSet CB) (List.map f (Feset.elements (CSet CA) s1)) =
                (t inSE? Feset.mk_set (CSet CB) (List.map f (Feset.elements (CSet CA) s2)))).
  {
    rewrite 2 Feset.mem_mk_set, eq_bool_iff, 2 Oeset.mem_bool_true_iff; split.
    - intros [t1 [Ht Ht1]].
      rewrite in_map_iff in Ht1.
      destruct Ht1 as [t2 [Ht1 Ht2]]; subst t1.
      assert (Ha2 := H2 t2); unfold nb_occ in Ha2; simpl in Ha2.
      assert (Aux := Feset.nb_occ_alt (CSet CA) t2); unfold Feset.nb_occ in Aux.
      rewrite 2 Aux in Ha2; clear Aux.
      rewrite (Feset.in_elements_mem _ _ _ Ht2) in Ha2.
      case_eq (t2 inSE? s2); intro Kt2; rewrite Kt2 in Ha2; try discriminate Ha2.
      rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Kt2.
      destruct Kt2 as [u2 [Kt2 Hu2]].
      exists (f u2); split.
      + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
        apply Hf; [ | | assumption].
        * apply in_elements_mem; apply Ht2.
        * apply in_elements_mem; apply Hu2.
      + rewrite in_map_iff; exists u2; split; trivial.
    - intros [t1 [Ht Ht1]].
      rewrite in_map_iff in Ht1.
      destruct Ht1 as [t2 [Ht1 Ht2]]; subst t1.
      assert (Ha2 := H2 t2); unfold nb_occ in Ha2; simpl in Ha2.
      assert (Aux := Feset.nb_occ_alt (CSet CA) t2); unfold Feset.nb_occ in Aux.
      rewrite 2 Aux in Ha2; clear Aux.
      rewrite (Feset.in_elements_mem _ _ _ Ht2) in Ha2.
      case_eq (t2 inSE? s1); intro Kt2; rewrite Kt2 in Ha2; try discriminate Ha2.
      rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Kt2.
      destruct Kt2 as [u2 [Kt2 Hu2]].
      exists (f u2); split.
      + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
        apply Hf; [ | | assumption].
        * rewrite (mem_eq_1 t2 u2); trivial.
          apply in_elements_mem; apply Hu2.
        * rewrite <- (mem_eq_1 t2 u2); trivial.
          apply in_elements_mem; apply Ht2.
      + rewrite in_map_iff; exists u2; split; trivial.
  }
  rewrite Aux; apply refl_equal.
- apply nb_occ_bag_map_eq; trivial.
Qed.

Lemma nb_occ_map_eq2 :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) 
         (f1 f2 : A -> B) (c : collection CA), 
    (forall x, mem x c = true -> Oeset.compare OB (f1 x) (f2 x) = Eq) ->
    forall t, nb_occ t (map CB f1 c) = nb_occ t (map CB f2 c).
Proof.
intros A B OA CA OB CB f1 f2 c H t.
unfold nb_occ, map, elements.
destruct c as [s | b].
- unfold Feset.map.
  assert (Aux := Feset.nb_occ_alt (CSet CB) t).
  unfold Feset.nb_occ in Aux; rewrite 2 Aux; clear Aux.
  assert (Aux : t inSE? Feset.mk_set (CSet CB) (List.map f1 (Feset.elements (CSet CA) s)) = 
                (t inSE? Feset.mk_set (CSet CB) (List.map f2 (Feset.elements (CSet CA) s)))).
  {
    rewrite eq_bool_iff, 2 Feset.mem_mk_set, 2 Oeset.mem_bool_true_iff; split.
    - intros [t1 [Ht Ht1]].
      rewrite in_map_iff in Ht1.
      destruct Ht1 as [x [Ht1 Hx]]; subst t1.
      exists (f2 x); split.
      + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
        apply (H x (Feset.in_elements_mem _ _ _ Hx)).
      + rewrite in_map_iff; exists x; split; trivial.
    - intros [t1 [Ht Ht1]].
      rewrite in_map_iff in Ht1.
      destruct Ht1 as [x [Ht1 Hx]]; subst t1.
      exists (f1 x); split.
      + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
        apply Oeset.compare_eq_sym.
        apply (H x (Feset.in_elements_mem _ _ _ Hx)).
      + rewrite in_map_iff; exists x; split; trivial.
  }
  rewrite Aux; apply refl_equal.
- unfold Febag.map.
  rewrite <- 2 Febag.nb_occ_elements, 2 Febag.nb_occ_mk_bag.
  apply permut_nb_occ; apply permut_refl_alt.
  assert (H' : forall x, In x (Febag.elements (CBag CA) b) -> Oeset.compare OB (f1 x) (f2 x) = Eq).
  {
    intros x Ha; apply H.
    apply Febag.in_elements_mem; assumption.
  }
  set (l := Febag.elements (CBag CA) b) in *; clearbody l.
  induction l as [ | x1 l]; simpl; trivial.
  rewrite H'; [ | left; apply refl_equal].
  apply IHl; intros; apply H'; right; assumption.
Qed.

Lemma nb_occ_filter_map :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB)  
    (c : collection CA) (g : A -> B) (f : B -> bool),
    (forall e e' : B, mem e (map CB g c) = true -> Oeset.compare OB e e' = Eq -> f e = f e') ->
    (forall x1 x2, mem x1 c = true -> mem x2 c = true -> Oeset.compare OA x1 x2 = Eq ->
                   Oeset.compare OB (g x1) (g x2) = Eq) ->
    forall t, nb_occ t (filter f (map CB g c)) = nb_occ t (map CB g (filter (fun x => f (g x)) c)).
Proof.
intros A B OA CA OB CB c g f H1 H2 t.
apply permut_nb_occ; apply permut_refl_alt.
unfold elements, filter, map; destruct c as [s | b]; 
[ apply Feset.elements_spec1; unfold Feset.map; rewrite Feset.equal_spec 
| apply Febag.elements_spec1; unfold Febag.map; rewrite Febag.nb_occ_equal].
- intro x; rewrite Feset.filter_spec, eq_bool_iff, 2 Feset.mem_mk_set, 
           Oeset.mem_bool_true_iff, Bool.andb_true_iff, Oeset.mem_bool_true_iff; [split | ].
  + intros [[x1 [Hx Hx1]] Hf].
    rewrite in_map_iff in Hx1; destruct Hx1 as [x2 [Hx1 Hx2]]; subst x1.
    assert (Kx2 : x2 inSE (Feset.filter (CSet CA) (fun y => f (g y)) s)).
    {
      rewrite Feset.filter_spec, Bool.andb_true_iff; [split | ].
      - apply Feset.in_elements_mem; assumption.
      - apply sym_eq; rewrite <- Hf; apply H1; [ | assumption].
        rewrite mem_map; exists x2; split; trivial.
      - intros y1 y2 Hy1 Hy; apply H1.
        + rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Hy1.
          destruct Hy1 as [z1 [Hy1 Hz1]].
          rewrite mem_map; exists z1; split; [ | assumption].
          apply Oeset.compare_eq_sym; apply H2.
          * apply in_elements_mem; assumption.
          * rewrite mem_elements, Oeset.mem_bool_true_iff.
            exists z1; split; trivial.
          * apply Oeset.compare_eq_sym; assumption.
        + apply H2; trivial.
          rewrite <- (mem_eq_1 _ _ _ Hy).
          rewrite mem_mem_set; apply Hy1.
    }
    rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Kx2.
    destruct Kx2 as [x3 [Kx2 Hx3]].
    exists (g x3); split.
    * refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
      {
        apply H2; trivial.
        - apply in_elements_mem; assumption.
        - rewrite mem_elements, Oeset.mem_bool_true_iff.
          exists x2; split; trivial.
          apply Oeset.compare_eq_sym; assumption.
      }
    * rewrite in_map_iff; exists x3; split; trivial.
  + intros [x1 [Hx Hx1]].
    rewrite in_map_iff in Hx1.
    destruct Hx1 as [x2 [Hx1 Hx2]]; subst x1.
    generalize (Feset.in_elements_mem _ _ _ Hx2); clear Hx2; intro Hx2.
    rewrite Feset.filter_spec, Bool.andb_true_iff in Hx2.
    * destruct Hx2 as [Hx2 Hf].
      rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Hx2.
      destruct Hx2 as [x3 [Hx2 Hx3]].
      {
        split; [exists (g x3); split | ].
        - refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
          apply H2; trivial.
          + rewrite mem_elements, Oeset.mem_bool_true_iff.
            exists x3; split; trivial.
          + apply in_elements_mem; assumption.
        - rewrite in_map_iff; exists x3; split; trivial.
        - rewrite <- Hf; apply H1; [ | assumption].
          rewrite mem_map.
          exists x3; split; [ | assumption].
          refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
          apply H2; trivial.
          + rewrite mem_elements, Oeset.mem_bool_true_iff.
            exists x3; split; trivial.
          + apply in_elements_mem; assumption.
      }
    * intros y1 y2 Hy Hy1.
      rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Hy.
      destruct Hy as [y3 [Hy Hx3]].
      {
        apply H1.
        - rewrite mem_map; exists y3; split; [ | assumption].
          apply H2; trivial.
          + unfold mem; rewrite Feset.mem_elements, Oeset.mem_bool_true_iff.
            exists y3; split; trivial.
          + apply in_elements_mem; assumption.
        - apply H2; trivial.
          + unfold mem; rewrite Feset.mem_elements, Oeset.mem_bool_true_iff.
            exists y3; split; trivial.
          + rewrite <- (mem_eq_1 _ _ _ Hy1), (mem_eq_1 _ _ _ Hy).
            apply in_elements_mem; assumption.
      }
  + intros y1 y2 Hy1; apply H1.
    rewrite Feset.mem_mk_set, Oeset.mem_bool_true_iff in Hy1.
    destruct Hy1 as [z1 [Hy1 Hz1]]; rewrite in_map_iff in Hz1.
    destruct Hz1 as [z2 [Hz1 Hz2]]; subst z1.
    rewrite mem_map; exists z2; split; trivial.
- intro x; rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_filter.
  + rewrite Febag.nb_occ_mk_bag.
    apply trans_eq with 
    (Oeset.nb_occ OB x
                  (List.map g (List.filter (fun x0 : A => f (g x0))
                                           (Febag.elements (CBag CA) b)))).
    * {
        rewrite <- filter_map, Oeset.nb_occ_filter.
        - case (f x).
          + rewrite N.mul_1_r; apply refl_equal.
          + rewrite N.mul_0_r; apply refl_equal.
        - intros y1 y2 Hy1 Hy; apply H1; [ | assumption].
          rewrite Oeset.mem_bool_true_iff in Hy1.
          destruct Hy1 as [z1 [Hy1 Hz1]]; rewrite in_map_iff in Hz1.
          destruct Hz1 as [z2 [Hz1 Hz2]]; subst z1.
          rewrite mem_map; exists z2; split; trivial.
      }
    * {
        apply (Oeset.nb_occ_map_eq_3 OA).
        - intros y1 y2 Hy1 Hy2.
          rewrite Oeset.mem_bool_true_iff in Hy1, Hy2.
          destruct Hy1 as [z1 [Hy1 Hz1]]; rewrite filter_In in Hz1.
          destruct Hz1 as [Hz1 Hz2].
          destruct Hy2 as [z2 [Hy2 _Hz2]].
          assert (__Hz2 := Febag.in_elements_mem _ _ _ _Hz2).
          rewrite Febag.mem_filter, Bool.andb_true_iff in __Hz2.
          + destruct __Hz2 as [__Hz1 __Hz2].
            apply H2.
            * rewrite (mem_eq_1 y1 z1 _ Hy1); apply in_elements_mem; assumption.
            * rewrite (mem_eq_1 y2 z2 _ Hy2), mem_mem_bag; apply __Hz1.
          + intros x1 x2 Hx1 Hx; apply H1.
            * simpl; rewrite Febag.mem_map.
              unfold Febag.mem in Hx1; rewrite Oeset.mem_bool_true_iff in Hx1.
              destruct Hx1 as [u1 [Hx1 Hu1]].
              exists u1; split; trivial.
              {
                apply H2.
                - rewrite (mem_eq_1 _ _ _ Hx1); apply in_elements_mem; apply Hu1.
                - apply in_elements_mem; assumption.
                - assumption.
              } 
            * {
                apply H2.
                - rewrite mem_mem_bag; apply Hx1.
                - rewrite <- (mem_eq_1 _ _ _ Hx); rewrite mem_mem_bag; apply Hx1.
                - assumption.
              } 
        - clear x; intro x.
          rewrite Oeset.nb_occ_filter.
          + rewrite <- 2 Febag.nb_occ_elements, Febag.nb_occ_filter.
            * case (f (g x)); [rewrite N.mul_1_r | rewrite N.mul_0_r]; apply refl_equal.
            * {
                intros y1 y2 Hy1 Hy.
                assert (Ky1 : y1 inBE b).
                {
                  rewrite Febag.mem_nb_occ.
                  destruct (Febag.nb_occ (CBag CA) y1 b); simpl; trivial.
                  apply False_rec; apply (Hy1 (refl_equal _)).
                }
                unfold Febag.mem in Ky1; rewrite Oeset.mem_bool_true_iff in Ky1.
                destruct Ky1 as [z1 [Ky1 Hz1]].
                apply H1.
                - rewrite mem_map.
                  exists z1; split; [ | assumption].
                  apply H2; trivial.
                  + rewrite (mem_eq_1 _ _ _ Ky1); apply in_elements_mem; assumption.
                  + apply in_elements_mem; assumption.
                - apply H2; trivial.
                  + rewrite (mem_eq_1 y1 z1 _ Ky1); apply in_elements_mem; assumption.
                  + rewrite <- (mem_eq_1 y1 _ _ Hy), (mem_eq_1 y1 z1 _ Ky1);
                    apply in_elements_mem; assumption.
              }
          + intros y1 y2 Hy1 Hy.
            rewrite Oeset.mem_bool_true_iff in Hy1.
            destruct Hy1 as [z1 [Hy1 Hz1]].
            apply H1.
            * rewrite mem_map.
              exists z1; split; [ | assumption].
              {
                apply H2; trivial.
                - rewrite (mem_eq_1 y1 z1 _ Hy1); apply in_elements_mem; assumption.
                - apply in_elements_mem; assumption.
              } 
            * {
                apply H2; trivial.
                - rewrite (mem_eq_1 y1 z1 _ Hy1); apply in_elements_mem; assumption.
                - rewrite <- (mem_eq_1 y1 _ _ Hy), (mem_eq_1 y1 z1 _ Hy1);
                    apply in_elements_mem; assumption.
              } 
      }
  + intros x1 x2 Hx1; apply H1.
    assert (Kx1 : x1 inBE (Febag.mk_bag (CBag CB) (List.map g (Febag.elements (CBag CA) b)))).
    {
      rewrite Febag.mem_nb_occ.
      destruct (Febag.nb_occ (CBag CB) x1
        (Febag.mk_bag (CBag CB) (List.map g (Febag.elements (CBag CA) b)))); simpl; trivial.
      apply False_rec; apply (Hx1 (refl_equal _)).
    }
    rewrite Febag.mem_mk_bag in Kx1; rewrite Oeset.mem_bool_true_iff in Kx1.
    destruct Kx1 as [y1 [Kx1 Hy1]].
    rewrite in_map_iff in Hy1.
    destruct Hy1 as [z1 [Hy1 Hz1]]; subst y1.    
    rewrite mem_map; exists z1; split; trivial.
Qed.
  
Lemma nb_occ_map_map :
  forall (A B C : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB)  
         (OC : Oeset.Rcd C) (CC : Rcd OC) (f1 : A -> B) (f2 : B -> C) (c : collection CA),
    (forall x1 x2, mem x1 (map CB f1 c) = true -> mem x2 (map CB f1 c) = true -> 
                   Oeset.compare OB x1 x2 = Eq ->
                   Oeset.compare OC (f2 x1) (f2 x2) = Eq) ->
    forall t, nb_occ t (map CC f2 (map CB f1 c)) = nb_occ t (map CC (fun x => f2 (f1 x)) c).
Proof.  
intros A B C OA CA OB CB OC CC f1 f2 c Hf t.
apply permut_nb_occ; apply permut_refl_alt.
unfold elements, map; destruct c as [s | b]; 
[ apply Feset.elements_spec1; unfold Feset.map; rewrite Feset.equal_spec 
| apply Febag.elements_spec1; unfold Febag.map; rewrite Febag.nb_occ_equal].
- intro x; rewrite eq_bool_iff, 2 Feset.mem_mk_set, 2 Oeset.mem_bool_true_iff; split.
  + intros [x1 [Hx Hx1]].
    rewrite in_map_iff in Hx1; destruct Hx1 as [x2 [Hx1 Hx2]]; subst x1.
    assert (Kx2 := Feset.in_elements_mem _ _ _ Hx2).
    rewrite Feset.mem_mk_set, Oeset.mem_bool_true_iff in Kx2.
    destruct Kx2 as [x3 [Kx2 Hx3]].
    rewrite in_map_iff in Hx3.
    destruct Hx3 as [x4 [Hx3 Hx4]]; subst x3.
    exists (f2 (f1 x4)); split.
    * refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
      {
        apply Hf; trivial.
        - rewrite (mem_eq_1 x2 (f1 x4)); [ | assumption].
          rewrite mem_map.
          exists x4; split; [apply Oeset.compare_eq_refl | assumption].
        - rewrite mem_map.
          exists x4; split; [apply Oeset.compare_eq_refl | assumption].
      }
    * rewrite in_map_iff; exists x4; split; trivial.
  + intros [x1 [Hx Hx1]].
    rewrite in_map_iff in Hx1.
    destruct Hx1 as [x2 [Hx1 Hx2]]; subst x1.
    assert (Hf1 : (f1 x2) inSE 
                          (Feset.mk_set (CSet CB) (List.map f1 (Feset.elements (CSet CA) s)))).
    {
      rewrite Feset.mem_mk_set, Oeset.mem_bool_true_iff.
      exists (f1 x2); split; [apply Oeset.compare_eq_refl | ].
      rewrite in_map_iff; exists x2; split; trivial.
    }
    rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Hf1.
    destruct Hf1 as [x3 [Hf1 Hx3]].
    exists (f2 x3); split.
    * refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
      {
        apply Hf; trivial.
        - rewrite mem_map.
          exists x2; split; [apply Oeset.compare_eq_refl | assumption].
        - apply in_elements_mem.
          apply Hx3.
      } 
    * rewrite in_map_iff; exists x3; split; trivial.
- intro x; rewrite 2 Febag.nb_occ_mk_bag.
  rewrite <- (map_map f1 f2).
  apply (Oeset.nb_occ_map_eq_3 OB).
  + intros x1 x2 Hx1 Hx; apply Hf; trivial.
    rewrite Oeset.mem_bool_true_iff in Hx.
    destruct Hx as [x3 [Hx Hx3]].
    rewrite in_map_iff in Hx3.
    destruct Hx3 as [_x [Hx3 _Hx]]; subst x3.
    rewrite mem_map; exists _x; split; trivial.
  + clear x; intro x.
    rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag.
    apply refl_equal.
Qed.

Lemma nb_occ_map_inj :
  forall (A B : Type) (OA : Oeset.Rcd A) (CA : Rcd OA) (OB : Oeset.Rcd B) (CB : Rcd OB) 
         (f : A -> B) (c : collection CA),
    (forall x1 x2, mem x1 c = true -> 
                   (Oeset.compare OB (f x1) (f x2) = Eq <-> Oeset.compare OA x1 x2 = Eq)) ->
    forall x, nb_occ (f x) (map CB f c) = nb_occ x c.
Proof.
intros A B OA CA OB CB f c H x.
destruct c as [s | b]; rewrite 2 nb_occ_unfold; simpl.
- case_eq (f x inSE? Feset.map (CSet CA) (CSet CB) f s); intro Hfx;
  case_eq (x inSE? s); intro Hx; trivial.
  + rewrite Feset.mem_map in Hfx.
    destruct Hfx as [y [Hfx Hy]]; rewrite Oeset.compare_lt_gt, CompOpp_iff in Hfx.
    assert (Ky := Feset.in_elements_mem _ _ _ Hy).
    assert (H1 := proj1 (H _ _ Ky) Hfx).
    rewrite (Feset.mem_eq_1 _ _ _ _ H1), Hx in Ky. 
    discriminate.
  + rewrite <- not_true_iff_false in Hfx.
    apply False_rec; apply Hfx.
    rewrite Feset.mem_map.
    rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Hx.
    destruct Hx as [y [Hx Hy]].
    exists y; split; [ | assumption].
    rewrite H; [assumption | ].
    simpl; rewrite Feset.mem_elements, Oeset.mem_bool_true_iff.
    exists y; split; assumption.
- unfold Febag.map; rewrite Febag.nb_occ_mk_bag.
  rewrite Febag.nb_occ_elements.
  assert (H' : forall x1 x2, 
                 Oeset.mem_bool OA x1 (Febag.elements (CBag CA) b) = true ->
                 (Oeset.compare OB (f x1) (f x2) = Eq <-> Oeset.compare OA x1 x2 = Eq)).
  {
    intros x1 x2 Hx; apply H.
    simpl; unfold Febag.mem; apply Hx.
  }
  set (l := Febag.elements (CBag CA) b) in *; clearbody l.
  induction l as [ | x1 l]; [apply refl_equal | ].
  rewrite ListFacts.map_unfold, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)).
  rewrite IHl.
  + apply f_equal2; [ | apply refl_equal].
    rewrite (Oeset.compare_lt_gt OA), (Oeset.compare_lt_gt OB).
    case_eq (Oeset.compare OA x1 x); intro Hx.
    * rewrite <- H' in Hx; [rewrite Hx; apply refl_equal | ].
      simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
    * case_eq (Oeset.compare OB (f x1) (f x)); intro Hfx; trivial.
      rewrite H', Hx in Hfx; [discriminate Hfx | ].
      simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
    * case_eq (Oeset.compare OB (f x1) (f x)); intro Hfx; trivial.
      rewrite H', Hx in Hfx; [discriminate Hfx | ].
      simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; apply refl_equal.
  + intros y1 y2 Hy; apply H'.
    simpl; rewrite Hy, Bool.orb_true_r; apply refl_equal.
Qed.

End Fecol.

Notation "a 'inCE' s" := (Fecol.mem a s = true) (at level 70, no associativity).
Notation "a 'inCE?' s" := (Fecol.mem a s) (at level 70, no associativity).
Notation "s1 '=CE=' s2" := (Fecol.equal s1 s2 = true) (at level 70, no associativity).
Notation "s1 '=CE?=' s2" := (Fecol.equal s1 s2) (at level 70, no associativity).
Notation "s1 'unionCE' f s2" := (Fecol.union f s1 s2) (at level 70, no associativity).
Notation "s1 'interCE' f s2" := (Fecol.inter f s1 s2) (at level 70, no associativity).
Notation "'emptyCE' f" := (Fecol.empty _ f) (at level 70, no associativity).
Notation "a 'addCE' s" := (Fecol.add a s) (at level 70, no associativity).

