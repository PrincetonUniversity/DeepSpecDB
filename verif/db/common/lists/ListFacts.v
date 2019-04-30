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

(** * Some additional properties for the Coq lists. *)

Set Implicit Arguments.

Require Import List Arith.
Require Import NArith.

(** ** Unfolding the usual definitions of lists' functions; 
      sometimes [simpl] simplifies too much. *)

Lemma app_unfold :
  forall (A : Type) (l1 l2 : list A),
    l1 ++ l2 = match l1 with
                 | nil => l2
                 | a1 :: l1 => a1 :: (l1 ++ l2)
               end.
Proof.
intros A l1 l2; case l1; intros; apply refl_equal.
Qed.

Lemma length_unfold :
  forall (A : Type) (l : list A),
    length l = match l with
                 | nil => 0
                 | _ :: l => S (length l)
               end.
Proof.
intros A l; case l; intros; apply refl_equal.
Qed.

Lemma map_unfold :  
 forall (A B : Type) (f : A -> B) l, 
   map f l = match l with 
               | nil => nil
               | a :: l => f a :: map f l
             end.
Proof.
intros A B f l; case l; intros; apply refl_equal.
Qed.

Lemma map_if :
  forall (A B : Type) (f' : A -> bool) (f : A -> B) a l,
    map f (if f' a then a :: l else l) = if f' a then map f (a :: l) else map f l.
Proof.
intros A B f' f a l; case (f' a); apply refl_equal.
Qed.

Lemma flat_map_unfold :
  forall (A B : Type) (f : A -> list B) a l, flat_map f (a :: l) = f a ++ flat_map f l.
Proof.
intros A B f a l; apply refl_equal.
Qed.

Lemma flat_map_if :
  forall (A B C : Type) (f' : C -> bool) (f : A -> list B) g c l,
    flat_map f (if f' c then g c :: l else l) = if f' c then flat_map f (g c :: l) else flat_map f l.
Proof.
intros A B C f' f g c l; case (f' c); apply refl_equal.
Qed.

Lemma flat_map_if_alt :
  forall (A B C : Type) (f' : C -> bool) (f : A -> list B) g c l,
    flat_map f (if f' c then g c :: l else l) = 
    (if f' c then f (g c) else nil) ++ flat_map f l.
Proof.
intros A B C f' f g c l; case (f' c); apply refl_equal.
Qed.

Lemma flat_map_app :
  forall (A B : Type) (f : A -> list B) l1 l2, 
    flat_map f (l1 ++ l2) = (flat_map f l1) ++ (flat_map f l2).
Proof.
intros A B f l1; induction l1 as [ | a1 l1]; intro l2; [apply refl_equal | simpl].
rewrite <- ass_app; apply f_equal; apply IHl1.
Qed.

Lemma flat_map_nil :
  forall (A B : Type) (f : A -> list B) l,
    (forall a, In a l -> f a = nil) -> flat_map f l = nil.
Proof.
intros A B f l; induction l as [ | a1 l]; intros Hl; [apply refl_equal | ].
simpl; rewrite (Hl a1 (or_introl _ (refl_equal _))), IHl; trivial.
do 2 intro; apply Hl; right; assumption.
Qed.

Lemma flat_map_rev : 
  forall (A B : Type) (f : A -> list B) l,
    rev (flat_map f l) = flat_map (fun a => rev (f a)) (rev l).
Proof.
  intros A B f l. induction l; [trivial | ].
  simpl; rewrite flat_map_app; simpl; rewrite <- app_nil_end.
  rewrite rev_app_distr, IHl; reflexivity.
Qed.

Lemma fold_right_unfold :
  forall (A B : Type) (f : B -> A -> A) l a,
    fold_right f a l = match l with
                         | nil => a
                         | b1 :: l => f b1 (fold_right f a l)
                       end.
Proof.
  intros A B f l a; case l; intros; apply refl_equal.
Qed.

Lemma fold_left_unfold :
  forall (A B : Type) (f : A -> B -> A) l a,
    fold_left f l a = match l with
                        | nil => a
                        | b1 :: l => fold_left f l (f a b1)
                      end.
Proof.
intros A B f l a; case l; intros; apply refl_equal.
Qed.

Lemma filter_unfold :
  forall (A : Type) (f : A -> bool) l,
    filter f l = match l with
                   | nil => nil
                   | a :: l => if (f a) then (a :: filter f l) else filter f l
                 end.
Proof.
intros A f l; case l; intros; simpl; apply refl_equal.
Qed.

Lemma filter_if :
  forall (A C : Type) (f' : C -> bool) (f : A -> bool) g c l,
    filter f (if f' c then g c :: l else l) = if f' c then filter f (g c :: l) else filter f l.
Proof.
intros A C f' f g c l; case (f' c); apply refl_equal.
Qed.

(** ** Compatibility properties, when the functions do coincide point wise over their list argument. *)

Section Sec.

Hypotheses A B : Type.

Section Compat.

Lemma forallb_unfold : 
  forall (f : A -> bool) l, 
    forallb f l = match l with nil => true | a1 :: l => andb (f a1) (forallb f l) end.
Proof.
intros f l; destruct l; apply refl_equal.
Qed.

Lemma forallb_eq : 
  forall (f1 f2 : A -> bool) l,
    (forall x, In x l -> f1 x = f2 x) -> forallb f1 l = forallb f2 l.
Proof.
fix h 3.
intros f1 f2 l; case l; clear l.
- intros _; apply refl_equal.
- intros x1 l H; simpl.
  rewrite (H x1 (or_introl _ (refl_equal _))).
  apply f_equal.
  simpl in H.
  auto.
Qed.

Lemma forallb_eq_alt : 
  forall (f1 f2 : A -> bool) l1 l2,
    l1 = l2 -> (forall x, In x l1 -> f1 x = f2 x) -> forallb f1 l1 = forallb f2 l2.
Proof.
intros f1 f2 l1 l2 H; subst l2; apply forallb_eq.
Qed.

Lemma forallb_map :
  forall (f : A -> bool) (g : B -> A) (l : list B), 
    forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
intros f g l; induction l as [ | b l]; simpl; trivial. 
apply f_equal; apply IHl.
Qed.

Lemma existsb_eq : 
  forall (f1 f2 : A -> bool) l,
    (forall x, In x l -> f1 x = f2 x) -> existsb f1 l = existsb f2 l.
Proof.
fix h 3.
intros f1 f2 l; case l; clear l.
- intros _; apply refl_equal.
- intros x1 l H; simpl.
  rewrite (H x1 (or_introl _ (refl_equal _))).
  apply f_equal.
  apply h.
  intros; apply H; right; assumption.
Qed.

Lemma map_eq : 
  forall (f g : A -> B) l, (forall a, In a l -> f a = g a) <-> map f l = map g l. 
Proof.
intros f g.
fix h 1.
intro l; case l; clear l.
- (* 1/2 *)
  split; 
  [exact (fun _ => refl_equal nil) 
  | intros _ a a_in_nil; contradiction a_in_nil].
- (* 1/1 *)
  split.
  + (* 1/2 *)
    intros H; rewrite (map_unfold f), (map_unfold g).
    apply f_equal2.
    * apply (H a (or_introl _ (refl_equal _))).
    * rewrite <-  h. simpl in H. auto.
  + (* 1/1 *)
    rewrite (map_unfold f), (map_unfold g).
    intro H; injection H; intros Hl Ha.
    intros x Hx; simpl in Hx; inversion Hx as [Ka | Kl].
    * rewrite <- Ka; exact Ha.
    * revert Kl. rewrite <- h in Hl. auto.
Qed.

Lemma map_eq_alt :
  forall (f g : A -> B) l1 l2, l1 = l2 ->
     ((forall a, In a l1 -> f a = g a) <-> map f l1 = map g l2). 
Proof.
intros f g l1 l2 H.
subst l2; apply map_eq.
Qed.

Lemma flat_map_eq : 
  forall (f g : A -> list B) l, (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l. 
Proof.
intros f g.
fix h 1.
intro l; case l; clear l.
- (* 1/2 *)
  exact (fun _ => refl_equal nil).
- (* 1/1 *)
  intros a l H; rewrite (flat_map_unfold f), (flat_map_unfold g).
  apply f_equal2.
  + apply (H a (or_introl _ (refl_equal _))).
  + apply h. simpl in H. auto.
Qed.

Lemma fold_left_eq :
  forall (f1 f2 : A -> B -> A) l a1 a2,
    a1 = a2 -> (forall a b, List.In b l -> f1 a b = f2 a b) ->
    fold_left f1 l a1 = fold_left f2 l a2.
Proof.
intros f1 f2.
fix h 1.
intros l a1 a2 H; case l; clear l.
- intros _; apply H.
- intros b1 l Hf; rewrite 2 (fold_left_unfold _ (_ :: _)).
  apply h.
  + rewrite H; apply Hf; left; apply refl_equal.
  + do 3 intro; apply Hf; right; assumption.
Qed.

Lemma partition_eq :
  forall (f g : A -> bool) l, (forall a, In a l -> f a = g a) -> partition f l = partition g l.
Proof.
intros f g.
fix h 1.
intro l; case l; clear l.
- (* 1/2 *)
  exact (fun _ => refl_equal _).
- (* 1/1 *)
  intros a l H; simpl.
  rewrite h ; [ | intros; apply H; right; trivial].
  destruct (partition g l) as [l1 l2].
  rewrite H; [ | left]; apply refl_equal.
Qed.

End Compat.

Section Morphism.

Lemma map_id :
  forall (f : A -> A) l, (forall a, In a l -> f a = a) -> map f l = l.
Proof.
fix h 2.
intros f l; case l; clear l.
- intros _; apply refl_equal.
- intros a l H.
  rewrite (map_unfold f).
  apply f_equal2. 
  + apply H; left; apply refl_equal.
  + apply h.
    intros a1 Ha1; apply H; right; assumption.
Qed.

Lemma filter_eq :
  forall (f1 f2 : A -> bool) l, (forall x, In x l -> f1 x = f2 x) -> filter f1 l = filter f2 l.
Proof.
intros f1 f2 l; induction l as [ | a1 l]; intro H; [apply refl_equal | ].
simpl; rewrite (H a1 (or_introl _ (refl_equal _))).
rewrite (IHl (fun x h => H x (or_intror _ h))).
apply refl_equal.
Qed.

Lemma filter_true :
  forall (f : A -> bool) l, 
    (forall x, List.In x l -> f x = true) -> filter f l = l.
Proof.
intros f l; induction l as [ | a1 l];
intros Hl; [apply refl_equal | ].
simpl; rewrite (Hl a1 (or_introl _ (refl_equal _))), IHl.  
- apply refl_equal.
- intros; apply Hl; right; assumption.
Qed.

Lemma filter_false :
  forall (f : A -> bool) l, 
    (forall x, List.In x l -> f x = false) -> filter f l = nil.
Proof.
intros f l; induction l as [ | a1 l];
intros Hl; [apply refl_equal | ].
simpl; rewrite (Hl a1 (or_introl _ (refl_equal _))), IHl.  
- apply refl_equal.
- intros; apply Hl; right; assumption.
Qed.

Lemma filter_app :
  forall (f : A -> bool) l1 l2, filter f (l1 ++ l2) = (filter f l1) ++ (filter f l2).
Proof.
intros f l1; induction l1 as [ | a1 l1]; intro l2; simpl.
- apply refl_equal.
- rewrite IHl1.
  case (f a1); apply refl_equal.
Qed.

Lemma filter_filter :
  forall (f1 f2 : A -> bool) l, filter f1 (filter f2 l) = filter (fun x => andb (f1 x) (f2 x)) l.
Proof.
intros f1 f2 l; induction l as [ | a1 l]; [apply refl_equal | simpl].
destruct (f2 a1); simpl; destruct (f1 a1); simpl; rewrite <- IHl; trivial.
Qed.

Lemma filter_map :
  forall (f : B -> bool) (g : A -> B) l, 
    filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof.
intros f g l; induction l as [ | a1 l]; [apply refl_equal | ].
simpl.
case (f (g a1)); simpl.
- apply f_equal; apply IHl.
- apply IHl.
Qed.

Lemma filter_rev :
  forall (f : A -> bool) l, filter f (rev l) = rev (filter f l).
Proof.
intros f l; induction l as [ | a1 l]; [apply refl_equal | ].
simpl; rewrite filter_app; simpl.
case (f a1).
- simpl; rewrite IHl; apply refl_equal.
- rewrite <- app_nil_end, IHl; apply refl_equal.
Qed.

End Morphism.


(** ** How to belong to a list. *)
Section In.

Lemma in_app :
  forall (l1 l2 : list A) a b,
    In a (l1 ++ l2) -> In a (l1 ++ b :: l2).
Proof.
fix h 1.
intros l1 l2 a b; case l1; clear l1.
- intro H; right; assumption.
- intros a1 l1; simpl app.
  intro H; simpl in H; destruct H as [H | H].
  + left; assumption.
  + right; apply h.
    assumption.
Qed.

Lemma in_app_iff :
  forall (l1 l2 : list A) a b,
    In a (l1 ++ b :: l2) <-> (a = b \/ In a (l1 ++ l2)).
Proof.
fix h 1.
intros l1 l2 a b; case l1; clear l1.
- rewrite 2 (app_unfold nil); simpl; split; intros [H | H].
  + left; apply sym_eq; assumption.
  + right; assumption.
  + left; apply sym_eq; assumption.
  + right; assumption.
- intros a1 l1; rewrite 2 (app_unfold (_ :: _)); simpl; split.
  + intros [H | H].
    * right; left; assumption.
    * rewrite in_app_iff in H. simpl in H.
      rewrite in_app_iff.
      destruct H as [H1 | [H2 | H3]]; auto.
  + intros [H | [H | H]].
    * subst b; right; apply in_or_app; right; left; apply refl_equal.
    * left; assumption.
    * right; apply in_app; assumption.
Qed.

Lemma in_fold_left :
  forall (fb : A -> bool) (ff : A -> A) t l1 l0, 
    In t (fold_left (fun acc t1 => if fb t1 then ff t1 :: acc else acc) l1 l0) <->
    (In t l0 \/ (exists t1, In t1 l1 /\ fb t1 = true /\ t = ff t1)).
Proof.
fix h 4.
intros fb ff t l1 l0.
case l1; clear l1.
- simpl; split.
  + intro H; left; apply H.
  + intros [H | [_ [H _]]]; [apply H | contradiction H].
- intros a1 l1; simpl.
  rewrite h; split; intros [H | H].
  + case_eq (fb a1); intro Ha1; rewrite Ha1 in H.
    simpl in H; destruct H as [H | H].
    * subst t.
      right; exists a1; split; [ | split; trivial].
      left; apply refl_equal.
    * left; assumption.
    * left; assumption.
  + destruct H as [t1 [Ht1 [Kt1 H]]].
    subst t.
    right; exists t1; split; [ | split; trivial].
    right; assumption.
  + left; case (fb a1).
    * right; assumption.
    * assumption.
  + destruct H as [t1 [[Ht1 | Ht1] [Kt1 H]]].
    * subst t; subst a1; rewrite Kt1.
      left; left; apply refl_equal.
    * subst t.
      right; exists t1; split; [ | split]; trivial.
Qed.

Lemma in_fold_left_app :
 forall l1 l2 a,
   In a (fold_left (app (A:= A * B)) l1 l2) <-> ((exists l, In l l1 /\ In a l) \/ In a l2).
Proof.
intros l1; induction l1 as [ | l l1]; intros l2 a; simpl.
- split; intro H.
  + right; apply H.
  + destruct H as [H | H].
    * destruct H as [l [Abs _]]; contradiction Abs.
    * assumption.
- rewrite IHl1; split; intros [H | H].
  + destruct H as [k [Hl Ha]].
    left; exists k; split.
    * right; assumption.
    * assumption.
  + destruct (in_app_or _ _ _ H) as [Ha | Ha].
    * right; assumption.
    * left; exists l; split; [left; apply refl_equal | assumption].
  + destruct H as [k [[H | H] Ha]]. 
    * subst l; right; apply in_or_app.
      right; assumption.
    * left; exists k; split; assumption.
  + right; apply in_or_app; left; assumption.
Qed.

Lemma in_fold_left2 :
  forall (fb : A -> A -> bool) (ff : A -> A -> A) t l1 l2 l0, 
    In t (fold_left
            (fun acc t1 =>
                  fold_left
                    (fun acc0 t2 =>
                       if fb t1 t2 then ff t1 t2 :: acc0 else acc0) l2 acc)
            l1 l0) <->
    (In t l0 \/ 
     (exists t1 t2, In t1 l1 /\ In t2 l2 /\ fb t1 t2 = true /\ t = ff t1 t2)).
Proof.
fix h 4.
intros fb ff t l1 l2 l0.
case l1; clear l1.
- simpl; split.
  + intro H; left; apply H.
  + intros [H | [_ [_ [H _]]]]; [apply H | contradiction H].
- intros a1 l1; simpl.
  rewrite h; split.
  + intros [H | H].
    * rewrite in_fold_left in H.
      destruct H as [H | H]; [left; assumption | ].
      destruct H as [t1 [Ht1 [Kt1 H]]].
      subst t; right.
      exists a1; exists t1; intuition.
    * destruct H as [t1 [t2 [Ht1 [Ht2 [H K]]]]].
      subst t; right.
      exists t1; exists t2; intuition.
  + rewrite in_fold_left; intros [H | H].
    * do 2 left; assumption.
    * {
        destruct H as [t1 [t2 [[Ht1 | Ht1] [Ht2 [H K]]]]].
        - subst t; subst a1.
          left; right.
          exists t2; intuition.
        - subst t; right; exists t1; exists t2; intuition.
      }
Qed.

Lemma nth_error_some_in :
  forall n (l : list A) a, nth_error l n = Some a -> In a l.
Proof.
intros n l; revert n.
induction l as [ | a1 l]; intros n a H.
- destruct n; discriminate H.
- destruct n as [ | n]; simpl in H.
  + injection H; clear H; intro H.
    left; apply H.
  + right; revert H; apply IHl.
Qed.

Lemma in_nth_error :
  forall (l : list A) a, In a l -> exists n, (n < length l /\ nth_error l n = Some a).
Proof.
intros l; induction l as [ | a1 l];
intros a Ha; [contradiction Ha | ].
simpl in Ha; destruct Ha as [Ha | Ha].
- subst a1.
  exists 0; simpl; split; [ | apply refl_equal].
  apply le_n_S; apply le_O_n.
- destruct (IHl _ Ha) as [n [Hn Kn]].
  exists (S n); simpl; split; [ | assumption].
  apply le_n_S; apply Hn.
Qed.

End In.

(** ** Pairwise distinct elements in a list *)
Section AllDiff.

Fixpoint all_diff (l : list A) :=
  match l with
	| nil | _ :: nil => True
	| a1 :: l => (forall a, In a l -> a1 <> a) /\ all_diff l
  end.

Lemma all_diff_unfold : 
  forall l, 
  all_diff l <-> match l with
	           | nil => True
	           | a1 :: l => (forall a, In a l -> a1 <> a) /\ all_diff l
  end.
Proof.
intro l; case l; clear l.
exact (conj (fun h => h) (fun h => h)).
intros a1 l.
case l; clear l; simpl.
split; [ | exact (fun _ => I)].
intros _; split; [intros a Abs; inversion Abs | exact I].
intros a2 l; exact (conj (fun h => h) (fun h => h)).
Qed.

Lemma all_diff_tl :
  forall a l, all_diff (a :: l) -> all_diff l.
Proof.
intros a l H; rewrite all_diff_unfold in H.
apply (proj2 H).
Qed.

Lemma all_diff_app1 :
  forall l1 l2, all_diff (l1 ++ l2) -> all_diff l1.
Proof.
fix h 1.
intro l1; case l1; clear l1.
- intros _ _; simpl; trivial.
- intros a1 l1 l2 H.
  simpl app in H; rewrite all_diff_unfold in H.
  rewrite all_diff_unfold; split.
  + intros a Ha; apply (proj1 H).
    apply in_or_app; left; assumption.
  + apply (h l1 l2); apply (proj2 H).
Qed.

Lemma all_diff_app2 :
  forall l1 l2, all_diff (l1 ++ l2) -> all_diff l2.
Proof.
fix h 1.
intro l1; case l1; clear l1.
- exact (fun _ h => h).
- intros a1 l1 l2 H.
  apply (h l1 l2).
  simpl app in H; rewrite all_diff_unfold in H.
  apply (proj2 H).
Qed.

Lemma all_diff_app :
  forall l1 l2, all_diff (l1 ++ l2) -> forall a, In a l1 -> In a l2 -> False.
Proof.
fix h 1.
intros l1; case l1; clear l1; [ | intros x1 l1]; intros l2 H a H1 H2.
- contradiction H1.
- simpl app in H; rewrite all_diff_unfold in H.
  simpl in H1; destruct H1 as [H1 | H1].
  + subst x1.
    apply (proj1 H a); [ | trivial].
    apply in_or_app; right; assumption.
  + apply (h _ _ (proj2 H) _ H1 H2).
Qed.

Lemma all_diff_app_iff :
  forall l1 l2, (all_diff l1 /\ all_diff l2 /\
                 (forall a, In a l1 -> In a l2 -> False)) <-> all_diff (l1 ++ l2).
Proof.
intros l1 l2; split.
- intros [H1 [H2 H]]; revert l2 H1 H2 H; 
  induction l1 as [ | a1 l1]; 
  intros l2 H1 H2 H; [apply H2 | ].
  simpl app; rewrite all_diff_unfold; split.
  + intros a Ha.
    destruct (in_app_or _ _ _ Ha) as [Ka | Ka].
    * rewrite all_diff_unfold in H1.
      apply (proj1 H1 _ Ka).
    * intro Ja; subst a.
      apply (H a1); [ | assumption].
      left; apply refl_equal.
  + apply IHl1.
    * rewrite all_diff_unfold in H1.
      apply (proj2 H1).
    * assumption.
    * intros a Ha Ka; apply (H a); [ | assumption].
      right; assumption.
- intro H; repeat split.
  + apply (all_diff_app1 _ _ H).
  + apply (all_diff_app2 _ _ H).
  + apply (all_diff_app _ _ H).
Qed.

Lemma all_diff_equiv : 
  forall (a1 a2 : A) l1 l2 l3, all_diff (l1 ++ a1 :: l2 ++ a2 :: l3) -> a1 = a2 -> False.
Proof.
intros a b l1 l2 l3 H K; subst b; revert l1 a l2 l3 H.
fix h 1.
intro l1; case l1; clear l1.
(* 1/2 *)
intros a l2 l3.
simpl app; rewrite all_diff_unfold; intros [H _]; apply (H a); [ | apply refl_equal].
apply in_or_app; right; left; apply refl_equal.
(* 1/1 *)
intros a1 l1 a l2 l3.
simpl app; rewrite all_diff_unfold; intros [_ H].
apply (h l1 a l2 l3 H).
Qed.

Lemma all_diff_equiv2 :
  forall l, (forall l1 l2 l3 a1 a2, l = l1 ++ a1 :: l2 ++ a2 :: l3 -> a1 = a2 -> False) ->
            all_diff l.
Proof.
intro l; induction l as [ | a l]; intro H; simpl; [trivial | ].
case_eq l; [trivial | ].
intros a2 k Hl; rewrite <- Hl; clear a2 k Hl.
split.
- intros b Hb.
  destruct (in_split _ _ Hb) as [l1 [l2 K]]; subst l.
  intro Kb.
  apply (H nil l1 l2 a b (refl_equal _) Kb).
- apply IHl.
  intros l1 l2 l3 a1 a2 K J.
  apply (H (a :: l1) l2 l3 a1 a2); [ | assumption].
  simpl; rewrite K; apply refl_equal.
Qed.

Lemma all_diff_fst :
  forall (l : list (A * B)), 
    all_diff (map (@fst _ _) l) -> 
    forall a b1 b2, In (a, b1) l -> In (a, b2) l -> b1 = b2.
Proof.
intros l Hl a b1 b2 H1 H2.
destruct (in_split _ _ H1) as [l1 [l2 K1]].
rewrite K1 in H2.
destruct (in_app_or _ _ _ H2) as [K2 | K2].
- destruct (in_split _ _ K2) as [k1 [k2 K3]].
  apply False_rec.
  rewrite K1, K3, 2 map_app, (map_unfold _ (_ :: _)), <- app_assoc in Hl.
  apply (all_diff_equiv _ _ _ Hl); trivial.
- simpl in K2; destruct K2 as [K2 | K2]; [injection K2; trivial | ].
  destruct (in_split _ _ K2) as [k1 [k2 K3]].
  apply False_rec.
  rewrite K1, K3, map_app, (map_unfold _ (_ :: _)), map_app, (map_unfold _ (_ :: _)) in Hl.
  apply (all_diff_equiv _ _ _ Hl); trivial.
Qed.

Lemma all_diff_rev :
  forall l, all_diff l -> all_diff (rev l).
Proof.
intro l; induction l as [ | a1 l]; intro H; [trivial | ].
simpl; rewrite <- all_diff_app_iff.
rewrite all_diff_unfold in H; destruct H as [H1 H2].
split; [apply IHl; apply H2 | ].
split; [simpl; trivial | ].
intros a Ha Ka; simpl in Ka; destruct Ka as [Ka | Ka]; [ | contradiction Ka].
subst a1.
apply (H1 a); [ | apply refl_equal].
rewrite In_rev; assumption.
Qed.

End AllDiff.

Section Mapi.

Fixpoint mapi_rec (f : nat -> A -> B) i l :=
  match l with
    | nil => nil
    | a1 :: l => (f i a1) :: (mapi_rec f (i+1) l)
end.



Fixpoint mapI_rec (f : N -> A -> B) i l :=
  match l with
    | nil => nil
    | a1 :: l => (f i a1) :: (mapI_rec f (i+1)%N l)
end.

Lemma mapI_rec_unfold :
  forall f i l, mapI_rec f i l =
                match l with
                  | nil => nil
                  | a1 :: l => (f i a1) :: (mapI_rec f (i+1)%N l)
                end.
Proof.
intros f i l; case l; intros; apply refl_equal.
Qed.

Lemma in_mapI_rec_iff :
  forall (f : N -> A -> B) i l x,
    In x (mapI_rec f i l) <-> 
    (exists n, exists an, 
                 0 <= n < length l /\ nth_error l n = Some an /\ x = (f (i+ (N_of_nat n))%N an)).
Proof.
intros f i l; revert i.
induction l as [ | a1 l]; intros i x; split.
- intro Abs; contradiction Abs.
- intros [n [an [H1 [H2 H3]]]].
  destruct n; discriminate H2.
- intro H; simpl in H.
  destruct H as [H | H].
  + exists 0; exists a1; repeat split.
    * apply le_n.
    * simpl; apply le_n_S; apply le_O_n.
    * simpl; rewrite N.add_0_r.
      apply sym_eq; apply H.
  + rewrite IHl in H.
    destruct H as [n [an [H1 [H2 H3]]]].
    exists (1 + n); exists an; repeat split.
    * apply le_O_n.
    * simpl; apply le_n_S; apply (proj2 H1).
    * simpl; rewrite H2.
      apply refl_equal.
    * rewrite H3.
      apply f_equal2; [ | apply refl_equal].
      rewrite <- N.add_assoc.
      apply f_equal.
      rewrite Nat2N.inj_add.
      apply refl_equal.
-  intros [n [an [H1 [H2 H3]]]].
   destruct n as [ | n].
   + simpl in H2; injection H2; clear H2; intro H2; subst an.
     simpl; left.
     rewrite H3.
     apply f_equal2; [ | apply refl_equal].
     rewrite N.add_comm; simpl.
     apply refl_equal.
   + simpl in H2.
     simpl; right.
     rewrite IHl.
     exists n; exists an; repeat split.
     * apply le_O_n.
     * simpl in H1.
       apply le_S_n; apply (proj2 H1).
     * assumption.
     * rewrite H3; apply f_equal2; [ | apply refl_equal].
       rewrite <- N.add_assoc; apply f_equal.
       replace (S n) with (1 + n); [ | apply refl_equal].
       rewrite Nat2N.inj_add.
       apply refl_equal.
Qed.

End Mapi.

(** ** Computing the size of a list, from the size of its elements, a generalization of length. *)

Section Size.

Hypothesis size : A -> nat.

Definition list_size := fix list_size (l : list A) {struct l} : nat :=
  match l with
  | nil => 0
  | h :: tl => size h + list_size tl
  end.

Lemma list_size_unfold :
  forall l, list_size l = match l with
                                 | nil => 0
                                 | h :: tl => size h + list_size tl
                               end.
Proof.
intros l; case l; intros; apply refl_equal.
Qed.

Lemma list_size_app :
  forall l1 l2, list_size (l1 ++ l2) = list_size l1 + list_size l2.
Proof.
fix h 1.
intros l1 l2; case l1; clear l1.
- apply refl_equal.
- intros a1 l1; simpl.
  rewrite <- plus_assoc; apply f_equal.
  apply h.
Qed.

Lemma in_list_size :
  forall l a,
    List.In a l -> size a <= list_size l.
Proof.
fix h 1.
intros l; case l; clear l.
- intros a H; contradiction H.
- intros a1 l a H; simpl in H.
  case H; clear H.
  + intro H; subst a1; simpl.
    apply le_plus_l.
  + intro H; simpl.
    refine (le_trans _ _ _ (h _ _ H) _).
    apply le_plus_r.
Qed.

End Size.

Lemma list_size_eq :
  forall f1 f2 l, (forall x, In x l -> f1 x = f2 x) -> list_size f1 l = list_size f2 l.
Proof.
intros f1 f2 l; induction l as [ | a1 l]; intro Hl; [apply refl_equal | ].
rewrite 2 (list_size_unfold _ (_ :: _)), (Hl a1 (or_introl _ (refl_equal _))).
apply f_equal; apply IHl.
intros; apply Hl; right; assumption.
Qed.

End Sec.

Lemma map_fst :
  forall (A B C : Type) (f : B -> C) (l : list (A * B)),
    map (fun (xy : A * B) => fst (let (x, y) := xy in (x, f y))) l = map (@fst _ _) l.
Proof.
intros A B C f l.
rewrite <- map_eq; intros x _; destruct x; trivial.
Qed.

Lemma list_size_map :
  forall (A B : Type) (f : A -> B) (size : B -> nat) l,
    list_size (fun a => size (f a)) l = list_size size (map f l).
Proof.
fix h 5.
intros A B f size l; case l; clear l.
- apply refl_equal.
- intros a l; simpl; apply f_equal.
  apply h.
Qed.


Lemma split_list :
  forall (A : Type) (l1 l2 k1 k2 : list A), 
    l1 ++ l2 = k1 ++ k2 ->
    {k : list A | (k1 = l1 ++ k /\ l2 = k ++ k2) \/ (l1 = k1 ++ k /\ k2 = k ++ l2)}.
Proof.
intro A.
fix h 1.
intro l1; case l1; clear l1.
- intros l2 k1 k2 H.
  exists k1; left; split.
  + apply refl_equal.
  + assumption.
- intros a1 l1 l2 k1 k2.
  case k1; clear k1.
  + intro H.
    exists (a1 :: l1); right; split.
    * apply refl_equal.
    * apply sym_eq; assumption.
  + intros b1 k1 H.
    simpl in H; injection H; clear H; intro H.
    intro; subst b1.
    assert (IH := h _ _ _ _ H).
    destruct IH as [k K].
    exists k.
    destruct K as [[K1 K2] | [K1 K2]].
    * left; split; [ | assumption].
      simpl; apply f_equal; assumption.
    * right; split; [ | assumption].
      simpl; apply f_equal; assumption.
Qed.

Lemma split_list_2 :
  forall (A : Type) 
   (a b : A) (l1 l2 k1 k2 : list A), l1 ++ a :: l2 = k1 ++ b :: k2 ->
   {l | l1 = k1 ++ b :: l /\ k2 = l ++ a :: l2} +
   {l | k1 = l1 ++ a :: l /\ l2 = l ++ b :: k2} +
   {a = b /\ l1 = k1 /\ l2 = k2}.
Proof.
intro A.
fix h 3.
intros a b l1; case l1; clear l1; [ | intros a1 l1]; (intros l2 k1; case k1; clear k1; [ | intros b1 k1]; intros k2 H).
(* 1/4 *)
simpl in H; injection H; clear H; do 2 intro; subst.
right; split; [ | split]; apply refl_equal.
(* 1/3 *)
simpl in H; injection H; clear H; do 2 intro; subst.
left; right; exists k1; split; [ | split]; apply refl_equal.
(* 1/2 *)
simpl in H; injection H; clear H; do 2 intro; subst.
left; left; exists l1; split; [ | split]; apply refl_equal.
(* 1/1 *)
simpl in H; injection H; clear H; intros H K; subst b1.
destruct (h  _ _ _ _ _ _ H) as [[[l [H1 H2]] | [l [H1 H2]]] | [H1 [H2 H3]]]; clear H.
(* 1/3 *)
subst l1 k2; do 2 left; exists l; split; [ | split]; apply refl_equal.
(* 1/2 *)
subst l2 k1; left; right; exists l; split; [ | split]; apply refl_equal.
(* 1/1 *)
right; split; [ | split; [ apply f_equal | ]]; assumption.
Qed.

Lemma all_diff_map : 
  forall (A B : Type) (f : A -> B) (l : list A), all_diff (map f l) -> all_diff l.
Proof.
intros A B f l; induction l as [ | a1 l]; intro H; [trivial | ].
simpl in H; simpl.
destruct l as [ | a2 l]; [trivial | rewrite map_unfold in H].
destruct H as [H1 H2]; assert (IH := IHl H2).
split; [ | apply IH].
intros a Ha Ka; subst a.
apply (H1 (f a1)); [ | apply refl_equal].
simpl in Ha; destruct Ha as [Ha | Ha]; [left; apply f_equal; assumption | ].
right; rewrite in_map_iff; exists a1; split; trivial.
Qed.

Lemma all_diff_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall a1 a2, In a1 l -> In a2 l -> f a1 = f a2 -> a1 = a2) ->
    all_diff l -> all_diff (map f l).
Proof.
intros A B f l; induction l as [ | a1 l];
intros Hl Kl; simpl; [trivial | ].
simpl in Kl; destruct l as [ | a2 l]; [trivial | ].
destruct Kl as [K1 K2].
assert (IH : all_diff (map f (a2 :: l))).
{
  apply IHl; [do 4 intro; apply Hl; right | ]; assumption.
}
unfold map at 1; split; [ | assumption].
intros b Hb Kb.
rewrite in_map_iff in Hb.
destruct Hb as [a [Hb Ha]]; subst b.
apply (K1 a Ha).
revert Kb; apply Hl; [left | right]; trivial.
Qed.

Definition one_to_one (A B : Type) l (rho : A -> B) :=
 forall a1 a2, In a1 l -> In a2 l -> rho a1 = rho a2 -> a1 = a2.

Lemma one_to_one_eq :
  forall (A B : Type) s1 s2 (f1 f2 : A -> B),
    (forall x, In x s1 <-> In x s2) -> (forall a, In a s1 -> f1 a = f2 a) ->
    one_to_one s1 f1 -> one_to_one s2 f2.
Proof.
intros A B s1 s2 f1 f2 Hs Hf H a1 a2 Ha1 Ha2 K.
rewrite <- Hs in Ha1, Ha2.
rewrite <- (Hf _ Ha1), <- (Hf _ Ha2) in K.
apply H; assumption.
Qed.

Lemma one_to_one_all_diff :
  forall (A B : Type) (l : list A) (f : A -> B), 
    all_diff l -> (one_to_one l f <-> all_diff (List.map (fun x => f x) l)).
Proof.
intros A B l; induction l as [ | a1 l]; intros f H.
- split; trivial.
  intros _ a1 a2 Ha1; contradiction Ha1.
- split; intro K.
  + unfold one_to_one in K.
    rewrite all_diff_unfold in H; destruct H as [H1 H2].
    rewrite all_diff_unfold, map_unfold, <- (IHl _ H2); split.
    * intros b Hb; rewrite in_map_iff in Hb.
      destruct Hb as [a [Hb Ha]]; subst b.
      intro Hf; apply (H1 a Ha); apply K; [left | right | ]; trivial.
    * intros x1 x2 Hx1 Hx2 Hx; apply K; [right | right | ]; trivial.
  + intros x1 x2 Hx1 Hx2 Hx.
    rewrite map_unfold, all_diff_unfold in K.
    destruct K as [K1 K2].
    simpl in Hx2, Hx2; destruct Hx1 as [Hx1 | Hx1]; destruct Hx2 as [Hx2 | Hx2]; subst; trivial.
    * absurd (f x1 = f x2); trivial;
      apply K1; rewrite in_map_iff; exists x2; split; trivial.
    * absurd (f x2 = f x1);
      [apply K1; rewrite in_map_iff; exists x1; split | apply sym_eq]; trivial.
    * rewrite all_diff_unfold in H.
      rewrite <- (IHl _ (proj2 H)) in K2.
      apply K2; trivial.
Qed.

Lemma partition_spec1 :
  forall (A : Type) (f : A -> bool) (l : list A), fst (partition f l) = filter f l.
Proof.
intros A f l; induction l as [ | a1 l]; simpl; trivial.
destruct (partition f l) as [l1 l2]; simpl; rewrite <- IHl.
destruct (f a1); apply refl_equal.
Qed.

Lemma partition_spec2 :
  forall (A : Type) (f : A -> bool) (l : list A), 
    snd (partition f l) = filter (fun x => negb (f x)) l.
Proof.
intros A f l; induction l as [ | a1 l]; simpl; trivial.
destruct (partition f l) as [l1 l2]; simpl; rewrite <- IHl.
destruct (f a1); apply refl_equal.
Qed.

Lemma partition_app1 :
  forall (A : Type) (f : A -> bool) (l1 l2 : list A),
    fst (partition f (l1 ++ l2)) = (fst (partition f l1)) ++ (fst (partition f l2)).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; intros l2; simpl; trivial.
assert (IH := IHl1 l2).
destruct (partition f (l1 ++ l2)); simpl in IH; rewrite IH.
destruct (partition f l1); destruct (f a1); simpl; trivial.
Qed.

Lemma partition_app2 :
  forall (A : Type) (f : A -> bool) (l1 l2 : list A),
    snd (partition f (l1 ++ l2)) = (snd (partition f l1)) ++ (snd (partition f l2)).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; intros l2; simpl; trivial.
assert (IH := IHl1 l2).
destruct (partition f (l1 ++ l2)); simpl in IH; rewrite IH.
destruct (partition f l1); destruct (f a1); simpl; trivial.
Qed.

Lemma snoc_not_nil {A} (x:A) : forall l l', l ++ x :: l' <> nil.
Proof.
  intros [ |y ys]; simpl.
  - discriminate.
  - intros  l' H. inversion H.
Qed.


Lemma list_nil_snoc {A} : forall (l:list A),
    l = nil \/ exists a l', l = l' ++ a::nil.
Proof.
  induction l as [ |x xs IHxs].
  - now left.
  - right. destruct IHxs as [IH|[a [l' IH]]]; subst xs.
    + now exists x, nil.
    + now exists a, (x::l').
Qed.
