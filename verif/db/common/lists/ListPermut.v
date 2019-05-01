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

Require Import Relations List Arith.

Require Import ListFacts Mem OrderedSet.

(** * Permutation over lists, and finite multisets. *)

Inductive _permut (A B : Type) (R : A -> B -> Prop) : (list A -> list B -> Prop) :=
  | Pnil : _permut R nil nil
  | Pcons : forall a b l l1 l2, R a b -> _permut R l (l1 ++ l2) ->
                   _permut R (a :: l) (l1 ++ b :: l2).

(** * Generalization of Pcons, the second constructor of _permut *)
Lemma _permut_strong :
  forall (A B : Type) (R : A -> B -> Prop) a1 a2 l1 k1 l2 k2, 
    R a1 a2 -> _permut R (l1 ++ k1) (l2 ++ k2) ->
    _permut R (l1 ++ a1 :: k1) (l2 ++ a2 :: k2).
Proof.
intros A B R a1 a2; fix h 1.
intro l1; case l1; clear l1; [ | intros u1 l1]; intros k1 l2 k2 a1_R_a2 P.
- apply (@Pcons _ _ R a1 a2 k1 l2 k2); trivial.
- inversion P as [ | b1 b2 l k k' b1_R_b2 Q H17 H18]; clear P; subst.
  destruct (split_list _ _ _ _ H18) as [l [[H1 H2] | [H1 H2]]]; clear H18.
  + subst l2.
    revert H2; case l; clear l.
    * intro H2; simpl in H2; subst k2; rewrite <- ass_app; simpl.
      assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (k ++ a2 :: nil) k' b1_R_b2).
      rewrite <- 2 ass_app in Q'; simpl in Q'.
      apply Q'.
      apply h; assumption.
    * intros _b2 l2 H2; simpl in H2.
      injection H2; clear H2; do 2 intro; subst _b2 k'; simpl; rewrite <- ass_app.
      assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) k (l2 ++ a2 :: k2) b1_R_b2).
      rewrite ass_app in Q'.
      apply Q'.
      apply (h _ _ _ _ a1_R_a2).
      rewrite <- ass_app; assumption.
  + subst k k2.
    assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (l2 ++ a2 :: l) k' b1_R_b2).
      rewrite <- 2 ass_app in Q'; simpl in Q'.
      apply Q'.
      apply (h _ _ _ _ a1_R_a2).
      rewrite ass_app; assumption.
Qed.      

(** * Inclusion of permutation relations *)
Lemma _permut_incl :
  forall (A B : Type) (R R' : A -> B -> Prop) l1 l2,
  (forall a b, R a b -> R' a b) -> _permut R l1 l2 -> _permut R' l1 l2.
Proof.
intros A B R R'.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 H P.
inversion P; apply Pnil.
inversion P as [ | a b k k1 k2 a_R_b Q]; subst.
apply Pcons.
apply (H _ _ a_R_b).
apply (h _ _ H Q).
Qed.

(** * Swapping the lists in _permut *)
Lemma _permut_rel_aux :
forall (A B : Type) (R : A -> B -> Prop) l1 l2,
  _permut R l1 l2 -> _permut (fun b a => R a b) l2 l1.
Proof.
intros A B R.
fix h 1.
intro l1; case l1; clear l1.
- intros l2 P.
  inversion P; subst.
  apply Pnil.
- intros a l1 l2 P.
  inversion P; clear P; subst.
  apply (_permut_strong (R := fun b a => R a b) b a l0 l3 nil l1 H1).
  simpl.
  apply h; assumption.
Qed.

Lemma _permut_rel :
forall (A B : Type) (R : A -> B -> Prop) l1 l2,
  _permut R l1 l2 <-> _permut (fun b a => R a b) l2 l1.
Proof.
intros A B R l1 l2; split; intro P.
- apply _permut_rel_aux; assumption.
- generalize (_permut_rel_aux P).
  apply _permut_incl.
  exact (fun _ _ h => h).
Qed.

(** * Various inversion lemmata *)
Lemma _permut_inv_right_strong :
  forall (A B : Type) (R : A -> B -> Prop) b l1 l2' l2'',
  _permut R l1 (l2' ++ b :: l2'') -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ _permut R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R.
fix h 2.
intros b l1; case l1; clear l1; [ | intros a1 l1]; intros l2' l2'' P.
- revert P; case l2'; clear l2'; [intro P | intros a2' l2' P]; inversion P.
- inversion P as [ | a b' l' l1' k2 a_R_b' Q H K]; subst.
  destruct (split_list _ _ _ _ K) as [l [[H1 H2] | [H1 H2]]]; clear K.
  + destruct l as [ | _b' l].
    * simpl in H2; injection H2; clear H2; do 2 intro.
      rewrite <- app_nil_end in H1.
      subst l2' l2'' b'.
      exists a1; exists nil; exists l1; split; [ | split]; trivial.
    * simpl in H2; injection H2; clear H2; do 2 intro.
      subst l2' k2 _b'.
      rewrite ass_app in Q.
      destruct (h b _ _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
      exists a; exists (a1 :: k1'); exists k1''; split; [assumption | ].
      split; [rewrite app_comm_cons; apply refl_equal | ].
      rewrite <- ass_app; simpl; apply Pcons; [assumption | ].
      rewrite ass_app; assumption.
  + destruct l as [ | _b l].
    * simpl in H2; injection H2; clear H2; do 2 intro.
      rewrite <- app_nil_end in H1.
      subst l2' l2'' b'.
      exists a1; exists nil; exists l1; split; [ | split]; trivial.
    * simpl in H2; injection H2; clear H2; do 2 intro.
      subst l1' l2'' _b.
      rewrite <- ass_app in Q; simpl in Q.
      destruct (h b _ _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
      exists a; exists (a1 :: k1'); exists k1''; split; [assumption | ].
      split; [rewrite app_comm_cons; apply refl_equal | ].
      rewrite ass_app; simpl; apply Pcons; [assumption | ].
      rewrite <- ass_app; assumption.
Qed.

Lemma _permut_inv_right :
  forall (A B : Type) (R : A -> B -> Prop) b l1 l2, _permut R l1 (b :: l2) -> 
  exists a, exists l1', exists l1'', (R a b /\ l1 = l1' ++ a :: l1'' /\ _permut R (l1' ++ l1'') l2).
Proof.
intros A B R b l1 l2 P.
apply (_permut_inv_right_strong (R := R) b (l1 := l1) nil l2 P).
Qed.

Lemma _permut_inv_left_strong :
  forall (A B : Type) (R : A -> B -> Prop) a l1' l1'' l2,
  _permut R (l1' ++ a :: l1'') l2 -> exists b, exists l2', exists l2'',
   (R a b /\ l2 = l2' ++ b :: l2'' /\ _permut R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R a l1' l1'' l2 P.
rewrite _permut_rel in P.
destruct (_permut_inv_right_strong _ _ _ P) as [b [l2' [l2'' [H1 [H2 H3]]]]].
exists b; exists l2'; exists l2''.
split; [assumption | ].
split; [assumption | ].
rewrite _permut_rel; assumption.
Qed.

(** * Compatibility of _permut *)
(** Permutation is compatible with length and size. *)
Lemma _permut_length :
  forall (A : Type) (R : relation A) l1 l2, _permut R l1 l2 -> length l1 = length l2.
Proof.
intros A R; fix h 1.
intro l; case l; clear l; [ | intros a l]; intros l' P.
inversion P; apply refl_equal.
inversion P as [ | _a b _l l1 l2 H1 H2]; clear P; subst _a _l l'.
rewrite app_length; simpl; rewrite plus_comm; simpl; rewrite plus_comm.
rewrite <- app_length; rewrite (h l (l1 ++ l2)); trivial.
Qed.

Lemma _permut_size :
  forall (A B : Type) (R : A -> B -> Prop) size size' l1 l2, 
  (forall a a', In a l1 -> In a' l2 -> R a a' -> size a = size' a') ->
  _permut R l1 l2 -> list_size size l1 = list_size size' l2.
Proof.
intros A B R size size'.
fix h 1. 
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 E P.
- (* 1/2 *)
  inversion P; apply refl_equal.
- (* 1/1 *)
  inversion P as [ | a b l1' l2' l2'' a_R_b P']; subst.
  rewrite list_size_app; simpl.
  rewrite (E a1 b); trivial.
  + rewrite (h _ (l2' ++ l2'')); [ | | apply P'].
    * rewrite list_size_app; simpl.
      rewrite plus_comm.
      rewrite <- plus_assoc.
      apply (f_equal (fun n => list_size size' l2' + n)).
      apply plus_comm.
    * intros a a' a_in_la a_in_l'; apply E; trivial.
      right; trivial.
      apply in_app; trivial.
  + left; trivial.
  + apply in_or_app; right; left; trivial.
Qed.

Lemma _permut_map :
  forall (A B A' B': Type) (R : A -> B -> Prop) (R' : A' -> B' -> Prop) f1 f2 l1 l2, 
    (forall a b, In a l1 -> In b l2 -> R a b -> R' (f1 a) (f2 b)) ->
    _permut R l1 l2 -> _permut R' (map f1 l1) (map f2 l2).
Proof.
intros A B A' B' R R' f1 f2.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 Compat P.
(* 1/1 *)
inversion P; apply Pnil.
(* 1/2 *)
inversion P as [ | a' b l1' l2' l2'' a_R_b P' H]; clear P; subst.
rewrite map_app; simpl; apply Pcons.
apply Compat; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
rewrite <- map_app; apply h; trivial.
intros a b' a_in_l1 b'_in_l2; apply Compat.
right; trivial.
apply in_app; trivial.
Qed.

Lemma _permut_app :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   _permut R l1 l2 -> _permut R l1' l2' -> _permut R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l1' l2 l2' P P'.
inversion P; subst; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; clear P; subst.
simpl; rewrite <- ass_app; simpl; apply Pcons; trivial.
rewrite ass_app; apply h; trivial.
Qed.

Lemma _permut_swapp :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   _permut R l1 l2 -> _permut R l1' l2' -> _permut R (l1 ++ l1') (l2' ++ l2).
Proof.
intros A B R.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l1' l2 l2' P P'.
inversion P; subst; rewrite <- app_nil_end; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; clear P; subst.
simpl; rewrite ass_app; apply Pcons; trivial.
rewrite <- ass_app; apply h; trivial.
Qed.

Lemma in_permut_in :
   forall (A : Type) l1 l2, _permut (@eq A) l1 l2 -> (forall a, In a l1 <-> In a l2).
Proof. 
assert (H : forall (A : Type) l1 l2, _permut (@eq A) l1 l2 -> forall a, In a l2 -> In a l1).
intros A l1 l2 P a a_in_l2;
destruct (In_split _ _ a_in_l2) as [l2' [l2'' H]]; subst.
destruct (_permut_inv_right_strong (R := @eq A) _ _ _ P)  as [a' [l1' [l1'' [a_eq_a' [H _]]]]]; subst.
apply in_or_app; right; left; trivial.
intros A l1 l2 P a; split; apply H; trivial.
rewrite _permut_rel.
revert P; apply _permut_incl.
exact (fun _ _ h => sym_eq h).
Qed.

(** * Permutation is an equivalence, whenever the underlying relation is *)
Lemma _permut_refl : 
   forall (A : Type) (R : A -> A -> Prop) l,  (forall a, In a l -> R a a) -> _permut R l l.
Proof.
intros A R.
fix h 1.
intro l; case l; clear l; [ | intros a l]; intro R_refl.
(* 1/2 *)
apply Pnil.
(* 1/1 *)
apply (@Pcons _ _ R a a l nil l).
apply R_refl; left; apply refl_equal.
simpl; apply (h l (fun x h => R_refl x (or_intror _ h))).
Qed.

Lemma _permut_sym :
  forall (A : Type) (R : A -> A -> Prop) l1 l2, 
    (forall a b, In a l1 -> In b l2 -> R a b -> R b a) ->
    _permut R l1 l2 -> _permut R l2 l1.
Proof.
intros A R; fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 R_sym P.
(* 1/2 *)
inversion P; apply Pnil.
(* 1/1 *)
inversion P as [ | a b l1' l2' l2'' a_R_b Q]; subst.
apply (_permut_strong (R := R) b a1 l2' l2'' (@nil A) l1).
apply R_sym; trivial; [left | apply in_or_app; right; left]; trivial.
simpl; apply h; trivial.
intros; apply R_sym; trivial; [right | apply in_app]; trivial.
Qed.

Lemma _permut_trans :
  forall (A : Type) (R : A -> A -> Prop) l1 l2 l3,
   (forall a b c, In a l1 -> In b l2 -> In c l3 -> R a b -> R b c -> R a c) ->
   _permut R l1 l2 -> _permut R l2 l3 -> _permut R l1 l3.
Proof.
intros A R; fix h 2.
intros l1 l2; case l2; clear l2; [ | intros a2 l2]; intros l3 R_trans P1 P2.
(* 1/2 *)
inversion P2; exact P1.
(* 1/1 *)
destruct (_permut_inv_right P1) as [a1 [l1' [l1'' [a1_R_a2 [H Q1]]]]]; clear P1; subst l1.
inversion P2 as [ | a2' a3 l2' l3' l3'' a2_R_a3 Q2]; subst.
apply _permut_strong.
apply R_trans with a2; trivial.
apply in_or_app; right; left; apply refl_equal.
left; apply refl_equal.
apply in_or_app; right; left; apply refl_equal.
apply h with l2; trivial.
intros a b c; intros; apply R_trans with b; trivial.
apply in_app; trivial.
right; trivial.
apply in_app; trivial.
Qed.

Lemma _permut_rev : 
   forall (A : Type) (R : A -> A -> Prop) l,  (forall a, In a l -> R a a) -> _permut R l (rev l).
Proof.
intros A R.
fix h 1.
intro l; case l; clear l; [ | intros a l]; intro R_refl.
- (* 1/2 *)
 apply Pnil.
- (* 1/1 *)
  apply (@Pcons _ _ R a a l (rev l) nil).
  + apply R_refl; left; apply refl_equal.
  + rewrite <- app_nil_end; apply h.
    intros; apply R_refl; right; assumption.
Qed.

(** * Removing elements in permutated lists *)

Lemma _permut_cons_inside :
  forall (A B : Type) (R : A -> B -> Prop) a b l l1 l2, 
  (forall a1 b1 a2 b2, In a1 (a :: l) -> In b1 (l1 ++ b :: l2) ->
                   In a2 (a :: l) -> In b2 (l1 ++ b :: l2) ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> _permut R (a :: l) (l1 ++ b :: l2) -> _permut R l (l1 ++ l2).
Proof.
intros A B R a b l l1 l2 trans_R a_R_b P;
destruct (_permut_inv_right_strong (R := R) _ _ _ P) as [a' [l1' [l1'' [a'_R_b [H P']]]]].
destruct l1' as [ | a1' l1']; injection H; clear H; intros; subst; trivial.
inversion P' as [ | a'' b' l' k1' k2' a''_R_b' P'' H17 H18]; subst.
apply _permut_strong; trivial.
apply trans_R with b a1'; trivial.
right; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
left; trivial.
apply in_app; rewrite <- H18; apply in_or_app; right; left; trivial.
Qed.

Lemma _permut_add_inside :
   forall (A B : Type) (R : A -> B -> Prop) a b l1 l1' l2 l2', 
  (forall a1 b1 a2 b2, In a1 (l1 ++ a :: l1') -> In b1 (l2 ++ b :: l2') ->
                   In a2 (l1 ++ a :: l1') -> In b2 (l2 ++ b :: l2') ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> _permut R (l1 ++ a :: l1') (l2 ++ b :: l2') -> _permut R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R a b l1 l1' l2 l2' trans_R a_R_b P.
destruct (_permut_inv_left_strong (R := R) _ _ _ P) as [b' [k2 [k2' [a_R_b' [H P']]]]].
destruct (split_list _ _ _ _ H) as [l [[H1 H2] | [H1 H2]]]; clear H.
- destruct l as [ | b1 l].
  + simpl in H1; injection H2; clear H2; do 2 intro.
    subst b' k2'.
    rewrite <- app_nil_end in H1; subst k2.
    assumption.
  + simpl in H2; injection H2; clear H2; do 2 intro.
    subst l2' k2 b1.
    rewrite <- ass_app in P'; simpl in P'.
    destruct (_permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
    rewrite H, ass_app.
    apply _permut_strong.
    * {
        apply trans_R with b a; trivial.
        - apply in_app; rewrite H.
          apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; do 2 right.
          apply in_or_app; right; left; apply refl_equal.
      }
    * rewrite <- ass_app; assumption.
- destruct l as [ | b1 l].
  + simpl in H1; injection H2; clear H2; do 2 intro.
    subst b' k2'.
    rewrite <- app_nil_end in H1; subst k2.
    assumption.
  + simpl in H2; injection H2; clear H2; do 2 intro.
    subst l2 k2' b1.
    rewrite ass_app in P'.
    destruct (_permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
    rewrite H, <- ass_app; simpl.
    apply _permut_strong.
    * {
        apply trans_R with b a; trivial.
        - apply in_app; rewrite H.
          apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; left.
          apply in_or_app; right; left; apply refl_equal.
      }
    * rewrite ass_app; assumption.
Qed.

Lemma _permut_app1 :
  forall (A : Type) (R : relation A), equivalence _ R ->
  forall l l1 l2, _permut R l1 l2 <-> _permut R (l ++ l1) (l ++ l2).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l]; trivial.
simpl; apply (@Pcons _ _ R u u (l ++ l1) (@nil A) (l ++ l2)); trivial.
apply (equiv_refl _ _ E).
(* <- case *)
induction l as [ | u l]; trivial.
apply IHl.
apply (@_permut_cons_inside A A R u u (l ++ l1) (@nil _) (l ++ l2)); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2.
apply (equiv_trans _ _ E) with b1; trivial.
apply (equiv_trans _ _ E) with a2; trivial.
apply (equiv_sym _ _ E); trivial.
apply (equiv_refl _ _ E).
Qed.

Lemma _permut_app2 :
  forall (A : Type) (R : relation A), equivalence _ R ->
  forall l l1 l2, _permut R l1 l2 <-> _permut R (l1 ++ l) (l2 ++ l).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end; trivial.
apply _permut_strong; trivial.
apply (equiv_refl _ _ E).

(* <- case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end in P; trivial.
apply IHl.
apply (@_permut_add_inside A A R u u); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2;
apply (equiv_trans _ _ E) with b1; trivial.
apply (equiv_trans _ _ E) with a2; trivial.
apply (equiv_sym _ _ E); trivial.
apply (equiv_refl _ _ E).
Qed.

(** * A function to decide wether 2 lists are in relation by _permut *)

Definition _remove_common_bool := fun (A : Type) (equiv_bool : A -> A -> bool) =>
fix _remove_common (l l' : list A) : ((list A) * (list A)) :=
match l with 
| nil => (l, l')
| h :: tl => 
  match remove_bool equiv_bool h l' with
  | Some l'' => _remove_common tl l''
  | None => match _remove_common tl l' with (k, k') => (h :: k, k')  end
  end
end.

Lemma _remove_common_bool_is_sound :
  forall (A : Type) equiv_bool (l1 l2 l1' l2': list A), 
    _remove_common_bool equiv_bool l1 l2 =  (l1',l2') ->
              {ll : list (A * A) | (forall t1 t2, In (t1,t2) ll -> equiv_bool t1 t2 = true) /\
                _permut (@eq A) l1 (l1' ++ (map (fun st => fst st) ll)) /\
                _permut (@eq A) l2 (l2' ++ (map (fun st => snd st) ll)) /\
                (forall t1 t2, In t1 l1' -> In t2 l2' -> equiv_bool t1 t2 = false)}.
Proof.
intros A equiv_bool.
fix h 1.
intros l1 l2 l1' l2'; case l1; clear l1; [ | intros a1 l1]; simpl.
- intro H; injection H; clear H; intros; subst.
  exists nil; split; [intros; contradiction | ].
  split; [apply Pnil | ].
  split.
  + simpl; rewrite <- app_nil_end; apply _permut_refl; intros; apply refl_equal.
  + intros; contradiction.
- case_eq (remove_bool equiv_bool a1 l2).
  + intros k2 H2 H.
    assert (K2 := remove_bool_some_is_sound _ _ _ H2).
    case K2; clear K2.
    intros [[a1' k2'] k2''] [K1 [K2 K3]].
    assert (IH := h _ _ _ _ H).
    case IH; clear IH.
    intros ll [Hll [J1 [J2 J3]]].
    exists ((a1, a1') :: ll); split; [ | split; [ | split]].
    * intros t1 t2 Ht; simpl in Ht.
      destruct Ht as [Ht | Ht]; [injection Ht; clear Ht; intros; subst; assumption | ].
      apply Hll; assumption.
    * rewrite map_unfold; simpl fst.
      apply Pcons; [apply refl_equal | assumption].
    * rewrite map_unfold; simpl snd.
      rewrite K2; apply _permut_strong; [apply refl_equal | ].
      rewrite <- K3; assumption.
    * assumption.
  + intros H2 H.
    assert (K2 := remove_bool_none_is_sound _ _ _ H2).
    case_eq (_remove_common_bool equiv_bool l1 l2).
    intros k k' K; rewrite K in H.
    injection H; clear H; do 2 intro; subst l1' l2'.
    assert (IH := h _ _ _ _ K).
    case IH; clear IH.
    intros ll [Hll [J1 [J2 J3]]].
    exists ll; split; [ | split; [ | split]].
    * assumption.
    * simpl.
      apply (@Pcons _ _ _ a1 a1 l1 nil (k ++ map (fun st : A * A => fst st) ll) (refl_equal _)).
      apply J1.
    * assumption.
    * intros t1 t2 Ht1 Ht2; simpl in Ht1.
      destruct Ht1 as [Ht1 | Ht1]; [ | apply J3; assumption].
      subst t1.
      apply K2.
      rewrite (in_permut_in J2).
      apply in_or_app; left; assumption.
Qed.

Definition _permut_bool := fun (A : Type) (equiv_bool : A -> A -> bool) =>
fix _permut_bool (l1 l2 : list A) : bool :=
match l1 with
| nil =>
  match l2 with
  | nil => true
  | _ => false
  end
| t1 :: k1 =>
    match remove_bool equiv_bool t1 l2 with
   | Some k2 => _permut_bool k1 k2
   | None => false
   end
end.

Lemma _permut_bool_true_is_sound :
  forall (A : Type) (equiv_bool : A -> A -> bool) (l1 l2 : list A),
    _permut_bool equiv_bool l1 l2 = true -> _permut (fun x y => equiv_bool x y = true) l1 l2. 
Proof.
intros A equiv_bool. 
fix h 1.
intro l1; case l1; clear l1.
- intros l2; case l2; clear l2.
  + intros _; simpl; apply Pnil.
  + intros a2 l2 P; discriminate P.
- intros a1 l1 l2.
  simpl.
  case_eq (remove_bool equiv_bool a1 l2).
  + intros k2 Hl2 P.
    case (remove_bool_some_is_sound _ _ _ Hl2).
    intros [[a' k] k'] [K1 [K2 K3]].
    subst l2 k2.
    apply Pcons; [assumption | ].
    apply (h l1 (k ++ k') P).
  + intros _ Abs; discriminate Abs.
Qed.

Lemma _permut_bool_is_sound :
  forall (A : Type) (equiv_bool : A -> A -> bool) (l1 l2 : list A),
    (forall a3 b1 a4 b2 : A, 
       In a3 l1 -> In b1 l2 -> In a4 l1 -> In b2 l2 -> 
       equiv_bool a3 b1 = true -> equiv_bool a4 b1 = true -> equiv_bool a4 b2 = true -> 
       equiv_bool a3 b2 = true) -> 
    match _permut_bool equiv_bool l1 l2 with 
      | true => _permut (fun x y => equiv_bool x y = true) l1 l2 
      | false => ~_permut (fun x y => equiv_bool x y = true) l1 l2 
    end.
Proof.
intros A equiv_bool l1 l2 H.
case_eq (_permut_bool equiv_bool l1 l2); intro P.
- apply (_permut_bool_true_is_sound _ _ _ P).
- revert l1 l2 H P.
  fix h 1.
  + intro l1; case l1; clear l1.
    * {
        intros l2; case l2; clear l2.
        - intros _ Abs; discriminate Abs.
        - intros a2 l2 _ _ P; inversion P.
      }
    * intros a1 l1 l2 H P Q.
      simpl in P.
      {
        case_eq (remove_bool equiv_bool a1 l2).
        - intros k2 H2; rewrite H2 in P.
          case (remove_bool_some_is_sound _ _ _ H2); clear H2.
          intros [[a1' k2'] k2''] [K1 [K2 K3]].
          subst l2 k2.
          assert (H' : forall a3 b1 a4 b2 : A,
                     In a3 l1 ->
                     In b1 (k2' ++ k2'') ->
                     In a4 l1 ->
                     In b2 (k2' ++ k2'') ->
                     equiv_bool a3 b1 = true ->
                     equiv_bool a4 b1 = true ->
                     equiv_bool a4 b2 = true -> equiv_bool a3 b2 = true).
          {
            do 8 intro; apply H.
            - right; assumption.
            - apply in_app; assumption.
            - right; assumption.
            - apply in_app; assumption.
          }
          apply (h _ _ H' P).
          apply _permut_cons_inside with a1 a1'; trivial.
        - intro H2.
          inversion Q; clear Q; subst.
          assert (Aux : In b (l0 ++ b :: l3)).
          {
            apply in_or_app; right; left; apply refl_equal.
          } 
          assert (Abs := remove_bool_none_is_sound _ _ _ H2 b Aux).
          rewrite H3 in Abs; discriminate Abs.
      }
Qed.          

Lemma permut_filter : 
  forall (A : Type) (R : relation A) (f : A -> bool) (l1 l2 : list A),
    (forall x1 x2, In x1 l1 -> R x1 x2 -> f x1 = f x2) ->
    _permut R l1 l2 -> _permut R (filter f l1) (filter f l2).
Proof.
intros A R f l1; induction l1 as [ | x1 l1]; intros l2 H P.
- inversion P; apply Pnil.
- inversion P; subst; rewrite filter_app; simpl.
  assert (Hx1 := H x1 b (or_introl _ (refl_equal _)) H2); rewrite <- Hx1.
  destruct (f x1).
  + apply Pcons; [assumption | ].
    rewrite <- filter_app.
    apply IHl1.
    * intros y1 y2 Hy; apply H; right; assumption.
    * assumption.
  + rewrite <- filter_app.
    apply IHl1.
    * intros y1 y2 Hy; apply H; right; assumption.
    * assumption.
Qed.

Section Sec.
Hypothesis A : Type.
Hypothesis EDS : Oeset.Rcd A.

Notation permut := (_permut (fun x y => Oeset.compare EDS x y = Eq)).

(** ** Permutation is a equivalence relation. 
      Reflexivity. *)
  Theorem permut_refl :  forall (l : list A), permut l l.
  Proof.
  intro l; apply _permut_refl.
  intros a _; apply Oeset.compare_eq_refl.
  Qed.

Lemma permut_refl_alt :
  forall l1 l2, comparelA (Oeset.compare EDS) l1 l2 = Eq -> permut l1 l2.
Proof.
intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
- apply Pnil.
- simpl in H.
  case_eq (Oeset.compare EDS a1 a2); intro Ha; rewrite Ha in H; try discriminate H.
  apply (Pcons (R := fun x y => Oeset.compare EDS x y = Eq) a1 a2 nil l2 Ha (IHl1 _ H)).
Qed.

Lemma permut_refl_alt2 :
  forall l1 l2, l1 = l2 -> permut l1 l2.
  Proof.
    intros l1 l2 H; subst l2; apply permut_refl.
  Qed.

  (** Symetry. *)
  Theorem permut_sym : forall l1 l2 : list A, permut l1 l2 -> permut l2 l1.
  Proof.
  intros l1 l2 P; apply _permut_sym; trivial.
  intros a b _ _ H.
  rewrite Oeset.compare_lt_gt, H; apply refl_equal.
  Qed.

  (** Transitivity. *)
  Theorem permut_trans :
    forall l1 l2 l3 : list A, permut l1 l2 -> permut l2 l3 -> permut l1 l3.
  Proof.
  intros l1 l2 l3 P1 P2; apply _permut_trans with l2; trivial.
  intros a b c _ _ _; apply Oeset.compare_eq_trans.
  Qed.


(** ** Compatibility Properties. 
      Permutation is compatible with mem. *)
Lemma mem_permut_mem :
  forall l1 l2 e, permut l1 l2 -> Oeset.mem_bool EDS e l1 = Oeset.mem_bool EDS e l2.
Proof.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 e P.
- inversion P; subst; apply refl_equal.
- inversion P; clear P; subst.
  rewrite Oeset.mem_bool_unfold, Oeset.mem_bool_app.
  rewrite (Oeset.mem_bool_unfold EDS e (b :: l3)).
  case_eq (Oeset.compare EDS e a1); intro He.
  + rewrite (Oeset.compare_eq_trans _ _ _ _ He H1), Bool.orb_true_r.
    apply refl_equal.
  + rewrite Bool.orb_false_l.
    rewrite (h _ _ _ H3), Oeset.mem_bool_app.
    rewrite (Oeset.compare_lt_eq_trans EDS _ _ _ He H1).
    apply refl_equal.
  + rewrite Bool.orb_false_l.
    rewrite (h _ _ _ H3), Oeset.mem_bool_app.
    rewrite Oeset.compare_lt_gt.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in H1, He.
    rewrite (Oeset.compare_eq_lt_trans EDS _ _ _ H1 He).
    apply refl_equal.
Qed.

Lemma mem_permut_mem_strong :
  forall l1 l2 e, _permut (@eq A) l1 l2 -> Oeset.mem_bool EDS e l1 = Oeset.mem_bool EDS e l2.
Proof.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 e P.
- inversion P; subst; apply refl_equal.
- inversion P; clear P; subst.
  rewrite Oeset.mem_bool_unfold, Oeset.mem_bool_app.
  rewrite (Oeset.mem_bool_unfold EDS e (b :: l3)).
  case_eq (Oeset.compare EDS e b); intro He.
  + rewrite Bool.orb_true_r; apply refl_equal.
  + rewrite 2 Bool.orb_false_l.
    rewrite (h _ _ _ H3), Oeset.mem_bool_app.
    apply refl_equal.
  + rewrite 2 Bool.orb_false_l.
    rewrite (h _ _ _ H3), Oeset.mem_bool_app.
    apply refl_equal.
Qed.

Lemma mem_morph : 
  forall x y, Oeset.compare EDS x y = Eq ->
  forall l1 l2, permut l1 l2 -> (Oeset.mem_bool EDS x l1 = Oeset.mem_bool EDS y l2).
Proof.
  intros e1 e2 e1_eq_e2 l1 l2 P.
  rewrite (mem_permut_mem e1 P).
  clear l1 P.
  induction l2 as [ | a l]; simpl; [trivial | ].
  unfold Oeset.eq_bool; rewrite IHl; apply f_equal2; [ | apply refl_equal].
  case_eq (Oeset.compare EDS e2 a); intro H.
  - rewrite (Oeset.compare_eq_trans _ _ _ _ e1_eq_e2 H).
    apply refl_equal.
  - rewrite (Oeset.compare_eq_lt_trans _ _ _ _ e1_eq_e2 H).
    apply refl_equal.
  - rewrite Oeset.compare_lt_gt, CompOpp_iff in e1_eq_e2, H.
    rewrite Oeset.compare_lt_gt.
    rewrite (Oeset.compare_lt_eq_trans _ _ _ _ H e1_eq_e2).
    apply refl_equal.
Qed.

 (** Permutation is compatible with addition and removal of common elements *)
  
Lemma permut_cons :
  forall e1 e2 l1 l2, 
    Oeset.compare EDS e1 e2 = Eq -> 
    (permut l1 l2 <-> permut (e1 :: l1) (e2 :: l2)).
Proof.
intros e1 e2 l1 l2 e1_eq_e2; split; intro P.
- apply (@Pcons _ _ _ e1 e2 l1 (@nil A) l2); trivial.
- replace l2 with (nil ++ l2); trivial;
    apply _permut_cons_inside with e1 e2; trivial.
  intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2.
    apply Oeset.compare_eq_trans with a2; trivial.
    apply Oeset.compare_eq_trans with b1; trivial.
    rewrite Oeset.compare_lt_gt, a2_eq_b1; apply refl_equal.
Qed.

Lemma cons_permut_mem :
  forall l1 l2 e1 e2, 
    Oeset.compare EDS e1 e2 = Eq -> permut (e1 :: l1) l2 -> 
    Oeset.mem_bool EDS e2 l2 = true.
Proof.
  intros l1 l2 e1 e2 e1_eq_e2 P.
  rewrite <- (mem_morph _ _ e1_eq_e2 P), Oeset.mem_bool_unfold, Oeset.compare_eq_refl.
  apply refl_equal.
Qed.

Lemma permut_add_inside :
    forall e1 e2 l1 l2 l3 l4, Oeset.compare EDS e1 e2 = Eq -> 
      (permut (l1 ++ l2) (l3 ++ l4) <-> permut (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).
Proof.
  intros e1 e2 l1 l2 l3 l4 e1_eq_e2; split; intro P.
  apply _permut_strong; trivial.
  apply _permut_add_inside with e1 e2; trivial.
  intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
  apply Oeset.compare_eq_trans with a2; trivial.
  apply Oeset.compare_eq_trans with b1; trivial.
  rewrite Oeset.compare_lt_gt, a2_eq_b1; apply refl_equal.
Qed.

Lemma permut_cons_inside :
  forall e1 e2 l l1 l2, Oeset.compare EDS e1 e2 = Eq ->
    (permut l (l1 ++ l2) <-> permut (e1 :: l) (l1 ++ e2 :: l2)).
Proof.
  intros e1 e2 l l1 l2 e1_eq_e2; apply (permut_add_inside _ _ nil l l1 l2 e1_eq_e2).
Qed.

(** Permutation is compatible with append. *)
Lemma permut_app1 :
  forall l l1 l2, permut l1 l2 <-> permut (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2; apply _permut_app1.
split.
- intro; apply Oeset.compare_eq_refl.
- do 3 intro; apply Oeset.compare_eq_trans.
- do 2 intro; intro H; rewrite Oeset.compare_lt_gt, H.
  apply refl_equal.
Qed.

 Lemma permut_app2 :
  forall l l1 l2, permut l1 l2 <-> permut (l1 ++ l) (l2 ++ l).
Proof.
intros l l1 l2; apply _permut_app2.
split.
- intro; apply Oeset.compare_eq_refl.
- do 3 intro; apply Oeset.compare_eq_trans.
- do 2 intro; intro H; rewrite Oeset.compare_lt_gt, H.
  apply refl_equal.
Qed.

(** ** Link with AC syntactic decomposition.*)
Lemma ac_syntactic_aux :
 forall (l1 l2 l3 l4 : list A),
 permut (l1 ++ l2) (l3 ++ l4) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
fix h 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 l3 l4 P.
- exists (nil : list A); exists (nil : list A); exists l3; exists l4.
  split; [apply permut_refl | ].
  split; [assumption | split; apply permut_refl].
- simpl in P.
  inversion P; clear P; subst.
  destruct (split_list _ _ _ _ H1) as [l [[K1 K2] | [K1 K2]]]; clear H1.
  + destruct l as [ | _b l].
    * rewrite <- app_nil_end in K1; simpl in K2; subst l3 l4.
      destruct (h _ _ _ _ H3) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]].
      {
        exists u1; exists (b :: u2); exists u3; exists u4; repeat split.
        - apply Pcons; assumption.
        - assumption.
        - assumption.
        - assert (H := @Pcons _ _ 
                              (fun x y => Oeset.compare EDS x y = Eq) b b l5 nil (u2 ++ u4) 
                              (Oeset.compare_eq_refl _ _) P4).
          simpl; simpl in H; apply H.
      }
    * simpl in K2; injection K2; clear K2.
      do 2 intro; subst l3 l5 _b.
      rewrite ass_app in H3.
      destruct (h _ _ _ _ H3) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]].
      {
        exists (b :: u1); exists u2; exists u3; exists u4; repeat split.
        - assert (H := @Pcons _ _ 
                              (fun x y => Oeset.compare EDS x y = Eq) a1 b l1 nil (u1 ++ u2) 
                              H2 P1).
          simpl; simpl in H; apply H.
        - assumption.
        - simpl.
          assert (H := permut_add_inside b b l0 l nil (u1 ++ u3) (Oeset.compare_eq_refl _ _)).
          rewrite H in P3; apply P3.
        - assumption.
      }
  + subst l0 l4.
    rewrite <- ass_app in H3.
    destruct (h _ _ _ _ H3) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]].
    exists u1; exists (b :: u2); exists u3; exists u4; repeat split.
    * apply Pcons; assumption.
    * assumption.
    * assumption.
    * assert (H := permut_add_inside b b l l5 nil (u2 ++ u4) (Oeset.compare_eq_refl _ _)).
      rewrite H in P4; apply P4.
Qed.

Lemma ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
intros l1 l2 l3 l4 P; apply ac_syntactic_aux.
apply permut_trans with (l2 ++ l1).
apply _permut_swapp; apply permut_refl.
apply permut_trans with (l4 ++ l3); trivial.
apply _permut_swapp; apply permut_refl.
Qed.

Lemma nb_occ_permut :
 forall l1 l2, (forall x, Oeset.nb_occ EDS x l1 = Oeset.nb_occ EDS x l2) -> permut l1 l2.
Proof.
intros l1; induction l1 as [ | a1 l1]; intros l2 Hl.
- destruct l2 as [ | a2 l2].
  + apply Pnil.
  + apply False_rec.
    assert (Ha2 := Hl a2); simpl in Ha2.
    rewrite Oeset.compare_eq_refl in Ha2.
    destruct (Oeset.nb_occ EDS a2 l2); discriminate Ha2.
- assert (Ha1 : Oeset.mem_bool EDS a1 l2 = true).
  {
    generalize (Oeset.not_mem_nb_occ EDS a1 l2).
    destruct (Oeset.mem_bool EDS a1 l2); [trivial | ].
    intro Abs; assert (Ha1 := Hl a1); simpl in Ha1.
    rewrite Oeset.compare_eq_refl, (Abs (refl_equal _)) in Ha1.
    destruct (Oeset.nb_occ EDS a1 l1); discriminate Ha1.
  }
  rewrite Oeset.mem_bool_true_iff in Ha1.
  destruct Ha1 as [b1 [Ha1 Hb1]].
  destruct (in_split _ _ Hb1) as [k1 [k2 K]]; subst l2.
  apply Pcons; [assumption | ].
  apply IHl1.
  intros x; generalize (Hl x).
  rewrite 2 Oeset.nb_occ_app, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)).
  case_eq (Oeset.compare EDS x a1); intro Ka1.
  + rewrite (Oeset.compare_eq_trans _ _ _ _ Ka1 Ha1); intro H.
    apply (BinNat.Nplus_reg_l BinNat.N.one). fold BinNat.N.one in H. rewrite H, BinNat.N.add_comm, <- BinNat.N.add_assoc.
    apply f_equal; apply BinNat.N.add_comm.
  + rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Ka1 Ha1); exact (fun h => h).
  + rewrite (Oeset.compare_gt_eq_trans _ _ _ _ Ka1 Ha1); exact (fun h => h).
Qed.

Lemma permut_nb_occ :
  forall x l1 l2, permut l1 l2 -> Oeset.nb_occ EDS x l1 = Oeset.nb_occ EDS x l2.
Proof.
intros x l1 l2 H.
rewrite 2 Oeset.nb_occ_list_size; apply f_equal.
apply (_permut_size (R := (fun x y => Oeset.compare EDS x y = Eq))); [ | apply H].
intros a1 a2 _ _ K.
case_eq (Oeset.compare EDS x a1); intro H1.
- rewrite (Oeset.compare_eq_trans _ _ _ _ H1 K); apply refl_equal.
- rewrite (Oeset.compare_lt_eq_trans _ _ _ _ H1 K); apply refl_equal.
- rewrite (Oeset.compare_gt_eq_trans _ _ _ _ H1 K); apply refl_equal.
Qed.

Definition permut_bool := 
  _permut_bool (fun x y => 
                  match Oeset.compare EDS x y with 
                    | Eq => true 
                    | _ => false 
                  end).

Lemma permut_bool_is_sound :
  forall (l1 l2 : list A),
    match permut_bool l1 l2 with 
      | true => permut l1 l2 
      | false => ~permut l1 l2 
    end.
Proof.
intros l1 l2.
unfold permut_bool.
generalize (_permut_bool_is_sound 
              (fun x y => match Oeset.compare EDS x y with Eq => true | _ => false end) 
              l1 l2).
case (_permut_bool
         (fun x y : A =>
          match Oeset.compare EDS x y with
          | Eq => true
          | Lt => false
          | Gt => false
          end) l1 l2).
- intro H.
  apply _permut_incl with (fun x y : A =>
         match Oeset.compare EDS x y with
         | Eq => true
         | Lt => false
         | Gt => false
         end = true).
  + intros a b K.
    rewrite compare_eq_true in K; apply K.
  + apply H.
    intros a3 b1 a4 b2 _ _ _ _ H1 H2 H3.
    rewrite compare_eq_true in H1, H2, H3.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in H2.
    rewrite (Oeset.compare_eq_trans _ _ _ _ H1 (Oeset.compare_eq_trans _ _ _ _ H2 H3)).
    apply refl_equal.
- intros H H'.
  apply H.
  + intros a3 b1 a4 b2 _ _ _ _ H1 H2 H3.
    rewrite compare_eq_true in H1, H2, H3.
    rewrite Oeset.compare_lt_gt, CompOpp_iff in H2.
    rewrite (Oeset.compare_eq_trans _ _ _ _ H1 (Oeset.compare_eq_trans _ _ _ _ H2 H3)).
    apply refl_equal.
  + revert H'; apply _permut_incl.
    intros a b K; rewrite K.
    apply refl_equal.
Qed.

End Sec.

Section PermutiSi.

Hypothesis A : Type.
Hypothesis R : A -> A -> Prop.
Hypothesis ER : equivalence _ R.

Inductive _permut_i_Si : (list A -> list A -> Prop) :=
  | PiSi : forall l1 a1 a2 b1 b2 l2, 
      R a1 a2 -> R b1 b2 -> _permut_i_Si (l1 ++ a1 :: b1 :: l2) (l1 ++ b2 :: a2 :: l2).

Inductive permut_i_Si : (list A -> list A -> Prop) :=
  | ReflStep : forall l1 l2, Forall2 R l1 l2 -> permut_i_Si l1 l2
  | SwappStep : forall l1 l2, _permut_i_Si l1 l2 -> permut_i_Si l1 l2
  | TransStep : forall l1 l2 l3, permut_i_Si l1 l2 -> permut_i_Si l2 l3 -> permut_i_Si l1 l3.

Lemma _permut_i_Si_permut :
  forall l1 l2, _permut_i_Si l1 l2 -> _permut R l1 l2.
Proof.
intros k1 k2 H.
inversion H; subst.
apply _permut_app1; [assumption | ].
apply (Pcons (R := R) a1 a2 (l := b1 :: l2) (b2 :: nil) l2).
- assumption.
- apply (Pcons (R := R) b1 b2 (l := l2) nil l2).
  + assumption.
  + apply _permut_refl; intros; destruct ER; apply equiv_refl.
Qed.

Lemma permut_i_Si_strong :
  forall l1 l1' a1 a2 b1 b2 l2 l2',
    Forall2 R l1 l1' -> R a1 a2 -> R b1 b2 -> Forall2 R l2 l2' ->
    permut_i_Si (l1 ++ a1 :: b1 :: l2) (l1' ++ b2 :: a2 :: l2').
Proof.
destruct ER.
intros l1 l1' a1 a2 b1 b2 l2 l2' H1 Ha Hb H2.
constructor 3 with (l1 ++ a1 :: b1 :: l2').
- constructor 1; clear H1.
  revert l2 l2' H2; induction l1 as [ | x1 l1]; intros l2 l2' H2.
    * simpl; repeat (constructor 2; trivial).
    * simpl; constructor 2; trivial.
      apply IHl1; trivial.
- constructor 3 with (l1' ++ a1 :: b1 :: l2').
  + constructor 1; clear H2.
    revert l1' l2' H1; induction l1 as [ | x1 l1]; intros [ | y1 l1'] l2' H1.
    * simpl; repeat (constructor 2; trivial).
      induction l2' as [ | y2 l2']; simpl; [constructor 1 | ].
      constructor 2; trivial.
    * inversion H1.
    * inversion H1.
    * inversion H1; subst; simpl; constructor 2; trivial.
      apply IHl1; trivial.
  + constructor 2.
    apply PiSi; trivial.
Qed.

Lemma permut_i_Si_cons :
  forall a1 a2 l1 l2, R a1 a2 -> permut_i_Si l1 l2 -> permut_i_Si (a1 :: l1) (a2 :: l2).
Proof.
destruct ER.
intros c1 c2 l1 l2 Hc Hl; revert c1 c2 Hc; induction Hl; intros c1 c2 Hc.
- constructor 1; constructor 2; assumption.
- inversion H as [k a1 a2 b1 b2 k']; subst.
  rewrite 2 app_comm_cons; apply permut_i_Si_strong; trivial.
  + constructor 2; trivial.
    clear H; induction k as [ | x k]; [constructor 1 | constructor 2; trivial].
  + clear H; induction k' as [ | x k']; [constructor 1 | constructor 2; trivial].
- constructor 3 with (c1 :: l2); [ | apply IHHl2; trivial].
  apply IHHl1; trivial.
Qed.

Lemma permut_i_Si_permut :
  forall l1 l2, permut_i_Si l1 l2 <-> _permut R l1 l2.
Proof.
destruct ER.
intros l1 l2; split; intro H.
- induction H.
  + revert l2 H; induction l1 as [ | a1 l1]; intros [ | a2 l2] H.
    * apply _permut_refl; intros a Ha; contradiction Ha.
    * inversion H.
    * inversion H.
    * inversion H; subst.
      apply (Pcons (R := R) a1 a2 (l := l1) nil l2); [assumption | ].
      apply IHl1; assumption.
  + apply _permut_i_Si_permut; assumption.
  + apply _permut_trans with l2; trivial.
    do 6 intro; apply equiv_trans.
- induction H.
  + constructor 1; constructor 1.
  + constructor 3 with (a :: (l1 ++ l2)); [apply permut_i_Si_cons; trivial | ].
    clear H0 IH_permut.
    revert l2; induction l1 as [ | a1 l1]; intro l2; simpl.
    * constructor 1; constructor 2; trivial.
      induction l2 as [ | a2 l2]; [constructor 1 | constructor 2; trivial].
    * {
        constructor 3 with (a1 :: a :: l1 ++ l2).
        - constructor 2; apply (@PiSi nil); trivial.
        - apply permut_i_Si_cons; trivial.
      }
Qed.

End PermutiSi.

Lemma partition_spec3_strong :
  forall (A : Type) (f : A -> bool) l l1 l2, partition f l = (l1, l2) -> _permut (@eq A) l (l1 ++ l2).
Proof.
intros A f l; induction l as [ | a1 l]; intros l1 l2 Hl; simpl in Hl.
- injection Hl; clear Hl; do 2 intro; subst l1 l2; apply _permut_refl; intros; apply refl_equal.
- case_eq (partition f l); intros k1 k2 Kl; rewrite Kl in Hl.
  case_eq (f a1); intro Ha1; rewrite Ha1 in Hl; injection Hl; clear Hl; do 2 intro; subst l1 l2.
  + simpl; apply (Pcons a1 a1 nil (k1 ++ k2)); [apply refl_equal | ].
    simpl; apply IHl; apply Kl.
  + apply Pcons; [apply refl_equal | ].
    apply IHl; apply Kl.
Qed.

Lemma partition_spec3 :
  forall (A : Type) (OA : Oeset.Rcd A) (f : A -> bool) l l1 l2, 
    partition f l = (l1, l2) -> _permut (fun x y => Oeset.compare OA x y = Eq) l (l1 ++ l2).
Proof.
intros A OA f l l1 l2 H.
generalize (partition_spec3_strong _ _ H).
apply _permut_incl.
intros a b K; subst b; apply Oeset.compare_eq_refl.
Qed.

Lemma partition_permut :
  forall (A : Type) (OA : Oeset.Rcd A) (f1 f2 : A -> bool) l,
    (forall x y, List.In x l -> Oeset.compare OA x y = Eq -> f1 x = f2 y) ->
    forall l1 l2 k k1 k2, partition f1 l = (l1, l2) -> partition f2 k = (k1, k2) ->
    _permut (fun x y => Oeset.compare OA x y = Eq) l k ->
    _permut (fun x y => Oeset.compare OA x y = Eq) l1 k1 /\  
    _permut (fun x y => Oeset.compare OA x y = Eq) l2 k2.
Proof.
intros A OA f1 f2 l; induction l as [ | a1 l]; intros Hl l1 l2 k k1 k2 Pl Pk H.
- inversion H; subst k; simpl in Pl, Pk; injection Pl; injection Pk; do 4 intro; subst.
  split; apply permut_refl.
- simpl in Pl.
  case_eq (partition f1 l); intros ll1 ll2; intro Pll; rewrite Pll in Pl.
  inversion H; clear H; subst.
  assert (Hb := sym_eq (Hl a1 b (or_introl _ (refl_equal _)) H2)).
  assert (Pk1 := partition_app1 f2 l3 (b :: l4)); rewrite Pk in Pk1.
  assert (Pk2 := partition_app2 f2 l3 (b :: l4)); rewrite Pk in Pk2.
  simpl in Pk1, Pk2; rewrite Hb in Pk1, Pk2.
  case_eq (partition f2 l3); intros l3' l3'' Hl3; rewrite Hl3 in Pk1, Pk2.
  case_eq (partition f2 l4); intros l4' l4'' Hl4; rewrite Hl4 in Pk1, Pk2.
  assert (Pkk : partition f2 (l3 ++ l4) = (l3' ++ l4', l3'' ++ l4'')).
  {
    generalize (partition_app1 f2 l3 l4); rewrite Hl3, Hl4; simpl.
    generalize (partition_app2 f2 l3 l4); rewrite Hl3, Hl4; simpl.
    destruct (partition f2 (l3 ++ l4)); simpl; do 2 intro; subst; apply refl_equal.
  }
  assert (IH := IHl (fun x y h => Hl x y (or_intror _ h)) _ _ _ _ _ Pll Pkk H4).
  destruct IH as [IH1 IH2].
  case_eq (f1 a1); intro Ha1; rewrite Ha1 in Hb, Pl, Pk1, Pk2; 
  injection Pl; clear Pl; do 2 intro; subst l1 l2; simpl in Pk1, Pk2; subst k1 k2.
  + split; [apply Pcons; [apply H2 | apply IH1] | apply IH2].
  + split; [apply IH1 | apply Pcons; [apply H2 | apply IH2]].
Qed.

Definition cartesian_product (A B C : Type) (f : A -> B -> C) l1 l2 :=
  flat_map (fun e1 => map (fun e2 => f e1 e2) l2) l1.

Lemma cartesian_product_app_1 : 
  forall (A B C : Type) (f : A -> B -> C) l1 l1' l2,
    cartesian_product f (l1 ++ l1') l2 = cartesian_product f l1 l2 ++ cartesian_product f l1' l2.
Proof.
intros A B C f l1; induction l1 as [ | a1 l1]; intros l1' l2; simpl; trivial.
- rewrite <-ass_app; apply f_equal.
  apply IHl1.
Qed.

Lemma cartesian_product_app_2 : 
  forall (A B C : Type) (f : A -> B -> C) l1 l2 l2',
    _permut eq (cartesian_product f l1 (l2 ++ l2')) (cartesian_product f l1 l2 ++ cartesian_product f l1 l2').
Proof.
intros A B C f l1; induction l1 as [ | a1 l1]; intros l2 l2'; simpl.
- constructor 1.
- apply _permut_trans with (map (fun e2 : B => f a1 e2) (l2 ++ l2') ++ 
                             (cartesian_product f l1 l2 ++ cartesian_product f l1 l2')).
  + intros; subst; trivial.
  + apply _permut_app1; [ | apply IHl1].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
  + rewrite map_app, <- 2 ass_app; apply _permut_app1.
    * split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
    * rewrite 2 ass_app; apply _permut_app2; 
        [ | apply _permut_swapp; apply _permut_refl; intros; subst; trivial].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
Qed.

Lemma permut_flat_map :
    forall (A B C : Type) (f : A -> B -> C) (lb1 : list (list A)) (lb2 : list (list B)),
      _permut eq (cartesian_product f (flat_map (fun x => x) lb1) (flat_map (fun x => x) lb2)) 
             (flat_map (fun x => x) (cartesian_product (cartesian_product f) lb1 lb2)).
Proof.
intros A B C f lb1; induction lb1 as [ | b1 lb1]; intros lb2; simpl.
- constructor 1.
- rewrite cartesian_product_app_1, flat_map_app.
  apply _permut_app; [ | apply IHlb1].
  clear lb1 IHlb1.
  revert b1; induction lb2 as [ | b2 lb2]; simpl.
  + intro b1; induction b1 as [ | x1 b1]; simpl.
    * constructor 1.
    * assumption.
  + intro b1; simpl.
    apply _permut_trans with
        (cartesian_product f b1 b2 ++
          (cartesian_product f b1 (flat_map (fun x : list B => x) lb2))).
    * intros; subst; trivial.
    * apply cartesian_product_app_2.
    * apply _permut_app1; [ | apply IHlb2].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
Qed.



