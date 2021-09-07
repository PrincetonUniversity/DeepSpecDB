(** Theory of Commutative Cancelative Monoids (CCMs) *)

Require Import Coq.Logic.Decidable.

From iris Require Export base.
From stdpp Require Export decidable.
From stdpp Require Export gmap.
From stdpp Require Import mapset.
From stdpp Require Import finite.
Require Import bst.gmap_more.

Declare Scope ccm_scope.
Delimit Scope ccm_scope with CCM.

(* Cancelable operations. *)
Class Cancelative {A} (R : relation A) (f : A → A → A) : Prop :=
  cancel x y z : R (f x y) (f x z) → R y z.

(* Partial inverse of a monoid operation. *)
Class PartialInv {A} (R: relation A) (f : A → A → A) (g : A → A → A) : Prop :=
  pinv x y : R (g (f x y) y) x.

Class CcmOp (A : Type) := ccmop : A → A → A.
Hint Mode CcmOp ! : typeclass_instances.
Instance: Params (@ccmop) 2 := {}.
Infix "+" := ccmop (at level 50, left associativity) : ccm_scope.
Notation "(+)" := ccmop (only parsing) : ccm_scope.

Class CcmOpInv (A : Type) := ccmop_inv : A → A → A.
Hint Mode CcmOpInv ! : typeclass_instances.
Instance: Params (@ccmop_inv) 2 := {}.
Infix "-" := ccmop_inv (at level 50, left associativity) : ccm_scope.
Notation "(-)" := ccmop_inv (only parsing) : ccm_scope.

Class CcmUnit (A : Type) := ccmunit : A.
Arguments ccmunit {_ _}.
Notation "0" := ccmunit : ccm_scope.

Open Scope ccm_scope.

(* Definition of CCMs *)
Class CCM (M: Type) :=
  {
    ccm_eq : EqDecision M;
    ccm_unit : CcmUnit M; (* 0 *)
    ccm_op: CcmOp M; (* (+) *)
    ccm_opinv: CcmOpInv M; (* (-) *)
    ccm_assoc : Assoc (=) ((+) : M → M → M);
    ccm_comm : Comm (=) ((+) : M → M → M);
    ccm_left_id : LeftId (=) 0 (+);
    ccm_cancel : Cancelative (=) ((+) : M → M → M);
    ccm_pinv : PartialInv (=) ((+) : M → M → M) (-);
  }.

Arguments ccm_op : simpl never.
Arguments ccm_opinv : simpl never.
(*Arguments ccm_unit : simpl never.*)
Hint Extern 0 (CcmOp _) => eapply (@ccm_op _) : typeclass_instances.
Hint Extern 0 (CcmOpInv _) => eapply (@ccm_opinv _) : typeclass_instances.
Hint Extern 0 (CcmUnit _) => eapply (@ccm_unit _) : typeclass_instances.

(** Auxiliary lemmas and type classes. *)

Instance ccm_eq_eq `{CCM A}: EqDecision A.
Proof.
  apply ccm_eq.
Defined.

Lemma ccm_right_id `{CCM M} : RightId (=) 0 (+).
Proof. intros x. etrans; [apply ccm_comm|apply ccm_left_id]. Qed.

Lemma ccm_pinv_unit `{CCM M} (x: M) : x - 0 = x.
Proof.
  rewrite <- (ccm_right_id x) at 1.
  apply ccm_pinv.
Qed.

Close Scope ccm_scope.

(** The CCM of natural numbers with addition. *)

Instance nat_op : CcmOp nat := plus.

Instance nat_opinv : CcmOpInv nat := λ x y, (x - y)%nat.

Instance nat_unit : CcmUnit nat := 0.

Instance plus_assoc: Assoc (=) nat_op.
Proof.
  unfold Assoc.
  intros.
  unfold nat_op.
  lia.
Qed.

Instance plus_comm: Comm (=) nat_op.
Proof.
  unfold Comm.
  intros.
  unfold nat_op.
  lia.
Qed.

Instance plus_leftid: LeftId (=) 0 nat_op.
Proof.
  unfold LeftId.
  intros.
  unfold nat_op.
  unfold nat_unit.
  lia.
Qed.

Instance plus_cancel: Cancelative (=) nat_op.
Proof.
  unfold Cancelative.
  intros.
  unfold nat_op in H.
  lia.
Qed.

Instance plus_pinv: PartialInv (=) nat_op nat_opinv.
Proof.
  unfold PartialInv.
  intros.
  unfold nat_op, nat_opinv.
  lia.
Qed.

Instance nat_ccm : CCM nat := { }.


(** Products of CCMs are CCMs *)

Section product.
  Context A1 A2 `{CCM A1} `{CCM A2}.

  Open Scope ccm_scope.

  Instance prod_eq: EqDecision (A1 * A2).
  Proof.
    apply prod_eq_dec.
  Defined.

  Instance prod_op : CcmOp (A1 * A2) := λ x y, (x.1 + y.1, x.2 + y.2).

  Instance prod_op_inv : CcmOpInv (A1 * A2) := λ x y, (x.1 - y.1, x.2 - y.2).

  Instance prod_unit: CcmUnit (A1 * A2) := (0, 0).

  Instance prod_comm: Comm (=) prod_op.
  Proof.
    unfold Comm, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    f_equal.
    all: apply ccm_comm.
  Defined.

  Instance prod_assoc: Assoc (=) prod_op.
  Proof.
    unfold Assoc, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct z as [z1 z2].
    f_equal.
    all: apply ccm_assoc.
  Defined.

  Instance prod_leftid: LeftId (=) 0 prod_op.
  Proof.
    unfold LeftId, prod_op, prod_unit.
    intros.
    destruct x as [x1 x2].
    f_equal.
    all: apply ccm_left_id.
  Defined.

  Instance prod_cancel: Cancelative (=) prod_op.
  Proof.
    unfold Cancelative, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct z as [z1 z2].
    inversion H1.
    f_equal.
    - generalize H3.
      apply ccm_cancel.
    - generalize H4.
      apply ccm_cancel.
  Defined.

  Instance prod_pinv: PartialInv (=) prod_op prod_op_inv.
  Proof.
    unfold PartialInv, prod_op, prod_op_inv.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    f_equal.
    all: simpl; apply ccm_pinv.
  Defined.

  Global Instance prod_ccm : CCM (A1 * A2) := { }.

End product.

(** Unique representations of non-zero maps over CCMs *)

Open Scope ccm_scope.

Definition nzmap_wf `{Countable K} `{CCM A} : gmap K A → Prop :=
  map_Forall (λ _ x, ¬ (x = 0)).

Instance nzmap_wf_decision K `{Countable K} `{CCM A} (m: gmap K A) : Decision (nzmap_wf m).
Proof.
  solve_decision.
Qed.

Lemma empty_nzmap_wf `{Countable K} `{CCM A} : nzmap_wf (∅ : gmap K A).
Proof.
  unfold nzmap_wf, map_Forall.
  intros.
  rewrite lookup_empty in H1.
  inversion H1.
Qed.

(* The type of non-zero maps over CCMs *)
Record nzmap K `{Countable K} A `{CCM A} :=
  NZMap {
      nzmap_car : gmap K A;
      nzmap_prf : bool_decide (nzmap_wf nzmap_car)
    }.

Arguments NZMap {_ _ _ _ _} _ _ : assert.
Arguments nzmap_car {_ _ _ _ _} _ : assert.

(* Lift some common operations from gmaps to nzmaps. *)

Instance nzmap_lookup `{Countable K} `{CCM A} : Lookup K A (nzmap K A) :=
  λ i m, let (m, _) := m in m !! i.

Definition nzmap_total_lookup `{Countable K} `{CCM A} i (m : nzmap K A) := default 0 (m !! i).

Notation "m ! i" := (nzmap_total_lookup i m) (at level 20).

Instance nzmap_dom `{Countable K} `{CCM A} : Dom (nzmap K A) (gset K) :=
  λ m, dom (gset K) (nzmap_car m).

Definition nzmap_unit `{Countable K} `{CCM A} := NZMap (∅ : gmap K A) (bool_decide_pack _ empty_nzmap_wf).

Instance nzmap_empty `{Countable K} `{CCM A} : Empty (nzmap K A) := nzmap_unit.

Lemma nzmap_is_wf `{Countable K} `{CCM A} (m : nzmap K A) : nzmap_wf (nzmap_car m).
Proof.
  destruct m.
  simpl.
  unfold bool_decide in nzmap_prf0.
  destruct nzmap_wf_decision eqn:?.
  all: naive_solver.
Qed.

Lemma nzmap_eq `{Countable K} `{CCM A} (m1 m2 : nzmap K A) :
  m1 = m2 ↔ ∀ k, m1 ! k = m2 ! k.
Proof.
  split; [by intros ->|intros].
  assert (nzmap_car m1 = nzmap_car m2).
  { pose proof (nzmap_is_wf m1) as Hm1_wf.
    pose proof (nzmap_is_wf m2) as Hm2_wf.
    destruct m1, m2; simplify_eq/=.
    apply map_eq.
    intros k.
    pose proof (H1 k) as Hk.
    unfold nzmap_wf, map_Forall in Hm1_wf, Hm2_wf.
    pose proof (Hm1_wf k) as Hm1_wf.
    pose proof (Hm2_wf k) as Hm2_wf.
    unfold nzmap_total_lookup, lookup, nzmap_lookup in Hk.
    destruct (nzmap_car0 !! k) eqn:?, (nzmap_car1 !! k) eqn:?; simplify_eq/=;
             try reflexivity.
    - pose proof (Hm1_wf 0) as Hm1_wf.
      naive_solver.
    - pose proof (Hm2_wf 0) as Hm2_wf.
      naive_solver.
  }
  destruct m1, m2; simplify_eq/=.
  f_equal.
  apply proof_irrel.
Qed.

Lemma nzmap_gmap_eq `{Countable K} `{CCM A} (m1 m2 : nzmap K A) :
  m1 = m2 ↔ nzmap_car m1 = nzmap_car m2.
Proof.
  split; [by intros ->|intros]. destruct m1, m2; simplify_eq/=.
  f_equal. apply proof_irrel.
Qed.

Instance nzmap_eq_eq `{Countable K} `{CCM A} : EqDecision (nzmap K A).
Proof.
  refine (λ m1 m2, cast_if (decide (nzmap_car m1 = nzmap_car m2)));
  try abstract (by rewrite nzmap_gmap_eq).
Defined.

Definition nzmap_merge_op `{CCM A} (f : A → A → A) :=
  λ (o1 o2 : option A),
  match o1, o2 with
    None, None => None
  | _, _ =>
    let r := f (default 0 o1) (default 0 o2) in
    if (decide (0 = r)) then None else Some r
  end.

Lemma nzmap_diag_merge_op `{CCM A} (f : A → A → A) :
  nzmap_merge_op f None None = None.
Proof.
  auto.
Qed.

Lemma nzmap_merge_wf `{Countable K} `{CCM A}
      (f : A → A → A) (m1 m2 : gmap K A) :
  nzmap_wf m1 → nzmap_wf m2 → nzmap_wf (merge (nzmap_merge_op f) m1 m2).
Proof.
  unfold nzmap_wf. unfold map_Forall.
  intros Hm1 Hm2 k x Hm.
  rewrite lookup_merge in Hm.
  unfold nzmap_merge_op in Hm.
  unfold diag_None in Hm.
  destruct (m1 !! _), (m2 !! _);
    try destruct (decide (0 = _)) eqn:?;
        naive_solver.
Qed.

Definition nzmap_merge `{Countable K} `{CCM A} :=
  λ (f : A → A → A)  (m1 m2 : nzmap K A),
    let (m1, Hm1) := m1 in
    let (m2, Hm2) := m2 in
    NZMap (merge (nzmap_merge_op f) m1 m2) (bool_decide_pack _ (nzmap_merge_wf f _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).


Definition nzmap_imerge_op `{Countable K} `{CCM A} (f : K → A → A → A) :=
  λ k (o1 o2 : option A),
  match o1, o2 with
    None, None => None
  | _, _ =>
    let r := f k (default 0 o1) (default 0 o2) in
    if (decide (0 = r)) then None else Some r
  end.

Lemma nzmap_diag_imerge_op `{Countable K} `{CCM A} (k: K) (f : K → A → A → A) :
  nzmap_imerge_op f k None None = None.
Proof.
  auto.
Qed.

Lemma nzmap_imerge_wf `{Countable K} `{CCM A}
      (f : K → A → A → A) (m1 m2 : gmap K A) :
  nzmap_wf m1 → nzmap_wf m2 → nzmap_wf (imerge (nzmap_imerge_op f) m1 m2).
Proof.
  unfold nzmap_wf. unfold map_Forall.
  intros Hm1 Hm2 k x Hm.
  rewrite gmap_imerge_prf in Hm.
  unfold nzmap_imerge_op in Hm.
  destruct (m1 !! _), (m2 !! _);
    try destruct (decide (0 = _)) eqn:?;
        naive_solver.
  intros. apply nzmap_diag_imerge_op.
Qed.

Definition nzmap_imerge `{Countable K} `{CCM A} :=
  λ (f : K → A → A → A)  (m1 m2 : nzmap K A),
    let (m1, Hm1) := m1 in
    let (m2, Hm2) := m2 in
    NZMap (imerge (nzmap_imerge_op f) m1 m2) (bool_decide_pack _ (nzmap_imerge_wf f _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).


Lemma nzmap_lookup_wf `{Countable K} `{CCM A} (m : gmap K A) i : nzmap_wf m → m !! i <> Some 0.
Proof.
  intros.
  unfold nzmap_wf, map_Forall in H0.
  firstorder.
Qed.


Lemma nzmap_elem_of_dom `{Countable K} `{CCM A} (m : nzmap K A) i : i ∈ dom (gset K) m ↔ is_Some (m !! i).
Proof.
  unfold dom, nzmap_dom.
  rewrite elem_of_dom.
  unfold lookup at 2, nzmap_lookup.
  unfold nzmap_car.
  destruct m.
  naive_solver.
Qed.

Lemma nzmap_elem_of_dom_total `{Countable K} `{CCM A} (m : nzmap K A) i : i ∈ dom (gset K) m ↔ m ! i <> 0.
Proof.
  pose proof (nzmap_is_wf m) as m_wf.
  unfold nzmap_total_lookup, default.
  split.
  - intro.
    apply nzmap_elem_of_dom in H1.
    unfold is_Some in H1.
    destruct H1 as [x ?].
    rewrite H1.
    apply (nzmap_lookup_wf (nzmap_car m) i) in m_wf.
    unfold lookup, nzmap_lookup in H1.
    destruct m. simpl in m_wf.
    unfold id.
    rewrite H1 in m_wf.
    naive_solver.
  - intros.
    rewrite nzmap_elem_of_dom.
    destruct (m !! i).
    naive_solver.
    contradiction.
Qed.

Lemma nzmap_empty_lookup `{Countable K} `{CCM A} (m: nzmap K A) : m <> ∅ ↔ ∃ i, m ! i <> 0.
Proof.
  pose proof (nzmap_is_wf m).
  split.
  - intros.
    destruct m.
    rewrite nzmap_gmap_eq in H2 *; intros; simpl in H1.
    unfold empty in H2.
    unfold nzmap_empty, nzmap_unit in H2.
    simpl in H2.
    apply map_choose in H2.
    destruct H2 as [i [x H2]].
    pose proof (nzmap_lookup_wf nzmap_car0 i).
    apply H3 in H1.
    exists i.
    unfold nzmap_total_lookup.
    unfold default, lookup, nzmap_lookup.
    rewrite H2.
    naive_solver.
  - naive_solver.
Qed.

Lemma nzmap_lookup_empty `{Countable K} `{CCM A} i : (∅ : nzmap K A) ! i = 0.
Proof.
  unfold empty, nzmap_empty, nzmap_unit.
  unfold nzmap_total_lookup, lookup, nzmap_lookup.
  rewrite lookup_empty.
  auto.
Qed.


Class UnitId A `(CCM A) (f : A → A → A) : Prop :=
  unit_id : f 0 0 = 0.

Instance ccm_op_unit_id `{CCM A} : UnitId A _ (+).
Proof.
  unfold UnitId.
    by rewrite ccm_left_id.
Defined.

Instance lift_opinv_unit_id `{CCM A} : UnitId A _ (-).
Proof.
  unfold UnitId.
  rewrite <- (ccm_right_id 0) at 1.
    by rewrite ccm_pinv.
Defined.


Lemma nzmap_lookup_merge `{Countable K} `{UnitId A f} (m1 m2 : nzmap K A) (k : K) :
  nzmap_merge f m1 m2 ! k = f (m1 ! k) (m2 ! k).
Proof.
  unfold nzmap_merge, nzmap_total_lookup, lookup, nzmap_lookup.
  destruct m1, m2.
  unfold nzmap_merge_op.
  rewrite lookup_merge.
  destruct (nzmap_car0 !! _) eqn:?,
           (nzmap_car1 !! _) eqn:?;
           simpl;
    try destruct (decide (0 = _));
    try rewrite <- e;
    simpl;
    try reflexivity.
  unfold UnitId in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma nzmap_lookup_imerge `{Countable K} `{CCM A} `{∀ k : K, UnitId A _ (f k)} (m1 m2 : nzmap K A) (k : K) :
  nzmap_imerge f m1 m2 ! k = f k (m1 ! k) (m2 ! k).
Proof.
  unfold nzmap_imerge, nzmap_total_lookup, lookup, nzmap_lookup.
  destruct m1, m2.
  unfold nzmap_imerge_op.
  rewrite gmap_imerge_prf.
  destruct (nzmap_car0 !! _) eqn:?,
           (nzmap_car1 !! _) eqn:?;
           simpl;
    try destruct (decide (0 = _));
    try rewrite <- e;
    simpl;
    try reflexivity.
  unfold UnitId in H1.
  rewrite H1.
  reflexivity.
  now intros.
Qed.

Lemma nzmap_imerge_empty {A} `{Countable K} `{CCM A} `{∀ k : K, UnitId A _ (f k)}
      : (∀ i y, f i y 0 = y) -> ∀ m, nzmap_imerge f m ∅ = m.
Proof.
  intros.
  apply nzmap_eq.
  intros.
  rewrite nzmap_lookup_imerge.
  unfold nzmap_total_lookup at 2.
  unfold lookup, nzmap_lookup, empty, nzmap_empty, nzmap_unit.
  rewrite lookup_empty. simpl.
  auto.
Qed.


Close Scope ccm_scope.

(** Lifting any CCM A to functions f: K → A yields a CCM. Here, we assume that f k ≠ 0 for finitely many k. Moreover, K must be countable. *)

Section lifting.
  Context K `{Countable K} A `{CCM A}.

  Open Scope ccm_scope.

  (* To obtain unique representations, we represent functions f: K → A
   * as g: gmap K A where f k = 0 ↔ g !! k = None *)

  Global Instance lift_unit : CcmUnit (nzmap K A) := nzmap_unit.

  (* Lift CCM operations on A to (nzmap K A) *)

  Instance lift_op : CcmOp (nzmap K A) := λ m1 m2,
    nzmap_merge (+) m1 m2.

  Instance lift_opinv : CcmOpInv (nzmap K A) := λ m1 m2,
    nzmap_merge (-) m1 m2.

  (* Prove that this yields again a CCM *)

  Instance lift_comm: Comm (=) lift_op.
  Proof.
    unfold Comm, lift_op.
    intros.
    apply nzmap_eq.
    intros.
    repeat rewrite nzmap_lookup_merge.
    apply ccm_comm.
  Qed.

  Instance lift_assoc: Assoc (=) lift_op.
  Proof.
    unfold Assoc, lift_op.
    intros.
    apply nzmap_eq.
    intros.
    repeat rewrite nzmap_lookup_merge.
    apply ccm_assoc.
  Defined.

  Instance lift_leftid: LeftId (=) 0 lift_op.
  Proof.
    unfold LeftId, lift_op.
    intros.
    rewrite nzmap_eq.
    intros.
    rewrite nzmap_lookup_merge.
    apply ccm_left_id.
  Defined.

  Instance lift_cancel: Cancelative (=) lift_op.
  Proof.
    unfold Cancelative, lift_op.
    intros.
    apply nzmap_eq.
    intros.
    rewrite nzmap_eq in H1 *.
    intros.
    pose proof (H1 k).
    repeat rewrite nzmap_lookup_merge in H2.
    apply ccm_cancel in H2.
    trivial.
  Defined.

  Instance lift_pinv: PartialInv (=) lift_op lift_opinv.
  Proof.
    unfold PartialInv.
    intros.
    apply nzmap_eq.
    intros.
    repeat rewrite nzmap_lookup_merge.
    apply ccm_pinv.
  Defined.

  Global Program Instance lift_ccm : CCM (nzmap K A) := { }.

  Implicit Types m : nzmap K A.

  (* The monoid operation distributes over lookup. *)
  Lemma lookup_op m1 m2 i : (m1 + m2) ! i = m1 ! i + m2 ! i.
  Proof.
    unfold ccm_op,ccmop at 1.
    unfold lift_op.
    apply nzmap_lookup_merge.
  Qed.

  Global Opaque nzmap_empty.
End lifting.

Arguments NZMap {_ _ _ _ _} _ _ : assert.
Arguments nzmap_car {_ _ _ _ _} _ : assert.
Arguments nzmap_total_lookup {_ _ _ _ _} _ _ : assert.

Section fold_right_ccm.

  Context A `{CCM A}.

  Open Scope ccm_scope.

  Lemma accumulate_perm: forall {B} (f: B -> A) init (l1 l2: list B),
      Permutation l1 l2 ->
      fold_right (fun x v => f x + v) init l1 =
      fold_right (fun x v => f x + v) init l2.
  Proof.
    intros. induction H0; simpl; auto.
    - now rewrite IHPermutation.
    - rewrite !ccm_assoc. now rewrite (ccm_comm (f y) (f x)).
    - now transitivity (fold_right (fun x v => f x + v) init l').
  Qed.

  Close Scope ccm_scope.

End fold_right_ccm.
