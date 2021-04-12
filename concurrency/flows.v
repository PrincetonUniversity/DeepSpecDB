(** Theory of Flow Interface *)

(* This formalization builds on the paper:

   Local Reasoning for Global Graph Properties: Siddharth Krishna and Alexander J. Summers and Thomas Wies, ESOP'20.
*)

(*From iris.heap_lang Require Import proofmode.*)
Require Export VST.veric.bi.
Require Import VST.progs.ghosts.

From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
From bst Require Export ccm gmap_more.
Require Import Coq.Setoids.Setoid.
Require Import bst.sepalg_ext.

Class Valid (A : Type) := valid : A → Prop.
Hint Mode Valid ! : typeclass_instances.
Instance: Params (@valid) 2 := {}.
Notation "✓ x" := (valid x) (at level 20) : stdpp_scope.

(* The set of nodes over which graphs are built. *)
(* Definition Node := nat. *)

Section flowint.

  Context `{HC: Countable Node}.

  (* The underlying flow domain. *)
  Context `{CCM flowdom}.

  Open Scope ccm_scope.

  (* Representation of flow interfaces:

     - The domain of the interface is the domain of its inflow infR.

     - The outflow function is defined using nzmap so that interface
       composition is cancelable.*)

  Record flowintR := {
    infR : gmap Node flowdom;
    outR : nzmap Node flowdom; }.

  (* The empty interface *)
  Definition I_emptyR := {| infR := ∅; outR := ∅ |}.
  Global Instance flowint_empty : Empty flowintR := I_emptyR.

  Definition inf (I: flowintR) (n: Node) := default 0 (infR I !! n).
  Definition out (I: flowintR) (n: Node) := outR I ! n.

  Global Instance flowint_dom : Dom flowintR (gset Node) :=
    λ I, dom (gset Node) (infR I).
  Definition domm (I : flowintR) := dom (gset Node) I.

  Global Instance flowint_elem_of : ElemOf Node flowintR := λ n I, n ∈ domm I.

  (* Some useful implicit type classes *)

  Canonical Structure flowintRAC := leibnizO flowintR.

  Global Instance int_eq_dec: EqDecision flowintR.
  Proof.
    unfold EqDecision.
    unfold Decision.
    repeat decide equality.
    - apply nzmap_eq_eq.
    - apply gmap_eq_eq.
  Qed.

  (** Interface validity *)

  Global Instance flowint_valid : Valid flowintR :=
    λ Ir, infR Ir ##ₘ nzmap_car (outR Ir) ∧ (infR Ir = ∅ → outR Ir = ∅).

  Global Instance flowint_valid_dec : ∀ I: flowintR, Decision (✓ I).
  Proof.
    intros.
    unfold valid; unfold flowint_valid.
    destruct I.
    all: solve_decision.
  Qed.

  (** Predicate that holds true iff two interfaces are composable *)

  Definition intComposable (I1: flowintR) (I2: flowintR) :=
    ✓ I1 ∧ ✓ I2 ∧
    domm I1 ## domm I2 ∧
    map_Forall (λ (n: Node) (m: flowdom), m = out I2 n +
                                              (inf I1 n - out I2 n)) (infR I1) ∧
    map_Forall (λ (n: Node) (m: flowdom), m = out I1 n +
                                              (inf I2 n - out I1 n)) (infR I2).

  Global Instance intComposable_dec (I1 I2: flowintR) : Decision (intComposable I1 I2).
  Proof. solve_decision. Qed.

  (** Interface composition *)

  (* Function to compute outflow of composite interface *)
  Definition outComp_op I1 I2 n (m1 m2 : flowdom) :=
    if decide (n ∈ domm I1 ∪ domm I2) then 0 else m1 + m2.

  Global Instance outComp_unit_id : ∀ n I1 I2, UnitId _ _ (outComp_op I1 I2 n).
  Proof.
    intros.
    unfold UnitId, outComp_op.
    destruct (decide _).
    all: auto using ccm_right_id.
  Qed.

  Definition outComp I1 I2 :=
    nzmap_imerge (outComp_op I1 I2) (outR I1) (outR I2).

  Lemma outComp_inv I1 I2 :
    ∀ n, n ∉ domm I1 ∪ domm I2 → outComp I1 I2 ! n = out I1 n + out I2 n.
  Proof.
    intros n D.
    unfold outComp.
    rewrite nzmap_lookup_imerge.
    unfold outComp_op.
    destruct (decide _).
    - contradiction.
    - unfold out.
      reflexivity.
  Qed.

  (* Function to compute inflow of composite interface *)
  Definition infComp_op I1 I2 n (o1 o2 : option flowdom) :=
    match o1, o2 with
    | Some m1, _ => Some (m1 - out I2 n)
    | _, Some m2 => Some (m2 - out I1 n)
    | _, _ => None
    end.

  Global Instance infComp_diag_none : ∀ I1 I2 n, DiagNone (infComp_op I1 I2 n).
  Proof.
    intros.
    unfold DiagNone, infComp_op.
    auto.
  Defined.

  Definition infComp I1 I2 := gmap_imerge (infComp_op I1 I2) (infR I1) (infR I2).

  Definition intComp (I1 I2: flowintR): option flowintR :=
    if decide (intComposable I1 I2) then
      Some {| infR := infComp I1 I2 ; outR := outComp I1 I2 |}
    else if decide (I1 = ∅) then Some I2
         else if decide (I2 = ∅) then Some I1
              else None.

  Global Instance intJoin: sepalg.Join flowintR :=
    λ I1 I2 I3, intComp I1 I2 = Some I3.

  (** Assorted auxiliary lemmas. These are used, in particular, to
  prove that flow interfaces form a ghost. *)

  (* The empty interface has no outflow. *)
  Lemma intEmp_out : ∀ n, out I_emptyR n = 0.
  Proof.
    intros.
    unfold out, I_emptyR.
    simpl.
    apply nzmap_lookup_empty.
  Qed.

  (* Valid interfaces don't give outflow to nodes in their domain. *)
  Lemma intValid_in_dom_not_out : ∀ I n, ✓ I → n ∈ domm I → out I n = 0.
  Proof.
    intros ? ? V D.
    unfold valid, flowint_valid in V.
    destruct V as (Disj & _).
    assert (dom (gset Node) (infR I) ## dom (gset Node) (nzmap_car (outR I))). {
      apply map_disjoint_dom. trivial. }
    unfold domm, dom, flowint_dom in D.
    assert (n ∉ dom (gset Node) (outR I)). {
      unfold dom, nzmap_dom.
      set_solver. }
    rewrite nzmap_elem_of_dom_total in H1 *.
    intros.
    apply dec_stable in H1.
    trivial.
  Qed.

  (* The empty interface is valid. *)
  Lemma intEmp_valid : ✓ I_emptyR.
  Proof.
    unfold valid.
    unfold flowint_valid.
    simpl.
    split.
    refine (map_disjoint_empty_l _).
    trivial.
  Qed.

  (* The empty interface is the unique valid interface whose domain is empty. *)
  Lemma intEmp_unique I : ✓ I → domm I ≡ ∅ → I = ∅.
  Proof.
    intros V D.
    unfold valid, flowint_valid in V.
    destruct V as (? & V).
    unfold domm, dom, flowint_dom in D.
    unfold empty, flowint_empty.
    unfold I_emptyR.
    destruct I as [Iinf Iout].
    simpl in V.
    simpl in D.
    apply (dom_empty_inv Iinf) in D.
    pose proof (V D) as O.
    rewrite D.
    rewrite O.
    reflexivity.
  Qed.

  (* Invalid interfaces are not composable. *)
  Lemma intComposable_invalid : ∀ I1 I2, ¬ ✓ I1 → ¬ (intComposable I1 I2).
  Proof.
    intros.
    unfold intComposable.
    unfold not.
    intros H_false.
    destruct H_false as [H_false _].
    now contradict H_false.
  Qed.

  (* Composing with an invalid interface yields an invalid interface. *)
  Lemma intJoin_invalid : ∀ I1 I2 I3: flowintR,
      intJoin I1 I2 I3 -> ¬ ✓ I1 → ¬ ✓ I3.
  Proof.
    intros.
    unfold intJoin, intComp in H0.
    rewrite decide_False in H0; last by apply intComposable_invalid.
    rewrite decide_False in H0; last first.
    - unfold not. intros H_false.
      contradict H1. rewrite H_false. apply intEmp_valid.
    - destruct (decide (I2 = ∅)); inversion H0. now subst.
  Qed.

  (* The empty interface is the right identity of interface composition. *)
  Lemma intJoin_unit : ∀ (I: flowintR), intJoin I I_emptyR I.
  Proof.
    intros.
    unfold intJoin, intComp, outComp.
    simpl.
    destruct (decide (intComposable I I_emptyR)).
    - (* True *)
      unfold infComp.
      rewrite gmap_imerge_empty.
      + f_equal.
        destruct I.
        f_equal.
        apply nzmap_eq.
        intros.
        rewrite nzmap_lookup_imerge.
        unfold outComp_op.
        destruct (decide _).
        * unfold domm in e.
          rewrite elem_of_union in e *.
          intros.
          destruct H0.
          -- unfold intComposable in i.
             destruct i as (V & _).
             unfold valid, flowint_valid in V.
             destruct V as (V & _).
             simpl in V.
             assert (dom (gset Node) infR0 ## dom (gset Node) (nzmap_car outR0)). {
               rewrite <- map_disjoint_dom. trivial. }
             unfold flowint_dom in H0.
             simpl in H0.
             unfold nzmap_total_lookup.
             destruct (outR0 !! k) eqn:?.
             ++ assert (k ∈ dom (gset Node) outR0). {
                  unfold dom, nzmap_dom.
                  rewrite elem_of_dom.
                  unfold is_Some.
                  exists f.
                  unfold lookup, nzmap_lookup in Heqo.
                  destruct outR0.
                  simpl.
                  trivial. }
                assert (k ∉ dom (gset Node) outR0). {
                  set_solver. }
                contradiction.
             ++ trivial.
          -- unfold dom, flowint_dom, I_emptyR in H0. simpl in H0.
             rewrite dom_empty in H0 *.
             intros.
             rewrite elem_of_empty in H0 *.
             naive_solver.
        * rewrite nzmap_lookup_empty.
          rewrite ccm_right_id. auto.
      + intros.
        case y.
        * intros.
          unfold infComp_op.
          rewrite intEmp_out.
            by rewrite ccm_pinv_unit.
        * auto.
    - (* False *)
      destruct (decide _).
      unfold empty, flowint_empty in e.
      rewrite e.
      reflexivity.
      destruct (decide _).
      reflexivity.
      unfold empty, flowint_empty in n1.
      contradiction.
  Qed.

  (* The intComposable predicate is commutative. *)
  Lemma intComposable_comm_1 : ∀ (I1 I2 : flowintR),
      intComposable I1 I2 → intComposable I2 I1.
  Proof.
    intros.
    unfold intComposable.
    repeat split.
    5: apply disjoint_intersection; rewrite intersection_comm_L;
      apply disjoint_intersection.
    unfold intComposable in H0.
    all: try apply H0.
  Qed.

  Lemma intComposable_comm : ∀ (I1 I2 : flowintR),
      intComposable I1 I2 ↔ intComposable I2 I1.
  Proof.
    intros. split. all: refine (intComposable_comm_1 _ _).
  Qed.

  (* The domain of a composite interface is the union of the domain of
  its component interfaces. *)

  Lemma infComp_dom : ∀ I1 I2, dom (gset Node) (infComp I1 I2) = domm I1 ∪ domm I2.
  Proof.
    intros.
    unfold domm.
    set_unfold.
    intros.
    rewrite ?elem_of_dom.
    unfold infComp.
    rewrite gmap_imerge_prf.
    unfold dom, flowint_dom.
    repeat rewrite elem_of_dom.
    unfold infComp_op.
    case_eq (infR I1 !! x).
    + intros ? H1.
      (*rewrite H1.*)
      rewrite ?is_Some_alt; simpl.
      naive_solver.
    + intros H1.
      (*rewrite H1.*)
      case_eq (infR I2 !! x).
      * intros ? H2.
        (*rewrite H2.*)
        rewrite ?is_Some_alt; simpl.
        naive_solver.
      * intros H2.
        (*rewrite H2.*)
        split.
        apply or_introl.
        intros.
        destruct H.
        all: clear - H0; firstorder.
  Qed.

  Lemma intJoin_dom : ∀ I1 I2 I3,
      intJoin I1 I2 I3 -> ✓ I3 → domm I3 = domm I1 ∪ domm I2.
  Proof.
    intros I1 I2 I3 Hi H_valid.
    unfold intJoin, intComp in Hi.
    destruct (decide (intComposable I1 I2)).
    - inversion Hi. subst I3. clear Hi.
      unfold domm at 1, dom, flowint_dom. simpl.
        by rewrite infComp_dom.
    - unfold domm.
      set_unfold.
      intros.
      unfold dom.
      rewrite ?elem_of_dom.
      destruct (decide (I1 = ∅)).
      + inversion Hi. subst I3. clear Hi. subst I1.
        simpl.
        rewrite lookup_empty.
        split; intros.
        * now apply or_intror.
        * destruct H0 as [H_false | H2]; [|easy].
          contradict H_false. exact is_Some_None.
      + destruct (decide (I2 = ∅)).
        * inversion Hi. subst I3 I2. clear Hi. simpl.
          rewrite lookup_empty.
          split; intros.
          -- now apply or_introl.
          -- destruct H0; [easy|].
             contradict H0. exact is_Some_None.
        * inversion Hi.
  Qed.

  (* Interface composition is commutative. *)
  Lemma intJoin_comm : ∀ (I1 I2 I3: flowintR), intJoin I1 I2 I3 -> intJoin I2 I1 I3.
  Proof.
    intros.
    unfold intJoin, intComp, infComp, outComp in *.
    destruct (decide (intComposable I1 I2)) as [H_comp | H_not_comp].
    - (* if composable *)
      inversion H0. subst I3. clear H0.
      rewrite decide_True; last rewrite intComposable_comm; auto.
      f_equal.
      f_equal.
      + (* infR equality *)
        rewrite map_eq_iff.
        intros.
        repeat rewrite gmap_imerge_prf; auto.
        case_eq (infR I1 !! i).
        all: case_eq (infR I2 !! i).
        * (* i in both *)
          intros f1 H_lookup2 f2 H_lookup1.
          exfalso.
          generalize H_comp.
          unfold intComposable.
          intros (_ & _ & H_false & _).
          unfold domm, dom, flowint_dom in H_false.
          simpl in *.
          rewrite <- map_disjoint_dom in H_false.
          generalize H_false. clear H_false.
          rewrite map_disjoint_alt.
          intros H_false.
          assert (H_contra := H_false i).
          destruct H_contra.
          contradict H0.
          now rewrite H_lookup1.
          contradict H0.
          now rewrite H_lookup2.
        * (* in I1 but not in I2 *)
          intros H_lookup2 f1 H_lookup1.
          (*rewrite H_lookup1. rewrite H_lookup2.*)
          auto.
        * (* in I2 but not in I1 *)
          intros f2 H_lookup2 H_lookup1.
          (*rewrite H_lookup1. rewrite H_lookup2.*)
          auto.
        * (* in neither *)
          intros H_lookup2 H_lookup1.
          (*rewrite H_lookup1. rewrite H_lookup2.*)
          auto.
      + (* outR equality *)
        apply nzmap_eq.
        intros.
        repeat rewrite nzmap_lookup_imerge.
        unfold outComp_op.
        pose proof (union_comm (domm I1) (domm I2)).
        repeat destruct (decide (k ∈ _)); try auto;
          try (rewrite H0 in e *; naive_solver).
        try (rewrite H0 in n *; naive_solver).
          by rewrite ccm_comm.
    - (* if not composable *)
      rewrite decide_False; last by rewrite intComposable_comm.
      rewrite <- H0.
      case_eq (decide (I2 = ∅)).
      case_eq (decide (I1 = ∅)).
      all: auto.
      intros.
      now rewrite e e0.
  Qed.

  (* The empty interface is also a left identity of interface composition. *)
  Lemma intJoin_left_unit : ∀ I : flowintR, intJoin I_emptyR I I.
  Proof.
    intros.
    apply intJoin_comm.
    now apply intJoin_unit.
  Qed.

  (* The components of valid composite interfaces are valid. *)
  Lemma intJoin_valid_proj1 : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> ✓ I3 → ✓ I1.
  Proof.
    intros I1 I2 I3 ?.
    rewrite <- Decidable.contrapositive.
    intros. apply intJoin_invalid in H0; auto.
    unfold Decidable.decidable.
    generalize (flowint_valid_dec I1).
    unfold Decision.
    intros.
    destruct H1.
    all: auto.
  Qed.

  Lemma intJoin_valid_proj2 : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> ✓ I3 → ✓ I2.
  Proof.
    intros I1 I2 I3 ?.
    apply intJoin_comm in H0.
    intros; now apply intJoin_valid_proj1 in H0.
  Qed.

  (* If a composite interface is empty then its components must have been empty. *)
  Lemma intJoin_positive_1 : ∀ (I1 I2: flowintR), intJoin I1 I2 ∅ → I1 = ∅.
  Proof.
    intros ? ? C.
    pose proof intEmp_valid as V.
    unfold empty, flowint_empty in C.
    pose proof (intJoin_valid_proj1 _ _ _ C V) as V1.
    pose proof (intJoin_valid_proj2 _ _ _ C V) as V2.
    assert (infR I1 = ∅) as D1. {
      apply map_eq.
      intros n.
      unfold intJoin, intComp in C.
      destruct (decide (intComposable I1 I2)).
      - inversion C.
        assert (infComp I1 I2 !! n = infR I_emptyR !! n) as CL. {
          rewrite H1. now simpl. } simpl in CL.
        rewrite gmap_imerge_prf in CL.
        rewrite H1 lookup_empty.
        rewrite lookup_empty in CL.
        destruct (infR I1 !! n);
          destruct (infR I2 !! n);
          inversion CL.
        reflexivity.
      - destruct (decide (I1 = ∅)).
        + rewrite e.
          unfold empty at 1, flowint_empty, I_emptyR.
          simpl. reflexivity.
        + destruct (decide (I2 = ∅)).
          * unfold empty, flowint_empty in n1.
            exfalso. apply n1. now inversion C.
          * inversion C. }
    assert (domm I1 ≡ ∅).
    unfold domm, dom, flowint_dom.
    rewrite D1.
    rewrite dom_empty.
    reflexivity.
    pose proof (intEmp_unique _ V1 H0).
    trivial.
  Qed.

  Lemma intJoin_positive_2 : ∀ (I1 I2: flowintR), intJoin I1 I2 ∅ → I2 = ∅.
  Proof.
    intros ? ? C.
    apply intJoin_comm in C.
    now apply intJoin_positive_1 in C.
  Qed.

  (* The empty interface is composable with any valid interface. *)
  Lemma intComposable_empty : ∀ I: flowintR, ✓ I → intComposable ∅ I.
  Proof.
    intros I IV.
    unfold intComposable. destruct IV.
    repeat split; auto.
    - unfold domm, dom, flowint_dom, empty, flowint_empty, I_emptyR. simpl.
      rewrite dom_empty.
      apply disjoint_empty_l.
    - unfold map_Forall.
      intros n x.
      unfold empty, flowint_empty, I_emptyR. simpl.
      rewrite lookup_empty.
      intros.
      inversion H2.
    - unfold map_Forall.
      intros n x.
      intros.
      unfold out, empty, flowint_empty, I_emptyR. simpl.
      rewrite nzmap_lookup_empty.
      rewrite ccm_left_id.
      rewrite ccm_pinv_unit.
      unfold inf.
      rewrite H2.
      auto.
  Qed.

  (* The components of valid composite interfaces are composable. *)
  Lemma intComposable_valid : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> ✓ I3 → intComposable I1 I2.
  Proof.
    intros I1 I2 I3 Hj IV.
    pose proof (intJoin_valid_proj1 I1 I2 _ Hj IV) as I1V.
    pose proof (intJoin_valid_proj2 I1 I2 _ Hj IV) as I2V.
    unfold intJoin, intComp in Hj.
    destruct (decide (intComposable I1 I2)). 1: trivial.
    destruct (decide (I1 = ∅)).
    - subst I1. now apply intComposable_empty.
    - destruct (decide (I2 = ∅)).
      + subst I2. rewrite intComposable_comm. now apply intComposable_empty.
      + inversion Hj.
  Qed.

  (* The composition of composable interfaces is valid. *)
  Lemma intValid_composable : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> intComposable I1 I2 → ✓ I3.
  Proof.
    intros ? ? ? Hj V.
    unfold intJoin, intComp in Hj.
    destruct (decide (intComposable I1 I2)).
    - unfold valid, flowint_valid. inversion Hj. subst I3. clear Hj.
      simpl. split.
      + assert (dom (gset Node) (infComp I1 I2) ##
                    dom (gset Node) (nzmap_car (outComp I1 I2))). {
          apply elem_of_disjoint.
          intros n Hin Hout.
          rewrite infComp_dom in Hin.
          rewrite nzmap_elem_of_dom_total in Hout *.
          intros.
          unfold outComp in H0.
          rewrite nzmap_lookup_imerge in H0.
          unfold outComp_op in H0.
          destruct (decide _).
          all: contradiction. }
        apply map_disjoint_dom in H0. trivial.
      + intros.
        assert (dom (gset Node) (infComp I1 I2) ≡
                    dom (gset Node) (∅ : gmap Node flowdom)).
        rewrite H0. auto.
        apply nzmap_eq.
        intros n.
        unfold outComp.
        rewrite nzmap_lookup_imerge.
        unfold outComp_op.
        rewrite nzmap_lookup_empty.
        rewrite infComp_dom in H1.
        rewrite dom_empty in H1 *.
        intros.
        destruct (decide _). auto.
        assert (domm I1 ≡ ∅) by set_solver.
        assert (domm I2 ≡ ∅) by set_solver.
        destruct V as (V1 & V2 & _).
        unfold valid, flowint_valid in V1,V2.
        destruct V1 as (_ & E1).
        destruct V2 as (_ & E2).
        unfold domm, dom, flowint_dom in H2, H3.
        apply dom_empty_inv in H2.
        apply dom_empty_inv in H3.
        apply E1 in H2.
        apply E2 in H3.
        rewrite H2.
        rewrite H3.
        rewrite nzmap_lookup_empty.
          by rewrite ccm_right_id.
    - contradiction.
  Qed.

  (* Characterization of inflows of composite interfaces. *)
  Lemma intJoin_unfold_inf_1 : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> ✓ I3 →
      ∀ n, n ∈ domm I1 → inf I1 n = inf I3 n + out I2 n.
  Proof.
    intros I1 I2 I3 Hj V n D.
    unfold domm, dom, flowint_dom in D.
    apply elem_of_dom in D.
    unfold is_Some in D.
    destruct D as [x D].
    pose proof (intComposable_valid I1 I2 _ Hj V).
    assert (IC := H0).
    unfold intComposable in H0.
    destruct H0 as (I1v & I2v & Disjoint & I1inf & I2inf).
    unfold map_Forall in I1inf.
    pose proof (I1inf n (inf I1 n)).
    unfold inf in H0.
    rewrite D in H0.
    unfold default, id in H0.
    assert (Some x = Some x) by reflexivity.
    apply H0 in H1.
    unfold valid, flowint_valid in V.
    unfold intJoin, intComp in Hj.
    destruct (decide (intComposable I1 I2)).
    - unfold inf. inversion Hj. simpl.
      rewrite gmap_imerge_prf.
      rewrite D.
      unfold default, id.
      rewrite ccm_comm in H1.
      trivial.
    - contradiction.
  Qed.

  Lemma intJoin_unfold_inf_2 : ∀ (I1 I2 I3: flowintR),
      intJoin I1 I2 I3 -> ✓ I3 →
      ∀ n, n ∈ domm I2 → inf I2 n = inf I3 n + out I1 n.
  Proof.
    intros.
    apply intJoin_comm in H0.
    now apply intJoin_unfold_inf_1.
  Qed.

  (* Characterization of outflow of composed interfaces. *)
  Lemma intJoin_unfold_out I1 I2 I3:
    intJoin I1 I2 I3 -> ✓ I3 → (∀ n, n ∉ domm I3 → out I3 n = out I1 n + out I2 n).
  Proof.
    intros Hj ? ? ?.
    apply (intJoin_dom _ _ _ Hj) in H0 as D.
    rewrite D in H1.
    pose proof (outComp_inv I1 I2 n H1).
    apply (intComposable_valid _ _ _ Hj) in H0.
    unfold intJoin, intComp in Hj.
    unfold out at 1.
    destruct (decide (intComposable I1 I2)); last first. 1: contradiction.
    inversion Hj. simpl.
    trivial.
  Qed.

  (* Characterization of inflow of composed interfaces. *)
  Lemma intJoin_inf_1 I1 I2 I3:
    intJoin I1 I2 I3 -> ✓ I3 →
    (∀ n, n ∈ domm I1 → inf I3 n = inf I1 n - out I2 n).
  Proof.
    intros Hj V n D.
    apply (intComposable_valid _ _ _ Hj) in V.
    unfold intJoin, intComp in Hj.
    destruct (decide (intComposable I1 I2)); last first. 1: contradiction.
    inversion Hj. subst I3. clear Hj.
    unfold inf at 1.
    simpl.
    rewrite gmap_imerge_prf.
    unfold domm, dom, flowint_dom in D.
    apply elem_of_dom in D.
    unfold is_Some in D.
    destruct D as [x D].
    unfold inf at 1.
    rewrite D.
    simpl.
    reflexivity.
  Qed.

  Lemma intJoin_inf_2 I1 I2 I3:
    intJoin I1 I2 I3 -> ✓ I3 →
    (∀ n, n ∈ domm I2 → inf I3 n = inf I2 n - out I1 n).
  Proof.
    intros Hj. intros.
    apply intJoin_comm in Hj.
    generalize H1.
    generalize n.
    now apply intJoin_inf_1.
  Qed.

  (* Characterization of interface composition as defined in ESOP'20. *)
  Lemma intJoin_fold I1 I2 I :
    ✓ I1 → ✓ I2 →
    domm I1 ## domm I2 →
    domm I = domm I1 ∪ domm I2 →
    (∀ n, n ∈ domm I1 → inf I1 n = out I2 n + inf I n) →
    (∀ n, n ∈ domm I2 → inf I2 n = out I1 n + inf I n) →
    outR I = outComp I1 I2 →
    intJoin I1 I2 I ∧ ✓ I.
  Proof.
    intros V1 V2 Disj D Inf1 Inf2 Out.
    assert (intComposable I1 I2) as C.
    { unfold intComposable.
      split; [|split; [|split; [|split]]]; try trivial.
      - unfold map_Forall.
        intros n x xDef.
        unfold domm, dom, flowint_dom in Inf1.
        pose proof (Inf1 n).
        rewrite elem_of_dom in H0 *.
        intro.
        apply mk_is_Some in xDef as H1.
        apply H0 in H1.
        rewrite H1.
        rewrite (ccm_comm _ (inf I n)).
        rewrite ccm_pinv.
        unfold inf at 1 in H1.
        rewrite xDef in H1.
        simpl in H1.
        rewrite H1.
        reflexivity.
      - unfold map_Forall.
        intros n x xDef.
        unfold domm, dom, flowint_dom in Inf2.
        pose proof (Inf2 n).
        rewrite elem_of_dom in H0 *.
        intro.
        apply mk_is_Some in xDef as H1.
        apply H0 in H1.
        rewrite H1.
        rewrite (ccm_comm _ (inf I n)).
        rewrite ccm_pinv.
        unfold inf at 1 in H1.
        rewrite xDef in H1.
        simpl in H1.
        rewrite H1.
        reflexivity.
    }
    cut (intJoin I1 I2 I). {
      intros; split; auto.
      now apply (intValid_composable _ _ _ H0) in C. }
    unfold intJoin, intComp, infComp, infComp_op.
    destruct (decide (intComposable I1 I2)).
    - f_equal.
      case_eq I.
      intros.
      f_equal.
      + apply map_eq.
        intros n.
        rewrite gmap_imerge_prf.
        case_eq (infR I1 !! n).
        * intros x xDef.
          assert (n ∈ domm I1) as nI1. {
            apply mk_is_Some in xDef.
            unfold domm, dom, flowint_dom.
            apply elem_of_dom.
            trivial. }
          assert (n ∈ domm I) as nI. {
            set_solver. }
          unfold domm, dom, flowint_dom in nI.
          apply elem_of_dom in nI.
          unfold is_Some in nI.
          destruct nI as [y nI].
          rewrite H0 in nI.
          simpl in nI.
          rewrite nI.
          f_equal.
          pose proof (Inf1 _ nI1) as In1n.
          unfold inf in In1n.
          rewrite xDef in In1n.
          simpl in In1n.
          rewrite ccm_comm in In1n.
          rewrite In1n.
          rewrite H0.
          simpl.
          rewrite nI.
          rewrite ccm_pinv.
          auto.
        * intros.
          assert (n ∉ domm I1). {
            unfold domm, dom, flowint_dom.
            rewrite elem_of_dom.
            rewrite H1.
            apply is_Some_None. }
          case_eq (infR I2 !! n).
          -- intros x xDef.
             assert (n ∈ domm I2) as nI2. {
               apply mk_is_Some in xDef.
               unfold domm, dom, flowint_dom.
               apply elem_of_dom.
               trivial. }
             assert (n ∈ domm I) as nI. {
               set_solver. }
             unfold domm, dom, flowint_dom in nI.
             apply elem_of_dom in nI.
             unfold is_Some in nI.
             destruct nI as [y nI].
             rewrite H0 in nI.
             simpl in nI.
             rewrite nI.
             f_equal.
             pose proof (Inf2 _ nI2) as In2n.
             unfold inf in In2n.
             rewrite xDef in In2n.
             simpl in In2n.
             rewrite ccm_comm in In2n.
             rewrite In2n.
             rewrite H0.
             simpl.
             rewrite nI.
             auto using ccm_pinv.
          -- intros.
             assert (n ∉ domm I2). {
               unfold domm, dom, flowint_dom.
               rewrite elem_of_dom.
               rewrite H3.
               apply is_Some_None. }
             assert (n ∉ domm I). {
               set_solver. }
             unfold domm, dom, flowint_dom in H5.
             rewrite elem_of_dom in H5 *.
             intros.
             rewrite H0 in H5.
             simpl in H5.
             rewrite <- eq_None_not_Some in H5. symmetry.
             trivial.
      + rewrite H0 in Out.
        simpl in Out. easy.
    - contradiction.
  Qed.

  (* Interface composition is associative (valid case). *)
  Lemma intJoin_assoc_valid (F1 F2 F3 F12 I : flowintR) :
    intJoin F1 F2 F12 -> intJoin F12 F3 I -> ✓ I →
    {F23 : flowintR & intJoin F2 F3 F23 /\ intJoin F1 F23 I}.
  Proof.
    intros HeqI23 HeqI V. apply intJoin_comm in HeqI23. apply intJoin_comm in HeqI.
    rename F1 into I3. rename F2 into I2. rename F12 into I23. rename F3 into I1.
    remember (outComp I1 I2) as out12.
    remember (λ n (o1 o2 : option flowdom),
              match o1, o2 with
              | Some _, _ => Some (inf I n + out I3 n)
              | _, Some _ => Some (inf I n + out I3 n)
              | None, None => None
              end) as f_inf.
    assert (∀ n, DiagNone (f_inf n)) as H_diag.
    { intros. unfold DiagNone. rewrite Heqf_inf. trivial. }
    remember (gmap_imerge f_inf (*(infComp_op I I3)*)
                          (infR I1) (infR I2)) as inf12.
    remember {| infR := inf12; outR := out12 |} as I12.
    apply (intJoin_valid_proj1 _ _ _ HeqI) in V as V1.
    apply (intJoin_valid_proj2 _ _ _ HeqI) in V as V23.
    apply (intJoin_valid_proj1 _ _ _ HeqI23) in V23 as V2.
    apply (intJoin_valid_proj2 _ _ _ HeqI23) in V23 as V3.
    apply (intComposable_valid _ _ _ HeqI) in V as C.
    apply (intComposable_valid _ _ _ HeqI23) in V23 as C23.
    assert (CU := C).
    unfold intComposable in CU.
    destruct CU as (_ & _ & Disj & Inf1 & Inf23).
    assert (CU23 := C23).
    unfold intComposable in CU23.
    destruct CU23 as (_ & _ & Disj23 & Inf2 & Inf3).
    apply (intJoin_dom _ _ _ HeqI) in V as D.
    apply (intJoin_dom _ _ _ HeqI23) in V23 as D23.
    rewrite D23 in Disj.
    unfold map_Forall in Inf1.
    unfold map_Forall in Inf23.
    unfold map_Forall in Inf2.
    unfold map_Forall in Inf3.
    assert (intJoin I1 I2 I12 ∧ ✓ I12) as I12Def.
    { apply intJoin_fold.
      - trivial.
      - trivial.
      - set_solver.
      - rewrite set_eq.
        intros n.
        rewrite elem_of_union.
        split.
        * intros nD.
          unfold domm, dom, flowint_dom in nD.
          rewrite HeqI12 in nD.
          simpl in nD.
          rewrite Heqinf12 in nD.
          rewrite elem_of_dom in nD *.
          intros nD.
          rewrite gmap_imerge_prf in nD.
          unfold domm, dom, flowint_dom.
          repeat rewrite elem_of_dom.
          destruct (infR I1 !! n).
          unfold is_Some.
          left.
          exists f.
          reflexivity.
          destruct (infR I2 !! n).
          right.
          exists f.
          reflexivity.
          rewrite Heqf_inf in nD.
          apply is_Some_None in nD.
          contradiction.
        * intros nD.
          unfold domm, dom, flowint_dom.
          rewrite HeqI12.
          simpl.
          rewrite Heqinf12.
          rewrite elem_of_dom.
          rewrite gmap_imerge_prf.
          rewrite Heqf_inf.
          destruct nD as [nD | nD];
            unfold domm, dom, flowint_dom in nD;
            rewrite elem_of_dom in nD *;
            intros nD;
            unfold is_Some in nD;
            destruct nD as [x nD];
            rewrite nD;
            destruct (infR I1 !! n);
            apply not_eq_None_Some;
            auto.
      - intros ? n_in_I1.
        assert (n_in_I11 := n_in_I1).
        unfold domm, dom, flowint_dom in n_in_I11.
        apply elem_of_dom in n_in_I11.
        unfold is_Some in n_in_I11.
        destruct n_in_I11 as [x n_inf].
        apply Inf1 in n_inf as xDef.
        unfold inf at 2.
        rewrite HeqI12.
        simpl.
        rewrite Heqinf12.
        rewrite gmap_imerge_prf.
        rewrite n_inf.
        rewrite Heqf_inf.
        simpl.
        pose proof (intJoin_inf_1 _ _ _ HeqI V _ n_in_I1).
        rewrite H0.
        unfold inf at 2.
        rewrite n_inf.
        simpl.
        rewrite xDef.
        rewrite (ccm_comm (out I23 n)).
        rewrite ccm_pinv.
        rewrite ccm_comm.
        rewrite <- ccm_assoc.
        rewrite (ccm_comm (out I3 n)).
        assert (n ∉ domm I23).
        rewrite D23.
        set_solver.
        apply (intJoin_unfold_out _ _ _ HeqI23) in H1.
        unfold inf at 1.
        rewrite n_inf.
        simpl.
        rewrite xDef.
        rewrite ccm_comm.
        rewrite <- H1.
        reflexivity.
        trivial.
      - intros ? n_in_I2.
        assert (n_in_I21 := n_in_I2).
        unfold domm, dom, flowint_dom in n_in_I21.
        apply elem_of_dom in n_in_I21.
        unfold is_Some in n_in_I21.
        destruct n_in_I21 as [x n_inf].
        apply Inf2 in n_inf as xDef.
        unfold inf at 2.
        rewrite HeqI12.
        simpl.
        rewrite Heqinf12.
        rewrite gmap_imerge_prf.
        rewrite n_inf.
        rewrite Heqf_inf.
        assert (n ∈ domm I2 ∪ domm I3) as n_in_I23.
        set_solver.
        rewrite <- D23 in n_in_I23.
        unfold inf at 2.
        assert (n ∉ domm I1) as n_nin_I1.
        set_solver.
        unfold domm, dom, flowint_dom in n_nin_I1.
        rewrite elem_of_dom in n_nin_I1 *.
        intros n_nin_I1.
        rewrite <- eq_None_not_Some in n_nin_I1.
        rewrite n_nin_I1.
        simpl.
        rewrite ccm_comm.
        rewrite <- ccm_assoc.
        rewrite (ccm_comm (out I3 n)).
        rewrite ccm_assoc.
        pose proof (intJoin_unfold_inf_2 I1 I23 _ HeqI V n n_in_I23).
        rewrite <- H0.
        pose proof (intJoin_unfold_inf_1 I2 I3 _ HeqI23 V23 n n_in_I2).
        rewrite H1.
        reflexivity.
      - rewrite HeqI12.
        auto. }
    destruct I12Def as (I12Def & V12).
    assert (intJoin I12 I3 I) as IDef.
    { apply intJoin_fold.
      - trivial.
      - trivial.
      - rewrite (intJoin_dom _ _ _ I12Def V12).
        set_solver.
      - rewrite (intJoin_dom _ _ _ I12Def V12).
        rewrite D.
        rewrite D23.
        set_solver.
      - intros n nI12.
        rewrite HeqI12.
        unfold inf at 1.
        simpl.
        rewrite Heqinf12.
        rewrite gmap_imerge_prf.
        rewrite (intJoin_dom _ _ _ I12Def V12) in nI12.
        rewrite elem_of_union in nI12 *.
        intro nI12.
        destruct nI12 as [nI1 | nI2].
        + unfold domm, dom, flowint_dom in nI1.
          apply elem_of_dom in nI1.
          unfold is_Some in nI1.
          destruct nI1 as [x nI1].
          rewrite nI1.
          simpl.
          rewrite Heqf_inf.
          simpl.
          auto using ccm_comm.
        + destruct (infR I1 !! n).
          * rewrite Heqf_inf. simpl.
            auto using ccm_comm.
          * unfold domm, dom, flowint_dom in nI2.
            apply elem_of_dom in nI2.
            unfold is_Some in nI2.
            destruct nI2 as [x nI2].
            rewrite nI2.
            rewrite Heqf_inf.
            simpl.
            auto using ccm_comm.
      - intros n nI3.
        assert (n ∉ domm I1 ∪ domm I2) as n_not_I12.
        set_solver.
        rewrite <- (intJoin_dom _ _ _ I12Def V12) in n_not_I12.
        pose proof (intJoin_unfold_out I1 I2 _ I12Def V12 n n_not_I12).
        rewrite H0.
        assert (n ∈ domm I23) as nI23.
        set_solver.
        pose proof (intJoin_unfold_inf_2 I1 I23 _ HeqI V n nI23).
        rewrite ccm_comm.
        rewrite ccm_assoc.
        rewrite <- H1.
        pose proof (intJoin_unfold_inf_2 I2 I3 _ HeqI23 V23 n nI3).
        rewrite <- H2.
        reflexivity.
      - unfold intJoin, intComp in HeqI.
        destruct (decide (intComposable I1 I23)); last first. 1: contradiction.
        inversion HeqI. rename H1 into HI. simpl.
        apply nzmap_eq.
        intros n.
        unfold outComp.
        repeat rewrite nzmap_lookup_imerge.
        unfold outComp_op.
        pose proof (intJoin_unfold_out I1 I2 _ I12Def V12 n).
        pose proof (intJoin_unfold_out I2 I3 _ HeqI23 V23 n).
        unfold out in H0.
        unfold out in H1.
        rewrite D23.
        pose proof (intJoin_dom _ _ _ I12Def V12) as D12.
        rewrite D12.
        destruct (decide _), (decide _); try auto.
        set_solver. set_solver.
        rewrite not_elem_of_union in n0 *.
        rewrite not_elem_of_union in n1 *.
        intros n0 n1.
        destruct n0 as (n0 & _).
        destruct n1 as (_ & n1).
        rewrite <- D12 in n0.
        rewrite <- D23 in n1.
        apply H0 in n0.
        apply H1 in n1.
        rewrite n0 n1.
          by rewrite ccm_assoc. }
    exists I12. split; now apply intJoin_comm.
  Qed.

  (* Interface composition is associative (invalid case). *)
  Lemma intJoin_assoc_invalid (F1 F2 F3 F12 I : flowintR) :
    intJoin F1 F2 F12 -> intJoin F12 F3 I -> ¬ (✓ I) →
    {F23 : flowintR & intJoin F2 F3 F23 /\ intJoin F1 F23 I}.
  Proof.
    intros HeqI12 HeqI IV.
    pose proof (intValid_composable _ _ _ HeqI12) as NC1.
    pose proof (intValid_composable _ _ _ HeqI) as NC2.
    assert (HI := HeqI).
    unfold intJoin, intComp in HeqI.
    destruct (decide (intComposable F12 F3)). 1: now apply NC2 in i. clear NC2.
    destruct (decide (F12 = ∅)).
    - inversion HeqI. subst.
      apply intJoin_positive_1 in HeqI12 as E1.
      apply intJoin_positive_2 in HeqI12 as E2.
      subst. exists I. split; apply intJoin_left_unit.
    - destruct (decide (F3 = ∅)). 2: inversion HeqI. inversion HeqI. subst.
      exists F2. split; auto. apply intJoin_unit.
  Qed.

  (* Interface composition is associative. *)
  Lemma intJoin_assoc (I1 I2 I3 I12 I : flowintR) :
    intJoin I1 I2 I12 -> intJoin I12 I3 I ->
    {I23 : flowintR & intJoin I2 I3 I23 /\ intJoin I1 I23 I}.
  Proof.
    intros.
    destruct (decide (✓ I)).
    - eapply intJoin_assoc_valid; eauto.
    - eapply intJoin_assoc_invalid; eauto.
  Qed.

  (** Auxiliary definitions for setting up flow interface camera. *)

  Lemma flowint_valid_unfold (I : flowintR) :
    ✓ I → infR I ##ₘ nzmap_car (outR I) ∧ (infR I = ∅ → outR I = ∅).
  Proof.
    intros.
    unfold valid in H0.
    now unfold flowint_valid in H0.
  Qed.

  (* Flow interface composition is cancelable. *)
  Lemma intJoin_cancelable (I1 I2 I3 I: flowintR) :
    ✓ I → intJoin I1 I2 I -> intJoin I1 I3 I → I2 = I3.
  Proof.
    intros V12 HeqI12 HeqI13.
    pose proof (intComposable_valid _ _ _ HeqI13 V12) as C13.
    pose proof (intComposable_valid _ _ _ HeqI12 V12) as C12.
    pose proof (intJoin_valid_proj1 _ _ _ HeqI12 V12) as V1.
    pose proof (intJoin_valid_proj2 _ _ _ HeqI12 V12) as V2.
    pose proof (intJoin_valid_proj2 _ _ _ HeqI13 V12) as V3.
    pose proof (flowint_valid_unfold _ V1) as (Disj1 & _).
    pose proof (flowint_valid_unfold _ V2) as (Disj2 & _).
    pose proof (flowint_valid_unfold _ V3) as (Disj3 & _).
    assert (C12' := C12).
    assert (C13' := C13).
    destruct C12' as (_ & _ & Disj12 & Inf12 & Inf2).
    unfold map_Forall in Inf2.
    destruct C13' as (_ & _ & Disj13 & Inf13 & Inf3).
    assert (domm I2 = domm I3) as D23.
    { pose proof (intJoin_dom _ _ _ HeqI12 V12).
      pose proof (intJoin_dom _ _ _ HeqI13 V12).
      set_solver. }
    case_eq I2.
    intros infR2 outR2 Ir2_def.
    case_eq I3.
    intros infR3 outR3 Ir3_def.
    f_equal.
    - apply map_eq.
      intros n.
      unfold intJoin, intComp in HeqI12, HeqI13.
      destruct (decide (intComposable I1 I2)); last first. contradiction.
      destruct (decide (intComposable I1 I3)); last first. contradiction.
      assert (infComp I1 I2 !! n = infComp I1 I3 !! n) as Eqinf. {
        rewrite <- HeqI12 in HeqI13. inversion HeqI13. now rewrite H1. }
      unfold infComp, infComp_op in Eqinf.
      repeat rewrite gmap_imerge_prf in Eqinf.
      unfold out at 1, out at 2 in Eqinf.
      destruct (decide (n ∈ domm I1)) as [n_in_I1 | n_nin_I1].
      + assert (n ∉ domm I2) as n_nin_I2 by set_solver.
        assert (n ∉ domm I3) as n_nin_I3 by set_solver.
        unfold domm, dom, flowint_dom in n_nin_I2.
        rewrite not_elem_of_dom in n_nin_I2 *.
        intros n_nin_I2.
        unfold domm, dom, flowint_dom in n_nin_I3.
        rewrite not_elem_of_dom in n_nin_I3 *.
        intros n_nin_I3.
        rewrite Ir2_def in n_nin_I2.
        simpl in n_nin_I2.
        rewrite Ir3_def in n_nin_I3.
        simpl in n_nin_I3.
        rewrite n_nin_I2.
        rewrite n_nin_I3.
        reflexivity.
      + unfold domm, dom, flowint_dom in n_nin_I1.
        rewrite not_elem_of_dom in n_nin_I1 *.
        intros n_nin_I1.
        rewrite n_nin_I1 in Eqinf.
        rewrite Ir2_def in Eqinf.
        rewrite Ir3_def in Eqinf.
        simpl in Eqinf.
        destruct (decide (n ∈ domm I2)) as [n_in_I2 | n_nin_I2].
        * assert (n ∈ domm I3) as n_in_I3.
          { rewrite <- D23. trivial. }
          unfold domm, dom, flowint_dom in n_in_I2, n_in_I3.
          rewrite elem_of_dom in n_in_I2 *.
          intros n_in_I2.
          rewrite elem_of_dom in n_in_I3 *.
          intros n_in_I3.
          unfold is_Some in n_in_I2, n_in_I3.
          destruct n_in_I2 as [x2 n_in_I2].
          destruct n_in_I3 as [x3 n_in_I3].
          rewrite Ir2_def in n_in_I2. simpl in n_in_I2.
          rewrite Ir3_def in n_in_I3. simpl in n_in_I3.
          rewrite n_in_I2 in Eqinf.
          rewrite n_in_I3 in Eqinf.
          pose proof (Inf2 n x2).
          rewrite Ir2_def in H0.
          unfold inf in H0.
          rewrite n_in_I2 in H0.
          simpl in H0.
          rewrite H0 in n_in_I2.
          pose proof (Inf3 n x3).
          rewrite Ir3_def in H1.
          unfold inf in H1.
          rewrite n_in_I3 in H1.
          simpl in H1.
          rewrite H1 in n_in_I3.
          assert (x2 - out I1 n = x3 - out I1 n) by naive_solver.
          rewrite H2 in n_in_I2.
          rewrite n_in_I3.
          rewrite n_in_I2.
          all: reflexivity.
        * assert (n ∉ domm I3) as n_nin_I3.
          { rewrite <- D23. trivial. }
          unfold domm, dom, flowint_dom in n_nin_I2, n_nin_I3.
          rewrite not_elem_of_dom in n_nin_I2 *.
          intros n_nin_I2.
          rewrite not_elem_of_dom in n_nin_I3 *.
          intros n_nin_I3.
          rewrite Ir2_def in n_nin_I2. simpl in n_nin_I2.
          rewrite Ir3_def in n_nin_I3. simpl in n_nin_I3.
          rewrite n_nin_I2.
          rewrite n_nin_I3.
          reflexivity.
    - apply nzmap_eq.
      intros n. assert (HeqI12' := HeqI12). assert (HeqI13' := HeqI13).
      unfold intJoin, intComp in HeqI12', HeqI13'.
      destruct (decide (intComposable I1 I2)); last first. contradiction.
      destruct (decide (intComposable I1 I3)); last first. contradiction.
      assert (outComp I1 I2 ! n = outComp I1 I3 ! n) as Eqout. {
        rewrite <- HeqI12' in HeqI13'. inversion HeqI13'. now rewrite H2. }
      unfold outComp in Eqout.
      repeat rewrite nzmap_lookup_imerge in Eqout.
      unfold outComp_op in Eqout.
      unfold map_Forall in Inf13, Inf12, Inf3, Inf2.
      destruct (decide _), (decide _).
      + destruct (decide (n ∈ domm I1)).
        * unfold domm, dom, flowint_dom in e1.
          pose proof (intJoin_inf_1 I1 I2 _ HeqI12 V12 n e1).
          pose proof (intJoin_inf_1 I1 I3 _ HeqI13 V12 n e1).
          rewrite elem_of_dom in e1 *.
          intros e1.
          unfold is_Some in e1.
          destruct e1 as [x e1].
          pose proof (Inf13 _ _ e1).
          pose proof (Inf12 _ _ e1).
          rewrite <- H0 in H3.
          rewrite <- H1 in H2.
          rewrite H3 in H2.
          repeat rewrite (ccm_comm (out _ _)) in H2.
          apply ccm_cancel in H2.
          rewrite Ir2_def in H2.
          rewrite Ir3_def in H2.
          unfold out in H2.
          simpl in H2.
            by rewrite H2.
        * assert (n ∈ domm I2) by set_solver.
          assert (n ∈ domm I3) by set_solver.
          pose proof (intValid_in_dom_not_out I2 n V2 H0).
          pose proof (intValid_in_dom_not_out I3 n V3 H1).
          rewrite Ir2_def in H2.
          rewrite Ir3_def in H3.
          unfold out in H2, H3.
          simpl in H2,H3.
          rewrite H2.
          rewrite H3.
          reflexivity.
      + rewrite D23 in e. contradiction.
      + rewrite D23 in n0. contradiction.
      + apply ccm_cancel in Eqout.
        rewrite Ir2_def in Eqout.
        rewrite Ir3_def in Eqout.
        simpl in Eqout.
          by rewrite Eqout.
  Qed.

  Global Instance flowintPerm: sepalg.Perm_alg flowintR.
  Proof.
    constructor; unfold sepalg.join; intros.
    - unfold intJoin in *. rewrite H0 in H1. now inversion H1.
    - eapply intJoin_assoc; eauto.
    - now apply intJoin_comm.
    - destruct (intJoin_assoc _ _ _ _ _ H0 H1) as [ab' [? ?]].
      pose proof (intJoin_unit a).
      destruct (decide (✓ a)).
      + pose proof (intJoin_cancelable _ _ _ _ v H3 H4). subst ab'.
        apply intJoin_positive_1 in H2. subst a'. clear H1 H4.
        unfold intJoin in *. rewrite H0 in H3. now inversion H3.
      + apply (intComposable_invalid a a') in n as IC1.
        apply (intJoin_invalid _ _ _ H0) in n as IV2.
        unfold intJoin, intComp in H0. destruct (decide (intComposable a a')). 1: easy.
        destruct (decide (a = ∅)).
        * subst a. pose proof intEmp_valid. easy.
        * destruct (decide (a' = ∅)); inversion H0. easy.
  Qed.

  Lemma list_join_unfold_out: forall (l: list flowintR) (c: flowintR),
      list_join l c -> ✓ c ->
      forall n, n ∉ domm c -> out c n = fold_right (fun x v => out x n + v) 0 l.
  Proof.
    induction l; intros; inversion H0; subst; simpl. 1: now rewrite ccm_right_id.
    red in H7. assert (✓ lj) by (eapply intJoin_valid_proj2; eauto).
    assert (n ∉ domm lj). {
      pose proof (intJoin_dom _ _ _ H7 H1). rewrite H4 in H2. intro. apply H2.
      now apply elem_of_union_r. }
    specialize (IHl _ H5 H3 _ H4). rewrite <- IHl. now apply intJoin_unfold_out.
  Qed.

  Global Program Instance flowintGhost : Ghost :=
    { G := flowintR; valid := flowint_valid; Join_G := intJoin }.
  Next Obligation.
    exists (fun _ => I_emptyR); intros; auto.
    apply intJoin_left_unit.
  Qed.
  Next Obligation.
    eapply intJoin_valid_proj1; eauto.
  Qed.

End flowint.

Section ghost.

  Context `{HC: Countable Node}.

  Context (flowdom: Type) `{CCM flowdom}.

  Open Scope ccm_scope.

  (* Contextual extension of flow interfaces. *)
  Definition contextualLeq (I1 I2: @flowintR Node EqDecision0 HC flowdom H) : Prop :=
    ✓ I1 ∧ ✓ I2 ∧ domm I1 ⊆ domm I2 ∧
    (∀ (n: Node), n ∈ domm(I1) → inf I1 n = inf I2 n) ∧
    (∀ (n: Node), n ∉ domm(I2) → out I1 n = out I2 n).

End ghost.
