Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Import VST.progs.ghosts.
From bst Require Export flows ccm.

(** Flow interface cameras and auxiliary lemmas for inset flows
  (used in the give-up template proof). *)

Section inset_flows.

  Context `{HC: Countable Node}.

  Context `{Countable K}.

  Parameter KS: gset K.

  (** CCM of multisets over keys *)

  Definition K_multiset := nzmap K nat.

  Global Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

  Definition dom_ms (m : K_multiset) := dom (gset K) m.

  Definition inset_flowint := @flowintR Node _ _ K_multiset K_multiset_ccm.

  Implicit Type I: inset_flowint.

  (** Insets, outsets, and keysets of flow interfaces *)

  Definition inset I n := dom_ms (inf I n).

  Definition outset I n := dom_ms (out I n).

  Definition in_inset k I n := k ∈ dom_ms (inf I n).

  Definition in_outset k I n := k ∈ dom_ms (out I n).

  Definition in_outsets k In := ∃ n, in_outset k In n.

  Definition keyset I n := dom_ms (inf I n) ∖ dom_ms (out I n).

  Lemma keyset_def : ∀ k I_n n, k ∈ inset I_n n → ¬ in_outsets k I_n
                                → k ∈ keyset I_n n.
  Proof.
    intros ? ? ? k_in_inset k_not_in_outsets.
    unfold keyset.
    unfold inset in k_in_inset.
    unfold in_outsets in k_not_in_outsets.
    rewrite elem_of_difference.
    naive_solver.
  Qed.

  (* The global invariant ϕ. *)
  Definition globalinv root I :=
    ✓I
    ∧ (root ∈ domm I)
    ∧ (∀ k n, k ∉ outset I n)
    ∧ (∀ k, k ∈ KS → k ∈ inset I root).

  (** Assorted lemmas about inset flows used in the template proofs *)

  Lemma globalinv_root_fp: ∀ I root, globalinv root I → root ∈ domm I.
  Proof.
    intros I root Hglob. unfold globalinv in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.

  Lemma flowint_step :
    ∀ I I1 I2 k n root,
      globalinv root I → intJoin I1 I2 I → k ∈ outset I1 n → n ∈ domm I2.
  Proof.
    intros I I1 I2 k n r gInv dI kOut.
    unfold globalinv in gInv.
    destruct gInv as (vI & rI & cI & _).

    assert (domm I = domm I1 ∪ domm I2) as disj. {
      apply (intJoin_dom _ _ _ dI vI). }

    (* First, prove n ∉ domm I1 *)
    destruct (decide (n ∈ domm I1)).
    - pose proof (intJoin_valid_proj1 I1 I2 I dI vI) as vI1.
      pose proof (intValid_in_dom_not_out I1 n vI1 e).
      unfold outset, dom_ms in kOut.
      rewrite nzmap_elem_of_dom_total in kOut *.
      intros.
      unfold ccmunit, ccm_unit, K_multiset_ccm, lift_ccm, lift_unit in H0.
      rewrite H0 in H1.
      rewrite nzmap_lookup_empty in H1.
      contradiction.

    (* Now, prove n ∈ domm I *)
    - assert (n ∈ domm I) as in_Inf_n. {
        pose proof (intJoin_unfold_out I1 I2 I dI vI n).
        destruct (decide (n ∉ domm I)).
        + apply H0 in n1.
          pose proof (cI k n) as not_k_out.
          unfold outset, dom_ms in not_k_out.
          rewrite nzmap_elem_of_dom_total in not_k_out *.
          intros not_k_out.
          apply dec_stable in not_k_out.
          unfold outset, dom_ms in kOut.
          rewrite nzmap_elem_of_dom_total in kOut *.
          intros kOut.
          assert (out I n ! k = (out I1 n + out I2 n)%CCM ! k) by now rewrite n1.
          rewrite lookup_op in H1.
          unfold ccmop, ccm_op in H1.
          unfold K_multiset_ccm,ccmunit,ccm_unit,nat_ccm,nat_unit,nat_op
            in kOut, not_k_out, H1. lia.
        + apply dec_stable in n1. trivial. }

      (* Finally, prove n ∈ domm I2 *)
      rewrite disj in in_Inf_n.
      set_solver.
  Qed.

  Lemma outset_distinct : ∀ I n, ✓ I ∧ (∃ k, k ∈ outset I n) → n ∉ domm I.
  Proof.
    intros.
    destruct H0 as (VI & Out).
    destruct Out as [k Out].

    apply flowint_valid_unfold in VI.
    destruct VI as (disj & _).

    rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in disj *.
    intros disj.

    unfold outset, dom_ms, nzmap_dom, out in Out.
    rewrite nzmap_elem_of_dom_total in Out *.
    intros Out.
    destruct (decide (outR I ! n = ∅)).
    - rewrite e in Out.
      rewrite nzmap_lookup_empty in Out.
      contradiction.
    - rewrite <- nzmap_elem_of_dom_total in n0.
      unfold dom, nzmap_dom in n0.
      unfold domm, dom, flowint_dom.
      set_solver.
  Qed.

  Lemma inset_monotone : ∀ I I1 I2 k n,
      ✓ I → intJoin I1 I2 I → k ∈ inset I n → n ∈ domm I1 → k ∈ inset I1 n.
  Proof.
    intros ? ? ? ? ? VI ID Inset Dom.
    (* rewrite ID in VI. *)
    pose proof (intJoin_unfold_inf_1 I1 I2 _ ID VI n) as Inf1.
    apply Inf1 in Dom.
    assert (Inset1 := Inset).
    unfold inset, dom_ms, nzmap_dom in Inset.
    rewrite nzmap_elem_of_dom in Inset *.
    intros Inset.
    unfold inf in Dom.
    pose proof (intJoin_valid_proj1 I1 I2 _ ID VI) as VI1.
    pose proof (intJoin_valid_proj2 I1 I2 _ ID VI) as VI2.

    unfold inset, inf, dom_ms.
    rewrite Dom.
    rewrite nzmap_elem_of_dom_total.
    rewrite lookup_op.
    unfold nzmap_total_lookup.
    unfold inf, is_Some in Inset.
    destruct Inset as [x Inset].
    rewrite Inset.
    simpl.

    assert (x <> 0). {
      unfold inset, dom_ms in Inset1.
      rewrite nzmap_elem_of_dom_total in Inset1 *.
      intros xDef.
      unfold inf in xDef.
      unfold nzmap_total_lookup in xDef.
      rewrite Inset in xDef.
      simpl in xDef.
      trivial. }

    unfold ccmop, ccm_op, nat_ccm, nat_op, out.
    unfold ccmunit, nat_unit.
    lia.
    all: apply K_multiset_ccm.
  Qed.

  Lemma flowint_inset_step : ∀ I I1 I2 k n,
      intJoin I1 I2 I → ✓ I → n ∈ domm I2 → k ∈ outset I1 n → k ∈ inset I2 n.
  Proof.
    intros ? ? ? ? ? IJ I12V Out Inset.

    pose proof (intJoin_valid_proj1 I1 I2 I IJ I12V) as I1V.
    pose proof (intJoin_valid_proj2 I1 I2 I IJ I12V) as I2V.

    pose proof (intJoin_unfold_inf_2 I1 I2 _ IJ I12V n Out) as Inf2.

    unfold outset in Inset.
    unfold inset, dom_ms.
    rewrite Inf2.
    unfold out.
    repeat rewrite nzmap_elem_of_dom_total.
    repeat rewrite lookup_op.

    unfold dom_ms, out in Inset.
    repeat (rewrite nzmap_elem_of_dom_total in Inset *; intros Inset).
    unfold ccmop, ccm_op, nat_ccm, nat_op.
    unfold ccmop, ccm_op, nat_ccm, nat_op in Inset.
    unfold ccmunit, ccm_unit, nat_unit, K_multiset_ccm, prod_ccm.
    unfold ccmunit, ccm_unit, nat_unit, K_multiset_ccm, prod_ccm in Inset.
    lia.
  Qed.

  Lemma contextualLeq_impl_globalinv : ∀ I I' root,
      globalinv root I →
      contextualLeq K_multiset I I' →
      (∀ n, n ∈ domm I' ∖ domm I → inset I' n = ∅) →
      globalinv root I'.
  Proof.
    intros ? ? ? GI CLeq InfI'.
    unfold contextualLeq in CLeq.
    unfold globalinv in GI.
    destruct GI as (_ & DomR & OutI & InfI).
    destruct CLeq as (VI & VI' & DS & InfR & OutR).
    unfold globalinv.
    split; [|split; [|split]].
    - trivial.
    - set_solver.
    - intros.
      destruct (decide (n ∈ domm I')).
      * apply flowint_valid_unfold in VI'.
        destruct VI' as [I'_disj _].
        rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in I'_disj *.
        intros.
        assert (outR I' ! n = 0%CCM).
        { assert (¬ (n ∈ dom (gset Node) (outR I'))).
          { unfold domm, dom, flowint_dom in e.
            set_solver.
          }
          rewrite nzmap_elem_of_dom_total in H1 *.
          intros.
          apply dec_stable in H1.
            by rewrite H1.
        }
        unfold outset, dom_ms, nzmap_dom, out.
        rewrite H1. simpl.
        rewrite dom_empty.
        apply not_elem_of_empty.
      * assert (n ∉ domm I) by set_solver.
        pose proof (OutR n n0).
        unfold outset. rewrite <- H1.
        pose proof (OutI k n).
        unfold outset in H2.
        trivial.
    - intros.
      (*destruct H2 as (H2 & _).*)
      specialize (InfI k).
      (*rewrite <- H0 in DomR.*)
      specialize (InfR root DomR).
      unfold inset.
      unfold inset in InfR.
      rewrite <- InfR.
      apply InfI in H0.
      trivial.
  Qed.

  Lemma globalinv_root_ins : ∀ I Ir root k,
      globalinv root I ∧ (exists I', intJoin Ir I' I) ∧ domm Ir = {[root]} ∧ k ∈ KS
      → k ∈ inset Ir root.
  Proof.
    intros I Ir root k ((Hv & _ & _ & Hl) & [I2 Hincl] & Hdom & kKS).
    specialize (Hl k kKS).
    apply (inset_monotone I Ir I2 k root); try done.
    set_solver.
  Qed.

  Lemma intJoin_out_zero I I1 I2 n :
    intJoin I1 I2 I → ✓ I → n ∉ domm I → out I n = 0%CCM → out I2 n = 0%CCM.
  Proof.
    intros IJ Hvld Hn Hout. apply nzmap_eq. intros k.
    assert (out I n = (out (I1) n) + (out I2 n))%CCM.
    { apply intJoin_unfold_out; try done. }
    assert (out I n ! k = (out (I1) n) ! k + (out I2 n) ! k)%CCM.
    { rewrite H0. by rewrite lookup_op. }
    rewrite Hout in H1. rewrite nzmap_lookup_empty in H1.
    unfold ccmunit,ccm_unit in H1. simpl in H1.
    unfold nat_unit in H1. unfold ccmop, nat_op in H1.
    assert (out I2 n ! k = 0). lia.
    rewrite H2. rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit.
    simpl. by unfold nat_unit.
  Qed.

End inset_flows.

Arguments inset_flowint _ {_ _} _ {_ _} : assert.
Arguments inset _ {_ _} _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ {_ _} _ _ : assert.
Arguments keyset _ {_ _} _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ {_ _} _ _ _: assert.
Arguments in_outsets _ {_ _} _ {_ _} _ _ : assert.
Arguments globalinv _ {_ _} _ {_ _} _ _ : assert.
