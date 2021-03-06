Require Export VST.veric.bi.
Require Import VST.progs.ghosts.

From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
From bst Require Export ccm gmap_more.

Definition keys := nzmap Z nat.

Definition keysComp (k1 k2: keys) : option keys :=
  if decide ((dom (gset Z) k1) ## (dom (gset Z) k2))
  then Some (ccmop k1 k2) else None.

Lemma keys_unitfor: forall t: keys, keysComp ∅ t = Some t.
Proof.
  intros. unfold keysComp.
  assert (@dom keys (gset Z) _ ∅ ## dom (gset Z) t). {
    unfold dom. unfold disjoint. unfold set_disjoint_instance. intros.
    apply nzmap_elem_of_dom_total in H. rewrite nzmap_lookup_empty in H.
    now apply H. }
  destruct (decide (@dom keys (gset Z) _ ∅ ## dom (gset Z) t)).
  rewrite ccm_left_id. auto. exfalso. now apply n.
Qed.

Instance keysJoin: sepalg.Join keys :=
  λ (k1 k2 k3: keys), keysComp k1 k2 = Some k3.

Lemma keysJoin_comm: forall (a b c : keys), keysJoin a b c -> keysJoin b a c.
Proof.
  unfold keysJoin. unfold keysComp. intros.
  destruct (decide (dom (gset Z) a ## dom (gset Z) b)); inversion H. clear H.
  symmetry in d. destruct (decide (dom (gset Z) b ## dom (gset Z) a)). 2: now exfalso.
  now rewrite ccm_comm.
Qed.

Lemma keys_dom: forall (a b: keys),
    dom (gset Z) (a + b)%CCM = dom (gset Z) a ∪ dom (gset Z) b.
Proof.
  intros. set_unfold. intros. unfold ccmop, ccm_op. simpl. unfold lift_op.
  rewrite nzmap_elem_of_dom_total.
  rewrite nzmap_lookup_merge.
  repeat rewrite nzmap_elem_of_dom_total.
  unfold ccmop, ccm_op. simpl. unfold nat_op. unfold ccmunit, nat_unit. lia.
Qed.

Lemma keysJoin_assoc: forall (a b c d e : keys),
    keysJoin a b d -> keysJoin d c e -> {f : keys & keysJoin b c f ∧ keysJoin a f e}.
Proof.
  intros. unfold keysJoin in *. unfold keysComp in *.
  destruct (decide (dom (gset Z) a ## dom (gset Z) b)); inversion H.
  destruct (decide (dom (gset Z) d ## dom (gset Z) c)); inversion H0. clear H H0.
  exists (b + c)%CCM.
  assert (dom (gset Z) a ## dom (gset Z) c ∧ dom (gset Z) b ## dom (gset Z) c). {
    rewrite <- H2 in d1.
    rewrite keys_dom in d1.
    now apply disjoint_union_l in d1. }
  destruct H.
  destruct (decide (dom (gset Z) b ## dom (gset Z) c)). 2: now exfalso. clear d2.
  split; auto.
  assert (dom (gset Z) a ## dom (gset Z) (b + c)%CCM). {
    rewrite keys_dom. rewrite disjoint_union_r. split; auto. }
  destruct (decide (dom (gset Z) a ## dom (gset Z) (b + c)%CCM)). 2: now exfalso.
  f_equal. rewrite <- H2. apply ccm_assoc.
Qed.

Lemma keys_ccm_positive: forall (a b: keys), (a + b)%CCM = 0%CCM -> a = 0%CCM.
Proof.
  intros. unfold ccmop, ccm_op in H. simpl in H. unfold lift_op in H.
  apply nzmap_eq. intros n.
  assert (nzmap_merge ccmop a b ! n = 0%CCM ! n) by now rewrite H.
  rewrite nzmap_lookup_merge in H0. unfold ccmop, ccm_op, nat_op in H0.
  rewrite nzmap_lookup_empty.
  rewrite nzmap_lookup_empty in H0.
  unfold ccmunit, ccm_unit in *. simpl in *.
  unfold nat_unit in *. lia.
Qed.

Program Instance keysGhost : Ghost :=
  { G := keys; valid := fun _ => True; Join_G := keysJoin }.
Next Obligation.
  exists (fun _ => ∅); intros; auto.
  hnf. apply keys_unitfor.
Qed.
Next Obligation.
  constructor; unfold sepalg.join; intros.
  - unfold keysJoin in *. rewrite H in H0. now inversion H0.
  - eapply keysJoin_assoc; eauto.
  - apply keysJoin_comm; auto.
  - unfold keysJoin in *. unfold keysComp in *.
    destruct (decide (dom (gset Z) a ## dom (gset Z) a')); inversion H. clear H.
    destruct (decide (dom (gset Z) b ## dom (gset Z) b')); inversion H0. clear H0.
    rewrite <- H2 in H1. rewrite <- ccm_assoc in H1.
    pose proof (ccm_right_id a). rewrite <- H in H1 at 2.
    apply ccm_cancel in H1. clear H. rewrite <- ccm_assoc.
    rewrite (ccm_comm b' a'). rewrite H1. rewrite ccm_right_id.
    rewrite ccm_comm in H1. apply keys_ccm_positive in H1. rewrite H1.
    now rewrite ccm_right_id.
Qed.
Next Obligation.
  intros. simpl. auto.
Qed.

Lemma bool_decide_nzmap_to1_wf:
  forall (s: gset Z), bool_decide (nzmap_wf (gset_to_gmap 1 s)).
Proof.
  intros. unfold bool_decide. destruct (nzmap_wf_decision Z (gset_to_gmap 1 s)). easy.
  assert (nzmap_wf (gset_to_gmap 1 s)). {
    unfold nzmap_wf. unfold map_Forall. intros. apply lookup_gset_to_gmap_Some in H.
    destruct H. subst x. easy. } now exfalso.
Qed.

Definition gset_to_keys (s: gset Z): keys :=
  NZMap (gset_to_gmap 1 s) (bool_decide_nzmap_to1_wf s).


