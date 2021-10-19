Require Import bst.puretree.
Require Import VST.floyd.proofauto.
Require Import VST.progs.bst.
Require Import VST.msl.iter_sepcon.
Require Import bst.flows.
Require Import bst.val_countable.
Require Import bst.inset_flows.
Require Import bst.verif_bst_flows_safe.
Require Import bst.sepalg_ext.

Open Scope Z_scope.
Open Scope logic.

Definition bst_inset_flowint := inset_flowint TreeNode Z.

Definition inset_global_inv (root: TreeNode) (NS: list TreeNode)
           (Iset: bst_inset_flowint) : Prop :=
  keyset_global_inv root Iset /\ list_to_set (map key_tn NS) ⊆ KS /\
    (forall n, n ∈ domm Iset -> n <> root -> inf Iset n = ∅).

Definition gmap_sub `{Countable K} {A} (s1 s2: gmap K A): Prop :=
  forall k a, s1 !! k = Some a -> s2 !! k = Some a.

Lemma inset_global_inv_perm: forall root l1 l2 I,
    Permutation l1 l2 -> inset_global_inv root l1 I -> inset_global_inv root l2 I.
Proof.
  unfold inset_global_inv. intros. destruct H0 as [? [? ?]]. do 2 (split; auto).
  apply (Permutation_map key_tn) in H.
  assert (@list_to_set _ (gset Z) _ _ _ (map key_tn l1) = @list_to_set _ (gset Z) _ _ _ (map key_tn l2)) by
    now apply list_to_set_perm_L. now rewrite <- H3.
Qed.

Lemma nzmap_subset_wf: forall `{Countable K} `{CCM A} (s1 s2: gmap K A),
    gmap_sub s1 s2 -> nzmap_wf s2 -> nzmap_wf s1.
Proof.
  unfold nzmap_wf. intros. rewrite map_Forall_lookup in H2 |- *. intros.
  rewrite map_Forall_lookup. intros. apply (H2 i). now apply H1.
Qed.

Lemma split_filter_sub: forall {K A} `{Countable K} (m: gmap K A) f,
    gmap_sub (list_to_map (List.filter f (map_to_list m))) m.
Proof.
  intros. unfold gmap_sub. intros. apply elem_of_list_to_map_2 in H0.
  apply elem_of_list_In in H0. apply filter_In in H0. destruct H0.
  rewrite <- elem_of_map_to_list. now rewrite elem_of_list_In.
Qed.

Definition splitLeft (mulst: gmap Z nat) (e: Z): gmap Z nat :=
  list_to_map (List.filter (fun zn => e >? (fst zn)) (map_to_list mulst)).

Lemma nzmap_left_wf: forall m e,  nzmap_wf m -> nzmap_wf (splitLeft m e).
Proof. intros. apply nzmap_subset_wf with m; auto. apply split_filter_sub. Qed.

Definition splitRight (mulst: gmap Z nat) (e: Z): gmap Z nat :=
  list_to_map (List.filter (fun zn => e <? (fst zn)) (map_to_list mulst)).

Lemma nzmap_right_wf: forall m e,  nzmap_wf m -> nzmap_wf (splitRight m e).
Proof. intros. apply nzmap_subset_wf with m; auto. apply split_filter_sub. Qed.

Definition split_left (s: K_multiset Z) (e: Z): K_multiset Z :=
  let (m, Hm) := s in
  NZMap (splitLeft m e)
        (bool_decide_pack _ (nzmap_left_wf m e (bool_decide_unpack _ Hm))).

Definition split_right (s: K_multiset Z) (e: Z): K_multiset Z :=
  let (m, Hm) := s in
  NZMap (splitRight m e)
        (bool_decide_pack _ (nzmap_right_wf m e (bool_decide_unpack _ Hm))).

Lemma filter_fst: forall {A B: Type} (f: A -> bool) (l: list (A * B)),
    (List.filter (fun zn => f zn.1) l).*1 = List.filter f l.*1.
Proof.
  intros. induction l; simpl; auto.
  destruct (f a.1); [rewrite fmap_cons |]; now rewrite IHl.
Qed.

Lemma split_right_lookup: forall s e i a,
    (split_right s e) !! i = Some a <-> (s !! i = Some a /\ i > e).
Proof.
  intros. split; intros; unfold lookup in *; destruct s; simpl in *.
  - unfold splitRight in H. apply elem_of_list_to_map_2 in H.
    apply elem_of_list_In in H. apply filter_In in H. simpl in H. destruct H.
    rewrite <- elem_of_list_In in H. apply elem_of_map_to_list in H. split; auto.
    apply Zlt_is_lt_bool in H0. lia.
  - unfold splitRight. apply elem_of_list_to_map.
    + rewrite filter_fst. rewrite NoDup_ListNoDup. apply List.NoDup_filter.
      rewrite <- NoDup_ListNoDup. apply NoDup_fst_map_to_list.
    + rewrite elem_of_list_In. rewrite filter_In. simpl. split.
      * rewrite <- elem_of_list_In. now rewrite elem_of_map_to_list.
      * rewrite <- Zlt_is_lt_bool. lia.
Qed.

Lemma split_left_lookup: forall s e i a,
    (split_left s e) !! i = Some a <-> (s !! i = Some a /\ i < e).
Proof.
  intros. split; intros; unfold lookup in *; destruct s; simpl in *.
  - unfold splitLeft in H. apply elem_of_list_to_map_2 in H.
    apply elem_of_list_In in H. apply filter_In in H. simpl in H. destruct H.
    rewrite <- elem_of_list_In in H. apply elem_of_map_to_list in H. split; auto.
    apply Zgt_is_gt_bool in H0. lia.
  - unfold splitLeft. apply elem_of_list_to_map.
    + rewrite filter_fst. rewrite NoDup_ListNoDup. apply List.NoDup_filter.
      rewrite <- NoDup_ListNoDup. apply NoDup_fst_map_to_list.
    + rewrite elem_of_list_In. rewrite filter_In. simpl. split.
      * rewrite <- elem_of_list_In. now rewrite elem_of_map_to_list.
      * rewrite <- Zgt_is_gt_bool. lia.
Qed.

Definition inset_edgeFn (x y: TreeNode): K_multiset Z -> K_multiset Z :=
  fun s => if (val_eqb x.(addr_tn) y.(addr_tn) || val_eqb y.(addr_tn) nullval)%bool
           then ∅
           else if val_eqb y.(addr_tn) x.(left_tn)
                then split_left s x.(key_tn)
                else if val_eqb y.(addr_tn) x.(right_tn)
                     then split_right s x.(key_tn)
                     else ∅.

Definition inset_local_inv (t: TreeNode) (It: bst_inset_flowint): Prop :=
  ✓ It /\ domm It = {[t]} /\ in_inset t.(key_tn) It t /\
    (forall n, out It n = inset_edgeFn t n (inf It t)).

Definition node_rep (t: TreeNode) (Ipc: pc_flowint) (Is: bst_inset_flowint): mpred :=
  !! (inset_local_inv t Is /\ pc_local_inv t Ipc) &&
    data_at Tsh t_struct_tree (Vint (Int.repr t.(key_tn)),
                                (t.(value_tn), (t.(left_tn), t.(right_tn)))) t.(addr_tn).

Definition tree_rep (l: list TreeNode) (Cpc: pc_flowint)
           (Cs: bst_inset_flowint): mpred :=
  EX fpc fs, !! (list_join fpc Cpc /\ list_join fs Cs /\
                   Datatypes.length fpc = Datatypes.length l /\
                   Datatypes.length fs = Datatypes.length l) &&
               iter_sepcon (fun x => node_rep x.1 x.2.1 x.2.2)
                           (combine l (combine fpc fs)).

Definition treebox_rep root l Cpc Cs (b: val) :=
  !!(pc_global_inv root l Cpc /\ inset_global_inv root l Cs) &&
    data_at Tsh (tptr t_struct_tree) (addr_tn root) b * tree_rep l Cpc Cs.

Definition lookup_spec :=
  DECLARE _lookup
          WITH b: val, x: Z, v: val, root: TreeNode, l: (list TreeNode), Cpc: pc_flowint,
                Cs: bst_inset_flowint
                      PRE [ tptr (tptr t_struct_tree), tint  ]
                      PROP (Int.min_signed <= x <= Int.max_signed; x ∈ KS)
                      PARAMS(b; Vint (Int.repr x))
                      SEP (treebox_rep root l Cpc Cs b)
                      POST [ tptr Tvoid ]
                      EX r,
                  PROP ((~ In x (map key_tn l) /\ r = nullval) \/
                          (exists t, In t l /\ key_tn t = x /\ value_tn t = r))
                       RETURN (r)
                       SEP (treebox_rep root l Cpc Cs b).

Definition Gprog : funspecs := ltac:(with_library prog [lookup_spec]).

Lemma tree_rep_impl_pc_tree_rep: forall l C C', tree_rep l C C' |-- pc_tree_rep l C.
Proof.
  intros. unfold tree_rep, pc_tree_rep. Intros fpc fs. Exists fpc. entailer.
  apply derives_trans with
    (iter_sepcon
       (λ x : TreeNode * (pc_flowint * bst_inset_flowint), pc_node_rep x.1 x.2.1)
       (combine l (combine fpc fs))).
  - apply conclib.iter_sepcon_derives. intros. destruct x as [t [Ipc Is]]. simpl.
    unfold node_rep, pc_node_rep. entailer !.
  - revert fpc fs C C' H1 H2 H H0. induction l; intros; simpl; auto.
    destruct fpc as [|Ipc fpc]. 1: simpl in H1; lia.
    destruct fs as [|Is fs]. 1: simpl in H2; lia. simpl. cancel. inv H. inv H0.
    eapply IHl; eauto.
Qed.

Lemma tree_rep_has_children: forall root l C C',
    !!(pc_global_inv root l C) && tree_rep l C C' |--
                                           !!(forall x, In x l ->
                                                        has_child_or_none x left_tn l /\
                                                          has_child_or_none x right_tn l).
Proof.
  intros. apply derives_trans with (!!(pc_global_inv root l C) && pc_tree_rep l C).
  - Intros. entailer !. apply tree_rep_impl_pc_tree_rep.
  - apply pc_tree_rep_has_children.
Qed.

Lemma tree_rep_is_ptr_null: forall n l C1 C2,
    In n l -> tree_rep l C1 C2 |-- !! is_pointer_or_null (addr_tn n).
Proof.
  intros. sep_apply tree_rep_impl_pc_tree_rep. now apply pc_tree_rep_is_ptr_null.
Qed.

Lemma tree_rep_saturate_local: forall root l C C',
    pc_global_inv root l C -> tree_rep l C C' |--
                                       !! is_pointer_or_null (addr_tn root).
Proof.
  intros. sep_apply tree_rep_impl_pc_tree_rep.
  now apply pc_tree_rep_saturate_local.
Qed.

Lemma tree_rep_neq_nullval: forall n l C1 C2,
    In n l -> tree_rep l C1 C2 |-- !! (addr_tn n <> nullval).
Proof.
  intros. sep_apply tree_rep_impl_pc_tree_rep.
  rewrite (pc_tree_rep_In_eq n); auto. Intros nI l' Cl.
  unfold pc_node_rep. Intros. entailer !.
Qed.

Lemma tree_rep_cons: forall n l C1 C2,
    tree_rep (n :: l) C1 C2 =
      EX nI nS Cl1 Cl2, !! (intJoin nI Cl1 C1 /\ intJoin nS Cl2 C2) &&
                          node_rep n nI nS * tree_rep l Cl1 Cl2.
Proof.
  intros. apply pred_ext.
  - unfold tree_rep. Intros fpc fs. destruct fpc. 1: simpl in H1; lia.
    destruct fs. 1: simpl in H2; lia. inv H. inv H0.
    simpl. Exists p b lj lj0. entailer!. Exists fpc fs. entailer !.
  - Intros nI nS Cl1 Cl2. unfold tree_rep. Intros fpc fs.
    Exists (nI :: fpc) (nS :: fs). simpl. entailer!.
    split; econstructor; eauto.
Qed.

Lemma tree_rep_perm': forall l1 l2 C1 C2,
    Permutation l1 l2 -> tree_rep l1 C1 C2 |-- tree_rep l2 C1 C2.
Proof.
  intros. revert C1 C2. induction H; auto; intros.
  - rewrite !tree_rep_cons. Intros nI nS Cl1 Cl2. Exists nI nS Cl1 Cl2. entailer !.
  - rewrite tree_rep_cons. Intros nIy nSy Cl1y Cl2y. do 2 rewrite tree_rep_cons.
    Intros nIx nSx Cl1x Cl2x. Exists nIx nSx. apply intJoin_comm in H, H0.
    destruct (intJoin_assoc _ _ _ _ _ H1 H) as [xyI []]. Exists xyI.
    destruct (intJoin_assoc _ _ _ _ _ H2 H0) as [xyS []]. Exists xyS. entailer !.
    rewrite tree_rep_cons. Exists nIy nSy Cl1x Cl2x. apply intJoin_comm in H3, H5.
    entailer !.
  - now transitivity (tree_rep l' C1 C2).
Qed.

Lemma tree_rep_perm: forall l1 l2 C1 C2,
    Permutation l1 l2 -> tree_rep l1 C1 C2 = tree_rep l2 C1 C2.
Proof. intros. apply pred_ext; apply tree_rep_perm'; auto. now symmetry. Qed.

Lemma tree_rep_In_eq: forall n l C1 C2,
    In n l -> tree_rep l C1 C2 =
                EX nI nS l' Cl1 Cl2, !! (intJoin nI Cl1 C1 /\ intJoin nS Cl2 C2 /\
                                           Permutation (n :: l') l) &&
                                       (node_rep n nI nS * tree_rep l' Cl1 Cl2).
Proof.
  intros. apply pred_ext.
  - apply in_split in H. destruct H as [l1 [l2 ?]]. subst l.
    pose proof (Permutation_middle l1 l2 n).
    rewrite <- (tree_rep_perm (n :: l1 ++ l2)); auto. rewrite tree_rep_cons.
    Intros nI nS Cl1 Cl2. Exists nI nS (l1 ++ l2) Cl1 Cl2. entailer !.
  - Intros nI nS l' Cl1 Cl2. rewrite <- (tree_rep_perm (n :: l') l); auto.
    rewrite tree_rep_cons. Exists nI nS Cl1 Cl2. entailer !.
Qed.

Lemma tree_rep_root_no_parent: forall root l C1 C2,
    !!(pc_global_inv root l C1) && tree_rep l C1 C2 |--
                                            !! (forall x, In x l -> left_tn x <> addr_tn root /\
                                                                      right_tn x <> addr_tn root).
Proof.
  intros. Intros. sep_apply tree_rep_impl_pc_tree_rep.
  sep_apply (pc_tree_rep_root_no_parent root); auto. entailer !.
Qed.

Lemma tree_rep_has_unique_parent: forall root l C1 C2,
    !!(pc_global_inv root l C1) && tree_rep l C1 C2|--
                                            !!(forall x, In x l -> x ≠ root ->
                                                         exists ! p, In p l /\ p ≠ x /\
                                                                       (p.(left_tn) = x.(addr_tn) \/
                                                                          p.(right_tn) = x.(addr_tn))).
Proof.
  intros. Intros. sep_apply tree_rep_impl_pc_tree_rep.
  sep_apply (pc_tree_rep_has_unique_parent root); auto. Intros.
  apply prop_right. intros. apply H0; auto.
Qed.

Lemma node_rep_valid_ptr: forall n nI nS,
    node_rep n nI nS |-- valid_pointer (addr_tn n).
Proof. intros. unfold node_rep. entailer !. Qed.

Lemma tree_rep_local_inv: forall l,
    iter_sepcon (fun x => node_rep x.1 x.2.1 x.2.2) l |--
                !! (forall x, In x l -> pc_local_inv x.1 x.2.1 /\
                                          inset_local_inv x.1 x.2.2).
Proof.
  intros. induction l.
  - apply prop_right. intros. inversion H.
  - simpl. sep_apply IHl. Intros. unfold node_rep at 2. Intros. apply prop_right.
    intros. destruct H2.
    + subst a. now split.
    + now apply H.
Qed.

Lemma tree_rep_nodup_addr: forall l C1 C2,
    tree_rep l C1 C2 |-- !! List.NoDup (map addr_tn l).
Proof.
  intros. sep_apply tree_rep_impl_pc_tree_rep. apply pc_tree_rep_nodup_addr.
Qed.

Lemma tree_rep_left_right: forall root l C1 C2,
    !!(pc_global_inv root l C1) && tree_rep l C1 C2 |--
             !! (forall x, In x l ->
                          left_tn x = right_tn x /\ left_tn x = nullval \/ left_tn x ≠ right_tn x).
Proof.
  intros. Intros. sep_apply tree_rep_impl_pc_tree_rep.
  sep_apply (pc_tree_rep_left_right root); auto. Intros.
  apply prop_right. intros. apply H0; auto.
Qed.

Lemma tree_rep_inset_cnnt:
  ∀ (root : TreeNode) (l : list TreeNode) (Cpc : pc_flowint) (Cs : bst_inset_flowint),
    pc_global_inv root l Cpc → inset_global_inv root l Cs
    → ∀ (fpc : list pc_flowint) (fs : list bst_inset_flowint),
        list_join fpc Cpc → list_join fs Cs → length fpc = length l → length fs = length l
        → iter_sepcon
            (λ x : TreeNode * (pc_flowint * bst_inset_flowint),
                node_rep x.1 x.2.1 x.2.2) (combine l (combine fpc fs))
            |-- !! (∀ x y : TreeNode * (pc_flowint * bst_inset_flowint),
                       In x (combine l (combine fpc fs)) → In y (combine l (combine fpc fs))
                       → left_tn x.1 = addr_tn y.1 ∨ right_tn x.1 = addr_tn y.1 → out x.2.2 y.1 = inf y.2.2 y.1).
Proof.
  intros. assert (Hit: iter_sepcon
                 (λ x : TreeNode * (pc_flowint * bst_inset_flowint),
                     node_rep x.1 x.2.1 x.2.2) (combine l (combine fpc fs)) |-- tree_rep l Cpc Cs). {
    unfold tree_rep. Exists fpc fs. entailer !. }
  assert_PROP (∀ x : TreeNode, In x l → x ≠ root →
                               ∃ y, unique (λ p : TreeNode, In p l ∧ p ≠ x ∧
                                                              (left_tn p = addr_tn x ∨ right_tn p = addr_tn x)) y). {
    sep_apply Hit. sep_apply (tree_rep_has_unique_parent root); auto. entailer !. } rename H5 into Hunq.
  assert_PROP (forall n, In n l -> addr_tn n ≠ nullval). {
    sep_apply Hit. eapply derives_trans. 2: apply allp_prop_left. apply allp_right. intros. rewrite prop_impl.
    apply imp_andp_adjoint. Intros.  now apply tree_rep_neq_nullval. } rename H5 into Hnull.
  assert_PROP (∀ x : TreeNode, In x l → left_tn x ≠ addr_tn root ∧ right_tn x ≠ addr_tn root). {
    sep_apply Hit. sep_apply (tree_rep_root_no_parent root); auto. entailer !. } rename H5 into Hrnp.
  assert_PROP (List.NoDup (map addr_tn l)). { sep_apply Hit. sep_apply tree_rep_nodup_addr. entailer !. }
  rename H5 into Hno. sep_apply tree_rep_local_inv. Intros. apply prop_right. rename H5 into Hloc. intros.
  destruct (Hloc _ H5). destruct (Hloc _ H6). destruct x as [x [xP xS]]. destruct y as [y [yP yS]].
  simpl fst in *. simpl snd in *. pose proof (in_combine_r _ _ _ _ H6). apply in_combine_r in H12.
  apply In_Permutation_cons in H12. destruct H12 as [fsl ?]. eapply list_join_perm in H2; eauto.
  apply list_join_cons_inv in H2. destruct H2 as [Cl [? ?]]. red in H13.  
  assert (x ≠ y) by (destruct H8 as [_ [? [? _]]]; intro; subst; destruct H7; exfalso; auto).
  pose proof (in_combine_r _ _ _ _ H5). apply in_combine_r in H15. eapply Permutation_in in H15; eauto.
  simpl in H15. destruct H15.
  - subst. destruct H9 as [_ [? _]]. destruct H11 as [_ [? _]]. rewrite H9 in H11.
    rewrite set_eq_subseteq in H11. destruct H11. rewrite singleton_subseteq in H11. exfalso. now apply H14.
  - destruct H0 as [[? ?] [? ?]]. pose proof (intJoin_unfold_inf_1 _ _ _ H13 H0 y).
    assert (y ∈ domm yS) by (destruct H11 as [? [? ?]]; rewrite H20; now apply elem_of_singleton_2).
    specialize (H19 H20). pose proof (intJoin_dom _ _ _ H13 H0). pose proof (in_combine_l _ _ _ _ H5).
    assert (y ∈ domm Cs) by (rewrite H21; rewrite elem_of_union; now left).
    assert (y ≠ root) by (intro; subst; destruct (Hrnp _ H22); destruct H7; auto). rewrite H18 in H19; auto.
    rewrite ccm_left_id in H19. apply In_Permutation_cons in H15. destruct H15 as [fsr ?].
    eapply list_join_perm in H2; eauto. apply list_join_cons_inv in H2. destruct H2 as [Cr [? ?]]. red in H25.
    assert (✓ Cl) by (apply (intJoin_valid_proj2 _ _ _ H13); auto).
    assert (y ∉ domm Cl). {
      assert (intComposable yS Cl) by (eapply intComposable_valid; eauto). destruct H27 as [_ [_ [? _]]]. intro.
      now apply (H27 y). } rewrite (intJoin_unfold_out _ _ _ H25 H26 _ H27) in H19.
    assert (✓ Cr) by (apply (intJoin_valid_proj2 _ _ _ H25); auto).
    assert (y ∉ domm Cr). {
      pose proof (intJoin_dom _ _ _ H25 H26). intro. apply H27. rewrite H29. rewrite elem_of_union. now right. }
    rewrite (list_join_unfold_out _ _ H2 H28 _ H29) in H19.
    assert (forall zS, In zS fsr -> out zS y = ∅). {
      intros. assert (In zS (yS :: xS :: fsr)) by (now do 2 right).
      assert (Permutation fs (yS :: xS :: fsr)) by (transitivity (yS :: fsl); auto). symmetry in H32.
      eapply Permutation_in in H31; eauto. apply (In_snd_combine fpc) in H31. 2: lia. destruct H31 as [zP ?].
      apply (In_snd_combine l) in H31. 2: rewrite combine_length; lia. destruct H31 as [z ?].
      destruct (Hloc _ H31) as [_ ?]. simpl in H33. destruct H33 as [? [? [? ?]]]. specialize (H36 y).
      unfold inset_edgeFn in H36. pose proof (in_combine_l _ _ _ _ H6). pose proof (Hnull _ H37).
      rewrite <- val_eqb_false in H38. rewrite H38 in H36. clear H38. apply in_combine_l in H31.
      assert (z ≠ y). {
        intro. assert (intComposable yS Cl) by (eapply intComposable_valid; eauto). destruct H39 as [_ [_ [? _]]].
        pose proof (H39 y). specialize (H40 H20). apply H40. rewrite (intJoin_dom xS Cr); auto.
        apply elem_of_union_r. subst z. pose proof (list_join_dom _ _ H2 H28 _ H30). rewrite elem_of_subseteq in H38.
        apply H38. rewrite H34. now apply elem_of_singleton_2. } destruct (In_Permutation_cons _ _ H37) as [ly ?].
      assert (In z ly). { apply (Permutation_in _ H39) in H31. simpl in H31. destruct H31; auto. exfalso; auto. }
      assert (addr_tn z ≠ addr_tn y). {
        apply (Permutation_map addr_tn) in H39. apply (Permutation_NoDup H39) in Hno. simpl in Hno.
        apply NoDup_cons_iff in Hno. destruct Hno as [Hno _]. intro. apply Hno. rewrite <- H41. now apply in_map. }
      rewrite <- val_eqb_false in H41. rewrite H41 in H36. simpl in H36. clear H41. specialize (Hunq _ H37 H24).
      destruct Hunq as [yPrnt Huni]. destruct Huni as [_ Huni]. assert (yPrnt = x) by (apply Huni; split; auto).
      subst yPrnt. assert (x ≠ z). {
        intro. assert (intComposable xS Cr) by (eapply intComposable_valid; eauto). destruct H42 as [_ [_ [? _]]].
        pose proof (H42 x). destruct H9 as [_ [? _]]. apply H43.
        - rewrite H9; now apply elem_of_singleton_2.
        - subst z. pose proof (list_join_dom _ _ H2 H28 _ H30). rewrite elem_of_subseteq in H41. apply H41.
          rewrite H34. now apply elem_of_singleton_2. }
      assert (val_eqb (addr_tn y) (left_tn z) = false). {
        rewrite val_eqb_false. intro. apply H41. apply Huni; auto. } rewrite H42 in H36.
      assert (val_eqb (addr_tn y) (right_tn z) = false). {
        rewrite val_eqb_false. intro. apply H41. apply Huni; auto. } now rewrite H43 in H36. }
    rewrite accumulate_zero in H19; auto. now rewrite ccm_right_id in H19.
Qed.

Lemma tree_rep_inset_out:
  ∀ (root : TreeNode) (l : list TreeNode) (Cpc : pc_flowint) (Cs : bst_inset_flowint),
    pc_global_inv root l Cpc → inset_global_inv root l Cs
    → ∀ (fpc : list pc_flowint) (fs : list bst_inset_flowint),
        list_join fpc Cpc → list_join fs Cs → length fpc = length l → length fs = length l
        → iter_sepcon
            (λ x : TreeNode * (pc_flowint * bst_inset_flowint),
                node_rep x.1 x.2.1 x.2.2) (combine l (combine fpc fs))
            |-- !! (∀ x y : TreeNode * (pc_flowint * bst_inset_flowint),
                       In x (combine l (combine fpc fs)) → In y (combine l (combine fpc fs))
                       → (left_tn x.1 = addr_tn y.1 → out x.2.2 y.1 = split_left (inf x.2.2 x.1) (key_tn x.1)) ∧
                           (right_tn x.1 = addr_tn y.1 → out x.2.2 y.1 = split_right (inf x.2.2 x.1) (key_tn x.1))).
Proof.
  intros. assert (Hit: iter_sepcon
                 (λ x : TreeNode * (pc_flowint * bst_inset_flowint),
                     node_rep x.1 x.2.1 x.2.2) (combine l (combine fpc fs)) |-- tree_rep l Cpc Cs). {
    unfold tree_rep. Exists fpc fs. entailer !. }
  assert_PROP (forall n, In n l -> addr_tn n ≠ nullval). {
    sep_apply Hit. eapply derives_trans. 2: apply allp_prop_left. apply allp_right. intros. rewrite prop_impl.
    apply imp_andp_adjoint. Intros.  now apply tree_rep_neq_nullval. } rename H5 into Hnull.
  assert_PROP (∀ x : TreeNode, In x l → left_tn x = right_tn x ∧ left_tn x = nullval ∨ left_tn x ≠ right_tn x). {
    sep_apply Hit. sep_apply (tree_rep_left_right root); auto. entailer !. } rename H5 into Hlr.
  assert_PROP (List.NoDup (map addr_tn l)). { sep_apply Hit. sep_apply tree_rep_nodup_addr. entailer !. }
  rename H5 into Hno. sep_apply tree_rep_local_inv. Intros. apply prop_right. rename H5 into Hloc. intros.
  destruct (Hloc _ H5). destruct (Hloc _ H6). destruct x as [x [xP xS]]. destruct y as [y [yP yS]].
  simpl fst in *. simpl snd in *. destruct H8 as [? [? [? ?]]]. specialize (H13 y). unfold inset_edgeFn in H13.
  assert (left_tn x = addr_tn y ∨ right_tn x = addr_tn y → val_eqb (addr_tn x) (addr_tn y) = false). {
    intros. assert (x ≠ y) by (destruct H7 as [_ [? [? _]]]; intro; subst; destruct H14; auto).
    apply in_combine_l in H5, H6. apply In_Permutation_cons in H5. destruct H5 as [l' ?].
    apply (Permutation_in _ H5) in H6. simpl in H6. destruct H6; [now exfalso|].
    apply (Permutation_map addr_tn) in H5. apply (Permutation_NoDup H5) in Hno. simpl in Hno.
    apply NoDup_cons_iff in Hno. destruct Hno as [Hno _]. rewrite val_eqb_false. intro. apply Hno.
    rewrite H16. now apply in_map. }
  assert (val_eqb (addr_tn y) nullval = false). {
    intros. apply in_combine_l in H6. apply Hnull in H6. now rewrite val_eqb_false. }
  split; intros; rewrite H14 in H13; auto; rewrite H15 in H13; simpl in H13.
  - symmetry in H16. rewrite <- val_eqb_true in H16. now rewrite H16 in H13.
  - apply in_combine_l in H5. specialize (Hlr _ H5). destruct Hlr as [[? ?] | ?].
    + rewrite H17 in H18. rewrite H16 in H18. rewrite val_eqb_false in H15. now exfalso.
    + assert (val_eqb (addr_tn y) (left_tn x) = false). {
        rewrite val_eqb_false. intro. rewrite H18 in H16. now apply H17. } rewrite H18 in H13.
      symmetry in H16. rewrite <- val_eqb_true in H16. now rewrite H16 in H13.
Qed.

Inductive ancestor: TreeNode -> TreeNode -> list TreeNode -> Prop :=
| ancestor_parent: forall x, ancestor x x (x :: nil)
| ancestor_more: forall x y z l, left_tn x = addr_tn z \/ right_tn x = addr_tn z ->
                                 ancestor z y l -> ancestor x y (x :: l).

Lemma tree_rep_root_for_all: forall root l Cpc Cs,
    !!(pc_global_inv root l Cpc /\ inset_global_inv root l Cs) &&
      tree_rep l Cpc Cs |--
               !! (forall x, In x l -> exists sl, ancestor root x sl /\ incl sl l).
Proof.
  intros. Intros. sep_apply (tree_rep_has_unique_parent root); auto. Intros. rename H1 into Huni.
  sep_apply tree_rep_nodup_addr. Intros. rename H1 into Hno.
  assert_PROP (forall n, In n l -> addr_tn n ≠ nullval). {
    eapply derives_trans. 2: apply allp_prop_left. apply allp_right. intros. rewrite prop_impl.
    apply imp_andp_adjoint. Intros.  now apply tree_rep_neq_nullval. } rename H1 into Hnull.
  sep_apply (tree_rep_left_right root); auto. Intros. rename H1 into Hlr. unfold tree_rep. Intros fpc fs.
  sep_apply (tree_rep_inset_cnnt root l Cpc Cs). Intros. rename H5 into Hcnt.
  sep_apply (tree_rep_inset_out root l Cpc Cs). Intros. rename H5 into Hout. sep_apply tree_rep_local_inv. Intros.
  apply prop_right.
  assert (forall x y, In x (combine l (combine fpc fs)) -> In y (combine l (combine fpc fs)) ->
                      left_tn x.1 = addr_tn y.1 \/ right_tn x.1 = addr_tn y.1 ->
                      inset y.2.2 y.1 ⊂ inset x.2.2 x.1). { admit. } intros. destruct (treenode_eq_dec x root).
  - subst. exists (root :: nil). split. 1: constructor. destruct H as [? [? [? [? ?]]]].
    repeat intro. simpl in H12. destruct H12; try easy. now subst.
  -
Abort.

Lemma tree_rep_inset_range:
  forall (l : list TreeNode) (Cpc : pc_flowint) (Cs : bst_inset_flowint)
         (fpc : list pc_flowint) (fs : list bst_inset_flowint) root,
    list_join fpc Cpc -> list_join fs Cs -> length fpc = length l ->
    length fs = length l -> pc_global_inv root l Cpc ->
    inset_global_inv root l Cs ->
    (forall x, In x (combine l (combine fpc fs)) ->
               pc_local_inv x.1 x.2.1 /\ inset_local_inv x.1 x.2.2) ->
    forall x xI xS y yI yS z,
      In (x, (xI, xS)) (combine l (combine fpc fs)) ->
      In (y, (yI, yS)) (combine l (combine fpc fs)) -> x ≠ y ->
      in_inset z xS x -> in_inset z yS y -> ancestor x y l \/ ancestor y x l.
Proof.
  intros.
Abort.

Definition lookup_inv (root: TreeNode) (b: val) (l: list TreeNode)
           (Cpc : pc_flowint) (Cs: bst_inset_flowint) (x: Z): environ -> mpred :=
  EX n: TreeNode, EX l': list TreeNode, EX nI: pc_flowint, EX Cl: pc_flowint,
            EX nS: bst_inset_flowint, EX Cls: bst_inset_flowint,
                PROP (intJoin nI Cl Cpc; intJoin nS Cls Cs;
                      if Val.eq (addr_tn n) nullval
                      then nI = ∅ /\ nS = ∅ /\ l' = l /\ Cl = Cpc /\ Cls = Cs /\
                             ~ In x (map key_tn l)
                      else in_inset x nS n /\ Permutation (n :: l') l)
                     LOCAL (temp _p (addr_tn n); temp _t b; temp _x (Vint (Int.repr x)))
                     SEP (data_at Tsh (tptr t_struct_tree) (addr_tn root) b;
                          if Val.eq (addr_tn n) nullval then emp else node_rep n nI nS;
                          tree_rep l' Cl Cls).


Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros. sep_apply (tree_rep_has_children root l Cpc Cs); auto.
  Intros. sep_apply (tree_rep_root_no_parent root); auto. Intros. rename H4 into Hr.
  sep_apply tree_rep_nodup_addr. Intros. rename H4 into Hno.
  sep_apply (tree_rep_has_unique_parent root); auto. Intros. rename H4 into Huni.
  sep_apply (tree_rep_left_right root); auto. Intros. rename H4 into Hlr. forward.
  - entailer. sep_apply (tree_rep_saturate_local root l Cpc Cs); auto. entailer !.
  - forward_while (lookup_inv root b l Cpc Cs x).
    + Exists root. destruct H1 as [_ [_ [_ [? _]]]].
      sep_apply (tree_rep_neq_nullval root l Cpc Cs). Intros.
      rewrite (tree_rep_In_eq root l Cpc Cs H1). Intros nI nS l' Cl1 Cl2.
      Exists l' nI Cl1 nS Cl2. if_tac. 1: now exfalso.
      assert_PROP (root ∈ domm nS). {
        unfold node_rep. Intros. apply prop_right. destruct H9 as [_ [? _]].
        rewrite H9. now apply elem_of_singleton_2. } entailer !.
      destruct H2 as [[? [_ [_ ?]]] _]. eapply inset_monotone; eauto.
    + if_tac.
      * Intros. subst. rewrite H4. entailer !.
      * sep_apply node_rep_valid_ptr. Intros. entailer !.
    + if_tac. 1: now exfalso. unfold node_rep. Intros. destruct H6.
      assert (In n l). { eapply Permutation_in; eauto. now left. }
      assert (data_at Tsh t_struct_tree
                      (Vint (Int.repr (key_tn n)),
                        (value_tn n, (left_tn n, right_tn n))) (addr_tn n) *
                tree_rep l' Cl Cls |-- tree_rep l Cpc Cs). {
        rewrite (tree_rep_In_eq n l Cpc Cs); auto. Exists nI nS l' Cl Cls.
        unfold node_rep. entailer !. } forward. specialize (H3 _ H11).
      destruct H3. forward_if.
      * forward; destruct H3 as [? | [p [? [? ?]]]].
        -- rewrite H3. entailer !.
        -- sep_apply H12. rewrite H16. sep_apply (tree_rep_is_ptr_null p l Cpc Cs). entailer !.
        -- Exists (empty_node, l, ∅ : pc_flowint, Cpc, ∅ : bst_inset_flowint, Cs). simpl fst. simpl snd.
           if_tac. 2: cbn in H15; now exfalso. clear H15. entailer. apply andp_right. 2: sep_apply H12; entailer !.
           unfold tree_rep. Intros fpc fs. sep_apply tree_rep_local_inv. Intros. apply prop_right.
           split; [|split]; [apply intJoin_left_unit..|]. destruct H9 as [? [? [? [? [? [? [? ?]]]]]]].
           rewrite Int.signed_repr in H14; auto.
        (* if the key was in some other node, then it would be removed from
           the inset of all that node's descendants, contradicting the assumption
           that it’s in the inset of a leaf node.  *)
           intro. apply list_in_map_inv in H32. destruct H32 as [xN [? ?]].
           assert (In xN l'). {
            symmetry in H10. apply (Permutation_in xN H10) in H33. destruct H33; auto. subst. lia. }
          admit.
        -- rewrite H16. assert (In p l'). {
            symmetry in H10. apply Permutation_in with (l' := n :: l') in H3; auto.
            simpl in H3. destruct H3; auto. symmetry in H3. now exfalso. }
          sep_apply (tree_rep_neq_nullval p l' Cl Cls). Intros.
           rewrite (tree_rep_In_eq p l' Cl Cls); auto. Intros pI pS pl pClpc pCls.
           apply intJoin_comm in H4, H5. destruct (intJoin_assoc _ _ _ _ _ H19 H4) as [pIpc [? ?]].
           destruct (intJoin_assoc _ _ _ _ _ H20 H5) as [pSs [? ?]].
           Exists (p, (n :: pl), pI, pIpc, pS, pSs). simpl fst. simpl snd. if_tac.
           1: now exfalso. unfold tree_rep at 1. Intros fpc fs. sep_apply tree_rep_local_inv. Intros.
           gather_SEP (iter_sepcon _ _) (node_rep _ _ _) (data_at Tsh t_struct_tree _ (addr_tn n)).
           replace_SEP 0 (iter_sepcon (λ y, node_rep y.1 y.2.1 y.2.2)
                                      (combine (p :: n :: pl) (combine (pI :: nI :: fpc) (pS :: nS :: fs)))). {
            entailer !. simpl combine. simpl iter_sepcon. cancel. unfold node_rep. rewrite <- H16. entailer !. }
          assert (p :: n :: pl ≡ₚ l). {
            transitivity (n :: p :: pl); [apply perm_swap | transitivity (n :: l'); auto]. } symmetry in H32.
           assert (pc_global_inv root (p :: n :: pl) Cpc) by (eapply pc_global_inv_perm; eauto).
           assert (inset_global_inv root (p :: n :: pl) Cs) by (eapply inset_global_inv_perm; eauto).
           assert (list_join (pI :: nI :: fpc) Cpc). {
            apply join_cons with pIpc; auto. apply intJoin_comm in H22. apply join_cons with pClpc; auto. }
          assert (list_join (pS :: nS :: fs) Cs). {
            apply join_cons with pSs; auto. apply intJoin_comm in H24. apply join_cons with pCls; auto. }
          assert (length (pI :: nI :: fpc) = length (p :: n :: pl)) by (simpl; auto).
           assert (length (pS :: nS :: fs) = length (p :: n :: pl)) by (simpl; auto).
           sep_apply (tree_rep_inset_cnnt root (p :: n :: pl) Cpc Cs); auto. Intros.
           sep_apply (tree_rep_inset_out root (p :: n :: pl) Cpc Cs); auto. Intros.
           assert (In (p, (pI, pS)) (combine (p :: n :: pl)
                                             (combine (pI :: nI :: fpc) (pS :: nS :: fs)))) by (simpl; now left).
           assert (In (n, (nI, nS)) (combine (p :: n :: pl) (combine (pI :: nI :: fpc) (pS :: nS :: fs)))). {
            simpl. right. now left. } specialize (H39 _ _ H42 H41). specialize (H40 _ _ H42 H41). simpl in H39, H40.
           destruct H40. specialize (H39 (or_introl H16)). specialize (H40 H16). symmetry in H32. entailer !.
           ++ red in H6. apply nzmap_elem_of_dom in H6. red in H6. destruct H6 as [a ?].
              red. rewrite <- H39. rewrite H40. rewrite nzmap_elem_of_dom. exists a.
              apply split_left_lookup. destruct H9 as [? _]. rewrite Int.signed_repr in H14; auto.
           ++ simpl iter_sepcon. cancel. rewrite tree_rep_cons. Exists nI nS pClpc pCls.
              apply intJoin_comm in H22, H24. unfold tree_rep. Exists fpc fs. entailer !.
      * forward_if.
        -- forward; destruct H13 as [? | [p [? [? ?]]]].
           ++ rewrite H13; entailer !.
           ++ sep_apply H12. rewrite H17. sep_apply (tree_rep_is_ptr_null p l Cpc Cs). entailer !.
           ++ admit.
           ++ rewrite H17. assert (In p l'). {
               symmetry in H10. apply Permutation_in with (l' := n :: l') in H13; auto.
               simpl in H13. destruct H13; auto. symmetry in H13. now exfalso. }
             sep_apply (tree_rep_neq_nullval p l' Cl Cls). Intros.
              rewrite (tree_rep_In_eq p l' Cl Cls); auto. Intros pI pS pl pClpc pCls.
              apply intJoin_comm in H4, H5. destruct (intJoin_assoc _ _ _ _ _ H20 H4) as [pIpc [? ?]].
              destruct (intJoin_assoc _ _ _ _ _ H21 H5) as [pSs [? ?]]. Exists (p, (n :: pl), pI, pIpc, pS, pSs).
              simpl fst. simpl snd. if_tac. 1: now exfalso. unfold tree_rep at 1. Intros fpc fs.
              sep_apply tree_rep_local_inv. Intros.
              gather_SEP (iter_sepcon _ _) (node_rep _ _ _) (data_at Tsh t_struct_tree _ (addr_tn n)).
              replace_SEP 0 (iter_sepcon (λ y, node_rep y.1 y.2.1 y.2.2)
                                      (combine (p :: n :: pl) (combine (pI :: nI :: fpc) (pS :: nS :: fs)))). {
            entailer !. simpl combine. simpl iter_sepcon. cancel. unfold node_rep. rewrite <- H17. entailer !. }
          assert (p :: n :: pl ≡ₚ l). {
            transitivity (n :: p :: pl); [apply perm_swap | transitivity (n :: l'); auto]. } symmetry in H33.
           assert (pc_global_inv root (p :: n :: pl) Cpc) by (eapply pc_global_inv_perm; eauto).
           assert (inset_global_inv root (p :: n :: pl) Cs) by (eapply inset_global_inv_perm; eauto).
           assert (list_join (pI :: nI :: fpc) Cpc). {
            apply join_cons with pIpc; auto. apply intJoin_comm in H23. apply join_cons with pClpc; auto. }
          assert (list_join (pS :: nS :: fs) Cs). {
            apply join_cons with pSs; auto. apply intJoin_comm in H25. apply join_cons with pCls; auto. }
          assert (length (pI :: nI :: fpc) = length (p :: n :: pl)) by (simpl; auto).
           assert (length (pS :: nS :: fs) = length (p :: n :: pl)) by (simpl; auto).
           sep_apply (tree_rep_inset_cnnt root (p :: n :: pl) Cpc Cs); auto. Intros.
           sep_apply (tree_rep_inset_out root (p :: n :: pl) Cpc Cs); auto. Intros.
           assert (In (p, (pI, pS)) (combine (p :: n :: pl)
                                             (combine (pI :: nI :: fpc) (pS :: nS :: fs)))) by (simpl; now left).
           assert (In (n, (nI, nS)) (combine (p :: n :: pl) (combine (pI :: nI :: fpc) (pS :: nS :: fs)))). {
            simpl. right. now left. } specialize (H40 _ _ H43 H42). specialize (H41 _ _ H43 H42). simpl in H41, H40.
           destruct H41. specialize (H40 (or_intror H17)). specialize (H44 H17). symmetry in H33. entailer !.
           ** red in H6. apply nzmap_elem_of_dom in H6. red in H6. destruct H6 as [a ?].
              red. rewrite <- H40. rewrite H44. rewrite nzmap_elem_of_dom. exists a. apply split_right_lookup.
              destruct H9 as [? _]. rewrite Int.signed_repr in H15; auto. split; auto. lia.
           ** simpl iter_sepcon. cancel. rewrite tree_rep_cons. Exists nI nS pClpc pCls.
              apply intJoin_comm in H23, H25. unfold tree_rep. Exists fpc fs. entailer !.
        -- forward; destruct H9 as [? [? [? [? [? [? [? ?]]]]]]].
           ++ entailer !.
           ++ sep_apply H12. forward. Exists (value_tn n). unfold treebox_rep.
              entailer !. right. exists n. split; [|split]; auto.
              rewrite Int.signed_repr in H14, H15; auto. lia.
    + if_tac. 2: now exfalso. forward. Exists nullval.
      destruct H6 as [? [? [? [? [? ?]]]]]. entailer !. unfold treebox_rep.
      entailer !.
Abort.
