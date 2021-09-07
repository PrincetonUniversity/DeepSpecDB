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
  intros. apply derives_trans with (pc_tree_rep l C1).
  - apply tree_rep_impl_pc_tree_rep.
  - now apply pc_tree_rep_is_ptr_null.
Qed.

Lemma tree_rep_saturate_local: forall root l C C',
    pc_global_inv root l C -> tree_rep l C C' |--
                                          !! is_pointer_or_null (addr_tn root).
Proof.
  intros. apply derives_trans with (pc_tree_rep l C).
  - apply tree_rep_impl_pc_tree_rep.
  - now apply pc_tree_rep_saturate_local.
Qed.

Lemma tree_rep_neq_nullval: forall n l C1 C2,
    In n l -> tree_rep l C1 C2 |-- !! (addr_tn n <> nullval).
Proof.
  intros. apply derives_trans with (pc_tree_rep l C1).
  - apply tree_rep_impl_pc_tree_rep.
  - rewrite (pc_tree_rep_In_eq n); auto. Intros nI l' Cl.
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
  intros. Intros. eapply derives_trans. 1: apply tree_rep_impl_pc_tree_rep.
  sep_apply (pc_tree_rep_root_no_parent root); auto. entailer !.
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
  forward.
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
      * forward; sep_apply H12; destruct H3 as [? | [p [? [? ?]]]].
        -- rewrite H3. entailer !.
        -- rewrite H16. sep_apply (tree_rep_is_ptr_null p l Cpc Cs). entailer !.
        -- admit.
        -- rewrite H16. sep_apply (tree_rep_neq_nullval p l Cpc Cs). Intros.
           rewrite (tree_rep_In_eq p l Cpc Cs); auto. Intros pI pS pl pClpc pCls.
           Exists (p, pl, pI, pClpc, pS, pCls). simpl fst. simpl snd. if_tac.
           1: now exfalso. unfold node_rep. Intros. unfold tree_rep at 1.
           Intros fpc fs. sep_apply tree_rep_local_inv. Intros. rename H28 into Hl.
           entailer !.
           ++ destruct H9 as [? [? [? [? [? [? [? ?]]]]]]].
              rewrite Int.signed_repr in H14; auto. destruct H8 as [? [? [? ?]]].
              specialize (H42 p). unfold inset_edgeFn in H42. red.
              rewrite <- H16 in H42. rewrite <- val_eqb_false in H33.
              rewrite H33 in H42. rewrite <- H16 in H17.
              rewrite <- val_eqb_false in H17. rewrite H17 in H42. simpl in H42.
              rewrite val_eqb_refl in H42. red in H6. apply nzmap_elem_of_dom in H6.
              red in H6. assert (p ≠ root). {
                intro. subst p. destruct (Hr _ H11). auto. }
              destruct H6 as [a ?].
              assert (x ∈ dom_ms (out nS p)). {
                rewrite nzmap_elem_of_dom. exists a. rewrite H42.
                apply split_left_lookup. now split. } rename H44 into Hi.
              assert (inf pS p = out nS p). {
                destruct H2 as [[? ?] [? ?]]. destruct H22 as [_ [? _]].
                pose proof (intJoin_unfold_inf_1 _ _ _ H19 H2 p).
                assert (p ∈ domm pS). {
                  rewrite H22. now apply elem_of_singleton_2. } specialize (H47 H48).
                pose proof (intJoin_dom _ _ _ H19 H2).
                assert (p ∈ domm Cs). {
                  rewrite H49. rewrite elem_of_union. now left. }
                rewrite H46 in H47; auto. rewrite ccm_left_id in H47.
                assert (✓ pCls) by (apply (intJoin_valid_proj2 _ _ _ H19); auto).
                assert (p ∉ domm pCls). {
                  assert (intComposable pS pCls) by
                      (eapply intComposable_valid; eauto).
                  destruct H52 as [_ [_ [? _]]]. intro. now apply (H52 p). }
                rewrite (list_join_unfold_out _ _ H25 H51 _ H52) in H47.
                assert (In n pl). {
                  symmetry in H20.
                  apply Permutation_in with (l' := p :: pl) in H11; auto.
                  simpl in H11. destruct H11; auto. now exfalso. }
                  
                admit. }
              admit.
           ++ unfold tree_rep. Exists fpc fs. entailer !.
      * forward_if.
        -- forward; sep_apply H12; destruct H13 as [? | [p [? [? ?]]]].
           ++ rewrite H13; entailer !.
           ++ rewrite H17. sep_apply (tree_rep_is_ptr_null p l Cpc Cs). entailer !.
           ++ admit.
           ++ rewrite H17. sep_apply (tree_rep_neq_nullval p l Cpc Cs). Intros.
           rewrite (tree_rep_In_eq p l Cpc Cs); auto. Intros pI pS pl pClpc pCls.
           Exists (p, pl, pI, pClpc, pS, pCls). simpl fst. simpl snd. if_tac.
           1: now exfalso. entailer !. admit.
        -- forward; destruct H9 as [? [? [? [? [? [? [? ?]]]]]]].
           ++ entailer !.
           ++ sep_apply H12. forward. Exists (value_tn n). unfold treebox_rep.
              entailer !. right. exists n. split; [|split]; auto.
              rewrite Int.signed_repr in H14, H15; auto. lia.
    + if_tac. 2: now exfalso. forward. Exists nullval.
      destruct H6 as [? [? [? [? [? ?]]]]]. entailer !. unfold treebox_rep.
      entailer !.
Abort.
