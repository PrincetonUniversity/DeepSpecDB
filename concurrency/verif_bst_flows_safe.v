Require Import bst.puretree.
Require Import VST.floyd.proofauto.
Require Import VST.progs.bst.
Require Import VST.msl.iter_sepcon.
Require Import bst.flows.
Require Import bst.val_countable.
Require Import bst.sepalg_ext.

Open Scope Z_scope.
Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.

Record TreeNode :=
  { addr_tn: val;
    key_tn: Z;
    value_tn: val;
    left_tn: val;
    right_tn: val
  }.

Instance treenode_eq_dec: EqDecision TreeNode.
Proof. hnf; intros. hnf. decide equality; subst; try apply Val.eq. apply Z.eq_dec. Qed.

Local Definition treenode_eq_type: Type := val * Z * val * val * val.

Local Instance treenode_eq_type_countable: Countable treenode_eq_type.
Proof. typeclasses eauto. Qed.

Local Definition treenode2eq (t: TreeNode) : treenode_eq_type :=
  (addr_tn t, key_tn t, value_tn t, left_tn t, right_tn t).

Local Definition eq2treenode (teq: treenode_eq_type): TreeNode :=
  match teq with | (a, k, v, l, r) => Build_TreeNode a k v l r end.

Local Lemma treenode_eq_inj: forall v, eq2treenode (treenode2eq v) = v.
Proof. intros. destruct v. easy. Qed.

Instance treenode_countable: Countable TreeNode :=
  inj_countable' treenode2eq eq2treenode treenode_eq_inj.

Definition pc_flowint := @flowintR TreeNode _ _ nat nat_ccm.

Definition val_eqb (x y: val): bool := if Val.eq x y then true else false.

Lemma val_eqb_true: forall x y, val_eqb x y = true <-> x = y.
Proof.
  intros. unfold val_eqb. destruct (Val.eq x y); split; auto. intros. discriminate.
Qed.

Lemma val_eqb_false: forall x y, val_eqb x y = false <-> x <> y.
Proof.
  intros. unfold val_eqb. destruct (Val.eq x y); split; auto.
  intros. exfalso; auto.
Qed.

Lemma val_eqb_refl: forall x, val_eqb x x = true.
Proof. intros. now rewrite val_eqb_true. Qed.

Definition pc_edgeFn (x y: TreeNode): nat -> nat :=
  fun v => if ((negb (val_eqb x.(addr_tn) y.(addr_tn))) &&
               (negb (val_eqb y.(addr_tn) nullval)) &&
               ((val_eqb y.(addr_tn) x.(left_tn)) ||
                (val_eqb y.(addr_tn) x.(right_tn))))%bool then v else O.

Definition address_in (n: TreeNode) (I: pc_flowint): Prop :=
  exists t, t ∈ domm I /\ addr_tn n = addr_tn t.

Lemma address_not_in_domm: forall n I, ~ address_in n I -> n ∉ domm I.
Proof. repeat intro. apply H. red. exists n. split; auto. Qed.

Definition pc_global_inv (root: TreeNode) (NS: list TreeNode) (Ipc: pc_flowint): Prop :=
  ✓Ipc /\ (forall n, n ∈ domm Ipc -> n <> root -> inf Ipc n = O) /\
  (inf Ipc root = 1%nat) /\ (In root NS) /\
  (forall n, ~ address_in n Ipc -> out Ipc n = O) /\ (domm Ipc = list_to_set NS).

Definition pc_local_inv (t: TreeNode) (It: pc_flowint): Prop :=
  Int.min_signed <= t.(key_tn) <= Int.max_signed /\
  t.(addr_tn) ≠ t.(left_tn) /\
  t.(addr_tn) ≠ t.(right_tn) /\
  tc_val (tptr Tvoid) t.(value_tn) /\
  ✓ It /\ inf It t = 1%nat /\
  (forall n, out It n = pc_edgeFn t n 1%nat) /\
  domm It = {[t]}.

Definition pc_node_rep (t: TreeNode) (It: pc_flowint): mpred :=
  !! pc_local_inv t It &&
  data_at Tsh t_struct_tree (Vint (Int.repr t.(key_tn)),
                             (t.(value_tn), (t.(left_tn), t.(right_tn)))) t.(addr_tn).

Definition pc_tree_rep (l: list TreeNode) (C: pc_flowint): mpred :=
  EX fl, !! (list_join fl C /\ Datatypes.length fl = Datatypes.length l) &&
         iter_sepcon (fun x => pc_node_rep x.1 x.2) (combine l fl).

Lemma pc_tree_rep_pc_local_inv: forall l,
    iter_sepcon (fun x => pc_node_rep x.1 x.2) l |--
                !!(forall x, In x l -> pc_local_inv x.1 x.2).
Proof.
  intros. induction l.
  - apply prop_right. intros. inversion H.
  - simpl.
    assert_PROP (forall x, In x l -> pc_local_inv x.1 x.2). {
      sep_apply IHl. Intros. apply prop_right. auto. }
    unfold pc_node_rep at 1. Intros. apply prop_right. intros. destruct H1; auto.
    now subst.
Qed.

Lemma iter_node_rep_nodup_addr: forall l,
    iter_sepcon (fun x => pc_node_rep x.1 x.2) l |--
                !! (List.NoDup (map (fun x => addr_tn (fst x)) l)).
Proof.
  intros. induction l.
  - apply prop_right. intros. constructor.
  - simpl. sep_apply IHl. Intros.
    assert_PROP (~ In (addr_tn a.1) (map (λ x : TreeNode * pc_flowint, addr_tn x.1) l)). {
      apply not_prop_right. intros. apply list_in_map_inv in H0. destruct H0 as [y [? ?]].
      apply (iter_sepcon_in_true (λ x : TreeNode * pc_flowint, pc_node_rep x.1 x.2)) in H1.
      sep_apply H1. unfold pc_node_rep. Intros. rewrite H0.
      sep_apply data_at_conflict; auto. entailer !. } apply prop_right.
    now constructor.
Qed.

Lemma In_fst_pair: forall {A B: Type} (l: list (A * B)) x,
    In x (map fst l) -> exists y, In (x, y) l.
Proof.
  intros until l. induction l; intros; simpl in H. 1: now exfalso. destruct H.
  - destruct a. simpl in *. subst x. exists b. now left.
  - specialize (IHl _ H). destruct IHl as [y ?]. exists y. simpl. now right.
Qed.

Lemma In_fst_combine: forall {A B: Type} (l1: list A) (l2: list B) x,
    (Datatypes.length l1 <= Datatypes.length l2)%nat ->
    In x l1 -> exists y, In (x, y) (combine l1 l2).
Proof.
  intros. revert l2 H H0. induction l1; intros.
  - inversion H0.
  - destruct l2; simpl in H. 1: lia. simpl in H0. destruct H0.
    + subst. exists b. simpl. now left.
    + assert (length l1 <= length l2)%nat by lia. specialize (IHl1 _ H1 H0).
      destruct IHl1 as [y ?]. simpl. exists y. now right.
Qed.

Lemma In_snd_pair: forall {A B: Type} (l: list (A * B)) x,
    In x (map snd l) -> exists y, In (y, x) l.
Proof.
  intros until l. induction l; intros; simpl in H. 1: now exfalso. destruct H.
  - destruct a. simpl in *. subst x. exists a. now left.
  - specialize (IHl _ H). destruct IHl as [y ?]. exists y. simpl. now right.
Qed.

Lemma In_snd_combine: forall {A B: Type} (l1: list A) (l2: list B) x,
    (Datatypes.length l2 <= Datatypes.length l1)%nat ->
    In x l2 -> exists y, In (y, x) (combine l1 l2).
Proof.
  intros. revert l2 H H0. induction l1; intros.
  - simpl in H. destruct l2; [inversion H0 | simpl in H; lia].
  - destruct l2; simpl in H. 1: inversion H0. simpl in H0. destruct H0.
    + subst. exists a. simpl. now left.
    + assert (length l2 <= length l1)%nat by lia. specialize (IHl1 _ H1 H0).
      destruct IHl1 as [y ?]. simpl. exists y. now right.
Qed.

Lemma In_pair_snd: forall {A B: Type} (l: list (A * B)) x y,
    In (x, y) l -> In y (map snd l).
Proof.
  intros. induction l. 1: inversion H. simpl in H. destruct H.
  - destruct a. inversion H. simpl. now left.
  - simpl. right. auto.
Qed.

Lemma In_pair_fst: forall {A B: Type} (l: list (A * B)) x y,
    In (x, y) l -> In x (map fst l).
Proof.
  intros. induction l. 1: inversion H. simpl in H. destruct H.
  - destruct a. inversion H. simpl. now left.
  - simpl. right. auto.
Qed.

Lemma sum_0_0:
  ∀ (A : Type) (f : A → nat) (l : list A),
    foldr (λ (x : A) (v : nat), (f x + v)%nat) O l = O
    → ∀ y : A, In y l → f y = 0%nat.
Proof.
  intros A f l H4. clear -H4. revert l H4. induction l; intros. 1: inversion H.
  simpl in H. simpl in H4. apply Nat.eq_add_0 in H4. destruct H4.
  destruct H; [subst | apply IHl]; easy.
Qed.

Lemma sum_0_1 {A: Type}: forall (f: A -> nat) (l: list A),
    fold_right (fun x v => (f x + v)%nat) O l = 1%nat ->
              exists ! y, In y l /\ f y = 1%nat.
Proof.
  intros until l. induction l; intros; simpl in H. 1: now apply n_Sn in H.
  assert (f a = O \/ f a = 1%nat) by lia. destruct H0; rewrite H0 in H; simpl in H.
  - apply IHl in H. destruct H as [y [[? ?] ?]]. exists y. simpl; split; auto.
    intros. destruct H3. destruct H3. 2: now apply H2. subst. rewrite H0 in H4. inv H4.
  - exists a. simpl; split; auto. intros. destruct H1. destruct H1; auto.
    assert (foldr (λ (x : A) (v : nat), (f x + v)%nat) 0%nat l = O) by lia.
    apply sum_0_0 with (y := x') in H3; auto. exfalso. rewrite H3 in H2. inv H2.
Qed.

Lemma list_join_domm: forall (l: list (TreeNode * pc_flowint)) C,
    ✓ C -> (forall x, In x l -> domm x.2 = {[x.1]}) -> list_join (map snd l) C ->
    domm C = list_to_set (map fst l).
Proof.
  induction l; intros; simpl in H1.
  - inversion H1. subst C. cbn. apply intEmp_domm.
  - destruct a as [ta Ia]. simpl in *. inversion H1; subst.
    red in H6. erewrite intJoin_dom; eauto. f_equal.
    + specialize (H0 (ta, Ia)). simpl in H0. apply H0. now left.
    + apply IHl; auto. now apply intJoin_valid_proj2 in H6.
Qed.

Lemma list_join_nodup_fst: forall (l: list (TreeNode * pc_flowint)) C,
    ✓ C -> (forall x, In x l -> domm x.2 = {[x.1]}) -> list_join (map snd l) C ->
    List.NoDup (map fst l).
Proof.
  induction l; intros; simpl in H1.
  - simpl. constructor.
  - destruct a as [ta Ia]. simpl in *. constructor; inversion H1; subst.
    + red in H6. destruct (intComposable_valid _ _ _ H6 H) as [_ [_ [? _]]]. intro.
      hnf in H2. apply list_join_domm in H4; auto.
      2: now apply intJoin_valid_proj2 in H6. specialize (H2 ta).
      rewrite H4 in H2. apply H2.
      * specialize (H0 (ta, Ia)). simpl in H0. rewrite H0. 2: now left.
        now apply elem_of_singleton_2.
      * rewrite elem_of_list_to_set. now rewrite elem_of_list_In.
    + apply IHl with lj; auto. eapply intJoin_valid_proj2; eauto.
Qed.

Lemma list_join_nodup_snd: forall (l: list (TreeNode * pc_flowint)) C,
    ✓ C -> (forall x, In x l -> domm x.2 = {[x.1]}) -> list_join (map snd l) C ->
    List.NoDup (map snd l).
Proof.
  intros. eapply list_join_nonempty_nodup; eauto. intros. apply In_snd_pair in H2.
  destruct H2 as [y ?]. specialize (H0 _ H2). simpl in H0. rewrite H0.
  apply non_empty_singleton_L.
Qed.

Lemma NoDup_pair_neq: forall {A B: Type} (l: list (A * B)) x y x0 y0,
    List.NoDup (map fst l) -> List.NoDup (map snd l) ->
    In (x, y) l -> In (x0, y0) l -> y ≠ y0 <-> x ≠ x0.
Proof.
  intros until l. induction l; intros. 1: inversion H1. destruct a as [a b].
  simpl in *. apply NoDup_cons_iff in H, H0. destruct H, H0. destruct H1, H2.
  - rewrite H1 in H2. inversion H2. tauto.
  - inversion H1; subst; clear H1. split; intro.
    + pose proof (In_pair_fst _ _ _ H2). intro. now subst.
    + pose proof (In_pair_snd _ _ _ H2). intro. now subst.
  - inversion H2; subst; clear H2. split; intro.
    + pose proof (In_pair_fst _ _ _ H1). intro. now subst.
    + pose proof (In_pair_snd _ _ _ H1). intro. now subst.
  - eapply IHl; eauto.
Qed.

Lemma NoDup_pair_eq: forall {A B: Type} (l: list (A * B)) x y x0 y0,
    List.NoDup (map fst l) -> List.NoDup (map snd l) ->
    In (x, y) l -> In (x0, y0) l -> y = y0 -> x = x0.
Proof.
  intros until l. induction l; intros. 1: inversion H1. destruct a as [a b].
  simpl in *. apply NoDup_cons_iff in H, H0. destruct H, H0. destruct H1, H2.
  - rewrite H1 in H2. now inversion H2.
  - inversion H1. subst. clear H1. pose proof (In_pair_snd _ _ _ H2). now exfalso.
  - inversion H2. subst. clear H2. pose proof (In_pair_snd _ _ _ H1). now exfalso.
  - eapply IHl; eauto.
Qed.

Lemma pc_tree_rep_nodup_addr: forall l C,
    pc_tree_rep l C |-- !! List.NoDup (map addr_tn l).
Proof.
  intros. unfold pc_tree_rep. Intros fl. sep_apply iter_node_rep_nodup_addr. Intros.
  apply prop_right. rewrite <- list_map_compose in H1. now rewrite combine_fst in H1.
Qed.

Lemma pc_tree_rep_cons: forall n l C,
    pc_tree_rep (n :: l) C =
    EX nI Cl, !! (intJoin nI Cl C) && pc_node_rep n nI * pc_tree_rep l Cl.
Proof.
  intros. apply pred_ext.
  - unfold pc_tree_rep. Intros fl. destruct fl. 1: simpl in H0; lia. inv H.
    simpl. Exists p lj. entailer!. Exists fl. entailer !.
  - Intros nI Cl. unfold pc_tree_rep. Intros fl. Exists (nI :: fl). simpl. entailer!.
    econstructor; eauto.
Qed.

Lemma pc_tree_rep_perm': forall l1 l2 C,
    Permutation l1 l2 -> pc_tree_rep l1 C |-- pc_tree_rep l2 C.
Proof.
  intros. revert C. induction H; auto; intros.
  - rewrite !pc_tree_rep_cons. Intros nI Cl. Exists nI Cl. entailer !.
  - rewrite pc_tree_rep_cons. Intros nIy Cly. rewrite pc_tree_rep_cons.
    rewrite pc_tree_rep_cons. Intros nIx Clx. Exists nIx. apply intJoin_comm in H.
    destruct (intJoin_assoc _ _ _ _ _ H0 H) as [xyI []]. Exists xyI. entailer !.
    rewrite pc_tree_rep_cons. Exists nIy Clx. apply intJoin_comm in H1. entailer !.
  - now transitivity (pc_tree_rep l' C).
Qed.

Lemma pc_tree_rep_perm: forall l1 l2 C,
    Permutation l1 l2 -> pc_tree_rep l1 C = pc_tree_rep l2 C.
Proof. intros. apply pred_ext; apply pc_tree_rep_perm'; auto. now symmetry. Qed.

Lemma pc_tree_rep_In_eq: forall n l C,
    In n l -> pc_tree_rep l C =
              EX nI l' Cl, !! (intJoin nI Cl C /\ Permutation (n :: l') l) &&
                           (pc_node_rep n nI * pc_tree_rep l' Cl).
Proof.
  intros. apply pred_ext.
  - apply in_split in H. destruct H as [l1 [l2 ?]]. subst l.
    pose proof (Permutation_middle l1 l2 n).
    rewrite <- (pc_tree_rep_perm (n :: l1 ++ l2)); auto. rewrite pc_tree_rep_cons.
    Intros nI Cl. Exists nI (l1 ++ l2) Cl. entailer !.
  - Intros nI l' Cl. rewrite <- (pc_tree_rep_perm (n :: l') l); auto.
    rewrite pc_tree_rep_cons. Exists nI Cl. entailer !.
Qed.

Lemma pc_tree_rep_neq_nullval: forall n l C,
    In n l -> pc_tree_rep l C |-- !! (addr_tn n <> nullval).
Proof.
  intros. rewrite (pc_tree_rep_In_eq n); auto. Intros nI l' Cl.
  unfold pc_node_rep. Intros. entailer !.
Qed.

Lemma map_nodup_neq_nodup: forall {A B: Type} (f: A -> B) (l: list A) x y,
    List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l; intros. 1: inversion H0. simpl in *.
  destruct H0, H1; subst; auto; apply NoDup_cons_iff in H; destruct H.
  - exfalso. apply (in_map f) in H1. now rewrite H2 in H.
  - exfalso. apply (in_map f) in H0. now rewrite H2 in H0.
  - now apply IHl.
Qed.                                  

Lemma pc_tree_rep_root_no_parent: forall root l C,
    !!(pc_global_inv root l C) && pc_tree_rep l C |--
          !! (forall x, In x l -> left_tn x <> addr_tn root /\
                                  right_tn x <> addr_tn root).
Proof.
  intros. Intros. assert_PROP (forall n, In n l -> addr_tn n <> nullval). {
    eapply derives_trans. 2: apply allp_prop_left. apply allp_right. intros.
    rewrite prop_impl. apply imp_andp_adjoint. Intros.
    now apply pc_tree_rep_neq_nullval. } rename H0 into Han.
  sep_apply pc_tree_rep_nodup_addr. Intros. rename H0 into Hnp.
  unfold pc_tree_rep. Intros fl. sep_apply pc_tree_rep_pc_local_inv.
  Intros. apply prop_right. intros. apply (In_fst_combine _ fl) in H3. 2: lia.
  destruct H3 as [y ?]. destruct (treenode_eq_dec x root).
  - subst. specialize (H2 _ H3). simpl in H2. destruct H2 as [? [? [? _]]]. auto.
  - destruct H as [? [? [? [? [? ?]]]]]. apply (In_fst_combine _ fl) in H6. 2: lia.
    destruct H6 as [rootF ?]. pose proof (in_combine_r _ _ _ _ H6).
    destruct (list_join_single _ _ _ H9 H0) as [l1 [l2 [rest [? [? ?]]]]].
    unfold sepalg.join in H12. pose proof (intJoin_unfold_inf_1 _ _ _ H12 H).
    assert (Hn1: List.NoDup l). {
      rewrite <- (combine_fst l fl); auto. apply (list_join_nodup_fst _ C); auto.
      - intros. specialize (H2 _ H14). now destruct H2 as [_ [_ [_ [_ [_ ?]]]]].
      - rewrite combine_snd; auto. }
    assert (Hn2: List.NoDup fl). {
      rewrite <- (combine_snd l fl); auto. apply (list_join_nodup_snd _ C); auto.
      - intros. specialize (H2 _ H14). now destruct H2 as [_ [_ [_ [_ [_ ?]]]]].
      - rewrite combine_snd; auto. }    
    pose proof (H2 _ H6). simpl in H14. destruct H14 as [? [? [? [? [? [? [? ?]]]]]]].
    assert (root ∈ domm rootF) by (rewrite H21; now apply elem_of_singleton_2).
    specialize (H13 _ H22). rewrite H19 in H13. rewrite H5 in H13.
    assert (out rest root = O). {
    clear -H13. unfold ccmop in H13. unfold ccm_op in H13. simpl in H13. lia. }
    assert (✓ rest) by (eapply intJoin_valid_proj2; eauto).
    assert (root ∉ domm rest). {
    assert (intComposable rootF rest) by (eapply intComposable_valid; eauto).
    destruct H25 as [_ [_ [? _]]]. intro. now apply (H25 root). }
    pose proof (list_join_unfold_out _ _ H11 H24 _ H25). unfold ccmop, ccm_op in H26.
    simpl in H26. unfold nat_op in H26. rewrite H23 in H26.
    unfold ccmunit, ccm_unit, nat_unit in H26. symmetry in H26.
    pose proof (sum_0_0 flowintR (fun x => out x root)). simpl in H27.
    specialize (H27 _ H26). specialize (H2 _ H3). simpl in H2.
    destruct H2 as [? [? [? [? [? [? [? ?]]]]]]]. specialize (H33 root).
    assert (In y (l1 ++ l2)). {
      pose proof H3. apply (in_combine_r) in H3. rewrite H10 in H3.
      apply in_elt_inv in H3. destruct H3. exfalso.
      eapply (NoDup_pair_eq _ x y root rootF) in H3; eauto.
      - rewrite combine_fst; auto.
      - rewrite combine_snd; auto.
      - apply H3. } specialize (H27 _ H35). rewrite H33 in H27.
    unfold pc_edgeFn in H27. apply in_combine_l in H6.
    specialize (Han _ H6). rewrite <- val_eqb_false in Han.
    assert (addr_tn x ≠ addr_tn root). {
      intro. apply in_combine_l in H3. eapply map_nodup_neq_nodup in H36; eauto. }
    rewrite Han in H27. rewrite <- val_eqb_false in H36. rewrite H36 in H27.
    simpl in H27. match goal with | H: context [match ?E with _ => _ end] |- _ =>
                                    destruct E eqn:?H in H end. 1: inversion H27.
    apply orb_false_elim in H37. destruct H37. apply val_eqb_false in H37, H38. auto.
Qed.

Lemma pc_tree_rep_has_unique_parent: forall root l C,
    !!(pc_global_inv root l C) && pc_tree_rep l C |--
                          !!(forall x, In x l -> x ≠ root ->
                          x.(addr_tn) ≠ nullval /\
                          exists ! p, In p l /\ p ≠ x /\
                                    (p.(left_tn) = x.(addr_tn) \/
                                     p.(right_tn) = x.(addr_tn))).
Proof.
  intros. Intros. unfold pc_tree_rep. Intros fl. sep_apply pc_tree_rep_pc_local_inv. Intros.
  apply prop_right. intros. pose proof H3. apply (In_fst_combine _ fl) in H5. 2: lia.
  destruct H5 as [y ?]. pose proof (H2 _ H5). simpl in H6.
  destruct H6 as [? [_ [_ [? [? [? [? ?]]]]]]]. pose proof (in_combine_r _ _ _ _ H5).
  destruct (list_join_single _ _ _ H12 H0) as [l1 [l2 [z [? [? ?]]]]].
  destruct H as [? [? [? [? [? ?]]]]]. unfold sepalg.join in H15.
  assert (Hn1: List.NoDup l). {
    rewrite <- (combine_fst l fl); auto. apply (list_join_nodup_fst _ C); auto.
    - intros. specialize (H2 _ H21). now destruct H2 as [_ [_ [_ [_ [_ ?]]]]].
    - rewrite combine_snd; auto. }
  assert (Hn2: List.NoDup fl). {
    rewrite <- (combine_snd l fl); auto. apply (list_join_nodup_snd _ C); auto.
    - intros. specialize (H2 _ H21). now destruct H2 as [_ [_ [_ [_ [_ ?]]]]].
    - rewrite combine_snd; auto. } pose proof (intJoin_unfold_inf_1 _ _ _ H15 H).
  assert (x ∈ domm y) by (rewrite H11; now apply elem_of_singleton_2).
  specialize (H21 _ H22). assert (x ∈ domm C). {
    rewrite H20. rewrite elem_of_list_to_set. now rewrite elem_of_list_In. }
  specialize (H16 _ H23 H4). rewrite H16 in H21. rewrite H9 in H21.
  assert (out z x = 1%nat). {
    clear -H21. unfold ccmop in H21. unfold ccm_op in H21. simpl in H21. easy. }
  assert (✓ z) by (eapply intJoin_valid_proj2; eauto).
  assert (x ∉ domm z). {
    assert (intComposable y z) by (eapply intComposable_valid; eauto).
    destruct H26 as [_ [_ [? _]]]. intro. now apply (H26 x). }
  pose proof (list_join_unfold_out _ _ H14 H25 _ H26). unfold ccmop, ccm_op in H27.
  simpl in H27. unfold nat_op in H27. unfold ccmunit, ccm_unit, nat_unit in H27.
  rewrite H24 in H27. symmetry in H27.
  assert (forall y, In y (l1 ++ l2) -> In y fl). {
    intros. rewrite H13. apply in_app_iff in H28. rewrite in_app_iff.
    destruct H28; auto. right. now right. } apply sum_0_1 in H27.
  destruct H27 as [y0 [[? ?] Hu]]. specialize (H28 _ H27).
  apply (In_snd_combine l) in H28. 2: lia. destruct H28 as [x0 ?].
  pose proof H2 as Hl. specialize (H2 _ H28). simpl in H2.
  destruct H2 as [_ [_ [_ [_ [_ [_ [? _]]]]]]]. assert (Hneq: x ≠ x0). {
    eapply (NoDup_pair_neq (combine l fl)); eauto.
    - rewrite combine_fst; auto.
    - rewrite combine_snd; auto.
    - rewrite H13 in Hn2. apply NoDup_remove_2 in Hn2. intro. now subst. }
  rewrite H2 in H29. unfold pc_edgeFn in H29.
  match goal with | H: context [match ?E with _ => _ end] |- _ =>
                    destruct E eqn:?H in H end. 2: inversion H29.
  apply andb_prop in H30. destruct H30. apply orb_prop in H31.
  apply andb_prop in H30. destruct H30. apply negb_true in H32.
  apply val_eqb_false in H32. split; auto. pose proof (in_combine_l _ _ _ _ H28).
  exists x0. split.
  - do 2 (split; auto). destruct H31; [left | right];
                          now apply val_eqb_true in H31.
  - intros. destruct H34 as [? []]. apply (In_fst_combine _ fl) in H34. 2: lia.
    destruct H34 as [y' ?]. pose proof (in_combine_r _ _ _ _ H34).
    assert (y' ≠ y). {
      erewrite (NoDup_pair_neq (combine l fl)); eauto.
      - rewrite combine_fst; auto.
      - rewrite combine_snd; auto. } assert (In y' (l1 ++ l2)). {
      rewrite H13 in H37. apply in_elt_inv in H37. destruct H37; easy. }
    assert (out y' x = 1%nat). {
      specialize (Hl _ H34). simpl in Hl.
      destruct Hl as [_ [? [? [_ [_ [_ [? _]]]]]]]. specialize (H42 x).
      unfold pc_edgeFn in H42.
      assert (negb (val_eqb (addr_tn x') (addr_tn x)) = true). {
        rewrite negb_true val_eqb_false. clear -H40 H41 H36.
        destruct H36; rewrite <- H; easy. } rewrite H43 in H42. clear H43.
      assert (negb (val_eqb (addr_tn x) nullval) = true). {
        rewrite negb_true val_eqb_false; auto. } rewrite H43 in H42. clear H43.
      assert (val_eqb (addr_tn x) (left_tn x') ||
              val_eqb (addr_tn x) (right_tn x') = true)%bool. {
        apply orb_true_intro. clear -H36. rewrite !val_eqb_true. intuition. }
      rewrite H43 in H42. clear H43. now simpl in H42. }
    specialize (Hu _ (conj H39 H40)). eapply (NoDup_pair_eq (combine l fl)); eauto.
    + rewrite combine_fst; auto.
    + rewrite combine_snd; auto.
Qed.

Definition has_child_or_none (x: TreeNode) (child: TreeNode -> val)
           (l: list TreeNode): Prop :=
  child x = nullval \/ exists p, In p l /\ p ≠ x /\ child x = p.(addr_tn).

Lemma negb_false: forall b, negb b = false <-> b = true.
Proof. intros; split; intros; destruct b; simpl in *; auto. Qed.

Lemma pc_edgeFn_x_y_eq_addr: forall x y v,
    addr_tn x = addr_tn y -> pc_edgeFn x y v = O.
Proof.
  intros. unfold pc_edgeFn.
  match goal with
  | |- context [match ?E with _ => _ end] => destruct E eqn:?H end; auto.
  do 2 (apply andb_prop in H0; destruct H0).
  apply negb_true in H0. apply val_eqb_false in H0. exfalso. now apply H0.
Qed.

Lemma addr_in_dec: forall n I, {address_in n I} + {~ address_in n I}.
Proof.
  intros. destruct (in_dec Val.eq (addr_tn n) (map addr_tn (elements (domm I)))).
  - left. apply in_map_iff in i. destruct i as [x [? ?]].
    rewrite <- elem_of_list_In in H0. apply elem_of_elements in H0.
    exists x. split; auto.
  - right. repeat intro. apply n0. rewrite in_map_iff. destruct H as [t [? ?]].
    exists t. split; auto. rewrite <- elem_of_list_In. now rewrite elem_of_elements.
Qed.

Lemma pc_tree_rep_has_children: forall root l C,
    !!(pc_global_inv root l C) && pc_tree_rep l C |--
             !!(forall x, In x l ->
                          has_child_or_none x left_tn l /\
                          has_child_or_none x right_tn l).
Proof.
  intros. unfold pc_tree_rep. Intros fl. sep_apply pc_tree_rep_pc_local_inv. Intros.
  apply prop_right. intros. pose proof H3. apply (In_fst_combine l fl) in H4. 2: lia.
  destruct H4 as [y ?]. pose proof (H2 _ H4). simpl in H5.
  destruct H5 as [? [? [? [? [? [? [? ?]]]]]]]. pose proof (in_combine_r _ _ _ _ H4).
  destruct (list_join_single _ _ _ H13 H0) as [l1 [l2 [z [? [? ?]]]]].
  red in H16. destruct H as [? [? [? [? [? ?]]]]]. split; red.
  - destruct (Val.eq x.(left_tn) nullval) as [?H | ?H]; [now left | right].
    pose proof (intJoin_unfold_out _ _ _ H16 H).
    assert (forall n, ~ address_in n C -> 0%nat = (pc_edgeFn x n 1 + out z n)%nat). {
      intros. specialize (H20 _ H24).
      specialize (H23 _ (address_not_in_domm _ _ H24)). rewrite H20 in H23.
      now rewrite H11 in H23. }
    remember (Build_TreeNode (left_tn x) 0 nullval nullval nullval) as n.
    destruct (addr_in_dec n C).
    + unfold address_in in a. destruct a as [t [? ?]]. rewrite Heqn in H26.
      simpl in H26. exists t. split; [|split]; auto.
      * clear -H25 H21. rewrite H21 in H25. apply elem_of_list_to_set in H25.
        now apply elem_of_list_In in H25.
      * intro. subst; auto.
    + specialize (H24 _ n0). cut (pc_edgeFn x n 1 = 1)%nat.
      * intros. exfalso. rewrite H25 in H24. lia.
      * unfold pc_edgeFn.
        match goal with
        | |- context [match ?E with _ => _ end] => destruct E eqn:?H end; auto.
        rewrite Heqn in H25. simpl in H25.
        rewrite ((proj2 (val_eqb_false (addr_tn x) (left_tn x))) H6) in H25.
        rewrite ((proj2 (val_eqb_false (left_tn x) nullval)) H22) in H25.
         rewrite val_eqb_refl in H25. simpl in H25. now exfalso.
  - destruct (Val.eq x.(right_tn) nullval) as [?H | ?H]; [now left | right].
    pose proof (intJoin_unfold_out _ _ _ H16 H).
    assert (forall n, ~ address_in n C -> 0%nat = (pc_edgeFn x n 1 + out z n)%nat). {
      intros. specialize (H20 _ H24).
      specialize (H23 _ (address_not_in_domm _ _ H24)). rewrite H20 in H23.
      now rewrite H11 in H23. }
    remember (Build_TreeNode (right_tn x) 0 nullval nullval nullval) as n.
    destruct (addr_in_dec n C).
    + unfold address_in in a. destruct a as [t [? ?]]. rewrite Heqn in H26.
      simpl in H26. exists t. split; [|split]; auto.
      * clear -H25 H21. rewrite H21 in H25. apply elem_of_list_to_set in H25.
        now apply elem_of_list_In in H25.
      * intro. subst; auto.
    + specialize (H24 _ n0). cut (pc_edgeFn x n 1 = 1)%nat.
      * intros. exfalso. rewrite H25 in H24. lia.
      * unfold pc_edgeFn.
        match goal with
        | |- context [match ?E with _ => _ end] => destruct E eqn:?H end; auto.
        rewrite Heqn in H25. simpl in H25.
        rewrite ((proj2 (val_eqb_false (addr_tn x) (right_tn x))) H7) in H25.
        rewrite ((proj2 (val_eqb_false (right_tn x) nullval)) H22) in H25.
        rewrite val_eqb_refl in H25. simpl in H25. rewrite orb_true_r in H25.
        now exfalso.
Qed.

Lemma pc_tree_rep_left_right: forall root l C,
    !! pc_global_inv root l C && pc_tree_rep l C |--
             !! (forall x, In x l ->
                          left_tn x = right_tn x /\ left_tn x = nullval \/ left_tn x ≠ right_tn x).
Proof.
  intros.
  assert_PROP (forall x, In x l -> has_child_or_none x left_tn l /\ has_child_or_none x right_tn l) by
    apply pc_tree_rep_has_children. Intros. eapply derives_trans. 2: apply allp_prop_left. apply allp_right. intros.
  rewrite prop_impl. apply imp_andp_adjoint. Intros. destruct (H _ H1). destruct H2, H3.
  - apply prop_right. left. rewrite H2. rewrite H3. auto.
  - destruct H3 as [p [? [? ?]]]. sep_apply (pc_tree_rep_neq_nullval p). Intros. apply prop_right. right.
    rewrite H2. rewrite H5. auto.
  - destruct H2 as [p [? [? ?]]]. sep_apply (pc_tree_rep_neq_nullval p). Intros. apply prop_right. right.
    rewrite H3. rewrite H5. auto.
  - destruct H2 as [p1 [? [? ?]]]. destruct H3 as [p2 [? [? ?]]]. sep_apply (pc_tree_rep_neq_nullval p1). Intros.
    sep_apply (pc_tree_rep_neq_nullval p2). Intros. rewrite H5. rewrite H7.
    destruct (Val.eq (addr_tn p1) (addr_tn p2)). 2: apply prop_right; now right.
    sep_apply pc_tree_rep_nodup_addr. Intros.
    assert (p1 = p2). {
      destruct (In_Permutation_cons _ _ H2) as [l' ?]. apply (Permutation_in _ H11) in H3. destruct H3; auto.
      apply (Permutation_map addr_tn) in H11. apply (Permutation_NoDup H11) in H10. simpl in H10.
      apply NoDup_cons_iff in H10. destruct H10. rewrite e in H10. exfalso. apply H10. now apply in_map. }
    subst p1. rename p2 into p. clear H3 H9 e.
    unfold pc_tree_rep. Intros fl. sep_apply pc_tree_rep_pc_local_inv. Intros.
Abort.


Fixpoint pc_tree_rep' (t: @tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    pc_tree_rep' a pa * pc_tree_rep' b pb
 end.

Definition pc_treebox_rep root l C (b: val) :=
  !!(pc_global_inv root l C) &&
  data_at Tsh (tptr t_struct_tree) (addr_tn root) b * pc_tree_rep l C.

Definition lookup_spec :=
 DECLARE _lookup
  WITH b: val, x: Z, v: val, root: TreeNode, l: (list TreeNode), C: pc_flowint
  PRE  [ tptr (tptr t_struct_tree), tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    PARAMS(b; Vint (Int.repr x))
    SEP (pc_treebox_rep root l C b)
  POST [ tptr Tvoid ]
    EX r,
    PROP()
    RETURN (r)
    SEP (pc_treebox_rep root l C b).

Definition Gprog : funspecs :=
  ltac:(with_library prog [lookup_spec]).

Lemma pc_node_rep_valid_ptr: forall n nI,
    pc_node_rep n nI |-- valid_pointer (addr_tn n).
Proof. intros. unfold pc_node_rep. entailer !. Qed.

Lemma pc_tree_rep_is_ptr_null: forall n l C,
    In n l -> pc_tree_rep l C |-- !! is_pointer_or_null (addr_tn n).
Proof.
  intros. apply in_split in H. destruct H as [l1 [l2 ?]]. subst l.
  pose proof (Permutation_middle l1 l2 n). symmetry in H.
  sep_apply (pc_tree_rep_perm (l1 ++ n :: l2) (n :: l1 ++ l2)).
  rewrite pc_tree_rep_cons. Intros nI Cl. unfold pc_node_rep. entailer !.
Qed.

Lemma pc_tree_rep_saturate_local: forall root l C,
    pc_global_inv root l C -> pc_tree_rep l C |-- !! is_pointer_or_null (addr_tn root).
Proof.
  intros. Intros. apply pc_tree_rep_is_ptr_null. now destruct H as [? [? [? [? ?]]]].
Qed.

Definition lookup_inv (root: TreeNode) (b: val) (l: list TreeNode)
           (C : pc_flowint) (x: Z): environ -> mpred :=
  EX n: TreeNode, EX l': list TreeNode, EX nI: pc_flowint, EX Cl: pc_flowint,
    PROP (intJoin nI Cl C;
         if Val.eq (addr_tn n) nullval then nI = ∅ /\ l' = l /\ Cl = C
         else  Permutation (n :: l') l)
    LOCAL (temp _p (addr_tn n); temp _t b; temp _x (Vint (Int.repr x)))
    SEP (data_at Tsh (tptr t_struct_tree) (addr_tn root) b;
        if Val.eq (addr_tn n) nullval then emp else pc_node_rep n nI;
        pc_tree_rep l' Cl).


Definition empty_node: TreeNode := {|
  addr_tn := nullval;
  key_tn := 0;
  value_tn := nullval;
  left_tn := nullval;
  right_tn := nullval |}.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold pc_treebox_rep. Intros. sep_apply (pc_tree_rep_has_children root l C); auto.
  Intros. forward.
  - entailer. sep_apply (pc_tree_rep_saturate_local root l C); auto. entailer !.
  - forward_while (lookup_inv root b l C x).
    + Exists root. destruct H0 as [_ [_ [_ [? _]]]].
      sep_apply (pc_tree_rep_neq_nullval root l C). Intros.
      rewrite (pc_tree_rep_In_eq root l C H0). Intros nI l' Cl. Exists l' nI Cl.
      if_tac. 1: now exfalso. entailer !.
    + if_tac.
      * Intros. subst. rewrite H2. entailer !.
      * sep_apply pc_node_rep_valid_ptr. Intros. entailer !.
    + if_tac. 1: now exfalso. unfold pc_node_rep. Intros.
      assert (In n l). {
        eapply Permutation_in; eauto. now left. }
      assert (data_at Tsh t_struct_tree
                      (Vint (Int.repr (key_tn n)),
                       (value_tn n, (left_tn n, right_tn n))) (addr_tn n) *
              pc_tree_rep l' Cl |-- pc_tree_rep l C). {
        rewrite (pc_tree_rep_In_eq n l C); auto. Exists nI l' Cl.
        unfold pc_node_rep. entailer !. } forward. specialize (H1 _ H6).
      destruct H1. forward_if.
      * forward; sep_apply H7; destruct H1 as [? | [p [? [? ?]]]].
        -- rewrite H1. entailer !.
        -- rewrite H11. sep_apply (pc_tree_rep_is_ptr_null p l C). entailer !.
        -- Exists (empty_node, l, ∅ : pc_flowint, C). simpl fst. simpl snd.
           if_tac. 2: cbn in H10; now exfalso. entailer !. apply intJoin_left_unit.
        -- rewrite H11. sep_apply (pc_tree_rep_neq_nullval p l C). Intros.
           rewrite (pc_tree_rep_In_eq p l C); auto. Intros pI pl pCl.
           Exists (p, pl, pI, pCl). simpl fst. simpl snd. if_tac. 1: now exfalso.
           entailer !.
      * forward_if.
        -- forward; sep_apply H7; destruct H8 as [? | [p [? [? ?]]]].
           ++ rewrite H8; entailer !.
           ++ rewrite H12. sep_apply (pc_tree_rep_is_ptr_null p l C). entailer !.
           ++ Exists (empty_node, l, ∅ : pc_flowint, C). simpl fst. simpl snd.
              if_tac. 2: cbn in H11; now exfalso. entailer !. apply intJoin_left_unit.
           ++ rewrite H12. sep_apply (pc_tree_rep_neq_nullval p l C). Intros.
           rewrite (pc_tree_rep_In_eq p l C); auto. Intros pI pl pCl.
           Exists (p, pl, pI, pCl). simpl fst. simpl snd. if_tac. 1: now exfalso.
           entailer !.
        -- forward.
           ++ destruct H5 as [? [? [? [? [? [? [? ?]]]]]]]. entailer !.
           ++ sep_apply H7. forward. Exists (value_tn n). unfold pc_treebox_rep.
              entailer !.
    + if_tac. 2: now exfalso. destruct H3 as [? [? ?]]. subst. forward.
      Exists nullval. unfold pc_treebox_rep. entailer !.
Qed.
