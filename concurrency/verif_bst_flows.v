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

Definition edgeFn (x y: TreeNode): nat -> nat :=
  fun v => if ((negb (val_eqb y.(addr_tn) nullval)) &&
               ((val_eqb y.(addr_tn) x.(left_tn)) ||
                (val_eqb y.(addr_tn) x.(right_tn))))%bool then v else O.

Definition global_inv (Ipc: pc_flowint) (root: TreeNode) (NS: list TreeNode): Prop :=
  ✓Ipc /\ (forall n, n ∈ domm Ipc -> n <> root -> inf Ipc n = O) /\
  (inf Ipc root = 1%nat) /\ (In root NS) /\
  (forall n, n ∉ domm Ipc -> out Ipc n = O) /\ (domm Ipc = list_to_set NS).

Definition single_inv (t: TreeNode) (It: pc_flowint): Prop :=
  Int.min_signed <= t.(key_tn) <= Int.max_signed /\
  tc_val (tptr Tvoid) t.(value_tn) /\
  ✓ It /\ inf It t = 1%nat /\
  (forall n, out It n = edgeFn t n 1%nat) /\
  domm It = {[t]}.

Definition node_rep (t: TreeNode) (It: pc_flowint): mpred :=
  !! single_inv t It &&
  data_at Tsh t_struct_tree (Vint (Int.repr t.(key_tn)),
                             (t.(value_tn), (t.(left_tn), t.(right_tn)))) t.(addr_tn).

Definition tree_rep (root: TreeNode) (l: list (TreeNode * pc_flowint)): mpred :=
  !! (exists C, list_join (map snd l) C /\ global_inv C root (map fst l)) &&
  iter_sepcon (fun x => node_rep x.1 x.2) l.

Lemma tree_rep_single_inv: forall root l,
    tree_rep root l |-- !!(forall x, In x l -> single_inv x.1 x.2).
Proof.
  intros. unfold tree_rep. Intros. clear H. induction l.
  - apply prop_right. intros. inversion H.
  - simpl.
    assert_PROP (forall x, In x l -> single_inv x.1 x.2). {
      sep_apply IHl. Intros. apply prop_right. auto. }
    unfold node_rep at 1. Intros. apply prop_right. intros. destruct H1; auto.
    now subst.
Qed.

Lemma In_fst_pair: forall {A B: Type} (l: list (A * B)) x,
    In x (map fst l) -> exists y, In (x, y) l.
Proof.
  intros until l. induction l; intros; simpl in H. 1: now exfalso. destruct H.
  - destruct a. simpl in *. subst x. exists b. now left.
  - specialize (IHl _ H). destruct IHl as [y ?]. exists y. simpl. now right.
Qed.

Lemma In_snd_pair: forall {A B: Type} (l: list (A * B)) x,
    In x (map snd l) -> exists y, In (y, x) l.
Proof.
  intros until l. induction l; intros; simpl in H. 1: now exfalso. destruct H.
  - destruct a. simpl in *. subst x. exists a. now left.
  - specialize (IHl _ H). destruct IHl as [y ?]. exists y. simpl. now right.
Qed.

Lemma In_pair_snd: forall {A B: Type} (l: list (A * B)) x y,
    In (x, y) l -> In y (map snd l).
Proof.
  intros. induction l. 1: inversion H. simpl in H. destruct H.
  - destruct a. inversion H. simpl. now left.
  - simpl. right. auto.
Qed.

Lemma sum_0or1_1 {A: Type}: forall (f: A -> nat) (l: list A),
    (forall x, In x l -> f x = O \/ f x = 1%nat) ->
    fold_right (fun x v => (f x + v)%nat) O l = 1%nat ->
              exists y, In y l /\ f y = 1%nat.
Proof.
  intros until l. induction l; intros; simpl in H0. 1: now apply n_Sn in H0.
  destruct (H _ (in_eq a l)); rewrite H1 in H0; simpl in H0.
  - apply IHl in H0.
    + destruct H0 as [y [? ?]]. exists y. simpl; split; auto.
    + intros. apply H. now right.
  - exists a. simpl; split; auto.
Qed.

Lemma edgeFn_0orv: forall x y v, edgeFn x y v = O \/ edgeFn x y v = v.
Proof.
  intros. unfold edgeFn.
  match goal with | |- context [match ?E with _ => _ end] => destruct E end; auto.
Qed.  

Lemma tree_rep_no_dangling_node: forall root l,
    tree_rep root l |--
             !!(forall x, In x (map fst l) -> x <> root ->
                          exists p, p.(left_tn) = x.(addr_tn) \/
                                    p.(right_tn) = x.(addr_tn)).
Proof.
  intros. sep_apply tree_rep_single_inv. Intros. unfold tree_rep. Intros.
  apply prop_right. intros. destruct H0 as [C [? ?]].
  destruct (In_fst_pair _ _ H1) as [y ?]. pose proof (H _ H4). simpl in H5.
  destruct H5 as [? [? [? [? [? ?]]]]]. apply In_pair_snd in H4.
  destruct (list_join_single _ _ _ H4 H0) as [[? ?] | [l1 [l2 [z [? [? ?]]]]]].
  - subst C. destruct H3 as [? [? [? [? _]]]]. clear -H14 H1 H11 H2. exfalso.
    destruct l. 1: simpl in H11; inversion H11. simpl in H11. inversion H11.
    destruct l. 2: simpl in H3; inversion H3. destruct p. simpl in *.
    destruct H14; auto. destruct H1; auto. rewrite H in H1. auto.
  - destruct H3 as [? [? [? [? [? ?]]]]]. unfold sepalg.join in H13.
    pose proof (intJoin_unfold_inf_1 _ _ _ H13 H3).
    assert (x ∈ domm y) by (rewrite H10; now apply elem_of_singleton_2).
    specialize (H19 _ H20).
    assert (x ∈ domm C). {
      rewrite H18. rewrite elem_of_list_to_set. now rewrite elem_of_list_In. }
    specialize (H14 _ H21 H2). rewrite H14 in H19. rewrite H8 in H19.
    assert (out z x = 1%nat). {
      clear -H19. unfold ccmop in H19. unfold ccm_op in H19. simpl in H19. easy. }
    assert (✓ z) by (eapply intJoin_valid_proj2; eauto).
    assert (x ∉ domm z). {
      assert (intComposable y z) by (eapply intComposable_valid; eauto).
      destruct H24 as [_ [_ [? _]]]. intro. now apply (H24 x). }
    pose proof (list_join_unfold_out _ _ H12 H23 _ H24). unfold ccmop, ccm_op in H25.
    simpl in H25. unfold nat_op in H25. unfold ccmunit, ccm_unit, nat_unit in H25.
    rewrite H22 in H25. symmetry in H25.
    assert (forall y, In y (l1 ++ l2) -> In y (map snd l)). {
      intros. rewrite H11. apply in_app_iff in H26. rewrite in_app_iff.
      destruct H26; auto. right. now right. } apply sum_0or1_1 in H25.
    + destruct H25 as [y0 [? ?]]. apply H26 in H25. apply In_snd_pair in H25.
      destruct H25 as [x0 ?]. specialize (H _ H25). simpl in H.
      destruct H as [_ [_ [_ [_ [? _]]]]]. rewrite H in H27. exists x0. clear -H27.
      unfold edgeFn in H27.
      match goal with | H: context [match ?E with _ => _ end] |- _ =>
                        destruct E eqn:?H in H end. 2: inversion H27.
      apply andb_prop in H0. destruct H0. apply orb_prop in H0. destruct H0.
      * left. unfold val_eqb in H0. now destruct (Val.eq (addr_tn x) (left_tn x0)).
      * right. unfold val_eqb in H0. now destruct (Val.eq (addr_tn x) (right_tn x0)).
    + intros. apply H26 in H27. apply In_snd_pair in H27. destruct H27 as [y0 ?].
      specialize (H _ H27). simpl in H. destruct H as [_ [_ [_ [_ [? _]]]]].
      rewrite !H. apply edgeFn_0orv.
Qed.
