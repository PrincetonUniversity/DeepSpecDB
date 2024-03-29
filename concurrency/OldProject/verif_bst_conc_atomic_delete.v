Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.puretree.
Require Import bst.bst_conc.
Require Import VST.atomics.general_locks.
Require Import bst.verif_bst_conc_atomic.
Require Import Coq.Sets.Ensembles.

Ltac allpr_intros x := apply allp_right; intros x. (* Temporary *)

Lemma gt_ghost_sorted : forall t1 t2 k k0 v0 g g0,
  gt_ghost (T_ghost t1 g k0 v0 t2 g0) k ->
  gt_ghost (V := val) t1 k /\ gt_ghost (V := val) t2 k.
Proof.
  intros. unfold gt_ghost in H.
  split; unfold gt_ghost; intros; apply H.
  * apply InLeft_ghost; auto.
  * apply InRight_ghost; auto.
Qed.

Lemma change_ghost_root: forall tg gl rootl rootr,
  sorted_ghost_tree tg ->
  ghost_tree_rep tg gl (rootl, rootr) |--
  EX o : option ghost_info,
    !! (match o with
        | None => tg = E_ghost
        | Some (x, y, g1, g2) => (exists tg1 tg2, tg = T_ghost tg1 g1 x y tg2 g2)
        end) &&
    (public_half gl (rootl, rootr, Some o)) *
    (ALL rootl2 : number, ALL rootr2 : number, ALL g : gname,
      !! (range_incl (rootl, rootr) (rootl2, rootr2) = true) &&
      public_half g (rootl2, rootr2, Some o) -* |==> ghost_tree_rep tg g (rootl2, rootr2)).
Proof.
  induction tg; intros.
  - simpl. Exists (None: @option ghost_info). entailer!.
    allpr_intros rootl2; allpr_intros rootr2; allpr_intros g.
    rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. Intros.
    apply ghost_seplog.bupd_intro.
  - simpl. Exists (Some (k, v, g, g0)). entailer!. { eauto. }
    allpr_intros rootl2; allpr_intros rootr2; allpr_intros g'.
    inv H. sep_apply IHtg1. sep_apply IHtg2.
    Intros o1 o2.
    rewrite <- wand_sepcon_adjoint.
    iIntros "((Ha & Hb) & Hc)". logic_to_iris.
    iDestruct "Ha" as "[root_left tree_left]".
    iDestruct "Hb" as "[root_right tree_right]".
    iSpecialize ("tree_left" $! (Finite_Integer k) rootr2  g0).
    iSpecialize ("tree_right" $! rootl2 (Finite_Integer k) g).
    iDestruct "Hc" as "[% Hc]". apply andb_prop in H1. destruct H1.
    assert (range_incl (rootl, Finite_Integer k) (rootl2, Finite_Integer k) = true). {
      apply andb_true_intro. split; try apply less_than_equal_refl. auto.
    }
    assert (range_incl (Finite_Integer k, rootr) (Finite_Integer k, rootr2) = true). {
      apply andb_true_intro. split; try apply less_than_equal_refl. auto.
    }
    iMod (public_half_range_incl with "root_right") as "root_right".
    { eauto. }
    iMod (public_half_range_incl with "root_left") as "root_left".
    { eauto. }
    repeat logic_to_iris.
    iMod ("tree_right" with "[$root_right]"). iPureIntro.
    split; auto.
    iMod ("tree_left" with "[$root_left]"). iPureIntro.
    split; auto. iModIntro. iFrame.
Qed.

Fixpoint pushdown_ghost {V} (c ab: @ghost_tree V) : ghost_tree :=
  match ab with
  | E_ghost => c
  | T_ghost a ga y v' b gb => T_ghost (pushdown_ghost c a) ga y v' b gb
  end.

Fixpoint delete_ghost {V} (x: key) (s: @ghost_tree V) : ghost_tree :=
  match s with
  | E_ghost => E_ghost
  | T_ghost a ga y v' b gb => if x <? y then T_ghost (delete_ghost x a) ga y v' b gb
                              else if y <? x then T_ghost a ga y v' (delete_ghost x b) gb
                              else pushdown_ghost a b
  end.

Arguments range_incl : simpl never.

(* up *)
Lemma Subtract_Union1 : forall {A} S1 S2 (x : A), ~In S2 x -> Subtract (Union S1 S2) x = Union (Subtract S1 x) S2.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ? Hin.
  - inv Hin.
    inv H0.
    + constructor 1; constructor 1; auto.
    + constructor 2; auto.
  - inv Hin.
    + inv H0.
      constructor; auto.
      constructor 1; auto.
    + constructor.
      constructor 2; auto.
      { intros X; inv X; contradiction. }
Qed.

Lemma Subtract_Add : forall {A} S (x : A), ~In S x -> Subtract (Add S x) x = S.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ??.
  - inv H0.
    inv H1; auto; contradiction.
  - constructor.
    + constructor 1; auto.
    + intros X; inv X; contradiction.
Qed.

Lemma In_same_map : forall tg1 tg2 x, tree_to_gmap tg1 = tree_to_gmap tg2 -> In_ghost x tg1 <-> In_ghost x tg2.
Proof.
  intros.
  rewrite !In_tree_to_gmap H; reflexivity.
Qed.

Lemma ghost_tree_delete: forall tg g_root g_in gl gr x v (r_root: range),
 Ensembles.In (find_ghost_set tg g_root) g_in ->
 keys_in_range_ghost tg r_root ->
 sorted_ghost_tree tg -> unique_gname tg ->
 ~Ensembles.In (find_ghost_set' tg) g_root ->
 ghost_tree_rep tg g_root r_root |--
 EX n n0:number, EX o1:option ghost_info,
 !!(range_incl (n,n0) r_root = true) &&
 public_half g_in (n, n0, Some o1) *
 (!!(o1 = Some (x,v,gl,gr)) -->
   EX o3 : option ghost_info,
  public_half gr (Finite_Integer x, n0, Some o3) *
 ((EX o2 : option ghost_info,
        public_half gl (n, Finite_Integer x, Some o2) * 
   (!!(o1 = Some (x,v,gl,gr) /\ o3 = None /\ (key_in_range x (n,n0) = true)) &&
      public_half g_in (n, n0, Some (* o1' *) o2) -* |==> (!! (In_ghost x tg
        /\ find_ghost_set (delete_ghost x tg) g_root = (Subtract (Subtract (find_ghost_set tg g_root) gl) gr)
        /\ Ensembles.In (find_ghost_set' tg) gl /\ Ensembles.In (find_ghost_set' tg) gr)
        && ghost_tree_rep (delete_ghost x tg) g_root r_root))%I)

   && (ALL gr1 gr2 : gname, ALL k : key, ALL y : val,
        (!!(o1 = Some (x,v,gl,gr) /\ o3 = Some (k, y, gr1, gr2)
          /\ (key_in_range x (n,n0) = true) /\ less_than (Finite_Integer x) (Finite_Integer k) = true) &&
        (public_half g_in (n, n0, Some (Some (k, y, gr, gr2)))
        * public_half gr (n, Finite_Integer k, Some (Some (x, v, gl, gr1))))
        -* |==> (EX tg',
          !!(tree_to_gmap tg = tree_to_gmap tg' /\
             find_ghost_set' tg = find_ghost_set' tg' /\
             sorted_ghost_tree tg' /\ unique_gname tg') &&
           ghost_tree_rep tg' g_root r_root)))%I)).
Proof.
  induction tg; destruct r_root as (rootl, rootr); simpl; intros Hin Hrange Hsorted Hunique Hroot.
  - inv Hin.
    Exists rootl rootr (None : @option ghost_info).
    rewrite range_incl_refl; entailer!.
    rewrite <- imp_andp_adjoint. Intros; discriminate.
  - apply keys_in_range_ghost_subtrees in Hrange as (Hk & Hl & Hr); auto.
    inv Hsorted; inv Hunique; inv Hin. inv H.
    + eapply IHtg1 in H0; [| eauto | eauto | eauto | eauto].
      simpl in H0; sep_apply H0; clear H0.
      Intros n1 n2 o1; Exists n1 n2 o1; entailer!.
      { eapply range_incl_trans; [eauto|].
        apply (key_in_range_l _ (_, _)); auto. }
      rewrite <- imp_andp_adjoint. Intros; subst.
      rewrite -> prop_imp by reflexivity.
      Intros o3 o2; Exists o3 o2; cancel.
      iIntros "((Hcase & ?) & ?)"; iSplit.
      * iDestruct "Hcase" as "[[$ IH] _]".
        iIntros "[(% & % & %) Hin]"; subst.
        iMod ("IH" with "[$Hin]") as "[(% & % & % & %) Hdel]"; [auto|].
        specialize (Hgtl _ H1).
        destruct (x <? k) eqn:?; [simpl; iFrame | lia].
        iPureIntro; split; auto; split3.
        -- apply InLeft_ghost; auto.
        -- rewrite -> empty_intersection in H8.
            rewrite H3 !Subtract_Union1; auto.
            ** rewrite find_ghost_set_equiv; intros X; inv X.
               unshelve eapply (H8 _ _ H14); eauto.
               inv H14; contradiction.
            ** rewrite find_ghost_set_equiv; intros X; inv X.
               unshelve eapply (H8 _ _ H14); eauto.
               inv H14; contradiction.
            ** intros X; inv X.
               contradiction Hroot; constructor 1.
               rewrite find_ghost_set_equiv; constructor 1; auto.
            ** intros X; inv X.
               contradiction Hroot; constructor 1.
               rewrite find_ghost_set_equiv; constructor 1; auto.
        -- split; rewrite find_ghost_set_equiv; do 2 constructor 1; auto.
      * iIntros (gr1 gr2 k0 y) "[(% & % & % & %) H]".
        iDestruct "Hcase" as "[_ IH]".
        logic_to_iris.
        iMod ("IH" $! gr1 gr2 k0 y with "[$H]") as (tg') "[(% & % & % & %) IH]"; [auto | subst].
        iExists (T_ghost tg' g k v tg2 g0); simpl; iFrame.
        iPureIntro; split; auto; split3.
        -- congruence.
        -- rewrite !find_ghost_set_equiv; congruence.
        -- split; constructor; rewrite <- ?H13; auto.
           intros ??; eapply Hgtl, In_same_map; eassumption.
    + eapply IHtg2 in H0; [| eauto | eauto | eauto | eauto].
      simpl in H0; sep_apply H0; clear H0.
      Intros n1 n2 o1; Exists n1 n2 o1; entailer!.
      { eapply range_incl_trans; [eauto|].
        apply (key_in_range_r _ (_, _)); auto. }
      rewrite <- imp_andp_adjoint; Intros; subst.
      rewrite -> prop_imp by reflexivity.
      Intros o3 o2; Exists o3 o2; cancel.
      iIntros "((Hcase & ?) & ?)"; iSplit.
      * iDestruct "Hcase" as "[[$ IH] _]".
        iIntros "[(% & % & %) Hin]"; subst.
        iMod ("IH" with "[$Hin]") as "[(% & % & % & %) Hdel]"; [auto|].
        specialize (Hltr _ H1).
        destruct (x <? k) eqn:?; [lia|].
        destruct (k <? x) eqn:?; [simpl; iFrame | lia].
        iPureIntro; split; auto; split3.
        -- apply InRight_ghost; auto.
        -- rewrite -> empty_intersection in H8.
            rewrite H3 Subtract_Union1.
            rewrite Subtract_Union1.
            rewrite (Union_comm _ (find_ghost_set _ _)) !Subtract_Union1.
            rewrite (Union_comm _ (find_ghost_set _ _)); auto.
            ** rewrite find_ghost_set_equiv; intros X; inv X.
               eapply (H8 _ H14); eauto.
               inv H14; contradiction.
            ** rewrite find_ghost_set_equiv; intros X; inv X.
               eapply (H8 _ H14); eauto.
               inv H14; contradiction.
            ** intros X; inv X.
               contradiction Hroot; constructor 2.
               rewrite find_ghost_set_equiv; constructor 1; auto.
            ** intros X; inv X.
               contradiction Hroot; constructor 2.
               rewrite find_ghost_set_equiv; constructor 1; auto.
        -- split; rewrite !find_ghost_set_equiv; constructor 2; constructor 1; auto.
      * iIntros (gr1 gr2 k0 y) "[(% & % & % & %) H]".
        iDestruct "Hcase" as "[_ IH]".
        logic_to_iris.
        iMod ("IH" $! gr1 gr2 k0 y with "[$H]") as (tg') "[(% & % & % & %) IH]"; [auto | subst].
        iExists (T_ghost tg1 g k v tg' g0); simpl; iFrame.
        iPureIntro; split; auto; split3.
        -- congruence.
        -- rewrite !find_ghost_set_equiv; congruence.
        -- split; constructor; rewrite <- ?H13; auto.
           intros ??; eapply Hltr, In_same_map; eassumption.
    + clear IHtg1 IHtg2. inv H. (* pushdown case *)
      Exists rootl rootr (Some (k, v, g, g0)); rewrite range_incl_refl; entailer!.
      rewrite <- imp_andp_adjoint; Intros. inv H.
      erewrite change_ghost_root by auto; Intros o2.
      destruct tg2; simpl.
      * Exists (None : @option ghost_info); cancel. apply andp_right.
        Exists o2; cancel. rewrite Z.ltb_irrefl. rewrite <- wand_sepcon_adjoint. entailer!.
        iIntros "(Ha & Hb)". iSpecialize ("Ha" $! rootl rootr g_in with "[$Hb]").
        { iPureIntro; split; auto. apply (key_in_range_l _ (_, _)); auto. }
        logic_to_iris. iMod "Ha" as "$"; iPureIntro.
        split; auto; split3.
        -- constructor 1; auto.
        -- unfold Add; rewrite -> 3Subtract_Union1, (find_ghost_set_equiv _ gl).
            fold (Add (find_ghost_set tg1 gl) gr). rewrite -> Subtract_Add by auto.
            fold (Add (find_ghost_set' tg1) gr). rewrite -> Subtract_Add by auto.
            apply find_ghost_set_equiv.
            { intros X; inv X; contradiction. }
            { intros X; inv X. contradiction Hroot. constructor 2; rewrite find_ghost_set_equiv; constructor 2; constructor. }
            { intros X; inv X. contradiction Hroot. constructor 1; rewrite find_ghost_set_equiv; constructor 2; constructor. }
        -- split; [constructor 1; rewrite find_ghost_set_equiv|]; constructor 2; constructor.
        -- allpr_intros gr1; allpr_intros gr2; allpr_intros k; allpr_intros y.
           rewrite <- wand_sepcon_adjoint; Intros; discriminate.
      * Exists (Some (k, v, g, g0)) o2; cancel. apply andp_right.
        { cancel. rewrite <- wand_sepcon_adjoint; Intros; discriminate. }
        allpr_intros gr1; allpr_intros gr2; allpr_intros k'; allpr_intros y.
        rewrite <- wand_sepcon_adjoint; entailer!.
        iIntros "(((((Ha & Hb) & Hc) & Hd) & He) & Hf)".
        iSpecialize ("Hb" $! rootl (Finite_Integer x) gl with "[$Ha]").
        { rewrite range_incl_refl; auto. }
        inv H0. logic_to_iris. iMod "Hb"; iModIntro.
        iExists (T_ghost (T_ghost tg1 gl x v0 tg2_1 gr1) gr k' y tg2_2 gr2); simpl; iFrame.
        iPureIntro; split; auto; split3; [.. | split].
        -- rewrite <- insert_union_l, <- insert_union_r, insert_commute, map_union_assoc; auto.
           { lia. }
           { destruct (eq_dec (tree_to_gmap tg1 !! k') None); auto. apply In_tree_to_gmap in n. specialize (Hgtl _ n); lia. }
        -- unfold Add; rewrite !Union_assoc.
           rewrite (Union_comm (Singleton _)); auto.
        -- inv Hsortedr. constructor; auto. constructor; auto.
           ++ intros ? Hin; apply Hltr. constructor 2; auto.
           ++ intros ? Hin; inv Hin; auto; try lia.
              specialize (Hgtl _ H3); lia.
        -- inv H6. constructor; auto. constructor; auto.
           ++ intros ?; subst. contradiction H10; simpl.
              constructor 1; rewrite find_ghost_set_equiv; constructor 2; constructor.
           ++ rewrite -> empty_intersection in *.
              intros ???; eapply H8; eauto.
              constructor 1; rewrite find_ghost_set_equiv; constructor 1; auto.
           ++ intros ?; contradiction H10; simpl.
              constructor 1; rewrite find_ghost_set_equiv; constructor 1; auto.
           ++ intros ?; rewrite -> empty_intersection in H8; eapply H8; eauto; simpl.
              constructor 1; rewrite find_ghost_set_equiv; constructor 2; constructor.
           ++ intros ?; subst. contradiction H11; simpl.
              constructor 2; rewrite find_ghost_set_equiv; constructor 2; constructor.
           ++ rewrite -> empty_intersection in *.
              simpl; intros ? Hunion ?; inv Hunion.
              rewrite find_ghost_set_equiv in H3; inv H3.
              { eapply H8; eauto; simpl. constructor 2; rewrite find_ghost_set_equiv; constructor 1; auto. }
              { inv H4; contradiction H10; simpl. constructor 2; rewrite find_ghost_set_equiv; constructor 1; auto. }
              { rewrite find_ghost_set_equiv in H3; inv H3. eapply H19; eauto. inv H4; contradiction. }
           ++ simpl; intros X; inv X.
              { rewrite find_ghost_set_equiv in H0; inv H0; auto. inv H3; contradiction. }
              { contradiction H11; simpl. constructor 1; auto. }
           ++ intros ?; contradiction H11; simpl. constructor 2; rewrite find_ghost_set_equiv; constructor 1; auto.
           ++ simpl; intros X; inv X.
              { rewrite find_ghost_set_equiv in H0; inv H0; auto.
                rewrite -> empty_intersection in H8; eapply H8; eauto; simpl. constructor 2; rewrite find_ghost_set_equiv; constructor 2; constructor.
                inv H3. contradiction H10; simpl. constructor 2; rewrite find_ghost_set_equiv; constructor 2; constructor. }
              { rewrite find_ghost_set_equiv in H0; inv H0; auto. inv H3; contradiction. }
Qed.

Lemma pushdown_tree_to_gmap : forall tg1 tg2,
  (forall x y, In_ghost x tg1 -> In_ghost y tg2 -> x < y) ->
  tree_to_gmap (pushdown_ghost tg1 tg2) = union (tree_to_gmap tg1) (tree_to_gmap tg2).
Proof.
  intros; revert dependent tg1; induction tg2; simpl; intros.
  - rewrite right_id; auto.
  - rewrite IHtg2_1.
    rewrite -map_union_assoc insert_union_r; auto.
    destruct (eq_dec (tree_to_gmap tg1 !! k) None); auto.
    apply In_tree_to_gmap, (H _ k) in n; first lia.
    constructor 1; auto.
    { intros; apply H; auto.
      constructor 2; auto. }
Qed.

Lemma delete_tree_to_gmap : forall tg x, sorted_ghost_tree tg ->
  tree_to_gmap (delete_ghost x tg) = delete x (tree_to_gmap tg).
Proof.
  intros; induction tg; auto; simpl.
  - symmetry; apply delete_empty.
  - inv H. destruct (x <? k) eqn: ?; [|destruct (k <? x) eqn: ?]; simpl.
    + rewrite IHtg1; auto.
      rewrite delete_insert_ne; last lia.
      rewrite delete_union (delete_notin (tree_to_gmap tg2)); auto.
      destruct (eq_dec (tree_to_gmap tg2 !! x) None); auto.
      apply In_tree_to_gmap, Hltr in n; lia.
    + rewrite IHtg2; auto.
      rewrite delete_insert_ne; last lia.
      rewrite delete_union (delete_notin (tree_to_gmap tg1)); auto.
      destruct (eq_dec (tree_to_gmap tg1 !! x) None); auto.
      apply In_tree_to_gmap, Hgtl in n; lia.
    + rewrite pushdown_tree_to_gmap.
      assert (x = k) by lia; subst; rewrite delete_insert; auto.
      rewrite lookup_union.
      destruct (eq_dec (tree_to_gmap tg1 !! k) None).
      * rewrite e; destruct (eq_dec (tree_to_gmap tg2 !! k) None).
        { rewrite e0; auto. }
        apply In_tree_to_gmap, Hltr in n; lia.
      * apply In_tree_to_gmap, Hgtl in n; lia.
      * intros ?? ?%Hgtl ?%Hltr; lia.
Qed.

Lemma In_pushdown_left_ghost: forall (t1 t2: ghost_tree) (x: key),
   In_ghost (V := val) x (pushdown_ghost t1 t2) -> In_ghost x t1 \/ In_ghost x t2.
Proof.
  intros. revert t2 H. induction t2; intros; simpl in *; auto. inv H.
  - right. now apply InRoot_ghost.
  - apply IHt2_1 in H1. destruct H1; [left | right]; auto. now apply InLeft_ghost.
  - right. now apply InRight_ghost.
Qed.

Lemma pushdown_left_ghost_sorted: forall (tg1 tg2: ghost_tree),
   sorted_ghost_tree tg1 -> sorted_ghost_tree tg2 -> (forall x y, In_ghost x tg1 -> In_ghost y tg2 -> x < y) ->
   sorted_ghost_tree (V := val) (pushdown_ghost tg1 tg2).
Proof.
  intros. revert tg2 H0 H1. induction tg2; intros; simpl in H0 |-*; auto.
  inv H0. constructor; auto.
  - apply IHtg2_1; auto. intros. apply H1; auto. now apply InLeft_ghost.
  - intros z ?. apply In_pushdown_left_ghost in H0. destruct H0.
    + apply Z.lt_gt, H1; auto. now apply InRoot_ghost.
    + now specialize (Hgtl _ H0).
Qed.

Lemma In_delete_ghost: forall (x: key) (t: ghost_tree) (y: key), In_ghost (V := val) y (delete_ghost x t) -> In_ghost y t.
Proof.
  intros. revert t H. induction t; intros; simpl in *; auto. destruct (x <? k).
  - inv H; try ((now apply InLeft_ghost) || (now apply InRoot_ghost) || (now apply InRight_ghost)).
    apply IHt1 in H1. now apply InLeft_ghost.
  - destruct (k <? x).
    + inv H; try ((now apply InLeft_ghost) || (now apply InRoot_ghost) || (now apply InRight_ghost)).
      apply IHt2 in H1. now apply InRight_ghost.
    + apply In_pushdown_left_ghost in H. destruct H; [apply InLeft_ghost | apply InRight_ghost]; easy.
Qed.

Lemma delete_ghost_sorted: forall (x: key) (t: ghost_tree),
   sorted_ghost_tree t -> sorted_ghost_tree (V := val) (delete_ghost x t).
Proof.
  intros. revert t H. induction t; intros; simpl; auto. inv H.
  destruct (x <? k) eqn: ?; [|destruct (k <? x) eqn: ?].
  - constructor; auto. intros ??%In_delete_ghost. now apply Hgtl.
  - constructor; auto. intros ??%In_delete_ghost. now apply Hltr.
  - apply pushdown_left_ghost_sorted; auto. intros.
    apply Hgtl in H; apply Hltr in H0; lia.
Qed.

Lemma in_tree_del : forall g s g1,
  in_tree g g1 * ghost_ref g s |-- (|==> ghost_ref g (Subtract s g1))%I.
Proof.
  intros. unfold in_tree at 1. Intros sh1. iIntros "H".
  rewrite ghost_part_ref_join.
  iMod (part_ref_update(P := set_PCM) _ _ _ _ (Subtract (Singleton g1) g1) (Subtract s g1) with "H") as "H".
  { intros. repeat constructor.
    - inversion 1; subst.
      inv H. inv H3. specialize (H x). contradict H.
      inv H1. split; auto.
    - inv H. apply Extensionality_Ensembles.
      split; unfold Included; intros.
      { inv H. inv H1.
        apply Union_introl. split; auto.
        apply Union_intror; auto. }
      { inv H. inv H1. congruence.
        split; auto.
        apply Union_intror; auto.
        inv H0. specialize (H x). contradict H.
        split; auto. } }
  fold (ghost_part_ref(P := set_PCM) sh1 (Subtract (Singleton g1) g1) (Subtract s g1) g).
  rewrite <- ghost_part_ref_join.
  iDestruct "H" as "[H $]". iMod (own_dealloc with "H"). auto.
Qed.

Lemma update_ghost_ref_delete: forall g gl gr s g_in, finite s ->
  (in_tree g g_in * ghost_ref g s * in_tree g gr * in_tree g gl  |-- |==>
    ghost_ref g (Subtract (Subtract s gl) gr) * in_tree g g_in)%I .
Proof.
  intros. iIntros "H". iDestruct "H" as "((Ha & Hc) & Hd)".
  iDestruct "Ha" as "(Ha & Hb)".
  iPoseProof (in_tree_del with "[$Hd $Hb]") as ">Hb".
  iPoseProof (in_tree_del with "[$Hc $Hb]") as ">Hb".
  iModIntro; iFrame.
Qed.

Lemma pushdown_find_ghost : forall t1 t2,
  sorted_ghost_tree t1 -> sorted_ghost_tree t2 ->
  find_ghost_set' (pushdown_ghost t1 t2) = Union (find_ghost_set' t1) (find_ghost_set' t2).
Proof.
  intros. revert dependent t1; induction t2; simpl; intros.
  + now rewrite -> Union_comm, Union_Empty.
  + inv H0. rewrite find_ghost_set_equiv.
    rewrite IHt2_1; auto. rewrite (find_ghost_set_equiv t2_1).
    unfold Add.
    rewrite <- (Union_assoc (find_ghost_set' t1) _ (find_ghost_set t2_2 g0)).
    rewrite -> (Union_assoc (find_ghost_set' t1) _ _). reflexivity.
Qed.

Lemma pushdown_left_ghost_unique: forall tg1 tg2,
  sorted_ghost_tree tg1 -> sorted_ghost_tree tg2 ->
  unique_gname tg1 -> unique_gname tg2 ->
  Intersection (find_ghost_set' tg1) (find_ghost_set' tg2) = @Empty_set gname ->
  (forall x y, In_ghost x tg1 -> In_ghost y tg2 -> x < y) ->
  unique_gname (pushdown_ghost tg1 tg2).
Proof.
  induction tg2; simpl; intros; auto.
  inv H0. inv H2. apply Unique_Tree; auto.
  - apply IHtg2_1; auto.
    rewrite -> empty_intersection in *; intros ???.
    eapply H3; eauto.
    constructor 1. rewrite find_ghost_set_equiv; constructor 1; auto.
    { intros; apply H4; auto. apply InLeft_ghost; auto. }
  - rewrite pushdown_find_ghost; auto.
    rewrite -> empty_intersection in *; intros ? Hin ?.
    inv Hin.
    + eapply H3; eauto.
      constructor 2. rewrite find_ghost_set_equiv; constructor 1; auto.
    + eapply H13; eauto.
  - rewrite pushdown_find_ghost; auto.
    intros Hcontra; inv Hcontra; try contradiction.
    rewrite -> empty_intersection in H3; eapply H3; eauto.
    constructor 1; rewrite find_ghost_set_equiv; constructor 2; constructor.
  - rewrite pushdown_find_ghost; auto.
    intros Hcontra; inv Hcontra; try contradiction.
    rewrite -> empty_intersection in H3; eapply H3; eauto.
    constructor 2; rewrite find_ghost_set_equiv; constructor 2; constructor.
Qed.

Lemma delete_find_ghost_weak: forall x tg k,
  sorted_ghost_tree tg -> In_ghost x tg ->
  In (find_ghost_set' (delete_ghost x tg)) k ->
  In (find_ghost_set' tg) k.
Proof.
  induction tg; simpl; intros.
  - inv H1.
  - inv H. inv H0; simpl in *.
    + rewrite Z.ltb_irrefl in H1.
      rewrite pushdown_find_ghost in H1; auto.
      rewrite -> !find_ghost_set_equiv. inv H1; [constructor 1 | constructor 2]; constructor 1; auto.
    + specialize (Hgtl _ H2). destruct (x <? k) eqn:?; try lia.
      inv H1.
      * rewrite -> !find_ghost_set_equiv in * |-*. (* H |-* does not rewrite the 2nd instance on goal *)
      inv H.
      apply Union_introl, Union_introl. apply IHtg1; auto.
      { inv H0; constructor 1; constructor 2; constructor. }
      * constructor 2; auto.
    + specialize (Hltr _ H2). destruct (x <? k) eqn:?; try lia. destruct (k <? x) eqn:?; try lia.
      inv H1.
      * constructor 1; auto.
      * rewrite -> !find_ghost_set_equiv in * |-*. (* H |-* does not rewrite the 2nd instance on goal *)
      inv H.
      apply Union_intror, Union_introl. apply IHtg2; auto.
      { inv H0; constructor 2; constructor 2; constructor. }
Qed.

Lemma delete_ghost_unique: forall x tg,
  In_ghost x tg -> sorted_ghost_tree tg ->
  unique_gname tg -> unique_gname (delete_ghost x tg).
Proof.
  induction tg; simpl; auto; intros.
  inv H0; inv H1. inv H.
  - rewrite Z.ltb_irrefl. apply pushdown_left_ghost_unique; auto.
    intros. apply Hgtl in H. apply Hltr in H0. lia.
  - specialize (Hgtl _ H1); destruct (x <? k) eqn:?; try lia. apply Unique_Tree; auto.
    + rewrite -> empty_intersection in *; intros ???.
      eapply H10; eauto.
      apply delete_find_ghost_weak in H; auto.
    + intros ?%delete_find_ghost_weak; auto.
    + intros ?%delete_find_ghost_weak; auto.
  - specialize (Hltr _ H1); destruct (x <? k) eqn:?; try lia. destruct (k <? x) eqn:?; try lia. apply Unique_Tree; auto.
    + rewrite -> empty_intersection in *; intros ???.
      eapply H10; eauto.
      apply delete_find_ghost_weak in H0; auto.
    + intros ?%delete_find_ghost_weak; auto.
    + intros ?%delete_find_ghost_weak; auto.
Qed.

Lemma ghost_tree_pushdown_left: forall t g g_root g_in gl gr x v,
  tree_rep g g_root t * in_tree g g_in * in_tree g gr |--
  EX n, EX n0, EX o1:option ghost_info,
  public_half g_in (n, n0, Some o1) *
  (!!(o1 = Some (x,v,gl,gr)) -->
     EX o3 : option ghost_info,
     public_half gr (Finite_Integer x, n0, Some o3) *
  ((in_tree g gl -* EX o2 : option ghost_info, (public_half gl (n, Finite_Integer x, Some o2) * ((
      (!!(o1 = Some (x,v,gl,gr) /\ o3 = None /\ (key_in_range x (n,n0) = true)) &&
      public_half g_in (n, n0, Some o2) -* |==> tree_rep g g_root (delete x t) * in_tree g g_in)))))%I
    && ((* turn_left *)(ALL gr1 gr2 : gname, ALL k : key, ALL y : val,
        (!!(o1 = Some (x,v,gl,gr) /\ o3 = Some (k, y, gr1, gr2)
          /\ (key_in_range x (n,n0) = true /\ less_than (Finite_Integer x) (Finite_Integer k) = true)) &&
        (public_half g_in (n, n0, Some (Some (k, y, gr, gr2)))
        * public_half gr (n, Finite_Integer k, Some (Some (x, v, gl, gr1))))
        -* |==> tree_rep g g_root t * in_tree g g_in * in_tree g gr)))%I)).
Proof.
  intros. unfold tree_rep at 1. Intros tg.
  sep_apply node_exist_in_tree; Intros.
  sep_apply (ghost_tree_delete tg g_root g_in gl gr x v); auto.
  Intros n n0 o1; Exists n n0 o1; cancel.
  apply imp_andp_adjoint; Intros; subst.
  rewrite prop_imp; [|auto].
  Intros o3; Exists o3; cancel.
  iIntros "(((Hcase & Hin) & Href) & Hr)"; iSplit.
  + iDestruct "Hcase" as "[Hcase _]"; iDestruct "Hcase" as (o2) "(? & Hcase)".
    iIntros "Hl"; iExists o2; iFrame.
    iIntros "[(% & % & %) Hpub]"; subst.
    iPoseProof (update_ghost_ref_delete with "[$Hin $Href $Hr $Hl]") as "Href".
    { apply find_ghost_set_finite. }
    repeat logic_to_iris. iMod "Href" as "[? $]".
    iMod ("Hcase" with "[$Hpub]") as "[(% & % & % & %) ?]"; [auto|].
    iModIntro.
    unfold tree_rep. iExists (delete_ghost x tg).
    rewrite H7 delete_tree_to_gmap; auto; iFrame.
    iPureIntro; split; auto; split3.
    * intros ?%delete_find_ghost_weak; auto.
    * apply delete_ghost_unique; auto.
    * split; auto; apply delete_ghost_sorted; auto.
  + iDestruct "Hcase" as "[_ Hcase]".
    iIntros (gr1 gr2 k y) "H".
    iSpecialize ("Hcase" $! gr1 gr2 k y with "H").
    repeat logic_to_iris. iMod "Hcase" as (tg') "[(% & % & % & %) ?]"; iModIntro.
    unfold tree_rep; iFrame.
    iExists tg'.
    rewrite -> !find_ghost_set_equiv, !H5 in *; iFrame; auto.
Qed.

Lemma public_update : forall g (a b a' : G), my_half g gsh1 a * public_half g b |-- (|==> my_half g gsh1 a' * public_half g a')%I.
Proof.
  intros; unfold public_half'.
  assert_PROP (sepalg.joins a (b.1, None)).
  { iIntros "(my1 & my2 & ?)".
    iPoseProof (own_valid_2(RA := ref_PCM _) with "[$my1 $my2]") as "%"; iPureIntro.
    destruct H as ((?, ?) & [J ?] & ?); simpl in *.
    destruct g0 as [(?, ?)|]; try contradiction.
    eexists; apply J. }
  destruct H.
  erewrite <- sepcon_assoc, my_half_join by eauto.
  sep_apply (public_update g x b a'); Intros; subst x.
  erewrite <- my_half_join with (a1 := a')(a2 := (fst a', None)); eauto.
  rewrite sepcon_assoc; apply derives_refl.
  { split; hnf; simpl.
    * symmetry; apply merge_id.
    * constructor. }
Qed.

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (
    EX p : val, EX lockp: val, EX tb : val, EX lockb: val, EX gb : gname, EX g_del : gname,
    EX r : range, EX gsh : share,
    PROP (key_in_range x r = true)
    LOCAL (temp _tgp p;  gvars gv)
    SEP (atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤ (λ M (_ : ()), fold_right_sepcon [tree_rep g g_root (delete x M)]) (λ _ : (), Q);
        mem_mgr gv;
        in_tree g g_del; my_half g_del gsh (r, Some (Some (x, vx, ga, gb)));
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        data_at Ews t_struct_tree (vint x, (vx, (ta, tb))) tp;
        ltree g g_del lsh2 gsh p lockp; ltree g ga lsh1 gsh1 ta locka; ltree g gb lsh1 gsh1 tb lockb;
        malloc_token Ews t_struct_tree tp; malloc_token Ews tlock lockp; malloc_token Ews t_struct_tree_t p))%assert.
  { Exists p lockp tb lockb gb g_del r gsh; entailer!. }
  clear dependent g_del r gsh.
  Intros p' lockp' tb' lockb' gb' g_del r gsh.
  unfold ltree at 1; Intros.
  forward.
  forward.
  forward.
  unfold ltree at 2; Intros.
  forward.
  forward_call (lockb', lsh1, node_lock_inv gsh1 g tb' gb' lockb').
  Local Typeclasses eauto := 5.
  Time setoid_rewrite node_lock_inv_def at 2.
  Intros b; destruct b as (rangeb, g_infob).
  rewrite node_rep_def. Intros tbv; simpl.
  forward.
  Time forward_if.
  { subst. unfold tree_rep_R. if_tac; [| contradiction]. Intros.
    freeze FR_ghostb := (in_tree _ gb') (my_half gb' _ _).
    freeze FR_lockb := (lock_inv lsh1 lockb' _) (lock_inv lsh2 lockb' _)
      (field_at Ews _ [StructField _t] _ tb') (malloc_token _ _ tb')
      (field_at lsh2 _ [StructField _lock] _ tb') (malloc_token _ _ lockb')
      (field_at lsh1 _ [StructField _lock] _ tb').
    freeze FR_p := (lock_inv lsh2 lockp' _) (malloc_token _ _ tp) (malloc_token _ _ lockp')
      (malloc_token _ _ p') (field_at lsh2 _ [StructField _lock] _ p').
    forward.
    unfold ltree at 1; Intros.
    forward.
    Time forward_call (locka, lsh1, node_lock_inv gsh1 g ta ga locka).
    Time setoid_rewrite node_lock_inv_def at 2.
    Intros a; destruct a as (rangea, g_infoa).
    rewrite node_rep_def; Intros tav; simpl.
    forward.
    forward.
    thaw FR_p.
    forward_call (t_struct_tree, tp, gv).
    { if_tac; entailer!. }
    thaw FR_lockb.
    freeze FR_p := (lock_inv lsh2 lockp' _) (malloc_token _ _ lockp')
      (malloc_token _ _ p') (field_at lsh2 _ [StructField _lock] _ p') (field_at Ews _ [StructField _t] _ p').
    freeze FR_a := (lock_inv lsh1 locka _) (field_at Ews t_struct_tree_t [StructField _t] _ ta)
      (malloc_token _ _ ta) (in_tree _ ga) (tree_rep_R tav _ _ _) (my_half ga _ _)
      (field_at lsh2 _ [StructField _lock] _ ta) (malloc_token _ _ locka) (lock_inv lsh2 locka _)
      (field_at lsh1 _ [StructField _lock] _ ta).
    forward_call (lockb', Ews, lsh2, node_lock_inv_pred gsh1 g tb' gb' lockb', node_lock_inv gsh1 g tb' gb' lockb').
    { lock_props.
      rewrite <- (lock_inv_share_join lsh1 lsh2 Ews lockb') by auto.
      cancel. }
    forward_call (tlock, lockb', gv).
    { if_tac; entailer!. }
    forward_call (t_struct_tree_t, tb', gv).
    { if_tac.
      { saturate_local. subst tb'. contradiction. }
      { unfold_data_at (data_at_ Ews t_struct_tree_t tb'). simpl; cancel.
        erewrite <- (field_at_share_join _ _ Ews _ [StructField _lock] _ tb') by eauto.
        cancel. } }
    thaw FR_a.
    forward.
    forward_call (locka, Ews, lsh2, node_lock_inv_pred gsh1 g ta ga locka, node_lock_inv gsh1 g ta ga locka).
    { lock_props.
      rewrite <- (lock_inv_share_join lsh1 lsh2 Ews locka) by auto.
      entailer!. }
    forward.
    forward_call (tlock, locka, gv).
    { if_tac; entailer!. }
    forward_call (t_struct_tree_t, ta, gv).
    { if_tac.
      { saturate_local. subst ta. contradiction. }
      unfold_data_at (data_at_ Ews t_struct_tree_t ta).
      cancel. simpl.
      erewrite <- (field_at_share_join _ _ Ews _ [StructField _lock] _ ta) by eauto.
      entailer!. }
    thaw FR_p. destruct r as (n, n0).
    assert_PROP (g_infoa <> None) as infoa. {
      unfold tree_rep_R.
      if_tac. entailer!.
      Intros a b c d e a1 a2 a3. entailer!.
    }
    thaw FR_ghostb.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (in_tree g g_del) (in_tree g ga) (in_tree g gb')
      (my_half gb' _ _) (my_half ga _ _) (tree_rep_R tav _ g_infoa g).
    rewrite -> 5sepcon_assoc.
    viewshift_SEP 0 (Q * (EX o2, EX n1 n2: number, !!(key_in_range x (n1,n2) = true) &&
      my_half g_del gsh ((n1, n2), o2) * in_tree g g_del * tree_rep_R tav (n1, n2) o2 g)). {
      go_lower. eapply sync_commit_gen1. rewrite <- sepcon_assoc.
      - intros. iIntros "[Ha Hb]".
        iDestruct "Ha" as "((H1 & H3) & (H2 & (H4 & H5 & H6)))".
        iPoseProof ((ghost_tree_pushdown_left _ _ _ g_del ga gb') with "[$H1 $H2 $Hb]") as "Hadd".
        iDestruct "Hadd" as (n1 n2 o) "[[Hmya Ha] Hb]".
        iExists (n1, n2, Some o).
        instantiate (1 := vx). instantiate (1 := x). iFrame.
        iIntros "!> %".
        apply node_info_incl' in H7 as [? Heq]; inv Heq.
        iSpecialize ("Hb" with "[% //]").
        iDestruct "Hb" as (o3) "[Ha Hb]".
        iDestruct ("Hb" with "H3") as (o2) "(Hb & Hd)".
        iDestruct (public_sub with "[$Hb $H5]") as %[? J1].
        iDestruct (public_sub with "[$Ha $H4]") as %[? J2].
        iPoseProof (public_update with "[$Hb $H5]") as ">Hga".
        iPoseProof (public_update with "[$Ha $H4]") as ">Hgb".
        instantiate (1:= (Finite_Integer x, n2, Some o3)).
        instantiate (1:= (n1, Finite_Integer x, Some o2)).
        inv J2.
        iIntros "!>".
        iExists ((n, n0), Some o2), ((n1, n2), Some o2); iSplit.
        { iPureIntro. intros (?, ?) H_sep. destruct H_sep; split; auto; simpl in *.
          inv H10; [constructor|].
          inv H14. }
        iIntros "[He Hf]".
        destruct g_infoa; try contradiction; inv J1.
        repeat logic_to_iris.
        iPoseProof (public_part_update(P := node_ghost) _ _ _ _ (n1, n2, Some o) (n1, n2, Some o) with "[$He $Hf]") as "[_ >[He Hf]]".
        { intros ? [J ?]; split; auto; hnf in J |- *.
          symmetry; rewrite puretree.merge_comm; eapply merge_again; rewrite puretree.merge_comm; eauto. }
        rewrite exp_sepcon1; iExists tt.
        assert (key_in_range x (n1, n2) = true) by (eapply key_in_range_incl; eauto).
        iMod ("Hd" with "[$Hmya $Hf]") as "[$ Hf]"; first auto.
        iDestruct "Hga" as "(Hga1 & (Hga2 & Hga3))".
        iDestruct "Hgb" as "(Hgb1 & (Hgb2 & Hgb3))".
        iMod (own_dealloc with "Hga1") as "_"; iMod (own_dealloc with "Hga2") as "_";
        iMod (own_dealloc with "Hga3") as "_".
        iMod (own_dealloc with "Hgb1") as "_"; iMod (own_dealloc with "Hgb2") as "_";
        iMod (own_dealloc with "Hgb3") as "_".
        iModIntro; iExists (Some o), n1, n2; iFrame "Hf".
        iFrame "He".
        iSplit; first auto.
        iApply range_incl_tree_rep_R; last iFrame.
        eapply range_incl_trans, key_in_range_l; eassumption. }
    forward_call (lockp', lsh2, node_lock_inv_pred gsh g p' g_del lockp', node_lock_inv gsh g p' g_del lockp').
    { lock_props.
      setoid_rewrite node_lock_inv_def at 2. Intros o2 n1 n2. Exists (n1, n2, o2).
      rewrite node_rep_def; simpl. Exists tav. cancel. }
    forward. }
  abbreviate_semax. unfold tree_rep_R at 1.
  if_tac.
  { Intros. contradiction. }
  { Intros gbl gbr k v tbl tbr ltbl ltbr.
    forward_call (p', tp, x, vx, ta, tb', tbv, k, v, tbl, tbr).
    forward.
    destruct r as (rangel, rangeh).
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (my_half gb' _ _) (in_tree g gb') (in_tree g g_del).
    repeat rewrite sepcon_assoc. do 2 rewrite <- sepcon_assoc.
    replace_SEP 0 (atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
          (λ M (_ : ()), tree_rep g g_root (delete x M) * emp) (λ _ : (), Q) *
      EX rangedell, EX rangedelh: _, !!(range_incl (rangel, rangeh) (rangedell, rangedelh) = true /\ range_incl rangeb (rangedell, rangedelh) = true /\ x < k) &&
      my_half g_del gsh ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))) * my_half gb' gsh1 ((rangedell, Finite_Integer k), Some (Some (x, vx, ga, gbl)))
    * (in_tree g gb' * in_tree g g_del)). {
      go_lower. rewrite !sepcon_assoc. eapply atomic_rollback.
      - intros. iIntros "((g_del & (gb & (in_gb & in_gdel))) & tree_rep)".
        iPoseProof ((ghost_tree_pushdown_left _ _ _ g_del ga gb') with "[$tree_rep $in_gb $in_gdel]") as (n1 n2 o) "[Ha Hb]".
        iDestruct (public_sub with "[$g_del $Ha]") as %[? J]; inv J.
        instantiate (1 := vx). instantiate (1 := x).
        iPoseProof ("Hb" with "[% //]") as (o3) "[Hpubb Hb]".
        iPoseProof (bi.and_elim_r with "Hb") as "Hb".
        iSpecialize ("Hb" $! gbl gbr k v).
        logic_to_iris.
        iDestruct (public_sub with "[$g_del $Ha]") as %[? J1].
        iDestruct (public_sub with "[$gb $Hpubb]") as %[Hincl J2].
        iDestruct "Ha" as "[Hmya Ha]".
        iPoseProof (public_part_update(P := node_ghost) _ _ _ _ (n1, n2, Some (Some (k, v, gb', gbr))) (n1, n2, Some (Some (k, v, gb', gbr))) with "[$g_del $Ha]") as "[_ >[Hmyga Hpubga]]".
        { intros ? [J J']; split; auto; hnf in J |- *.
          symmetry; rewrite puretree.merge_comm; eapply merge_again; rewrite puretree.merge_comm; eauto.
          destruct c; inv J'; auto; [constructor|].
          inv H14. }
        iPoseProof (public_update _ _ _ (n1, Finite_Integer k, Some (Some (x, vx, ga, gbl))) with "[$gb $Hpubb]") as ">(Hmygb & Hpubgb)".
        inv J2.
        assert (key_in_range x (n1, n2) = true).
        { eapply key_in_range_incl; eauto. }
        assert (x < k).
        { eapply key_in_range_incl in Hincl; [|eauto].
          apply andb_prop in Hincl as []; simpl in *; lia. }
        iDestruct ("Hb" with "[$Hpubgb $Hmya $Hpubga]") as ">(($ & Hgdel) & Hgb)".
        { iPureIntro; repeat (split; auto).
          simpl; lia. }
        iExists n1, n2; iFrame.
        iPureIntro; repeat (split; auto).
        eapply range_incl_trans; try eassumption.
        apply (key_in_range_r _ (_, _)); auto. }
    Intros rangedell rangedelh.
    forward_call (lockp', lsh2, node_lock_inv_pred gsh g p' g_del lockp', node_lock_inv gsh g p' g_del lockp').
    { lock_props.
      setoid_rewrite node_lock_inv_def at 4.
      Exists ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))).
      rewrite node_rep_def; simpl. Exists tbv; cancel.
      unfold tree_rep_R.
      if_tac. { contradiction. }
      Exists gb' gbr k v tb' tbr lockb' ltbr; cancel.
      unfold ltree at 3. do 2 rewrite sepcon_andp_prop'. apply andp_right.
      - apply prop_right. repeat (split; auto). eapply key_in_range_incl; eauto.
      - cancel. eapply derives_trans.
        2: { apply sepcon_derives; [apply now_later| apply derives_refl]. }
        entailer!. }
    Exists tb' lockb' tbl ltbl gbl gb' (rangedell, Finite_Integer k) gsh1; entailer!.
    { eapply key_in_range_incl in H1; [|eauto].
      unfold key_in_range in *; apply andb_prop in H1 as [-> _]; simpl; lia. }
    unfold ltree. entailer!. }
Qed.

Definition delete_inv (b: val) (lock: val) (sh: share) (x: Z) (g_root: gname) gv
           (inv_names : invG) (Q : mpred) (g:gname) : environ -> mpred :=
  (EX np: val, EX r: node_info, EX g_in: gname, EX lock_in: val, EX gsh : share,
  PROP (key_in_range x (fst r) = true)
  LOCAL (temp _l lock_in; temp _tgt np; temp _t b; temp _x (vint x); gvars gv)
  SEP (nodebox_rep g g_root sh lock b;
      field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
      malloc_token Ews tlock lock_in;
      node_rep np g g_in r; my_half g_in gsh r;
      |> lock_inv lsh2 lock_in  (node_lock_inv gsh g np g_in lock_in);
      atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
        (λ M (_ : ()), fold_right_sepcon [tree_rep g g_root (delete x M)]) (λ _: (), Q); mem_mgr gv))%assert.

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, node_lock_inv (fst (Share.split gsh1)) g np g_root lock). (* acquire(_l); *)
  unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
  fold (node_lock_inv (fst (Share.split gsh1)) g np g_root lock). unfold node_lock_inv_pred, sync_inv.
  Intros rp; destruct rp as (rangep, g_infop). rewrite node_rep_def. Intros tp.
  forward_loop (delete_inv b lock sh x g_root gv inv_names Q g).
  { (* current status implies lookup_inv *)
    unfold delete_inv. Exists np (Neg_Infinity, Pos_Infinity, g_infop) g_root lock (fst (Share.split gsh1)).
    sep_apply (my_half_range_inf g_root (Share.split gsh1).1 (Share.split gsh1).2 rangep (Neg_Infinity, Pos_Infinity)).
    entailer!.
    sep_apply (range_incl_tree_rep_R tp _ _ g_infop g (range_incl_infty rangep)).
    unfold nodebox_rep. Exists np. cancel. unfold ltree. entailer!.
    rewrite node_rep_def. Exists tp. simpl. cancel. }
  (* loop body *)
  clear np H0 rangep g_infop tp. unfold delete_inv. Intros np r g_in lock_in gsh.
  rewrite node_rep_def. Intros tp.
  forward. (* _p = (_tgt -> _t); *)
  forward_if. (* if (_p == (tptr tvoid) (0)) *)
  + (* then branch *)
    subst tp. unfold tree_rep_R. simpl. Intros.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g _).
    viewshift_SEP 0 (Q * (in_tree g g_in * my_half g_in gsh r)). {
      go_lower. apply sync_commit_same1. intros t.
      unfold tree_rep at 1. Intros tg.
      assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in) as Hin. {
        sep_apply node_exist_in_tree. entailer!. }
      sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ Hin). Intros r0.
      iIntros "([[? ?] Hclose] & ? & ?) !>".
      iExists r0; iFrame.
      iIntros "% !> [? ?] !>".
      apply node_info_incl' in H7 as [].
      iExists tt; iFrame.
      unfold tree_rep; iExists tg; iFrame.
      destruct r, r0; simpl in *; subst.
      iSplit.
      { iPureIntro; repeat (split; auto).
        rewrite delete_notin; auto; subst.
        eapply range_info_not_in_gmap; last eassumption; auto.
        eapply key_in_range_incl; eauto. }
      iApply "Hclose"; iFrame. }
    forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np g_in lock_in, node_lock_inv gsh g np g_in lock_in). (* _release2(_l); *)
    { lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
      fold (node_lock_inv gsh g np g_in lock_in). unfold node_lock_inv_pred.
      unfold sync_inv. Exists r. rewrite node_rep_def. Exists nullval.
      unfold tree_rep_R. simpl. entailer!. }
    forward. cancel.
  + (* else branch *)
    unfold tree_rep_R. rewrite if_false; auto. Intros ga gb x0 v pa pb locka lockb.
    forward. (* _y = (_p -> _key); *)
    forward_if. (* if (_x < _y) { *)
    * forward. (* _tgt = (_p -> _left); *)
      forward. (* _l_old = _l; *) unfold ltree at 1. Intros.
      forward. (* _l = (_tgt -> _lock); *)
      forward_call (locka, lsh1, node_lock_inv gsh1 g pa ga locka). (* _acquire(_l); *)
      unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
      fold (node_lock_inv gsh1 g pa ga locka). unfold node_lock_inv_pred, sync_inv.
      Intros a. rewrite node_rep_def. Intros tpa.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g g_in) (my_half ga _ _).
      sep_apply (in_tree_left_range unit
                   (λ M (_ : ()), tree_rep g g_root (delete x M) * emp) (λ _ : (), Q)
                   x x0 g g_root inv_names v g_in ga gb). Intros ba.
      forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np g_in lock_in, node_lock_inv gsh g np g_in lock_in). (* _release2(_l_old); *)
      { lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
         rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
         rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
         unfold ltree. entailer!. rewrite sepcon_comm. rewrite !later_sepcon. cancel. }
      unfold delete_inv. destruct a as [rangea a]. simpl fst in *. simpl snd in *.
      Exists pa (ba, Finite_Integer x0, a) ga locka gsh1. simpl fst.
      sep_apply (range_incl_tree_rep_R tpa _ _ a g H9). entailer!.
      { simpl. rewrite andb_true_iff. clear -H0 H6 H8. split; [|lia].
        destruct r, g. simpl fst in *.
        unfold key_in_range in H0. apply andb_true_iff in H0. destruct H0.
        eapply less_than_equal_less_than_trans; eauto. }
      rewrite node_rep_def. Exists tpa. simpl. cancel.
    * forward_if. (* if (_y < _x) { *)
      - forward. (* _tgt = (_p -> _right); *)
        forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
        forward. (* _l = (_tgt -> _lock); *)
        forward_call (lockb, lsh1, node_lock_inv gsh1 g pb gb lockb).
        (* _acquire(_l); *)
        unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
        fold (node_lock_inv gsh1 g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
        Intros a. rewrite node_rep_def. Intros tpb.
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g g_in) (my_half gb _ _).
        sep_apply (in_tree_right_range unit
                     (λ M (_ : ()), tree_rep g g_root (delete x M) * emp) (λ _ : (), Q)
                     x x0 g g_root inv_names v g_in ga gb). Intros ta.
        forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np g_in lock_in, node_lock_inv gsh g np g_in lock_in). (* _release2(_l_old__1); *)
        { lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
          rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
          rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
          unfold ltree. entailer!. rewrite !later_sepcon. cancel. }
        unfold delete_inv. destruct a as [rangea a]. simpl fst in *.
        simpl snd in *. Exists pb (Finite_Integer x0, ta, a) gb lockb gsh1.
        simpl fst. sep_apply (range_incl_tree_rep_R tpb _ _ a g H10). entailer!.
        { unfold key_in_range. rewrite andb_true_iff. clear -H0 H7 H9.
          split. 1: simpl; now rewrite Z.ltb_lt. destruct r, g. simpl fst in *.
          simpl in H9. unfold key_in_range in H0. apply andb_true_iff in H0.
          destruct H0. eapply less_than_less_than_equal_trans; eauto. }
        rewrite node_rep_def. Exists tpb. simpl. cancel.
      - assert (x0 = x) by lia. subst x0. clear H6 H7. destruct r as [range ?].
        simpl fst in *. simpl snd in *. subst g0.
        forward_call (np, tp, lock_in, gsh, x, v, locka, lockb, pa, pb, g, g_root, gv, range, g_in, ga, gb, Q, inv_names).
        { rewrite sepcon_andp_prop'; apply andp_right.
          { entailer!.
            rewrite -> field_compatible_cons in H2; apply H2. }
          unfold ltree; cancel. }
        forward.
Qed.
