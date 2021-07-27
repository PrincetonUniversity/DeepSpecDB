Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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
  apply InLeft_ghost; auto.
  apply InRight_ghost; auto.
Qed.

Lemma gt_ghost_ensembles_equiv : forall x k t v,
  sorted_ghost_tree t ->
  gt_ghost t k -> Ensembles.In (find_tree_kv_ghost t) (x, v)
  -> k > x.
Proof.
  intros. induction t.
  - inv H1.
  - unfold gt_ghost in H0. inv H. inv H1. inv H.
    apply IHt1; auto.
    unfold gt_ghost; intros. apply H0. apply InLeft_ghost; auto.
    apply IHt2; auto.
    unfold gt_ghost; intros. apply H0. apply InRight_ghost; auto.
    inv H. apply H0. apply InRoot_ghost; auto.
Qed.

Lemma gt_ghost_kv_set : forall t tg k,
  sorted_ghost_tree t -> sorted_ghost_tree tg ->
  find_tree_kv_ghost t = find_tree_kv_ghost tg ->
  gt_ghost t k -> gt_ghost tg k.
Proof.
  intros. unfold gt_ghost; intros.
  apply in_find_tree_kv_ghost in H3. destruct H3 as [v H3].
  rewrite <- H1 in H3.
  apply gt_ghost_ensembles_equiv with (t := t) (v := v); auto.
Qed.

Lemma lt_ghost_ensembles_equiv : forall x k t v,
  sorted_ghost_tree t ->
  lt_ghost t k -> Ensembles.In (find_tree_kv_ghost t) (x, v)
  -> k < x.
Proof.
  intros. induction t.
  - inv H1.
  - unfold lt_ghost in H0. inv H. inv H1. inv H.
    apply IHt1; auto.
    unfold lt_ghost; intros. apply H0. apply InLeft_ghost; auto.
    apply IHt2; auto.
    unfold lt_ghost; intros. apply H0. apply InRight_ghost; auto.
    inv H. apply H0. apply InRoot_ghost; auto.
Qed.

Lemma lt_ghost_kv_set : forall t tg k,
  sorted_ghost_tree t -> sorted_ghost_tree tg ->
  find_tree_kv_ghost t = find_tree_kv_ghost tg ->
  lt_ghost t k -> lt_ghost tg k.
Proof.
  intros. unfold lt_ghost; intros.
  apply in_find_tree_kv_ghost in H3. destruct H3 as [v H3].
  rewrite <- H1 in H3.
  apply lt_ghost_ensembles_equiv with (t := t) (v := v); auto.
Qed.

Lemma extract_public_half_from_ghost_tree_rep_pushdown: forall tg gl rootl rootr,
  sorted_ghost_tree tg ->
  ghost_tree_rep tg gl (rootl, rootr) |--
  EX o : option ghost_info,
    !! (match o with
        | None => tg = E_ghost
        | Some (x, y, g1, g2) => (exists tg1 tg2, tg = T_ghost tg1 g1 x y tg2 g2)
        end) &&
    (public_half gl (rootl, rootr, Some o)) *
    (ALL rootl2 : number, ALL rootr2 : number, ALL g : gname,
      !! (range_inclusion (rootl, rootr) (rootl2, rootr2) = true) &&
      public_half g (rootl2, rootr2, Some o) -* |==> ghost_tree_rep tg g (rootl2, rootr2)).
Proof.
  induction tg; intros.
  - simpl. Exists (None: @option ghost_info). entailer!.
    allpr_intros rootl2; allpr_intros rootr2; allpr_intros g.
    rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. Intros.
    apply ghost_seplog.bupd_intro.
  - simpl. Exists (Some (k, v, g, g0)). entailer!.
    eauto. allpr_intros rootl2; allpr_intros rootr2; allpr_intros g'.
    inv H. sep_apply IHtg1. sep_apply IHtg2.
    Intros o1. Intros o2.
    rewrite <- wand_sepcon_adjoint.
    iIntros "((Ha & Hb) & Hc)". logic_to_iris.
    iDestruct "Ha" as "[root_left tree_left]".
    iDestruct "Hb" as "[root_right tree_right]".
    iSpecialize ("tree_left" $! (Finite_Integer k) rootr2  g0).
    iSpecialize ("tree_right" $! rootl2 (Finite_Integer k) g).
    iDestruct "Hc" as "[% Hc]". apply andb_prop in H1. destruct H1.
    assert (range_inclusion (rootl, Finite_Integer k) (rootl2, Finite_Integer k) = true). {
      apply andb_true_intro. split; try apply less_than_equal_itself. auto.
    }
    assert (range_inclusion (Finite_Integer k, rootr) (Finite_Integer k, rootr2) = true). {
      apply andb_true_intro. split; try apply less_than_equal_itself. auto.
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


Lemma extract_public_half_from_ghost_tree_rep_pushdown_left3: forall tg g_root g_in gl gr x v (r_root: number * number),
 Ensembles.In (find_ghost_set tg g_root) g_in ->
 (forall k, In_ghost k tg -> check_key_exist' k r_root = true) ->
 sorted_ghost_tree tg -> unique_gname tg ->
 ~Ensembles.In (find_ghost_set' tg) g_root ->
 ghost_tree_rep tg g_root r_root |--
 EX n:number, EX n0:number, EX o1:option ghost_info,
 !!(range_inclusion (n,n0) r_root = true) &&
 public_half g_in (n, n0, Some o1) *
 (!!(o1 = Some (x,v,gl,gr)) -->
   EX o3 : option ghost_info,
  public_half gr (Finite_Integer x, n0, Some o3) *
 ((EX o2 : option ghost_info,
        public_half gl (n, Finite_Integer x, Some o2) * 
   (!!(o1 = Some (x,v,gl,gr) /\ o3 = None /\ (check_key_exist' x (n,n0) = true)) &&
      public_half g_in (n, n0, Some (* o1' *) o2) -* |==> (!! (In_ghost x tg
        /\ find_ghost_set (delete_ghost x tg) g_root = (Subtract ( Subtract (find_ghost_set tg g_root) gl) gr)
        /\ Ensembles.In (find_ghost_set' tg) gl /\ Ensembles.In (find_ghost_set' tg) gr)
        && ghost_tree_rep (delete_ghost x tg) g_root r_root))%I)

   && (ALL gr1 gr2 : gname, ALL k : key, ALL y : val,
        (!!(o1 = Some (x,v,gl,gr) /\ o3 = Some (k, y, gr1, gr2)
          /\ (check_key_exist' x (n,n0) = true) /\ less_than (Finite_Integer x) (Finite_Integer k) = true) &&
        (public_half g_in (n, n0, Some (Some (k, y, gr, gr2)))
        * public_half gr (n, Finite_Integer k, Some (Some (x, v, gl, gr1))))
        -* |==> (EX tg',
          !!(find_tree_kv_ghost tg = find_tree_kv_ghost tg' /\
             find_ghost_set' tg = find_ghost_set' tg' /\
             sorted_ghost_tree tg' /\ unique_gname tg') &&
           ghost_tree_rep tg' g_root r_root)))%I)).
Proof.
 intros. revert dependent g_root. destruct r_root as (rootl, rootr).
  revert dependent rootl. revert dependent rootr. induction tg.
  - intros. simpl in H; inv H. simpl.
    Exists rootl rootr (None : @option ghost_info).
    do 1 rewrite -> sepcon_andp_prop'. apply andp_right;
    [apply prop_right | rewrite <- sepcon_emp at 1].
    + repeat rewrite less_than_equal_itself; auto.
    + cancel. rewrite <- imp_andp_adjoint. rewrite andp_comm.
      apply derives_extract_prop; intros. congruence.
  - intros ? ? ? ? ? Hroot. inv H1. simpl in H. inv H.
    + inv H1; inv H2.
      { Opaque range_inclusion check_key_exist'. simpl.
        Transparent range_inclusion check_key_exist'.
        sep_apply IHtg1; clear IHtg1 IHtg2.
        { intros.
          assert (check_key_exist' k0 (rootl, rootr) = true). {
            apply H0. apply InLeft_ghost. apply H1.
          }
          unfold gt_ghost in H11. apply H11 in H1.
          unfold check_key_exist' in H2. apply andb_prop in H2; destruct H2.
          unfold check_key_exist'. rewrite H2; simpl.
          apply Zaux.Zlt_bool_true; omega. }
        { Intros n1 n2 o1.
          Exists n1 n2 o1.
          rewrite !sepcon_andp_prop'; apply andp_right;
            [apply prop_right | rewrite sepcon_assoc; apply cancel_left].
          { unfold range_inclusion in *. apply andb_prop in H1; destruct H1. (* need a range_inclusion lemma *)
            assert (check_key_exist' k (rootl, rootr) = true). {
              apply H0. apply InRoot_ghost. auto.
            }
            unfold check_key_exist' in H3. apply andb_prop in H3; destruct H3.
            rewrite H1; simpl. apply less_than_to_less_than_equal in H4.
            apply (less_than_equal_transitivity _ _ _ H2 H4). }
          { rewrite <- imp_andp_adjoint. rewrite andp_comm.
            apply derives_extract_prop; intros.
            rewrite prop_imp; auto.
            Intros o3 o2.
            Exists o3 o2.
            rewrite (sepcon_comm _ (public_half _ _ * ghost_tree_rep tg2 _ _)).
            cancel. rewrite -> distrib_sepcon_andp. apply andp_derives.
            { cancel.
              rewrite <- (emp_wand (public_half g_root _ * ghost_tree_rep _ _ _)).
              rewrite -> wand_sepcon_wand. rewrite -> emp_sepcon.
              rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm.
              rewrite -> wand_frame_elim.
              rewrite (ghost_seplog.bupd_frame_l (public_half _ _ * _)).
              apply ghost_seplog.bupd_mono.
              entailer!. pose proof (H11 x H3).
              assert ((x <? k) = true) as ->. { rewrite Z.ltb_lt; lia. }
              split. apply InLeft_ghost; auto. split; simpl.
              { rewrite H4. apply Extensionality_Ensembles.
                split; unfold Included; intros ? Hset.
                { inversion_clear Hset as [? ? | ? ?]. inv H8. inv H20. inv H8. split. split.
                  apply Union_introl, Union_introl; auto. auto. auto.
                  split. split.
                  apply Union_introl, Union_intror; auto.
                  apply find_ghost_set_empty_intersection_in in H15.
                  destruct H15 as [Htg1gl Htg2gl]. intros Hcontra; inv Hcontra.
                  rewrite find_ghost_set_equiv in H20. inv H20. eapply Htg2gl; eauto.
                  inv H8. congruence.
                  apply find_ghost_set_empty_intersection_in in H15.
                  destruct H15 as [Htg1gl Htg2gl]. intros Hcontra; inv Hcontra.
                  rewrite find_ghost_set_equiv in H20. inv H20. eapply Htg1gl; eauto.
                  inv H8. congruence.
                  inv H8. split. split.
                  apply Union_intror; constructor.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  apply Union_introl. rewrite find_ghost_set_equiv.
                  apply Union_introl; auto.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  apply Union_introl. rewrite find_ghost_set_equiv.
                  apply Union_introl; auto. }
                { inv Hset. inv H8. inv H21. inv H8.
                  apply Union_introl, Union_introl. split; auto.
                  split; auto.
                  apply Union_introl, Union_intror; auto.
                  inv H8. apply Union_intror; constructor; auto. }}
              { repeat rewrite -> find_ghost_set_equiv.
                split; apply Union_introl, Union_introl; auto. }
              pose proof (H11 x H3).
              assert ((x <? k) = true) as ->. { rewrite Z.ltb_lt; lia. }
              simpl. cancel. }
            { allpr_intros gr1; allpr_intros gr2; allpr_intros k0; allpr_intros y.
              repeat (rewrite allp_sepcon2; eapply allp_left).
              instantiate (1 := gr1); instantiate (1 := k0);
              instantiate (1 := gr2); instantiate (1 := y).
              rewrite <- (emp_wand (public_half g_root _ * ghost_tree_rep tg2 _ _)) at 1.
              rewrite wand_sepcon_wand. rewrite emp_sepcon.
              rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm.
              rewrite wand_frame_elim.
              rewrite (ghost_seplog.bupd_frame_l (public_half _ _ * _)).
              apply ghost_seplog.bupd_mono. Intros tg'.
              Exists (T_ghost tg' g k v0 tg2 g0); simpl.
              apply andp_right; [apply prop_right| cancel].
              rewrite !find_ghost_set_equiv.
              rewrite H3; rewrite H4. split; auto.
              split; auto. split. constructor; auto.
              apply gt_ghost_kv_set with (t := tg1); auto.
              constructor; auto. rewrite <- H4; auto.
              rewrite <- H4; auto. rewrite <- H4; auto. }}}}
      { Opaque range_inclusion check_key_exist'. simpl.
        Transparent range_inclusion check_key_exist'.
        sep_apply IHtg2; clear IHtg1 IHtg2.
        { intros.
          assert (check_key_exist' k0 (rootl, rootr) = true). {
            apply H0. apply InRight_ghost; assumption.
          }
          apply H12 in H1. apply andb_prop in H2; destruct H2.
          unfold check_key_exist'. rewrite H3; simpl.
          rewrite andb_true_r. now apply Zaux.Zlt_bool_true. }
        { Intros n1 n2 o1.
          Exists n1 n2 o1.
          rewrite !sepcon_andp_prop'; apply andp_right;
            [apply prop_right | rewrite sepcon_assoc; apply cancel_left].
          { unfold range_inclusion in *. apply andb_prop in H1; destruct H1. (* maybe range_inclusion lemma *)
            assert (check_key_exist' k (rootl, rootr) = true). {
              apply H0. apply InRoot_ghost. auto.
            }
            unfold check_key_exist' in H3. apply andb_prop in H3; destruct H3.
            rewrite H2; simpl. apply less_than_to_less_than_equal in H3.
            rewrite (less_than_equal_transitivity _ _ _ H3 H1); auto. }
          { rewrite <- imp_andp_adjoint. rewrite andp_comm.
            apply derives_extract_prop; intros.
            rewrite prop_imp; auto.
            Intros o3 o2.
            Exists o3 o2.
            rewrite (sepcon_comm _ (public_half _ _ * ghost_tree_rep tg1 _ _)).
            cancel. rewrite -> distrib_sepcon_andp. apply andp_derives.
            { cancel.
              rewrite <- (emp_wand (public_half g_root _ * ghost_tree_rep _ _ _)).
              rewrite -> wand_sepcon_wand. rewrite -> emp_sepcon.
              rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm.
              rewrite -> wand_frame_elim.
              rewrite (ghost_seplog.bupd_frame_l (public_half _ _ * _)).
              apply ghost_seplog.bupd_mono.
              entailer!.
              pose proof (H12 x H3).
              assert ((k <? x) = true) as ->. { rewrite Z.ltb_lt; lia. }
              assert ((x <? k) = false) as ->. { rewrite Z.ltb_nlt; lia. }
              split; simpl. apply InRight_ghost; auto. split.
              { rewrite H4. apply Extensionality_Ensembles. split; unfold Included; intros.
                { inv H8. inv H20. split. split.
                  apply Union_introl, Union_introl; auto.
                  apply find_ghost_set_empty_intersection_in in H15.
                  destruct H15 as [Htg1gl Htg2gl]. intros Hcontra; inv Hcontra.
                  rewrite find_ghost_set_equiv in H8. inv H8. eapply Htg1gl; eauto.
                  inv H15. congruence.
                  apply find_ghost_set_empty_intersection_in in H15.
                  destruct H15 as [Htg1gl Htg2gl]. intros Hcontra; inv Hcontra.
                  rewrite find_ghost_set_equiv in H8. inv H8. eapply Htg1gl; eauto.
                  inv H15. congruence.
                  inv H8. inv H20. split. split.
                  apply Union_introl, Union_intror; auto. auto. auto.
                  inv H20. split. split. apply Union_intror; constructor.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  apply Union_intror. rewrite find_ghost_set_equiv.
                  apply Union_introl; auto.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  apply Union_intror. rewrite find_ghost_set_equiv.
                  apply Union_introl; auto. }
                { inv H8. inv H20. inv H8. inv H20.
                  apply Union_introl, Union_introl; auto.
                  apply Union_introl, Union_intror. split; auto. split; auto.
                  inv H20. apply Union_intror; constructor. }}
              { repeat rewrite -> find_ghost_set_equiv.
                split; apply Union_intror, Union_introl; auto. }
              pose proof (H12 x H3).
              assert ((k <? x) = true) as ->. { rewrite Z.ltb_lt; lia. }
              assert ((x <? k) = false) as ->. { rewrite Z.ltb_nlt; lia. }
              simpl; cancel. }
            { allpr_intros gr1; allpr_intros gr2; allpr_intros k0; allpr_intros y.
              repeat (rewrite allp_sepcon2; eapply allp_left).
              instantiate (1 := gr1); instantiate (1 := k0);
              instantiate (1 := gr2); instantiate (1 := y).
              rewrite <- (emp_wand (public_half g_root _ * ghost_tree_rep tg1 _ _)) at 1.
              rewrite wand_sepcon_wand. rewrite emp_sepcon.
              rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm.
              rewrite wand_frame_elim.
              rewrite (ghost_seplog.bupd_frame_l (public_half _ _ * _)).
              apply ghost_seplog.bupd_mono. Intros tg'.
              Exists (T_ghost tg1 g k v0 tg' g0); simpl.
              apply andp_right; [apply prop_right| cancel].
              rewrite !find_ghost_set_equiv.
              rewrite H3; rewrite H4. split; auto.
              split; auto. split. constructor; auto.
              apply lt_ghost_kv_set with (t := tg2); auto.
              constructor; auto. rewrite <- H4; auto.
              rewrite <- H4; auto. rewrite <- H4; auto. }}}}
    + clear IHtg1 IHtg2. inv H1. inv H2. (* pushdown case *)
      Opaque range_inclusion check_key_exist'. simpl.
      Transparent range_inclusion check_key_exist'.
      Exists rootl rootr (Some (k, v0, g, g0)). entailer!.
(*       rewrite !sepcon_andp_prop'; apply andp_right; *)
(*       [apply prop_right | rewrite !sepcon_assoc; apply cancel_left]. *)
      { unfold range_inclusion. repeat rewrite less_than_equal_itself; auto. }
      { rewrite <- imp_andp_adjoint. rewrite andp_comm.
        apply derives_extract_prop; intros. inv H.
        erewrite extract_public_half_from_ghost_tree_rep_pushdown; auto.
        Intros o2.
        Opaque less_than less_than_equal. destruct tg2; simpl. Transparent less_than less_than_equal.
        { Exists (None : @option ghost_info). cancel. apply andp_right.
            { Exists o2. cancel.
              rewrite Z.ltb_irrefl. rewrite <- wand_sepcon_adjoint. entailer!.
              iIntros "(Ha & Hb)". iSpecialize ("Ha" $! rootl rootr g_in with "[$Hb]").
              iSplit; auto. iPureIntro. apply andb_prop in H1. destruct H1.
              apply andb_true_intro; split.
              apply less_than_equal_itself. apply less_than_to_less_than_equal in H2; auto.
              repeat logic_to_iris. iMod "Ha". iModIntro.
              iSplit.
              { iPureIntro. split. constructor; auto. split.
                apply Extensionality_Ensembles. split; unfold Included; intros.
                { rewrite find_ghost_set_equiv in H2. inv H2.
                  split. split. rewrite find_ghost_set_equiv.
                  apply Union_introl, Union_introl, Union_introl; auto.
                  intros Hcontra; inv Hcontra. apply H15; auto.
                  intros Hcontra; inv Hcontra. apply H18; auto.
                  split. split. apply Union_intror; auto. inv H3.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  rewrite find_ghost_set_equiv.
                  apply Union_introl, Union_intror; constructor.
                  intros Hcontra; inv Hcontra. apply Hroot; simpl.
                  inv H3. rewrite find_ghost_set_equiv.
                  apply Union_intror; constructor. }
                { inv H2. inv H3. inv H2. inv H3.
                  rewrite find_ghost_set_equiv in H2. inv H2.
                  rewrite find_ghost_set_equiv. apply Union_introl; auto.
                  congruence. congruence. inv H3.
                  rewrite find_ghost_set_equiv; apply Union_intror; constructor. }
                { repeat rewrite find_ghost_set_equiv.
                  split. apply Union_introl, Union_intror; constructor.
                  apply Union_intror; constructor. }}
              { iFrame. }}
            { allpr_intros gr1; allpr_intros gr2; allpr_intros k; allpr_intros y.
              rewrite <- wand_sepcon_adjoint. entailer!. inv H1. }}
        Exists (Some (k, v0, g, g0)) o2.
          cancel. apply andp_right.
          { cancel.
            rewrite Z.ltb_irrefl. rewrite prop_false_andp.
            * rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite FF_sepcon.
              apply FF_left.
            * unfold not; intros. destruct H1 as [_ [Hcontra H2]].
              discriminate Hcontra. }
          { allpr_intros gr1; allpr_intros gr2; allpr_intros k'; allpr_intros y.
            rewrite <- wand_sepcon_adjoint. entailer!.
            iIntros "Ha".
            iDestruct "Ha" as"(((((Ha & Hb) & Hc) & Hd) & He) & Hf)".
            iSpecialize ("Hb" $! rootl (Finite_Integer x) gl with "[$Ha]").
            iSplit; auto. iPureIntro.
            apply andb_true_intro; split; apply less_than_equal_itself.
            inv H1. logic_to_iris. iMod "Hb". iModIntro.
            iExists (T_ghost (T_ghost tg1 gl x v tg2_1 gr1) gr k' y tg2_2 gr2).
            simpl.
            iSplit. iSplit; auto.
            { iPureIntro.
              apply Extensionality_Ensembles. split; unfold Included; intros.
              { inv H1. inv H4.
                apply Union_introl, Union_introl, Union_introl, Union_introl; auto.
                inv H1. inv H4.
                apply Union_introl, Union_introl, Union_introl, Union_intror; auto.
                apply Union_introl, Union_intror; auto.
                apply Union_intror; auto.
                apply Union_introl, Union_introl, Union_intror; auto. }
              { inv H1. inv H4. inv H1. inv H4.
                apply Union_introl, Union_introl; auto.
                apply Union_introl, Union_intror, Union_introl, Union_introl; auto.
                apply Union_intror; auto.
                apply Union_introl, Union_intror, Union_introl, Union_intror; auto.
                apply Union_introl, Union_intror, Union_intror; auto. }}
            iSplit; auto.
            { iPureIntro. unfold Add.
              rewrite <- (Union_assoc (find_ghost_set tg1 gl) _ _).
              rewrite <- (Union_assoc (find_ghost_set tg1 gl) _ _).
              rewrite -> (Union_assoc _ _ (Singleton gr)).
              rewrite -> (Union_comm (find_ghost_set tg2_2 gr2) (Singleton gr)).
              rewrite <- (Union_assoc _ _ (find_ghost_set tg2_2 gr2)).
              reflexivity. }
            { iPureIntro. inv H10. split.
              constructor; auto. constructor; auto.
              unfold lt_ghost in H11. unfold lt_ghost; intros.
              pose proof (InLeft_ghost x0 tg2_1 gr1 tg2_2 gr2 k' y H1).
              apply H12 in H4; auto. rewrite -> Z.ltb_lt in H3.
              unfold gt_ghost; intros. inv H1; auto.
              omega.
              apply H11 in H5. omega.
              inv H9. constructor; auto. constructor; auto.
              intro Hcontra; subst. apply H16. simpl.
              apply Union_introl. rewrite find_ghost_set_equiv.
              apply Union_intror; constructor.
              apply find_ghost_set_empty_intersection_in in H14. destruct H14.
              apply Extensionality_Ensembles; split; unfold Included; intros.
              inv H5. apply H1 in H6. contradict H6; simpl.
              rewrite -> !find_ghost_set_equiv.
              apply Union_introl, Union_introl; auto. inv H5.
              intros Hcontra. apply H16; simpl.
              rewrite find_ghost_set_equiv. apply Union_introl, Union_introl; auto.
              apply find_ghost_set_empty_intersection_in in H14. destruct H14.
              intros Hcontra. apply H1 in Hcontra. apply Hcontra; simpl.
              rewrite find_ghost_set_equiv.
              apply Union_introl, Union_intror; constructor.
              intros Hcontra; subst. apply H17; simpl.
              rewrite -> !find_ghost_set_equiv.
              apply Union_intror, Union_intror; constructor.
              apply find_ghost_set_empty_intersection_in in H14.
              simpl; rewrite -> !find_ghost_set_equiv. destruct H14.
              apply Extensionality_Ensembles; split; unfold Included; intros.
              inv H5. inv H6. inv H5. apply H1 in H6. contradict H6; simpl.
              rewrite -> !find_ghost_set_equiv.
              apply Union_intror, Union_introl; auto.
              inv H6. contradict H16; simpl. rewrite -> !find_ghost_set_equiv.
              apply Union_intror, Union_introl; auto.
              apply find_ghost_set_empty_intersection_in in H27. destruct H27.
              inv H5. apply H6 in H14. congruence. inv H14. congruence.
              inv H5.
              simpl. rewrite -> find_ghost_set_equiv. intros Hcontra.
              inv Hcontra. inv H1. congruence. inv H4. congruence.
              apply H17; simpl. apply Union_introl; auto.
              intros Hcontra. apply H17; simpl. rewrite -> !find_ghost_set_equiv.
              apply Union_intror, Union_introl; auto.
              simpl; rewrite -> !find_ghost_set_equiv.
              intros Hcontra. inv Hcontra. inv H1.
              apply find_ghost_set_empty_intersection_in in H14. destruct H14.
              apply H1 in H4. apply H4; simpl. rewrite !find_ghost_set_equiv.
              apply Union_intror, Union_intror; constructor. inv H4.
              contradict H16; simpl. rewrite !find_ghost_set_equiv.
              apply Union_intror, Union_intror; constructor.
              inv H1. congruence. inv H4. congruence. }
            iFrame. }}
Qed.

Lemma pushdown_equiv : forall t1 t2,
  sorted_tree t1 -> sorted_tree t2 ->
  find_tree_kv_pure (pushdown_left t1 t2) = Union (find_tree_kv_pure t1) (find_tree_kv_pure t2).
Proof.
  intros. revert dependent t1. induction t2; intros.
  - simpl. rewrite Union_comm. rewrite -> Union_Empty; auto.
  - simpl. inv H0. rewrite IHt2_1; auto.
    unfold Add.
    rewrite <- (Union_assoc _ _ (Singleton (k, v))).
    rewrite <- (Union_assoc (find_tree_kv_pure t1) _ _).
    reflexivity.
Qed.

Lemma delete_sub_equiv : forall t x default,
  sorted_tree t ->
  find_tree_kv_pure (delete x t) =
  Subtract (find_tree_kv_pure t) (x, lookup default x t).
Proof.
  intros. induction t; simpl.
  - rewrite Subtract_Empty; reflexivity.
  - inv H. destruct (x <? k) eqn:E; simpl.
    + rewrite IHt1; auto. unfold Add.
      apply Extensionality_Ensembles. split; unfold Included; intros.
      { inv H. inv H0. inv H. unfold Subtract, Setminus. split.
        { apply Union_introl, Union_introl; auto. }
        { auto. }
        unfold Subtract, Setminus. split.
        { apply Union_introl, Union_intror; auto. }
        { unfold not; intros. inv H0.
          apply find_tree_kv_in in H.
          apply H7 in H. rewrite -> Z.ltb_lt in E. omega. }
        unfold Subtract, Setminus; split.
        { apply Union_intror; auto. }
        { unfold not; intros. inv H. inv H0.
          now rewrite Z.ltb_irrefl in E. }}
      { inv H. inv H0. inv H.
        apply Union_introl, Union_introl. split; auto.
        apply Union_introl, Union_intror; auto.
        apply Union_intror; auto. }
    + destruct (k <? x) eqn:E2; simpl.
      { rewrite IHt2; auto. unfold Add.
        apply Extensionality_Ensembles. split; unfold Included; intros.
        { inv H. inv H0. unfold Subtract, Setminus; split.
          { apply Union_introl, Union_introl; auto. }
          { unfold not; intros. inv H0.
            apply find_tree_kv_in in H.
            apply H6 in H. rewrite -> Z.ltb_lt in E2. omega. }
          inv H. unfold Subtract, Setminus; split.
          { apply Union_introl, Union_intror; auto. }
          { auto. }
          unfold Subtract, Setminus; split.
          { apply Union_intror; auto. }
          { unfold not; intros. inv H. inv H0.
            now rewrite Z.ltb_irrefl in E2. }}
        { inv H. inv H0. inv H.
          apply Union_introl, Union_introl; auto.
          apply Union_introl, Union_intror. split; auto.
          apply Union_intror; auto. }}
      { apply Extensionality_Ensembles. split; unfold Included; intros.
        { rewrite pushdown_equiv in H; auto. inv H.
          split.
          { apply Union_introl, Union_introl; auto. }
          { unfold not; intros. inv H.
            apply find_tree_kv_in in H0. apply H6 in H0.
            rewrite -> Z.ltb_nlt in E. omega. }
          split.
          { apply Union_introl, Union_intror; auto. }
          { unfold not; intros. inv H.
            apply find_tree_kv_in in H0. apply H7 in H0.
            rewrite -> Z.ltb_nlt in E2. omega. }}
        { rewrite pushdown_equiv; auto. inv H. inv H0.
          auto.
          assert (x = k). {
            rewrite -> Z.ltb_nlt in E. rewrite -> Z.ltb_nlt in E2. omega.
          }
          subst x.
          contradiction H1; auto. }}
Qed.

Lemma pushdown_equiv_ghost : forall t1 t2,
  sorted_ghost_tree t1 -> sorted_ghost_tree t2 ->
  find_tree_kv_ghost (pushdown_ghost t1 t2) = Union (find_tree_kv_ghost t1) (find_tree_kv_ghost t2).
Proof.
  intros. revert dependent t1. induction t2; intros.
  - simpl. rewrite Union_comm. rewrite -> Union_Empty; auto.
  - simpl. inv H0. rewrite IHt2_1; auto.
    unfold Add.
    rewrite <- (Union_assoc _ _ (Singleton (k, v))).
    rewrite <- (Union_assoc (find_tree_kv_ghost t1) _ _).
    reflexivity.
Qed.

Lemma delete_sub_equiv_ghost : forall t x default,
  sorted_ghost_tree t ->
  find_tree_kv_ghost (delete_ghost x t) =
  Subtract (find_tree_kv_ghost t) (x, lookup_ghost default x t).
Proof.
  intros. induction t; simpl.
  - rewrite Subtract_Empty; reflexivity.
  - inv H. destruct (x <? k) eqn:E; simpl.
    + rewrite IHt1; auto. unfold Add.
      apply Extensionality_Ensembles. split; unfold Included; intros.
      { inv H. inv H0. inv H. unfold Subtract, Setminus. split.
        { apply Union_introl, Union_introl; auto. }
        { auto. }
        unfold Subtract, Setminus. split.
        { apply Union_introl, Union_intror; auto. }
        { unfold not; intros. inv H0.
          apply find_tree_kv_inghost in H.
          apply H9 in H. rewrite -> Z.ltb_lt in E. omega. }
        unfold Subtract, Setminus; split.
        { apply Union_intror; auto. }
        { unfold not; intros. inv H. inv H0.
          now rewrite Z.ltb_irrefl in E. }}
      { inv H. inv H0. inv H.
        apply Union_introl, Union_introl. split; auto.
        apply Union_introl, Union_intror; auto.
        apply Union_intror; auto. }
    + destruct (k <? x) eqn:E2; simpl.
      { rewrite IHt2; auto. unfold Add.
        apply Extensionality_Ensembles. split; unfold Included; intros.
        { inv H. inv H0. unfold Subtract, Setminus; split.
          { apply Union_introl, Union_introl; auto. }
          { unfold not; intros. inv H0.
            apply find_tree_kv_inghost in H.
            apply H8 in H. rewrite -> Z.ltb_lt in E2. omega. }
          inv H. unfold Subtract, Setminus; split.
          { apply Union_introl, Union_intror; auto. }
          { auto. }
          unfold Subtract, Setminus; split.
          { apply Union_intror; auto. }
          { unfold not; intros. inv H. inv H0.
            now rewrite Z.ltb_irrefl in E2. }}
        { inv H. inv H0. inv H.
          apply Union_introl, Union_introl; auto.
          apply Union_introl, Union_intror. split; auto.
          apply Union_intror; auto. }}
      { apply Extensionality_Ensembles. split; unfold Included; intros.
        { rewrite pushdown_equiv_ghost in H; auto. inv H.
          split.
          { apply Union_introl, Union_introl; auto. }
          { unfold not; intros. inv H.
            apply find_tree_kv_inghost in H0. apply H8 in H0.
            rewrite -> Z.ltb_nlt in E. omega. }
          split.
          { apply Union_introl, Union_intror; auto. }
          { unfold not; intros. inv H.
            apply find_tree_kv_inghost in H0. apply H9 in H0.
            rewrite -> Z.ltb_nlt in E2. omega. }}
        { rewrite pushdown_equiv_ghost; auto. inv H. inv H0.
          auto.
          assert (x = k). {
            rewrite -> Z.ltb_nlt in E. rewrite -> Z.ltb_nlt in E2. omega.
          }
          subst x.
          contradiction H1; auto. }}
Qed.

Lemma delete_preserved_in_ghost_tree_unstructured: forall t tg x,
  sorted_tree t -> sorted_ghost_tree tg ->
  find_tree_kv_ghost tg = find_tree_kv_pure t ->
  find_tree_kv_ghost (delete_ghost x tg) = find_tree_kv_pure (delete x t).
Proof.
  intros.
  rewrite (delete_sub_equiv_ghost _ _ nullval); auto.
  rewrite (delete_sub_equiv _ _ nullval); auto.
  rewrite H1.
  rewrite (lookup_find_equiv t tg _ _); auto.
Qed.

Lemma pushdown_left_Inghost: forall (t1 t2: ghost_tree) (x: key),
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
  - intros z ?. apply pushdown_left_Inghost in H0. destruct H0.
    + apply Z.lt_gt, H1; auto. now apply InRoot_ghost.
    + now specialize (H10 _ H0).
Qed.

Lemma delete_Inghost: forall (x: key) (t: ghost_tree) (y: key), In_ghost (V := val) y (delete_ghost x t) -> In_ghost y t.
Proof.
  intros. revert t H. induction t; intros; simpl in *; auto. destruct (x <? k).
  - inv H; try ((now apply InLeft_ghost) || (now apply InRoot_ghost) || (now apply InRight_ghost)).
    apply IHt1 in H1. now apply InLeft_ghost.
  - destruct (k <? x).
    + inv H; try ((now apply InLeft_ghost) || (now apply InRoot_ghost) || (now apply InRight_ghost)).
      apply IHt2 in H1. now apply InRight_ghost.
    + apply pushdown_left_Inghost in H. destruct H; [apply InLeft_ghost | apply InRight_ghost]; easy.
Qed.

Lemma delete_ghost_sorted: forall (x: key) (t: ghost_tree),
   sorted_ghost_tree t -> sorted_ghost_tree (V := val) (delete_ghost x t).
Proof.
  intros. revert t H. induction t; intros; simpl; auto. inv H.
  destruct (x <? k) eqn: ?.
  - apply Z.ltb_lt in Heqb. constructor; auto. intros y ?.
    apply delete_Inghost in H. now apply H8.
  - apply Z.ltb_ge in Heqb. destruct (k <? x) eqn: ?.
    + apply Z.ltb_lt in Heqb0. constructor; auto. intros y ?.
      apply delete_Inghost in H. now apply H9.
    + apply pushdown_left_ghost_sorted; auto. intros y z ? ?.
      apply H8 in H. apply H9 in H0. lia.
Qed.

Lemma in_tree_del : forall g s g1,
  in_tree g g1 * ghost_ref g s |--
    (|==> ghost_ref g (Subtract s g1))%I.
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
        split; auto. }}
  change (own g _ _) with (ghost_part_ref(P := set_PCM) sh1 (Subtract (Singleton g1) g1) (Subtract s g1) g).
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
  (* ~In gname (find_ghost_set t1 g1) g2 -> *)
  find_ghost_set' (pushdown_ghost t1 t2) = (Union (find_ghost_set' t1) (find_ghost_set' t2)).
Proof.
  intros. revert dependent t1. induction t2; intros.
  + simpl. now rewrite -> Union_comm, Union_Empty.
  + simpl. inv H0. rewrite find_ghost_set_equiv.
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
  intros. revert dependent tg2. induction tg2; intros; simpl; auto.
  inv H0. inv H2. apply Unique_Tree; auto.
  - apply IHtg2_1; auto.
    apply find_ghost_set_empty_intersection_in in H3; destruct H3.
    apply Extensionality_Ensembles; split; unfold Included; intros.
    inv H3. apply H0 in H5. simpl in H5. contradict H5.
    rewrite find_ghost_set_equiv. apply Union_introl, Union_introl; auto.
    inv H3. intros. apply H4; auto. apply InLeft_ghost; auto.
  - rewrite pushdown_find_ghost; auto.
    apply find_ghost_set_empty_intersection_in in H3; destruct H3.
    apply Extensionality_Ensembles; split; unfold Included; intros x Hinv; inv Hinv.
    inv H3. apply H0 in H6. contradict H6; simpl. rewrite -> !find_ghost_set_equiv.
    apply Union_intror, Union_introl; auto.
    apply find_ghost_set_empty_intersection_in in H17; destruct H17.
    apply H3 in H6. congruence.
  - rewrite pushdown_find_ghost; auto.
    intros Hcontra. inv Hcontra.
    apply find_ghost_set_empty_intersection_in in H3; destruct H3.
    apply H2 in H0. apply H0; simpl. rewrite find_ghost_set_equiv.
    apply Union_introl, Union_intror; constructor. congruence.
  - rewrite pushdown_find_ghost; auto.
    intros Hcontra. inv Hcontra.
    apply find_ghost_set_empty_intersection_in in H3; destruct H3.
    apply H2 in H0. apply H0; simpl. rewrite -> !find_ghost_set_equiv.
    apply Union_intror, Union_intror; constructor. congruence.
Qed.

Lemma delete_find_ghost_weak: forall x tg k,
  sorted_ghost_tree tg -> In_ghost x tg ->
  In (find_ghost_set' (delete_ghost x tg)) k ->
  In (find_ghost_set' tg) k.
Proof.
  intros. induction tg.
  - simpl in H. inv H0.
  - inv H. inv H0; simpl in *.
    + rewrite Z.ltb_irrefl in H1.
      rewrite pushdown_find_ghost in H1; auto.
      rewrite -> !find_ghost_set_equiv. inv H1.
      apply Union_introl, Union_introl; auto.
      apply Union_intror, Union_introl; auto.
    + specialize (H10 x H2). apply Z.gt_lt in H10. rewrite <- Z.ltb_lt in H10.
      rewrite H10 in H1; simpl in H1. inv H1.
      rewrite -> !find_ghost_set_equiv in * |-*. (* H |-* does not rewrite the 2nd instance on goal *)
      inv H.
      apply Union_introl, Union_introl. apply IHtg1; auto.
      inv H0. apply Union_introl, Union_intror; constructor.
      apply Union_intror; auto.
    + specialize (H11 x H2); simpl in H2.
      destruct (x <? k0) eqn:E. rewrite -> Z.ltb_lt in E. lia.
      rewrite <- Z.ltb_lt in H11. rewrite H11 in H1; simpl in H1. inv H1.
      apply Union_introl; auto. rewrite -> !find_ghost_set_equiv in *.
      inv H. apply Union_intror, Union_introl. apply IHtg2; auto.
      inv H0. apply Union_intror, Union_intror; constructor.
Qed.

Lemma delete_ghost_unique: forall x tg,
  In_ghost x tg -> sorted_ghost_tree tg ->
  unique_gname tg -> unique_gname (delete_ghost x tg).
Proof.
  intros. induction tg; simpl; auto; inv H; inv H0; inv H1.
  - rewrite Z.ltb_irrefl. apply pushdown_left_ghost_unique; auto.
    intros. apply H9 in H. apply H10 in H0. lia.
  - destruct (x <? k) eqn:E. apply Unique_Tree; auto.
    apply find_ghost_set_empty_intersection_in in H14; destruct H14.
    apply Extensionality_Ensembles; split; unfold Included; intros x0 Hinv; inv Hinv.
    apply H0 in H2. apply delete_find_ghost_weak in H1; auto. congruence.
    intros Hcontra. apply delete_find_ghost_weak in Hcontra; auto.
    intros Hcontra. apply delete_find_ghost_weak in Hcontra; auto.
    apply H10 in H3. rewrite -> Z.ltb_nlt in E. lia.
  - specialize (H11 x H3). destruct (x <? k) eqn:E. rewrite -> Z.ltb_lt in E.
    lia. rewrite <- Z.ltb_lt in H11. rewrite H11. apply Unique_Tree; auto.
    apply find_ghost_set_empty_intersection_in in H14; destruct H14.
    apply Extensionality_Ensembles; split; unfold Included; intros x0 Hinv; inv Hinv.
    apply H in H1. apply delete_find_ghost_weak in H2; auto. congruence.
    intros Hcontra. apply delete_find_ghost_weak in Hcontra; auto.
    intros Hcontra. apply delete_find_ghost_weak in Hcontra; auto.
Qed.

(* Optimize Heap.
Optimize Proof. *)

Lemma extract_treerep2_for_pushdown_left: forall t g g_root g_in gl gr x v, sorted_tree t ->
  tree_rep3 g g_root t * in_tree g g_in * in_tree g gr |--
  EX n, EX n0, EX o1:option ghost_info,
  public_half g_in (n, n0, Some o1) *
  (!!(o1 = Some (x,v,gl,gr)) -->
     EX o3 : option ghost_info,
     public_half gr (Finite_Integer x, n0, Some o3) *
  ((in_tree g gl -* EX o2 : option ghost_info, (public_half gl (n, Finite_Integer x, Some o2) * ((
      (!!(o1 = Some (x,v,gl,gr) /\ o3 = None /\ (check_key_exist' x (n,n0) = true)) &&
      public_half g_in (n, n0, Some o2) -* |==> tree_rep3 g g_root (delete x t) * in_tree g g_in)))))%I
    && ((* turn_left *)(ALL gr1 gr2 : gname, ALL k : key, ALL y : val,
        (!!(o1 = Some (x,v,gl,gr) /\ o3 = Some (k, y, gr1, gr2)
          /\ (check_key_exist' x (n,n0) = true /\ less_than (Finite_Integer x) (Finite_Integer k) = true)) &&
        (public_half g_in (n, n0, Some (Some (k, y, gr, gr2)))
        * public_half gr (n, Finite_Integer k, Some (Some (x, v, gl, gr1))))
        -* |==> tree_rep3 g g_root t * in_tree g g_in * in_tree g gr)))%I)).
Proof.
  intros. unfold tree_rep3 at 1. Intros tg.
  rewrite !sepcon_assoc.
  rewrite (sepcon_comm (ghost_tree_rep _ _ _)).
  rewrite <- sepcon_assoc.
  rewrite (sepcon_comm (ghost_ref g _)).
  assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in). {
    do 2 apply sepcon_derives_prop. apply node_exist_in_tree.
  }
  rewrite (extract_public_half_from_ghost_tree_rep_pushdown_left3 tg g_root g_in gl gr x v); auto.
  { Intros n n0 o1. Exists n n0 o1. cancel.
    apply imp_andp_adjoint. rewrite andp_comm. apply derives_extract_prop; intros.
    rewrite prop_imp; [ | rewrite H6; auto].
    Intros o3. Exists o3. cancel.
    repeat (rewrite distrib_sepcon_andp). repeat apply andp_derives.
    + rewrite <- wand_sepcon_adjoint. Intros o2. Exists o2. cancel.
      sep_apply (update_ghost_ref_delete). apply find_ghost_set_finite.
      iIntros "(Ha & Hb)". iMod "Ha" as "(Hc & Ha)".
      iIntros "[% H]".
      iSpecialize ("Hb" with "[$H]"). { iSplit; auto. }
      unfold tree_rep3. iMod "Hb" as "[% Hb]". iModIntro. iFrame "Ha".
      iExists (delete_ghost x tg).
      erewrite delete_preserved_in_ghost_tree_unstructured; eauto.
      destruct H7. destruct H8 as [? [-> [? ?]]].
      iFrame. iPureIntro. repeat (split; auto).
      intros Hcontra. apply delete_find_ghost_weak in Hcontra; auto.
      apply delete_ghost_unique; auto.
      apply delete_ghost_sorted; auto.
    + iIntros "(((Ha & Hb) & Hc) & Hd)".
      iIntros (gr1 gr2 k y) "H".
      iSpecialize ("Hd" $! gr1 gr2 k y with "[$H]").
      repeat logic_to_iris. iMod "Hd". iModIntro.
      unfold tree_rep3. iFrame "Ha Hc".
      iDestruct "Hd" as (tg') "[% Hd]".
      iExists (tg'). iFrame.
      destruct H7 as [H7 [H8 H9]].
      rewrite <- H8, <- H7.
      rewrite -> !find_ghost_set_equiv.
      rewrite <- H8. iFrame. iPureIntro. destruct H9. repeat (split; auto). }
Qed.

Lemma public_update : forall g (a b a' : G),
  (my_half g gsh1 a * public_half g b |--
    !!(∃ x : node_info, sepalg.join a x b) && |==> my_half g gsh1 a' * public_half g a')%I.
Proof.
Admitted.

Lemma public_sub : forall a b g,
  my_half g gsh1 a * public_half g b
         |-- !! (∃ x : node_info, sepalg.join a x b).
Proof.
Admitted.

Lemma body_pushdown_left3: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (
    EX p : val, EX lockp: val, EX tb : val, EX lockb: val, EX gb : gname, EX g_del : gname,
    EX range : number * number,
    PROP (check_key_exist' x range = true)
    LOCAL (temp _tgp p;  gvars gv)
    SEP (atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep3 g g_root BST) ∅ ⊤
        (λ (BST : tree) (_ : ()), fold_right_sepcon [!!sorted_tree (delete x BST) && tree_rep3 g g_root (delete x BST)])
        (λ _ : (), Q);
        mem_mgr gv;
        in_tree g g_del; my_half g_del gsh1 (range, Some (Some (x, vx, ga, gb)));
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        data_at Ews t_struct_tree (vint x, (vx, (ta, tb))) tp;
        ltree g g_del lsh2 p lockp;
        ltree g ga lsh1 ta locka; ltree g gb lsh1 tb lockb;
        malloc_token Ews t_struct_tree tp;
        malloc_token Ews tlock lockp;
        malloc_token Ews t_struct_tree_t p))%assert.
  { Exists p lockp tb lockb gb g_del range. entailer!. }
  clear dependent g_del range.
  Intros p' lockp' tb' lockb' gb' g_del range.
  unfold ltree at 1; Intros.
  forward.
  forward.
  forward.
  unfold ltree at 2; Intros.
  forward.
  forward_call (lockb', lsh1, node_lock_inv g tb' gb' lockb').
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
    Time forward_call (locka, lsh1, node_lock_inv g ta ga locka).
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
    forward_call (lockb', Ews, lsh2, node_lock_inv_pred g tb' gb' lockb', node_lock_inv g tb' gb' lockb').
    { lock_props.
      rewrite <- (lock_inv_share_join lsh1 lsh2 Ews lockb') by auto.
      cancel. }
    forward_call (tlock, lockb', gv).
    { if_tac; entailer!. }
    forward_call (t_struct_tree_t, tb', gv).
    { if_tac.
      { saturate_local. subst tb'. contradiction. }
(*       { entailer!. } (* cannot do this because -> Anomaly "Uncaught exception Failure("hd")." *) *)
      { unfold_data_at (data_at_ Ews t_struct_tree_t tb'). simpl; cancel.
        erewrite <- (field_at_share_join _ _ Ews _ [StructField _lock] _ tb') by eauto.
        cancel. }}
    thaw FR_a.
    forward.
    forward_call (locka, Ews, lsh2, node_lock_inv_pred g ta ga locka, node_lock_inv g ta ga locka).
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
    thaw FR_p. destruct range as (n, n0).
    assert_PROP (g_infoa <> None) as infoa. {
      unfold tree_rep_R.
      if_tac. entailer!.
      Intros a b c d e a1 a2 a3. entailer!.
    }
    thaw FR_ghostb.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (in_tree g g_del) (in_tree g ga) (in_tree g gb')
      (my_half gb' _ _) (my_half ga _ _) (tree_rep_R tav _ g_infoa g).
    rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite sepcon_assoc.
    viewshift_SEP 0 (Q * (EX o2: _ , EX n1 n2: number, !!(check_key_exist' x (n1,n2) = true) &&
      my_half g_del gsh1 ((n1, n2), o2) * (in_tree g g_del) * (tree_rep_R tav (n1, n2) o2 g))). {
      go_lower. eapply sync_commit_gen1. rewrite <- sepcon_assoc.
      - intros. iIntros "[Ha Hb]". iDestruct "Hb" as "[% Hb]".
        iDestruct "Ha" as "((H1 & H3) & (H2 & (H4 & H5 & H6)))".
        iPoseProof ((extract_treerep2_for_pushdown_left _ _ _ g_del ga gb' _ _) with "[H1 H2 Hb]") as "Hadd".
        + eassumption.
        + iFrame.
        + iDestruct "Hadd" as (n1 n2 o(*  o3 *)) "[[Hmya Ha] Hb]".
          iExists (n1, n2, Some o).
          instantiate (1 := vx). instantiate (1 := x).
          iFrame.
          iIntros "!> %".
          assert (o = Some (x, vx, ga, gb')). {
            if_tac in a. pose proof (gsh1_not_Tsh H8); congruence.
            destruct a as [? Hsep]. inversion_clear Hsep as [Hsep1 Hsep2].
            simpl in Hsep1, Hsep2. inversion_clear Hsep2 as [? | ? | ? ? ? Hinv]; auto.
            inv Hinv.
          }
          iSpecialize ("Hb" with "[% //]").
          iDestruct "Hb" as (o3) "[Ha Hb]".
          iDestruct ("Hb" with "H3") as (o2) "(Hb & Hd)".
          iPoseProof (public_update with "[Hb H5]") as "Hga". iFrame.
          iDestruct "Hga" as "[% >Hga]".
          iPoseProof (public_update with "[Ha H4]") as "[% >Hgb]". iFrame.
          instantiate (1:= (Finite_Integer x, n2, Some o3)).
          instantiate (1:= (n1, Finite_Integer x, Some o2)). (* node_info_join_Some *)
          destruct H9. pose proof H9 as Hrangea. apply sepalg_range_inclusion in Hrangea.
          inv H9. destruct H10. inv H5. simpl in H8,H9,H11,H12,Hrangea.
          iIntros "!>".
          iExists ((n, n0), Some o2).
          iExists ((n1, n2), Some o2).
          iSplit.
          { iPureIntro. intros b H_sep. inversion_clear H_sep as [Hsep1 Hsep2].
            destruct b. simpl in Hsep1, Hsep2. inv Hsep1. inversion_clear Hsep2.
            { hnf; simpl; split. auto. constructor. }
            { inv H5. }}
          iIntros "[He Hf]".
          match goal with |-context[(|==> ?P)%logic] => change ((|==> P)%logic) with ((|==> P)%I) end.
          iPoseProof (public_update with "[He Hmya Hf]") as "Hmod". unfold public_half'. iFrame.
          iDestruct "Hmod" as "[% > [Hmy Hpub]]".
          iSpecialize ("Hd" with "[Hpub]").
          iSplit. iPureIntro.
          { assert (o3 = None). { inv H9; auto. inv H15. }
            split; auto. split; auto.
            rewrite if_false in a. destruct a as [x3 Hr].
            apply sepalg_range_inclusion in Hr. destruct Hr as [Hlte Hr].
            simpl in Hlte, Hr. apply andb_prop in Hlte. destruct Hlte as [Hlte1 Hlte2].
            unfold check_key_exist' in H1 |-*. apply andb_prop in H1.
            destruct H1 as [Hn Hn0]. apply andb_true_intro; split.
            apply less_than_equal_less_than_transitivity with (b := n); auto.
            apply less_than_less_than_equal_transitivity with (b := n0); auto.
            apply gsh1_not_Tsh. }
          iFrame. Opaque less_than. unfold public_half'; simpl. Transparent less_than.
          iDestruct "Hga" as "(Hga1 & (Hga2 & Hga3))".
          iDestruct "Hgb" as "(Hgb1 & (Hgb2 & Hgb3))".
          iMod (own_dealloc with "Hga1") as "_"; iMod (own_dealloc with "Hga2") as "_";
          iMod (own_dealloc with "Hga3") as "_".
          iMod (own_dealloc with "Hgb1") as "_"; iMod (own_dealloc with "Hgb2") as "_";
          iMod (own_dealloc with "Hgb3") as "_".
          iMod "Hd" as "[Hd He]".
          unfold tree_rep_R. if_tac.
          { iModIntro. iSplitR "He Hmy H6". iExists tt. 
            iFrame. iSplit; auto. iPureIntro. apply delete_sorted; auto.
            iExists (Some o2). destruct H5. iExists n1, n2. iFrame. iSplit.
            iSplit. iPureIntro. rewrite if_false in a. destruct a as [? a].
            apply sepalg_range_inclusion in a; simpl in a. destruct a as [a _].
            unfold check_key_exist' in H1. rewrite -> andb_true_iff in H1, a |-*.
            destruct a as [Hn1 Hn2]; destruct H1 as [Hn Hn0]. split.
            apply less_than_equal_less_than_transitivity with (b := n); auto.
            apply less_than_less_than_equal_transitivity with (b := n0); auto.
            apply gsh1_not_Tsh. iFrame.
            iDestruct "H6" as "[% _]". inv H12; auto. }
          { iDestruct "H6" as (g1 g2 key val p1 p2 lock1 lock2) "((((% & Hdata) & Htoken) & Htreeg1) & Htreeg2)".
            iModIntro. iSplitL "Hd". iExists tt.
            iFrame. iSplit; auto. iPureIntro. apply delete_sorted; auto.
            iExists (Some o2). iExists n1, n2. iFrame. iSplit.
            iPureIntro. split; try done.
            { rewrite if_false in a. destruct a as [? a].
              apply sepalg_range_inclusion in a; simpl in a. destruct a as [a _].
              unfold check_key_exist' in H1. rewrite -> andb_true_iff in H1, a |-*.
              destruct a as [Hn1 Hn2]; destruct H1 as [Hn Hn0]. split.
              apply less_than_equal_less_than_transitivity with (b := n); auto.
              apply less_than_less_than_equal_transitivity with (b := n0); auto.
              apply gsh1_not_Tsh. }
            iExists g1, g2, key, val, p1, p2, lock1, lock2.
            iSplitR "Htreeg2"; iFrame. iSplit; auto.
            destruct H13 as [? [? [? [? [? ckey]]]]].
            iPureIntro. repeat (split; try assumption).
            hnf in H12. simpl in H12. destruct H12. inv H13. auto. inv H13. inv H12.
            destruct rangea as [rangeal rangear].
            destruct Hrangea as [Hrangea _]. unfold range_inclusion in Hrangea.
            apply andb_prop in Hrangea; destruct Hrangea.
            apply andb_prop in ckey; destruct ckey. apply andb_true_intro; split.
            apply less_than_equal_less_than_transitivity with (b := rangeal); auto.
            apply less_than_less_than_equal_transitivity with (b := rangear); auto.
            apply andb_prop in H1. destruct H1 as [Hn Hn0]. destruct H5.
            apply sepalg_range_inclusion in H1; simpl in H1. destruct H1 as [H1 _].
            apply andb_prop in H1; destruct H1.
            apply less_than_equal_transitivity with (b := (Finite_Integer x)); auto.
            apply less_than_to_less_than_equal.
            apply less_than_less_than_equal_transitivity with (b := n0); auto. }}
    forward_call (lockp', lsh2, node_lock_inv_pred g p' g_del lockp', node_lock_inv g p' g_del lockp').
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
    destruct range as (rangel, rangeh).
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (my_half gb' _ _) (in_tree g gb') (in_tree g g_del).
    repeat rewrite sepcon_assoc. do 2 rewrite <- sepcon_assoc.
    replace_SEP 0 (
      atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep3 g g_root BST) ∅ ⊤
          (λ (BST : tree) (_ : ()),
             !! sorted_tree (delete x BST) && tree_rep3 g g_root (delete x BST) * emp)
          (λ _ : (), Q) *
      EX rangedell, EX rangedelh: _, !!(range_inclusion (rangel, rangeh) (rangedell, rangedelh) = true /\ range_inclusion rangeb (rangedell, rangedelh) = true) &&
      my_half g_del gsh1 ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))) * my_half gb' gsh1 ((rangedell, Finite_Integer k), Some (Some (x, vx, ga, gbl)))
    * (in_tree g gb' * in_tree g g_del)). {
      go_lower. rewrite !sepcon_assoc. eapply atomic_rollback.
      - intros. iIntros "((g_del & (gb & (in_gb & in_gdel))) & % & tree_rep)".
        iPoseProof ((extract_treerep2_for_pushdown_left _ _ _ g_del ga gb' _ _) with "[tree_rep in_gb in_gdel]") as "Hadd".
        + eassumption.
        + instantiate (1:= g). instantiate (1:= g_root). iFrame.
        + iDestruct "Hadd" as (n1 n2 o) "[Ha Hb]".
          iPoseProof (public_sub with "[$g_del $Ha]") as "%".
          instantiate (1 := vx). instantiate (1 := x).
          destruct H11 as [[rangex1 ox1] H11]. inv H11. simpl in H13.
          inv H13;[| inv H15]. simpl in H12.
          iPoseProof ("Hb" with "[% //]") as (o3) "[Hpubb Hb]".
          iPoseProof (bi.and_elim_r with "Hb") as "Hb".
          iSpecialize ("Hb" $! gbl gbr k v).
          logic_to_iris.
          iPoseProof (public_update with "[$g_del $Ha]") as "[% >Hga]".
          iPoseProof (public_update with "[$gb $Hpubb]") as "[% >Hgb]".
          instantiate (1 := (n1, Finite_Integer k, Some (Some (x, vx, ga, gbl)))).
          instantiate (1 := (n1, n2, Some (Some (k, v, gb', gbr)))).
          iDestruct "Hga" as "(Hmyga & Hpubga)".
          iDestruct "Hgb" as "(Hmygb & Hpubgb)".
          iDestruct ("Hb" with "[$Hpubgb $Hpubga]") as ">Hb". iPureIntro.
          repeat (split; auto). destruct H11. apply node_info_join_Some in H11.
          inv H11; auto.
          apply andb_prop in H1. destruct H1 as [Hn Hn0].
          destruct H6 as [? Hr]. apply sepalg_range_inclusion in Hr; simpl in Hr.
          destruct Hr as [Hr _]. apply andb_prop in Hr. destruct Hr as [Hn1 Hn2].
          unfold check_key_exist'. apply andb_true_intro; split.
          apply less_than_equal_less_than_transitivity with (b := rangel); auto.
          apply less_than_less_than_equal_transitivity with (b := rangeh); auto.
          destruct rangeb as [rangebl rangebh].
          apply andb_prop in H9. destruct H9 as [Hrangebl Hrangebh].
          destruct H11 as [? Hr]. apply sepalg_range_inclusion in Hr.
          destruct Hr as [Hr _]. apply andb_prop in Hr. destruct Hr as [Hx Hn2].
          apply less_than_equal_less_than_transitivity with (b := rangebl); auto.
          iDestruct "Hb" as "((Htree & Hgdel) & Hgb)".
          iModIntro. iSplitL "Htree".
          { iFrame. auto. }
          { iExists (n1). iExists n2. iFrame. iSplit; try done.
            iPureIntro.
            split. destruct H6 as [? Hr]. apply sepalg_range_inclusion in Hr.
            destruct Hr as [Hr _]. auto.
            destruct rangeb as [rangebl rangebh].
            destruct H6 as [? Hr]. apply sepalg_range_inclusion in Hr.
            destruct Hr as [Hr _]. simpl in Hr. apply andb_prop in Hr. destruct Hr as [Hn1 Hn2].
            destruct H11 as [? Hr]. apply sepalg_range_inclusion in Hr.
            destruct Hr as [Hr _]. apply andb_prop in Hr. destruct Hr as [Hx Hbn2].
            unfold check_key_exist' in H1. apply andb_prop in H1. destruct H1 as [Hxl Hxh].
            apply andb_true_intro; split.
            apply less_than_equal_transitivity with (b := rangel); auto.
            apply less_than_equal_transitivity with (b := (Finite_Integer x)); auto.
            apply less_than_to_less_than_equal; auto. auto. }}
    Intros rangedell rangedelh.
    forward_call (lockp', lsh2, node_lock_inv_pred g p' g_del lockp', node_lock_inv g p' g_del lockp').
    { lock_props.
      setoid_rewrite node_lock_inv_def at 4.
      Exists ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))).
      rewrite node_rep_def; simpl. Exists tbv. cancel.
      unfold tree_rep_R.
      if_tac.
      { contradiction. }
      { Exists gb' gbr k v tb' tbr lockb' ltbr.
        cancel.
        unfold ltree at 3. do 2 rewrite sepcon_andp_prop'. apply andp_right.
        - apply prop_right. repeat (split; auto). unfold range_inclusion in H11.
          destruct rangeb as [rangebl rangebr]. unfold check_key_exist' in H9 |-*.
          rewrite -> andb_true_iff in H9. destruct H9 as [Hrangebl Hrangebr].
          rewrite -> andb_true_iff in H11. destruct H11 as [Hrangedell Hrangedelh].
          apply andb_true_intro; split.
          apply less_than_equal_less_than_transitivity with (b := rangebl); auto.
          apply less_than_less_than_equal_transitivity with (b := rangebr); auto.
        - cancel. eapply derives_trans.
          2: { apply sepcon_derives; [apply now_later| apply derives_refl]. }
          entailer!. }}
    Exists tb' lockb' tbl ltbl gbl gb' (rangedell, Finite_Integer k).
    entailer!.
    { admit. (* Missing x < k *) }
    unfold ltree. entailer!. }
Admitted.

Definition delete_inv (b: val) (lock: val) (sh: share) (x: Z) (g_root: gname) gv
           (inv_names : invG) (Q : mpred) (g:gname) : environ -> mpred :=
  (EX np: val, EX r: node_info,
   EX g_in: gname, EX lock_in: val,
  PROP ( check_key_exist' x (fst r) = true )
  LOCAL (temp _l lock_in; temp _tgt np; temp _t b; temp _x (vint x); gvars gv)
  SEP (nodebox_rep g g_root sh lock b;
      field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
      malloc_token Ews tlock lock_in;
      node_rep np g g_in r; my_half g_in gsh1 r;
      |> lock_inv lsh2 lock_in  (node_lock_inv g np g_in lock_in);
      atomic_shift
        (λ BST : @tree val, !! sorted_tree BST && tree_rep2 g g_root BST ) ∅ ⊤
        (λ (BST : @tree val) (_ : ()),
         fold_right_sepcon [!! sorted_tree (delete x BST) &&
                            tree_rep2 g g_root (delete x BST) ])
        (λ _: (), Q); mem_mgr gv))%assert.

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, node_lock_inv g np g_root lock). (* acquire(_l); *)
  unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
  fold (node_lock_inv g np g_root lock). unfold node_lock_inv_pred, sync_inv.
  Intros rp; destruct rp as (rangep, g_infop). rewrite node_rep_def. Intros tp.
  forward_loop (delete_inv b lock sh x g_root gv inv_names Q g).
  - (* current status implies lookup_inv *)
    unfold delete_inv. Exists np (Neg_Infinity, Pos_Infinity, g_infop) g_root lock.
    gather_SEP (my_half g_root gsh1 _) (my_half g_root gsh2 _).
    rewrite (my_half_range_inf _ _ (Neg_Infinity, Pos_Infinity)). entailer. cancel.
    sep_apply (range_incl_tree_rep_R tp _ _ g_infop g (range_incl_infty rangep)).
    unfold nodebox_rep. Exists np. cancel. unfold ltree. entailer!.
    rewrite node_rep_def. Exists tp. simpl. cancel.
  - (* loop body *)
    clear np H0 rangep g_infop tp. unfold delete_inv. Intros np r g_in lock_in.
    rewrite node_rep_def. Intros tp.
    forward. (* _p = (_tgt -> _t); *)
    forward_if. (* if (_p == (tptr tvoid) (0)) *)
    + (* then branch *)
      subst tp. unfold tree_rep_R. simpl. Intros.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g _).
      viewshift_SEP 0 (Q * (in_tree g g_in * my_half g_in gsh1 r)). {
        go_lower. apply sync_commit_same1. intros t. unfold tree_rep2 at 1. Intros tg.
        assert_PROP (Ensembles.In _ (find_ghost_set tg g_root) g_in). {
          sep_apply node_exist_in_tree. entailer!. }
        sep_apply (ghost_tree_rep_public_half_ramif
                     _ _ (Neg_Infinity, Pos_Infinity) _ H4). Intros r0.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_false in H6; auto with share.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint. destruct H6 as [r1 ?].
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists tt. entailer. rewrite sepcon_comm. rewrite <- !sepcon_assoc.
        sep_apply wand_frame_elim. destruct r as [range r2]. simpl in H1, H0. subst r2.
        destruct r0 as [rg ?]. pose proof H6. apply node_info_join_Some in H6.
        simpl in H6. subst g0. inv H1. simpl in H3. hnf in H3. symmetry in H3.
        assert (delete x (find_pure_tree tg) = find_pure_tree tg). {
          apply delete_not_in.
          apply (range_info_in_tree_not_In
                   _ _ rg (Neg_Infinity, Pos_Infinity)); auto.
          apply merge_range_incl in H3.
          eapply range_incl_check_key_exist'; eauto. }
      rewrite !H1. apply andp_right. 1: apply prop_right; auto.
      cancel. unfold tree_rep2. Exists tg. entailer!. }
      forward_call (lock_in, lsh2, node_lock_inv_pred g np g_in lock_in,
                    node_lock_inv g np g_in lock_in). (* _release2(_l); *)
      * lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
        fold (node_lock_inv g np g_in lock_in). unfold node_lock_inv_pred.
        unfold sync_inv. Exists r. rewrite node_rep_def. Exists nullval.
        unfold tree_rep_R. simpl. entailer!.
      * forward. cancel.
    + (* else branch *)
      unfold tree_rep_R. rewrite if_false; auto. Intros ga gb x0 v pa pb locka lockb.
      forward. (* _y = (_p -> _key); *)
      forward_if. (* if (_x < _y) { *)
      * forward. (* _tgt = (_p -> _left); *)
        forward. (* _l_old = _l; *) unfold ltree at 1. Intros.
        forward. (* _l = (_tgt -> _lock); *)
        forward_call (locka, lsh1, (node_lock_inv g pa ga locka)). (* _acquire(_l); *)
        unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
        fold (node_lock_inv g pa ga locka). unfold node_lock_inv_pred, sync_inv.
        Intros a. rewrite node_rep_def. Intros tpa.
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _)
                   (in_tree g g_in) (my_half ga _ _).
        sep_apply (in_tree_left_range
                     unit
                     (λ (BST : tree) (_ : ()),
                      !! sorted_tree (delete x BST) &&
                      tree_rep2 g g_root (delete x BST) * emp) (λ _ : (), Q)
                     x x0 g g_root inv_names v g_in ga gb r a). Intros ba.
        forward_call (lock_in, lsh2, node_lock_inv_pred g np g_in lock_in,
                      node_lock_inv g np g_in lock_in). (* _release2(_l_old); *)
        -- lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
           rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
           rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
           unfold ltree. entailer!. rewrite sepcon_comm. rewrite !later_sepcon. cancel.
        -- unfold delete_inv. destruct a as [rangea a]. simpl fst in *. simpl snd in *.
           Exists pa (ba, Finite_Integer x0, a) ga locka. simpl fst.
           sep_apply (range_incl_tree_rep_R tpa _ _ a g H9). entailer!.
           ++ simpl. rewrite andb_true_iff. clear -H0 H6 H8. split.
              2: now rewrite Z.ltb_lt. destruct r, g. simpl fst in *.
              unfold check_key_exist' in H0. apply andb_true_iff in H0. destruct H0.
              eapply less_than_equal_less_than_transitivity; eauto.
           ++ rewrite node_rep_def. Exists tpa. simpl. cancel.
      * forward_if. (* if (_y < _x) { *)
        -- forward. (* _tgt = (_p -> _right); *)
           forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
           forward. (* _l = (_tgt -> _lock); *)
           forward_call (lockb, lsh1, (node_lock_inv g pb gb lockb)).
           (* _acquire(_l); *)
           unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
           fold (node_lock_inv g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
           Intros a. rewrite node_rep_def. Intros tpb.
           gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _)
                      (in_tree g g_in) (my_half gb _ _).
           sep_apply (in_tree_right_range
                        unit
                        (λ (BST : tree) (_ : ()),
                         !! sorted_tree (delete x BST) &&
                         tree_rep2 g g_root (delete x BST) * emp) (λ _ : (), Q)
                        x x0 g g_root inv_names v g_in ga gb r a). Intros ta.
           forward_call (lock_in, lsh2, node_lock_inv_pred g np g_in lock_in,
                         node_lock_inv g np g_in lock_in). (* _release2(_l_old__1); *)
           ++ lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
              rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
              rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
              unfold ltree. entailer!. rewrite !later_sepcon. cancel.
           ++ unfold delete_inv. destruct a as [rangea a]. simpl fst in *.
              simpl snd in *. Exists pb (Finite_Integer x0, ta, a) gb lockb.
              simpl fst. sep_apply (range_incl_tree_rep_R tpb _ _ a g H10). entailer!.
              ** unfold check_key_exist'. rewrite andb_true_iff. clear -H0 H7 H9.
                 split. 1: simpl; now rewrite Z.ltb_lt. destruct r, g. simpl fst in *.
                 simpl in H9. unfold check_key_exist' in H0. apply andb_true_iff in H0.
                 destruct H0. eapply less_than_less_than_equal_transitivity; eauto.
              ** rewrite node_rep_def. Exists tpb. simpl. cancel.
        -- assert (x0 = x) by lia. subst x0. clear H6 H7. destruct r as [range ?].
           simpl fst in *. simpl snd in *. subst g0.
           forward_call (np, tp, lock_in, x, v, locka, lockb, pa, pb, g, g_in, gv,
                         range, ga, gb, Q, inv_names).
           ++ unfold ltree.
              assert (Frame = [nodebox_rep g g_root sh lock b]); subst Frame; [easy|].
              clear H2. entailer!.
              ** clear -H2. hnf in *. destruct H2 as [? [? [? [? ?]]]].
                 repeat split; auto.
              ** simpl. cancel. apply atomic_shift_derives'. intros t. Intros.
                 admit.
           ++ forward.
Abort.
