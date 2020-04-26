Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc.
Require Import VST.atomics.general_locks.
Require Import bst.verif_bst_conc_atomic.

Definition SEP_index : list Z := upto 22.

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (
    EX p : val, EX lockp: val, EX tb : val, EX lockb: val, EX gb : gname,
    PROP ()
    LOCAL (temp _tgp p;  gvars gv)
    SEP (atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep2 g g_root BST) ∅ ⊤
        (λ (BST : tree) (_ : ()), fold_right_sepcon [!! sorted_tree (delete x BST) && tree_rep2 g g_root (delete x BST)])
        (λ _ : (), Q);
        mem_mgr gv;
        in_tree g g_root; my_half g_root (range, Some (x, vx, ga, gb));
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        data_at Ews t_struct_tree (vint x, (vx, (ta, tb))) tp; 
        ltree g g_root lsh2 p lockp;
        ltree g ga lsh1 ta locka; ltree g gb lsh1 tb lockb;
        malloc_token Ews t_struct_tree tp;
        malloc_token Ews tlock lockp;
        malloc_token Ews t_struct_tree_t p))%assert.
  { Exists p lockp tb lockb gb. entailer!. }
  Intros p' lockp' tb' lockb' gb'.
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
  { freeze FR_ghostb := (in_tree _ gb') (tree_rep_R tbv _ _ _) (my_half gb' _).
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
      (malloc_token _ _ ta) (in_tree _ ga) (tree_rep_R tav _ _ _) (my_half ga _)
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
    thaw FR_p.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_root _) (in_tree g g_root).
    viewshift_SEP 0 (Q * (my_half g_root (rangea, g_infoa) * in_tree g g_root)). {
      go_lower. eapply sync_commit_gen1.
      - intros. iIntros "[Ha Hb]". iDestruct "Hb" as "[% Hb]".
        iPoseProof (extract_lemmas_for_treerep2 with "[Ha Hb]") as "Hadd".
        + apply H5.
        + iFrame.
        + iDestruct "Hadd" as (n1 n2 o) "[Ha Hb]". iExists (n1, n2, o).
          iModIntro. iFrame.
      admit. }
    forward_call (lockp', lsh2, node_lock_inv_pred g p' g_root lockp', node_lock_inv g p' g_root lockp').
    { lock_props.
      setoid_rewrite node_lock_inv_def at 2. Exists (rangea, g_infoa).
      rewrite node_rep_def; simpl. Exists tav. cancel. }
    unfold tree_rep_R. rewrite H3; simpl; Intros.
    forward. admit. }
  unfold tree_rep_R at 1. abbreviate_semax.
  if_tac.
  { Intros. contradiction. }
  { Intros gbl gbr k v tbl tbr ltbl ltbr.
    forward_call (p', tp, x, vx, ta, tb', tbv, k, v, tbl, tbr).
(*     { admit. } (* Need fix in assert_PROP to handle later statements. *) *)
    forward.
    forward_call (lockp', lsh2, node_lock_inv_pred g p' g_root lockp', node_lock_inv g p' g_root lockp').
    { lock_props.
      setoid_rewrite node_lock_inv_def at 4.
      Exists (range, Some (x, vx, ga, gb')).
      rewrite node_rep_def; simpl. Exists tbv. cancel.
      unfold tree_rep_R.
      if_tac.
      { contradiction. }
      { Exists g_root gbr k v tb' tbr lockb' ltbr. cancel.
        unfold ltree at 3. entailer!.
(*        rewrite later_sepcon. cancel. }
    Exists tb' lockb' tbl ltbl.
    entailer!.
    unfold ltree at 1.
    entailer!. }
*)
Admitted.

Definition delete_inv (b: val) (lock: val) (sh: share) (x: Z) (g_root: gname) gv
           (inv_names : invG) (Q : mpred) (g:gname) : environ -> mpred :=
  (EX np: val, EX r: number * number * option ghost_info,
   EX g_in: gname, EX lock_in: val,
  PROP ( check_key_exist' x (fst r) = true )
  LOCAL (temp _l lock_in; temp _tgt np; temp _t b; temp _x (vint x); gvars gv)
  SEP (nodebox_rep g g_root sh lock b; 
      field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
      malloc_token Ews tlock lock_in;
      node_rep np g g_in r; my_half g_in r;
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
    unfold delete_inv. Exists np (rangep, g_infop) g_root lock.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _) (in_tree g _).
    sep_apply (in_tree_root_range
                 unit
                 (λ (BST : tree) (_ : ()),
                  !! sorted_tree (delete x BST) && tree_rep2 g g_root (delete x BST) *
                  emp) (λ _ : (), Q) g g_root inv_names rangep g_infop).
    entailer. cancel. unfold nodebox_rep. Exists np. cancel. unfold ltree. entailer!.
    rewrite node_rep_def. Exists tp. simpl. cancel.
  - (* loop body *)
    clear np H0 rangep g_infop tp. unfold delete_inv. Intros np r g_in lock_in.
    rewrite node_rep_def. Intros tp.
    forward. (* _p = (_tgt -> _t); *)
    forward_if. (* if (_p == (tptr tvoid) (0)) *)
    + (* then branch *)
      subst tp. unfold tree_rep_R. simpl. Intros.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _) (in_tree g _).
      viewshift_SEP 0 (Q * (in_tree g g_in * my_half g_in r)). {
        go_lower. apply sync_commit_gen1. intros t. unfold tree_rep2 at 1. Intros tg.
        assert_PROP (Ensembles.In _ (find_ghost_set tg g_root) g_in). {
          sep_apply node_exist_in_tree. entailer!. }
        sep_apply (ghost_tree_rep_public_half_ramif
                     _ _ (Neg_Infinity, Pos_Infinity) _ H4). Intros r0.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. cancel.
        apply imp_andp_adjoint. Intros. subst r0.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists r. rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists tt. entailer. rewrite sepcon_comm. rewrite <- !sepcon_assoc.
        sep_apply wand_frame_elim. destruct r as [rg r2]. simpl in H1, H0. subst r2.
        assert (delete x (find_pure_tree tg) = find_pure_tree tg). {
          apply delete_not_in.
          apply (range_info_in_tree_not_In
                   _ _ rg (Neg_Infinity, Pos_Infinity)); auto. }
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
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _)
                   (in_tree g g_in) (my_half ga a).
        sep_apply (in_tree_left_range
                     unit
                     (λ (BST : tree) (_ : ()),
                      !! sorted_tree (delete x BST) &&
                      tree_rep2 g g_root (delete x BST) * emp) (λ _ : (), Q)
                     x x0 g g_root inv_names v g_in ga gb r a). Intros.
        forward_call (lock_in, lsh2, node_lock_inv_pred g np g_in lock_in,
                      node_lock_inv g np g_in lock_in). (* _release2(_l_old); *)
        -- lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
           rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
           rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
           unfold ltree. entailer!. rewrite sepcon_comm. rewrite !later_sepcon. cancel.
        -- unfold delete_inv. Exists pa a ga locka. entailer!.
           ++ rewrite H8. rewrite andb_true_iff. destruct r. destruct p.
              simpl fst in *. apply andb_true_iff in H0. destruct H0. simpl.
              rewrite Z.ltb_lt. now split.
           ++ rewrite node_rep_def. Exists tpa. cancel.
      * forward_if. (* if (_y < _x) { *)
        -- forward. (* _tgt = (_p -> _right); *)
           forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
           forward. (* _l = (_tgt -> _lock); *)
           forward_call (lockb, lsh1, (node_lock_inv g pb gb lockb)).
           (* _acquire(_l); *)
           unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
           fold (node_lock_inv g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
           Intros a. rewrite node_rep_def. Intros tpb.
           gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _)
                      (in_tree g g_in) (my_half gb a).
           sep_apply (in_tree_right_range
                        unit
                        (λ (BST : tree) (_ : ()),
                         !! sorted_tree (delete x BST) &&
                         tree_rep2 g g_root (delete x BST) * emp) (λ _ : (), Q)
                        x x0 g g_root inv_names v g_in ga gb r a). Intros.
           forward_call (lock_in, lsh2, node_lock_inv_pred g np g_in lock_in,
                         node_lock_inv g np g_in lock_in). (* _release2(_l_old__1); *)
           ++ lock_props. setoid_rewrite node_lock_inv_def at 4. Exists r.
              rewrite node_rep_def. Exists tp. cancel. unfold tree_rep_R at 2.
              rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
              unfold ltree. entailer!. rewrite !later_sepcon. cancel.
           ++ unfold delete_inv. Exists pb a gb lockb. entailer!.
              ** rewrite H9. rewrite andb_true_iff. destruct r. destruct p.
                 simpl fst in *. simpl snd in *. apply andb_true_iff in H0.
                 destruct H0. split; auto. simpl. now rewrite Z.ltb_lt.
              ** rewrite node_rep_def. Exists tpb. cancel.
        -- assert (x0 = x) by lia. subst x0. clear H6 H7.
Abort.
