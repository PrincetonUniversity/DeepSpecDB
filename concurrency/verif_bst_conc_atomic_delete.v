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
        rewrite later_sepcon. cancel. }
    Exists tb' lockb' tbl ltbl.
    entailer!.
    unfold ltree at 1.
    entailer!. }
Admitted.

Definition delete_inv (b: val) (sh: share) (* (lock: val) *) (x: Z) (* (v: val) *) (g_root: gname) gv (inv_names : invG) (Q : mpred) (g:gname) : environ -> mpred :=
  ( EX np: val, EX r: number * number * option ghost_info, EX g_in :gname, EX lock : val,
  PROP ( check_key_exist x (fst r) = true )
  LOCAL (temp _l lock; temp _tgt np; temp _t b; temp _x (vint x); (* temp _value v; *) gvars gv)
  SEP (lock_inv sh lock (node_lock_inv g np g_in lock);
  node_lock_inv g np g_in lock;
(* lock_inv sh lock (sync_inv g_in (node_rep np g )); node_rep np g g_in r; my_half g_in r; *)
  atomic_shift (λ BST : @tree val, tree_rep2 g g_root BST ) ∅ ⊤
    (λ (BST : @tree val) (_ : ()),
       fold_right_sepcon [tree_rep2 g g_root (delete x BST) ]) 
    (λ _ : (), Q);
    mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b ;
(*      !!(field_compatible t_struct_tree_t nil np) && *)
    field_at sh t_struct_tree_t [StructField _lock] lock np))%assert.

Set Default Timeout 30.

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  unfold nodebox_rep; Intros p.
  unfold ltree; Intros.
  forward.
  forward.
  forward_call (lockb, sh, node_lock_inv g p g_root lockb). (* acquire(_l); *)
  setoid_rewrite node_lock_inv_def at 2.
  Intros rp; destruct rp as (rangep, g_infop).
  rewrite node_rep_def; Intros tpv; simpl.
  forward_loop (delete_inv b sh (* lockb *) x g_root gv inv_names Q g).
  { unfold delete_inv.
    Exists (p) (rangep, g_infop) (g_root) (lockb).
    go_lower. entailer!.
    { admit. }
    { setoid_rewrite node_lock_inv_def at 2.
      Exists (rangep, g_infop). cancel.
      rewrite node_rep_def. Exists tpv; simpl. cancel. }}
  unfold delete_inv. clear dependent p. Intros p rp g_in lockp.
  setoid_rewrite node_lock_inv_def at 2. Intros rp'; destruct rp' as (rangep', g_infop').
  rewrite node_rep_def; Intros tpv'; simpl.
  forward.
  forward_if. (* p == NULL *)
  { forward_call (lockp, lsh2, node_lock_inv_pred g p g_in lockp, node_lock_inv g p g_in lockp).
    { lock_props.
      setoid_rewrite node_lock_inv_def at 3. Exists (rangep', g_infop').
      rewrite node_rep_def. Exists tpv'; simpl.
      cancel. }
    forward.
    { admit. }}
  { unfold tree_rep_R. if_tac.
    { contradiction. }
    { Intros gl gr k v pl pr lockl lockr.
      forward. (* y = p->key *)
      forward_if. (* x < y *)
      { forward.
        forward.
        unfold ltree at 1; Intros.
        forward.
        forward_call (lockl, lsh1, node_lock_inv g pl gl lockl). (* acquire(_l); *)
        forward_call (lockp, lsh2, node_lock_inv_pred g p g_in lockp, node_lock_inv g p g_in lockp).
        { lock_props.
          setoid_rewrite node_lock_inv_def at 5. Exists (rangep', g_infop').
          rewrite node_rep_def. Exists tpv'; simpl.
          unfold tree_rep_R.
          if_tac.
          { contradiction. }
          { Exists (gl) (gr) k v pl pr lockl lockr. cancel.
            unfold ltree at 1. entailer!.
            rewrite later_sepcon.
            cancel. }}
        unfold delete_inv.
        Exists (pl) (rangep', g_infop') (g_in) (lockl).
        go_lower. entailer!.
        { admit. }
        admit.
        (* rewrite t_lock_pred_def at 1. Intros t' tp'.
        unfold t_lock_pred_base. Exists (t') (tp').
        entailer!. *) }
      forward_if. (* y < x *)
      { admit. (* forward.
        forward.
        unfold ltree at 2; Intros.
        forward.
        forward_call (lockr, lsh1, t_lock_pred pr lockr). (* acquire(_l); *)
        forward_call (lockp, lsh2, t_lock_pred_base p lockp, t_lock_pred p lockp).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 4. Exists (tvp) (tp).
          unfold node_rep. rewrite E.
          Exists (pl) (pr) (lockl) (lockr). unfold ltree at 3.
          entailer!.
          rewrite later_sepcon.
          cancel. }
        unfold delete_inv.
        Exists (pr) (lockr).
        rewrite t_lock_pred_def at 1. Intros t' tp'.
        unfold t_lock_pred_base. Exists t' tp'.
        entailer!. *)
        }
      { (* else case *)
        assert_PROP (field_compatible t_struct_tree_t [] p). {
          entailer!.
        }
        forward_call (p, tp, lockp, k, v, lockl, lockr, pl, pr, gv).
        { unfold ltree. entailer!. }
        forward. }
      }
    }
Qed.
