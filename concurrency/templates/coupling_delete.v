Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template_coupling.
Require Import bst.coupling_lib.
Require Import bst.coupling_traverse.
Require Import VST.floyd.library.

Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH gv: globals
  PRE  [  ]
    PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX p: val, EX newt: val, EX lock: val,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (mem_mgr gv; atomic_int_at Ews (vint 0) lock;
         malloc_token Ews t_struct_tree_t newt;
         data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), lock) newt;
         malloc_token Ews (tptr t_struct_tree_t) p;
         data_at Ews (tptr t_struct_tree_t) newt p).

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv).
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv).
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (gv).
  Intros l. (* lock_t *l *)
  forward.
  forward.
  sep_apply atomic_int_isptr.
  Intros.
  forward_call release_nonatomic (l).
  forward.
  Exists p. Exists newt. Exists l.
  entailer !.
Qed.

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH l: val, tl: val, x: Z, vx: val, tll: val,
       r: val, tr: val, y: Z, vy: val, mid: val, trr: val
  PRE  [tptr t_struct_tree_t, tptr t_struct_tree_t]
    PROP (is_pointer_or_null mid)
    PARAMS (l; r) GLOBALS ()
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tl l;
         field_at Ews (t_struct_tree_t) [StructField _t] tr r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, r))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (mid, trr))) tr)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tr l;
         field_at Ews (t_struct_tree_t) [StructField _t] tl r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, mid))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (r, trr))) tr).

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

Program Definition pushdown_left_spec :=
 DECLARE _pushdown_left
 ATOMIC TYPE (rmaps.ConstType
                (val * val * lock_handle * share * Z * val *
                 lock_handle * lock_handle * val * val *
                   gname * gname * globals * range *
                   gname * gname * gname))
 OBJ M INVS ∅
 WITH p, tp, lockp, gsh, x, vx,
      locka, lockb, ta, tb,
       g, g_root, gv, r,
       g_del, ga, gb
  PRE [ tptr t_struct_tree_t ]
    PROP (Int.min_signed <= x <= Int.max_signed;
          tc_val (tptr Tvoid) vx;
          key_in_range x r = true)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv;
         in_tree g g_del;
         my_half g_del gsh (r, Some (Some (x, vx, ga, gb)));
         field_at Ews t_struct_tree_t [StructField _t] tp p;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (ta, tb))) tp;
         ltree g g_del lsh2 gsh2 gsh p lockp;
         ltree g ga lsh1 gsh1 gsh1 ta locka;
         ltree g gb lsh1 gsh1 gsh1 tb lockb;
         malloc_token Ews t_struct_tree tp;
         (* malloc_token Ews t_lock (ptr_of lockp); *)
         malloc_token Ews t_struct_tree_t p) | (tree_rep g g_root M)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv) | (tree_rep g g_root (base.delete x M)).

Program Definition delete_spec :=
 DECLARE _delete
 ATOMIC TYPE (rmaps.ConstType (_ * _ * _ * _ * _ * _ * _))
         OBJ M INVS ∅
 WITH b, x, lock, gv, sh, g, g_root
 PRE  [ tptr (tptr t_struct_tree_t), tint]
    PROP (Int.min_signed <= x <= Int.max_signed; writable_share sh)
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root (base.delete x M)).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; traverse_spec; findnext_spec; pushdown_left_spec; turn_left_spec;
                             delete_spec; freelock_spec ]).

(* Proving delete function satisfies spec *)
Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree.
  Intros np.
  forward_call (t_struct_pn, gv).
  Intros nb.
  forward.
  forward.
  forward.
  forward.
  set (AS := atomic_shift _ _ _ _ _).
  (* acquire(pn->n->lock); *)
  forward_call acquire_inv_simple (sh, lock, node_lock_inv (Share.split gsh1).1 g np g_root lock).
  {
    set Q1:= fun (b : (bool * ( val * (val * (lock_handle * (share * (gname * node_info))))))%type) =>
              if b.1 then AS else AS.
    (* traverse(pn, x, nullval) *)
    (* we assign value to nullval*)
    forward_call (nb, np, sh, lock, x, nullval, gv, g, g_root, Q1).
    {
      unfold pn_rep_1, node_lock_inv'.
      Exists (default_val t_struct_pn).1.
      unfold node_lock_inv.
      sep_apply self_part_eq.
      assert (lsh2 <> Share.bot).
      { apply readable_not_bot. apply readable_lsh2. }
      auto.
      entailer !.
      rewrite -> 2sepcon_assoc. rewrite sepcon_comm.
      rewrite -> sepcon_assoc; apply sepcon_derives; [|cancel].
      unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      iExists m.
      iFrame "Hm".
      iSplit; iFrame.
      { by iApply bi.and_elim_l. }
      {
        iDestruct "HClose" as "[HClose _]".
        iIntros (pt) "[H _]".
        iMod ("HClose" with "H") as "H".
        iModIntro.
        unfold Q1.
        destruct (decide (pt.1 = true)). { rewrite e; iFrame. }
        { apply not_true_is_false in n; rewrite n; iFrame. }
      }
    }
    Intros pt.
    destruct pt as (fl & (p1 & (tp & (lock_in & (gsh & (g_in & r)))))).
    simpl in H1, H2.
    destruct fl.
    simpl.
    change emp with seplog.emp.
    - destruct H2.
      forward_if (
          PROP ( )
            LOCAL (temp _t'4 (ptr_of lock_in); temp _t'3 p1; temp _t'2 Vtrue;
                   temp _t'7 (ptr_of lock); temp _t'6 np; temp _t'8 np;
                   temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x))
            SEP (Q; mem_mgr gv; data_at Ews t_struct_pn (p1, p1) nb;
                 my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                 data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np;
                 lock_inv sh lock
                   (selflock (node_lock_inv_pred (Share.split gsh1).1 g np g_root (ptr_of lock))
                      gsh2 lock);
                 malloc_token Ews t_struct_pn nb)); unfold node_lock_inv_new.
      + pose proof (Int.one_not_zero); easy.
      + (* prove satisfies if_condition*)
        Intros.
        forward.
        forward.
        rewrite H3.
        unfold tree_rep_R, Q1.
        rewrite -> if_true by auto.
        simpl.
        Intros.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (Q * (in_tree g g_in * my_half g_in gsh r)).
        {
          go_lower.
          unfold AS.
          simpl.
          apply sync_commit_same1.
          intros t.
          unfold tree_rep at 1.
          Intros tg.
          assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in) as Hin.
          { sep_apply node_exist_in_tree. entailer!. }
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ Hin).
          Intros r0.
          iIntros "([[? ?] Hclose] & ? & ?) !>".
          iExists r0; iFrame.
          iIntros "% !> [? ?] !>".
          apply node_info_incl' in H12 as []. 
          iExists tt; iFrame.
          unfold tree_rep; iExists tg; iFrame.
          destruct r, r0; simpl in *; subst.
          iSplit.
          { iPureIntro; repeat (split; auto).
            rewrite delete_notin; auto; subst.
            eapply range_info_not_in_gmap; last eassumption; auto.
            eapply key_in_range_incl; eauto.
          }
          iApply "Hclose"; iFrame.
        }
        (*  (_release2(_t'4); *)
        change emp with seplog.emp.
        forward_call release_self (gsh2, lock_in,
                    node_lock_inv_pred gsh g p1 g_in (ptr_of lock_in)).
        {
          unfold node_lock_inv_pred at 3, sync_inv.
          Exists r.
          rewrite node_rep_def.
          unfold node_lock_inv, tree_rep_R.
          Exists nullval.
          rewrite -> if_true by auto.
          entailer !.
        }
        entailer !.
      + forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        forward.
        unfold nodebox_rep, ltree.
        Exists np.
        entailer !.
   - (* _pushdown_left(_t'5);) *)
     unfold Q1.
     destruct H2 as ( ?  & v2 & g21 & g22 & ?).
      simpl.
      forward_if(
          PROP ( )
            LOCAL (temp _t'5 p1; temp _t'2 Vfalse; temp _t'7 (ptr_of lock); temp _t'6 np; 
                   temp _t'8 np; temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x))
            SEP (Q; mem_mgr gv; data_at Ews t_struct_pn (p1, p1) nb;
                 my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                 data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np;
                 lock_inv sh lock
                   (selflock (node_lock_inv_pred (Share.split gsh1).1 g np g_root (ptr_of lock))
                      gsh2 lock);
                 malloc_token Ews t_struct_pn nb)).
      + unfold node_lock_inv_new, tree_rep_R.
        rewrite -> if_false; auto.
        Intros g1 g2 x1 v p1' p2' l1 l2.
        forward.
        destruct r as (x0 & y0).
        simpl in H8.
        simpl in H5. subst y0.
        injection H3.
        intros. subst x1. subst v2. subst g21. subst g22.
        assert_PROP (field_compatible t_struct_tree_t [] p1) by entailer !.
        forward_call (p1, tp, lock_in, gsh, x, v, l1, l2, p1', p2',
                       g, g_root, gv, x0, g_in, g1, g2, Q).
        {
          unfold AS.
          unfold ltree.
          entailer !.
          rewrite ->  5sepcon_assoc; apply sepcon_derives; [|cancel].
          unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "[Hm HClose]".
          iModIntro.
          iExists m.
          iFrame "Hm".
          iSplit; iFrame.
          { by iApply bi.and_elim_l. }
          {
            iDestruct "HClose" as "[_ HClose]".
            done.
          }
        }
        entailer !.
      + (* contradiction, since  Int.one = Int.zero *)
       pose proof Int.one_not_zero; contradiction.
      + (* _free(_pn__2); *)
        forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        forward.
        unfold nodebox_rep, ltree.
        Exists np.
        entailer !.
     }
Qed.

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (
    EX p : val, EX lockp: lock_handle, EX tb : val, EX lockb: lock_handle,
              EX gb : gname, EX g_del : gname, EX r : range, EX gsh : share,
    PROP (key_in_range x r = true)
    LOCAL (temp _tgp p;  gvars gv)
    SEP (atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ (λ M (_ : ()),
             fold_right_sepcon [tree_rep g g_root (delete x M)]) (λ _ : (), Q);
        mem_mgr gv;
        in_tree g g_del; my_half g_del gsh (r, Some (Some (x, vx, ga, gb)));
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        data_at Ews t_struct_tree (vint x, (vx, (ta, tb))) tp;
         ltree g g_del lsh2 gsh2 gsh p lockp;
         ltree g ga lsh1 gsh1 gsh1 ta locka;
         ltree g gb lsh1 gsh1 gsh1 tb lockb;
        malloc_token Ews t_struct_tree tp;
        (* malloc_token Ews t_lock (ptr_of lockp); *)
         malloc_token Ews t_struct_tree_t p))%assert.
  { Exists p lockp tb lockb gb g_del r gsh.
    entailer!.
  }
  clear dependent g_del r gsh.
  Intros p' lockp' tb' lockb' gb' g_del r gsh.
  unfold ltree at 1; Intros.
  change emp with seplog.emp.
  forward.
  forward.
  forward.
  unfold ltree at 2; Intros.
  forward.
  forward_call acquire_inv_simple  (gsh1, lockb', node_lock_inv gsh1 g tb' gb' lockb').
  Local Typeclasses eauto := 5.
  rewrite later_sepcon.
  rewrite later_sepcon.
  unfold sync_inv at 1.
  rewrite <- sepcon_assoc.
  rewrite sepcon_assoc.
  rewrite later_exp'; [ |apply (Neg_Infinity, Pos_Infinity, None)].
  Intros b; destruct b as (rangeb, g_infob).
  rewrite later_sepcon.
  rewrite node_rep_def.
  rewrite later_exp'; last apply ta.
  Intros tbv; simpl.
  rewrite later_sepcon.
  rewrite later_sepcon.
  rewrite later_sepcon.
  Intros.
  forward.
  forward_if.
  { subst.
    unfold tree_rep_R.
    if_tac; [| contradiction].
    Intros.
    change emp with seplog.emp.
    forward.
    unfold ltree at 1; Intros.
    forward.
    forward_call acquire_inv_simple (gsh1, locka, node_lock_inv gsh1 g ta ga locka).
    rewrite later_sepcon.
    rewrite later_sepcon.
    unfold sync_inv at 1.
    rewrite <- sepcon_assoc.
    rewrite sepcon_assoc.
    rewrite later_exp'; [ |apply (Neg_Infinity, Pos_Infinity, None)].
    Intros a; destruct a as (rangea, g_infoa).
    rewrite later_sepcon.
    rewrite node_rep_def.
    rewrite -> later_exp'; last apply ta.
    Intros tav; simpl. 
    rewrite later_sepcon.
    rewrite later_sepcon.
    rewrite later_sepcon.
    Intros.
    forward.
    forward.
    assert_PROP (tp <> nullval) by entailer !.
    forward_call (t_struct_tree, tp, gv).
    { rewrite if_false; auto. cancel. }
    forward_call freelock_self (gsh1, gsh2, lockb',
        node_lock_inv_pred gsh1 g tb' gb' (ptr_of lockb')).
    { unfold node_lock_inv at 2; cancel. }
    assert_PROP (tb' <> nullval) by entailer !.
    forward_call (t_struct_tree_t, tb', gv).
    {
      rewrite if_false; auto.
      unfold_data_at (data_at_ Ews t_struct_tree_t tb'); simpl; cancel.
      rewrite <- (field_at_share_join _ _ Ews _ [StructField _lock] _ tb') by eauto; cancel.
    }
    forward.
    forward_call freelock_self (gsh1, gsh2, locka, node_lock_inv_pred gsh1 g ta ga (ptr_of locka)).
    { unfold node_lock_inv; cancel. }
    assert_PROP (ta <> nullval) by entailer !.
    forward_call (t_struct_tree_t, ta, gv).
    {
      rewrite -> if_false; auto.
      unfold_data_at (data_at_ Ews t_struct_tree_t ta); simpl; cancel.
      rewrite <- (field_at_share_join _ _ Ews _ [StructField _lock] _ ta) by eauto; cancel.
    }
    destruct r as (n, n0).
    assert_PROP (g_infoa <> None) as infoa.
    {
      unfold tree_rep_R.
      if_tac.
      change emp with seplog.emp.
      Intros.
      entailer!.
      Intros a' b' c' d' e' a1 a2 a3. entailer!.
    }
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (in_tree g g_del)
      (in_tree g ga) (in_tree g gb') (my_half gb' _ _) (my_half ga _ _) (tree_rep_R tav _ g_infoa g).
    rewrite -> 5sepcon_assoc.
    viewshift_SEP 0 (Q * (EX o2, EX n1 n2: number, !!(key_in_range x (n1,n2) = true) &&
      my_half g_del gsh ((n1, n2), o2) * in_tree g g_del * tree_rep_R tav (n1, n2) o2 g)).
    {
      go_lower. eapply sync_commit_gen1. rewrite <- sepcon_assoc.
      - intros. iIntros "[Ha Hb]".
        iDestruct "Ha" as "((H1 & H3) & (H2 & (H4 & H5 & H6)))".
        iPoseProof ((ghost_tree_pushdown_left _ _ _ g_del ga gb') with "[$H1 $H2 $Hb]") as "Hadd".
        iDestruct "Hadd" as (n1 n2 o) "[[Hmya Ha] Hb]".
        iExists (n1, n2, Some o).
        instantiate (1 := vx). instantiate (1 := x). iFrame.
        iIntros "!> %".
        apply node_info_incl' in H13 as [? Heq]; inv Heq.
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
          inv H16; [constructor|].
          simpl in *. auto. simpl in *.
          apply sepalg.join_unit2.
          apply psepalg.None_unit; eauto. auto.
          inversion H20. intros; inversion H17; subst. auto.
        }
        iIntros "[He Hf]".
        destruct g_infoa; try contradiction; inv J1.
        repeat logic_to_iris.
        iPoseProof (public_part_update(P := node_ghost) _ _ _ _ (n1, n2, Some o) (n1, n2, Some o)
                     with "[$He $Hf]") as "[_ >[He Hf]]".
        { intros. destruct H15. split. split; auto; simpl.
          hnf in H15; hnf.
          symmetry; rewrite puretree.merge_comm; eapply merge_again.
          symmetry; rewrite puretree.merge_comm; eauto.
          intros; subst; auto.
        }
        rewrite exp_sepcon1; iExists tt.
        assert (key_in_range x (n1, n2) = true) by (eapply key_in_range_incl; eauto).
        iMod ("Hd" with "[$Hmya $Hf]") as "[$ Hf]"; first auto.
        iDestruct "Hga" as "(Hga1 & (Hga2 & Hga3))".
        iDestruct "Hgb" as "(Hgb1 & (Hgb2 & Hgb3))".
        iModIntro; iExists (Some o), n1, n2; iFrame "Hf".
        iFrame "He".
        iSplit; first auto.
        rewrite range_incl_tree_rep_R; last first.
        eapply range_incl_trans, key_in_range_l; eauto.
        simpl in *. apply H5. iFrame; iClear "∗"; done.
    }
    forward_call release_self (gsh2, lockp',
                    node_lock_inv_pred gsh g p' g_del (ptr_of lockp')).
    {
      Intros o2 n1 n2.
      unfold node_lock_inv.
      unfold node_lock_inv_pred.
      unfold sync_inv.
      Exists (n1, n2, o2).
      rewrite node_rep_def.
      simpl.
      Exists tav.
      cancel.
    }
    forward.
  }
  abbreviate_semax.
  unfold tree_rep_R at 1.
  assert_PROP (tbv <> nullval) by entailer !.
  rewrite -> if_false; auto.
  Intros gbl gbr k v tbl tbr ltbl ltbr.
  forward_call (p', tp, x, vx, ta, tb', tbv, k, v, tbl, tbr).
  forward.
  destruct r as (rangel, rangeh).
  gather_SEP (atomic_shift _ _ _ _ _) (my_half g_del _ _) (my_half gb' _ _)
    (in_tree g gb') (in_tree g g_del).
  repeat rewrite sepcon_assoc. do 2 rewrite <- sepcon_assoc.
  replace_SEP 0 (|={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
          (λ M (_ : ()), tree_rep g g_root (delete x M) * emp) (λ _ : (), Q) *
                   EX rangedell, EX rangedelh: _,
        !!(range_incl (rangel, rangeh) (rangedell, rangedelh) = true /\
             range_incl rangeb (rangedell, rangedelh) = true /\ x < k) &&
      my_half g_del gsh ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))) *
          my_half gb' gsh1 ((rangedell, Finite_Integer k), Some (Some (x, vx, ga, gbl))) *
          (in_tree g gb' * in_tree g g_del)).
  {
    go_lower.
    rewrite !sepcon_assoc.
    eapply atomic_rollback_fupd.
    - intros.
      iIntros "((g_del & (gb & (in_gb & in_gdel))) & tree_rep)".
      iPoseProof ((ghost_tree_pushdown_left _ _ _ g_del ga gb')
                   with "[$tree_rep $in_gb $in_gdel]") as (n1 n2 o) "[Ha Hb]".
      iDestruct (public_sub with "[$g_del $Ha]") as %[? J]; inv J.
      instantiate (1 := vx). instantiate (1 := x).
      iPoseProof ("Hb" with "[% //]") as (o3) "[Hpubb Hb]".
      iPoseProof (bi.and_elim_r with "Hb") as "Hb".
      iSpecialize ("Hb" $! gbl gbr k v).
      logic_to_iris.
      iDestruct (public_sub with "[$g_del $Ha]") as %[? J1].
      iDestruct (public_sub with "[$gb $Hpubb]") as %[Hincl J2].
      iDestruct "Ha" as "[Hmya Ha]".
      iPoseProof (public_part_update(P := node_ghost) _ _ _ _ (n1, n2, Some (Some (k, v, gb', gbr)))
                    (n1, n2, Some (Some (k, v, gb', gbr)))
                   with "[$g_del $Ha]") as "[_ >[Hmyga Hpubga]]".
      { intros. destruct H13. split. split; auto; simpl.
        hnf in H13; hnf.
        symmetry; rewrite puretree.merge_comm; eapply merge_again.
        symmetry; rewrite puretree.merge_comm; eauto.
        simpl in *.
        inversion H14.
        apply sepalg.join_unit2. apply psepalg.None_unit. reflexivity.
        subst. inversion H18.
        intros; auto.
      }
      iPoseProof (public_update _ _ _ (n1, Finite_Integer k, Some (Some (x, vx, ga, gbl)))
                     with "[$gb $Hpubb]") as ">(Hmygb & Hpubgb)".
      inv J2.
      assert (key_in_range x (n1, n2) = true).
      { eapply key_in_range_incl; eauto. }
      assert (x < k).
      { eapply key_in_range_incl in Hincl; [|eauto].
        apply andb_prop in Hincl as []; simpl in *; lia.
      }
      iDestruct ("Hb" with "[$Hpubgb $Hmya $Hpubga]") as ">(($ & Hgdel) & Hgb)".
      { iPureIntro; repeat (split; auto). simpl; lia. }
      iExists n1, n2; iFrame.
      iPureIntro; repeat (split; auto).
      eapply range_incl_trans; try eassumption.
      apply (key_in_range_r _ (_, _)); auto.
   }
   match goal with |-context[|={⊤}=> ?P] => viewshift_SEP 0 P by entailer! end.
   Intros rangedell rangedelh.
   gather_SEP (lock_inv _ lockb' (node_lock_inv gsh1 g tb' gb' lockb')) (self_part _ lockb').
   unfold node_lock_inv at 1.
   sep_apply self_part_eq.
   apply readable_not_bot.
   apply readable_gsh2.
   unfold ltree at 1.
   unfold ltree at 2.
   Intros.
   forward_call release_self (gsh2, lockp', node_lock_inv_pred gsh g p' g_del (ptr_of lockp')).
   {
     unfold node_lock_inv_pred at 4.
     unfold sync_inv.
     Exists ((rangedell, rangedelh), Some (Some (k, v, gb', gbr))).
     rewrite node_rep_def; simpl. Exists tbv; cancel.
     unfold tree_rep_R.
     rewrite -> if_false; auto.
     Exists gb' gbr k v tb' tbr lockb' ltbr; cancel.
     unfold node_lock_inv. cancel.
     unfold ltree at 1.
     do 2 rewrite sepcon_andp_prop'.
     apply andp_right.
     {
       apply prop_right.
       repeat (split; auto).
       eapply key_in_range_incl; eauto.
     }
     {
       cancel. eapply derives_trans.
       2: { apply sepcon_derives; [apply now_later| apply derives_refl]. }
       entailer !.
     }
   }
   Exists tb' lockb' tbl ltbl gbl gb' (rangedell, Finite_Integer k) gsh1; entailer!.
   { eapply key_in_range_incl in H1; [|eauto].
     unfold key_in_range in *; apply andb_prop in H1 as [-> _]; simpl; lia.
   }
   unfold ltree.
   entailer !.
   apply derives_refl.
Qed.
