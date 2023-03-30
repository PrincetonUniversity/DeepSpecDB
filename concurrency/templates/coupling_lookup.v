Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template_coupling.
Require Import bst.coupling_lib.
Require Import bst.coupling_traverse.
Require Import VST.floyd.library.
Import FashNotation.

(* Specification of lookup function *)
Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * lock_handle * Z * globals * gname * gname))
         OBJ M INVS ∅
  WITH b, sh, lock, x, gv, g, g_root
  PRE [tptr (tptr t_struct_tree_t), tint]
    PROP (writable_share sh;
    and (Z.le Int.min_signed x)(Z.le x Int.max_signed))
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) |
  (tree_rep g g_root M)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!! (ret = match M !! x with Some v => v | None => nullval end) && tree_rep g g_root M).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; traverse_spec; findnext_spec; lookup_spec]).

(* Proving lookup function satisfies spec *)
Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
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
            LOCAL (temp _v nullval; temp _t'2 Vtrue; temp _t'8 (ptr_of lock);
                   temp _t'7 np; temp _t'9 np; temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x))
            SEP (Q1 (true, (p1, (tp, (lock_in, (gsh, (g_in, r)))))); mem_mgr gv; emp;
                 node_lock_inv_new gsh g p1 g_in lock_in tp r;
                 data_at Ews t_struct_pn (p1, p1) nb;
                 my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                 data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np;
                 lock_inv sh lock
                   (selflock (node_lock_inv_pred (Share.split gsh1).1 g np g_root (ptr_of lock))
                      gsh2 lock);
                 malloc_token Ews t_struct_pn nb)).
      + pose proof (Int.one_not_zero); easy.
      + Intros.
        forward.
        unfold node_lock_inv_new.
        entailer !.
      + rewrite H3.
        unfold node_lock_inv_new, tree_rep_R.
        rewrite -> if_true by auto.
        unfold Q1.
        simpl.
        Intros.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (EX y, Q y * (!! (y = nullval) && (in_tree g g_in * my_half g_in gsh r))).
        {
          go_lower.
          apply sync_commit_same.
          intro t.
          unfold tree_rep at 1.
          Intros tg.
          sep_apply node_exist_in_tree; Intros.
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H9).
          Intros r0.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists r0.
          unfold public_half'; cancel.
          apply imp_andp_adjoint.
          Intros.
          apply node_info_incl' in H11 as [].
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          simpl.
          simpl in H12.
          Exists nullval; simpl; entailer!.
          - destruct r as [range r2], r0 as [rg ?]; simpl in *; subst.
            rewrite -> range_info_not_in_gmap
              with (rn := rg)(r_root := (Neg_Infinity, Pos_Infinity)); auto.
            eapply key_in_range_incl; eauto.
          - unfold tree_rep. Exists tg. entailer!. iIntros "[[? H] ?]".
            iApply "H". iFrame. 
        }
        Intros y.
        subst y.
        (*  (_release2(_t'4); *)
        change emp with seplog.emp.
        forward.
        forward.
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
        forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        forward.
        unfold nodebox_rep, ltree.
        Exists nullval np.
        entailer !.
    - (* v = pn->p->t->value; *)
      unfold Q1.
      destruct H2 as ( ?  & v2 & g21 & g22 & ?).
      simpl.
      forward_if (
            PROP ( )
                 LOCAL (temp _v v2; temp _t'2 Vfalse; temp _t'8 (ptr_of lock); temp _t'7 np;
                        temp _t'9 np; temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x))
                 SEP (Q1 (false, (p1, (tp, (lock_in, (gsh, (g_in, r))))));
                    mem_mgr gv; seplog.emp;
                    field_at Ews t_struct_tree_t (DOT _t) tp p1 *
                      malloc_token Ews t_struct_tree_t p1 * in_tree g g_in *
                      (EX (ga gb : gname) (x1 : Z) (v0 pa pb : val) (locka lockb : lock_handle),
                        !! (r.2 = Some (Some (x1, v0, ga, gb))
                            ∧ (Int.min_signed ≤ x1 ≤ Int.max_signed)%Z
                            ∧ is_pointer_or_null pa
                            ∧ is_pointer_or_null pb ∧ tc_val (tptr Tvoid) v0 ∧
                              key_in_range x1 r.1 = true) &&
                          data_at Ews t_struct_tree (vint x1, (v0, (pa, pb))) tp *
                          malloc_token Ews t_struct_tree tp *
                          |> ltree g ga lsh1 gsh1 gsh1 pa locka *
                          |> ltree g gb lsh1 gsh1 gsh1 pb lockb) *
                      my_half g_in gsh r *
                      field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p1 *
                      |> lock_inv gsh2 lock_in (node_lock_inv gsh g p1 g_in lock_in);
                    data_at Ews t_struct_pn (p1, p1) nb;
                    my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                    data_at sh (tptr t_struct_tree_t) np b;
                    field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np;
                    lock_inv sh lock (node_lock_inv (Share.split gsh1).1 g np g_root lock);
                    malloc_token Ews t_struct_pn nb)); unfold node_lock_inv_new, tree_rep_R.
      + rewrite -> if_false; auto.
        Intros g1 g2 x1 v p1' p2' l1 l2.
        change emp with seplog.emp.
        forward.
        forward.
        forward.
        Exists g1 g2 x1 v p1' p2' l1 l2.
        unfold Q1.
        entailer !. auto.
      + pose proof Int.one_not_zero; contradiction.
      + Intros g1 g2 x1 v p1' p2' l1 l2.
        change emp with seplog.emp.
        forward.
        forward.
        simpl in H1, H3, H4, H5, H6, H7.
        rewrite H4 in H3.
        injection H3.
        intros. subst x1. subst v2. subst g21. subst g22.
        unfold Q1.
        simpl.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 ( EX y, Q y * (!!(y = v) && (in_tree g g_in * my_half g_in gsh r))).
        {
          go_lower.
          apply sync_commit_same.
          intro t.
          unfold tree_rep at 1.
          Intros tg.
          sep_apply node_exist_in_tree; Intros.
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H14).
          Intros r0.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists r0.
          unfold public_half'; cancel.
          apply imp_andp_adjoint.
          Intros.
          apply node_info_incl' in H16 as [].
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists v; entailer!.
          simpl. entailer !.
          - destruct r as [range r2], r0 as [range0 r0]. simpl in *; subst.
            erewrite range_info_in_gmap; eauto.
          - iIntros "[[[? H] ?] ?]".
            unfold tree_rep. iExists tg. iFrame; iSplit; auto.
            iApply "H"; iFrame.
        }
        Intros y.
        subst y.
        Intros.
        forward_call release_self (gsh2, lock_in,
                    node_lock_inv_pred gsh g p1 g_in (ptr_of lock_in)).
        {
          unfold node_lock_inv, node_lock_inv_pred at 4, sync_inv.
          Exists r.
          rewrite node_rep_def.
          Exists tp.
          unfold tree_rep_R, ltree.
          rewrite -> if_false by auto.
          Exists g1 g2 x v p1' p2' l1 l2.
          entailer !.
          rewrite <- later_sepcon;
            eapply derives_trans;
            [|apply sepcon_derives, derives_refl; apply now_later].
          cancel.
        }
        forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        forward.
        unfold nodebox_rep, ltree.
        Exists v np.
        entailer !.
  }
Qed.

