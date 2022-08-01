Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template.
Require Import bst.bst_template_lib.
Require Import bst.verif_bst_template.
Require Import VST.floyd.library.
Import FashNotation.

(* insertOp spec *)
Definition insertOp_spec :=
  DECLARE _insertOp
  WITH b: val, sh: share, x: Z, v: val,
              p : val, tp: val,
              gv: globals
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP ( writable_share sh;
       and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
         is_pointer_or_null v )
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP  (mem_mgr gv;
                data_at sh (t_struct_pn) (p, p) b;
                field_at Ews t_struct_tree_t (DOT _t) tp p)
  POST[ tvoid ]
  EX (pnt p1' p2' : val) (lock1 lock2 : val),
  PROP (pnt <> nullval)
        LOCAL ()
        SEP (mem_mgr gv;
             data_at sh t_struct_pn (p, p) b;
             field_at Ews t_struct_tree_t (DOT _t) pnt p;
             malloc_token Ews t_struct_tree pnt;
             malloc_token Ews t_struct_tree_t p1';
             malloc_token Ews t_struct_tree_t p2';
             atomic_int_at Ews (vint 0) lock1;
             atomic_int_at Ews (vint 0) lock2;
             data_at Ews t_struct_tree (vint x, (v, (p1', p2'))) pnt;
             data_at Ews t_struct_tree_t (Vlong (Int64.repr (Int.signed (Int.repr 0))), lock1) p1';
             data_at Ews t_struct_tree_t (Vlong (Int64.repr (Int.signed (Int.repr 0))), lock2) p2').

(* insert spec *)
Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val *  share * lock_handle * Z * val * globals * gname * gname))
  OBJ M INVS ∅
  WITH  b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_tree_t), tint, tptr tvoid ]
          PROP (writable_share sh; and (Z.le Int.min_signed x)(Z.le x Int.max_signed);
          is_pointer_or_null v )
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root (<[x:=v]>M)).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; (*free_atomic_spec; *)
     surely_malloc_spec; traverse_spec; insertOp_spec; insert_spec; findnext_spec]).

(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  change emp with seplog.emp.
  Intros.
  Intros.
  forward_call (t_struct_tree_t, gv).
  Intros p1'.
  forward_call (t_struct_tree_t, gv).
  Intros p2'.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer!.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer!.
  forward_call (gv).
  Intros lock1.
  forward.
  sep_apply atomic_int_isptr.
  Intros.
  forward_call release_nonatomic (lock1).
  forward_call (gv).
  Intros lock2.
  forward.
  Intros.
  forward_call release_nonatomic (lock2).
  (* make lock invariant *)
  forward_call (t_struct_tree, gv).
  Intros pnt.
  forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward.
  Exists pnt p1' p2' lock1 lock2.
  entailer !.
Qed.

(* Proving insert function satisfies spec *)
Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
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
    (* traverse(pn, x, value) *)
    forward_call (nb, np, sh , lock, x, v, gv, g, g_root, Q1).
    {
      unfold pn_rep_1, node_lock_inv', node_lock_inv.
      Exists (default_val t_struct_pn).1.
      sep_apply self_part_eq. apply readable_not_bot, readable_lsh2.
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
    destruct pt as (fl & (p1 & (tp & (lock_in & (gsh & (g_in & (x0 & r))))))).
    simpl in H2, H3.
    destruct fl.
    simpl.
    - destruct H3.
      forward_if (PROP ( )
                 LOCAL (temp _t'2 Vtrue; temp _t'8 (ptr_of lock); temp _t'7 np; temp _t'9 np;
                        temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x); temp _value v)
                 SEP (|={⊤}=> (|={⊤}=> Q * mem_mgr gv *
                      EX pt : bool * (val * (val * (lock_handle * (share * (gname * node_info))))),
                      !! (pt.1 = true  /\ pt.2.2.1 <> nullval) && seplog.emp *
                         (node_lock_inv_new pt.2.2.2.2.1 g pt.2.1
                           pt.2.2.2.2.2.1 pt.2.2.2.1 pt.2.2.1 pt.2.2.2.2.2.2 *
                         data_at Ews t_struct_pn (pt.2.1, pt.2.1) nb *
                         my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None) *
                         data_at sh (tptr t_struct_tree_t) np b *
                         field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np *
                         lock_inv sh lock (node_lock_inv (Share.split gsh1).1 g np g_root lock) *
                         malloc_token Ews t_struct_pn nb)))); try contradiction.
      + (* insertOp(pn, x, value) *)
        unfold Q1.
        Intros.
        simpl.
        change emp with seplog.emp.
        forward_call(nb, Ews, x, v, p1, tp, gv).
        { unfold node_lock_inv_new. rewrite H4; cancel. }
        Intros pt.
        destruct x0.
        subst r.
        gather_SEP AS (my_half g_in _  _)  (in_tree g  _).
        replace_SEP 0 (
            (|={⊤}=> Q * (EX g1 g2:gname, EX n1 n2:number,
                              (!!(key_in_range x (n1,n2) = true) &&
                                 my_half g_in gsh (n1, n2, Some (Some(x,v,g1,g2))) *
                                 in_tree g g_in *
                                 my_half g1 gsh1 (n1, Finite_Integer x, Some (@None ghost_info)) *
                                 my_half g2 gsh1 (Finite_Integer x, n2, Some (@None ghost_info)) *
                                 in_tree g g1 * in_tree g g2)))).
        {
          go_lower.
          eapply sync_commit_gen1.
          intros.
          iIntros "[H1 H2]".
          iModIntro.
          iPoseProof (tree_rep_insert with "[$H1 $H2]") as "Hadd".
          iDestruct "Hadd" as (r o0) "([Hmy H1] & H2)".
          iExists (r, Some o0). iFrame. iDestruct "H2" as "[[Hnew _] _]".
          iIntros "H"; iDestruct "H" as %Hsub.
          iMod "Hnew".
          iDestruct "Hnew" as (g1 g2) "H".
          iModIntro.
          iExists (r, Some (Some(x, v, g1, g2))).
          iExists (r, Some (Some (x, v, g1, g2))).
          apply node_info_incl' in Hsub as [? Heq]. simpl snd in *. inv Heq.
          logic_to_iris. iSplit.
          {
            iPureIntro.
            intros ? Hincl.
            destruct b0 as ((n3, n4), i).
            hnf.
            simpl.
            destruct (range_incl_join _ _ _ Hincl).
            simpl in *; subst. split; [|reflexivity].
            split.
            { symmetry; rewrite puretree.merge_comm; apply merge_range_incl'; auto. }
            destruct Hincl as [_ Hincl]; simpl in Hincl.
            inv Hincl; try constructor.
            inv H12.
          }
          iIntros "(H1 & H2)".
          instantiate (1 := x).
          instantiate (1 := v).
          iSpecialize ("H" with "[$H2 $Hmy]").
          iSplit; auto.
          {
            iPureIntro.
            split; auto.
            eapply key_in_range_incl; eassumption.
          }
          iDestruct "H" as "(((((? & ?) & ?) & ?) & ?) & ?)".
          iModIntro. rewrite exp_sepcon1; iExists tt.
          rewrite !exp_sepcon2; iExists g1.
          rewrite !exp_sepcon2; iExists g2.
          rewrite !exp_sepcon2; iExists r.1.
          rewrite !exp_sepcon2; iExists r.2; destruct r; iFrame.
          iPureIntro; split; auto.
          eapply key_in_range_incl; eassumption.
        }
        go_lower.
        rewrite -> prop_true_andp; auto.
        destruct pt as ((((pnt & p1') & p2') & lock1) & lock2).
        simpl.
        unfold_data_at (data_at _ _ _ p1').
        unfold_data_at (data_at _ _ _ p2').
        assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer !.
        assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer !.
        setoid_rewrite <- field_at_share_join with (p:= p1') at 2 ; eauto.
        setoid_rewrite <- field_at_share_join with (p:= p2') at 2 ; eauto.
        unfold tree_rep_R.
        rewrite -> if_true; auto.
        eapply derives_trans.
        apply fupd_frame_r.
        apply fupd_mono.
        (* do Iris here to have pieces of thing we need *)
        iIntros "[[H1 H2] H2x]".
        iDestruct "H2" as (g1 g2 n1 n2) "((((((%H2y & H3) & H4) & H5) & H6) & H7) & H8)".
        iDestruct "H2x" as "(G1 & (G2 & (G3 & (G4 &
                (G5 & (G6 & (G7 & (G8 & (G9 & (G10 &
                (G11 & (G12 & (_ & (G14 & (G15 &
                (G16 & (G17 & (G18 & (G19 & G20)))))))))))))))))))".
        iDestruct "G10" as "(G10x & G10y & G10z)".
        iDestruct "G11" as "(G11x & G11y & G11z)".
        iAssert (node_lock_inv_pred gsh1 g p1' g1 lock1) with "[G10x G10z G5 H5 H7]" as "HRLock1".
        {
          unfold node_lock_inv_pred, sync_inv; auto.
          iFrame.
          iExists (n1, Finite_Integer x, Some None).
          rewrite node_rep_def.
          iFrame.
          iExists nullval.
          unfold tree_rep_R.
          rewrite -> if_true; auto.
        }
        iAssert (node_lock_inv_pred gsh1 g p2' g2 lock2) with "[G11x G11z G6 H6 H8]" as "HRLock2".
        {
          unfold node_lock_inv_pred, sync_inv; auto.
          iFrame.
          iExists (Finite_Integer x, n2, Some None).
          rewrite node_rep_def.
          iFrame.
          iExists nullval.
          unfold tree_rep_R.
          rewrite -> if_true; auto.
        }
        iAssert (|={⊤}=>
                   (EX plock1, !!(ptr_of plock1 = lock1 /\ name_of plock1 = nroot .@ "Nlock1") &&
                              lock_inv lsh1 plock1 (node_lock_inv gsh1 g p1' g1 plock1) ∗
                        EX plock2, !!(ptr_of plock2 = lock2 /\ name_of plock2 = nroot .@ "Nlock2") &&
                              lock_inv lsh1 plock2 (node_lock_inv gsh1 g p2' g2 plock2)))
          with "[G7 G8 HRLock1 HRLock2]" as "HRL".
        {
          Intros. iVST.
          rewrite <- 2sepcon_assoc.
          eapply derives_trans
            with (Q := |={⊤}=>(EX plock1 : lock_handle,
                                 !! (ptr_of plock1 = lock1 ∧ name_of plock1 = nroot.@"Nlock1") &&
                                   lock_inv lsh1 plock1 (node_lock_inv gsh1 g p1' g1 plock1)) *
                               (EX plock2 : lock_handle,
                                  !! (ptr_of plock2 = lock2 ∧ name_of plock2 = nroot.@"Nlock2") &&
                                     lock_inv lsh1 plock2 (node_lock_inv gsh1 g p2' g2 plock2))).
          iIntros "(((H1x & H1y) & H2) & H3)".
          iSplitL "H1x H2".
          Intros. iVST.
          unfold node_lock_inv.
          eapply derives_trans.
          eapply make_lock_inv_0_self with (sh1 := lsh1) (sh2 := lsh2) (N := nroot .@ "Nlock1").
          apply readable_not_bot, readable_lsh1.
          eapply lsh1_lsh2_join.
          eapply derives_trans, fupd_mono with
          (P := EX h : lock_handle, !! (ptr_of h = lock1 ∧ name_of h = nroot.@"Nlock1") &&
                                      lock_inv lsh1 h (node_lock_inv_pred gsh1 g p1' g1 lock1 *
                                                         self_part lsh2 h)).
          entailer !.
          iIntros  "H".
          iDestruct "H" as (l1) "H".
          iExists l1.
          Intros. iVST.
          rewrite pull_left_special0.
          entailer !.
          Intros. iVST.
          eapply derives_trans.
          apply make_lock_inv_0_self with (sh1 := lsh1) (sh2 := lsh2) (N := nroot .@ "Nlock2").
          apply readable_not_bot, readable_lsh1.
          eapply lsh1_lsh2_join.
          eapply derives_trans, fupd_mono
            with (P := EX h : lock_handle, !! (ptr_of h = lock2 ∧ name_of h = nroot.@"Nlock2") &&
                                      lock_inv lsh1 h (node_lock_inv_pred gsh1 g p2' g2 lock2 *
                                                         self_part lsh2 h)).
          entailer !.
          iIntros  "H".
          iDestruct "H" as (l2) "H".
          iExists l2.
          unfold node_lock_inv.
          Intros. iVST.
          rewrite pull_left_special0.
          entailer !.
          cancel.
        }
        unfold node_lock_inv_new.
        iFrame.
        iIntros. iVST.
        rewrite <- 10sepcon_comm; rewrite <- 10sepcon_assoc.
        iIntros "((H & H1) & H2)".
        iIntros. iVST.
        rewrite <- sepcon_assoc.
        rewrite -> sepcon_comm.
        iIntros "H1".
        iPoseProof (fupd_frame_r with "[$H1]") as "H1".
        iApply (fupd_mono with "H1").
        iIntros "((H1 & H2) & H3)".
        iDestruct "H1" as (plock1) "[%H1x H1y]".
        iDestruct "H2" as (plock2) "[%H2x H2y]".
        iExists (true, (p1, (pnt, (lock_in, (gsh, (g_in, (n1, n2, Some (Some (x, v, g1, g2))))))))).
        simpl.
        iDestruct "H3" as "((((((G2 & G3) & G4) & G5) & G6) & G7) & G8)".
        iDestruct "G2" as "((((K1 & K2) & K3) & K4) & K5)".
        iSplit; try done.
        iFrame.
        unfold tree_rep_R.
        simpl in H6.
        rewrite -> if_false; auto.
        iExists g1, g2, x, v, p1', p2', plock1, plock2.
        unfold ltree.
        iFrame.
        Intros. iVST.
        assert_PROP (is_pointer_or_null p1') by entailer !.
        assert_PROP (is_pointer_or_null p2') by entailer !.
        entailer !.
        iIntros "H".
        iApply bi.later_sep_1.
        iModIntro.
        Intros. iVST.
        destruct H1x, H2x.
        rewrite H4.
        rewrite H16.
        cancel.
        repeat split; auto.
      + repeat (match goal with |-context[|={⊤}=> ?P] => viewshift_SEP 0 P by entailer! end).
        change emp with seplog.emp.
        Intros pt.
        destruct pt as (fl2 & (p2 & (tp2 & (lock_in2 & (gsh2 & (g_in2 & r2)))))).
        unfold node_lock_inv_new.
        simpl.
        Intros.
        forward.
        forward.
        (* _release2(_t'4) *)
        unfold tree_rep_R.
        rewrite if_false; auto.
        Intros g1 g2 x1 v1 p1' p2' l1 l2.
        assert_PROP (tp2 <> nullval) by entailer !.
        (*  (_release2(_t'4); *)
        forward_call release_self (lsh2, lock_in2,
                    node_lock_inv_pred gsh2 g p2 g_in2 (ptr_of lock_in2)).
        {
          unfold node_lock_inv.
          cancel.
          unfold node_lock_inv_pred at 2, sync_inv.
          destruct r2 as [p o].
          simpl in H7, H10.
          destruct p as [n1 n2].
          Exists (n1, n2, Some (Some(x1, v1, g1, g2))).
          rewrite node_rep_def.
          Exists tp2.
          unfold tree_rep_R.
          assert_PROP (tp2 <> nullval) by entailer!.
          rewrite -> if_false by auto.
          Exists g1 g2 x1 v1 p1' p2' l1 l2.
          unfold ltree.
          entailer !.
          rewrite <- later_sepcon.
          eapply derives_trans;
              [|apply sepcon_derives, derives_refl; apply now_later].
          cancel.
        }
        forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        unfold nodebox_rep.
        entailer !.
        Exists np.
        unfold ltree, node_lock_inv.
        entailer !.
      - (* (_t'6->_value) = _value;) *)
        forward_if (
            PROP ( )
              LOCAL (temp _t'2 Vfalse; temp _t'8 (ptr_of lock); temp _t'7 np; temp _t'9 np;
                      temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x); temp _value v)
              SEP (Q1 (false, (p1, (tp, (lock_in, (gsh, (g_in, (x0, r)))))));
                    mem_mgr gv; seplog.emp;
                    field_at Ews t_struct_tree_t (DOT _t) tp p1 *
                      malloc_token Ews t_struct_tree_t p1 * in_tree g g_in *
                      (EX (ga gb : gname) (x1 : Z) (v0 pa pb : val) (locka lockb : lock_handle),
                        !! ((x0, r).2 = Some (Some (x1, v0, ga, gb))
                            ∧ (Int.min_signed ≤ x1 ≤ Int.max_signed)%Z
                            ∧ is_pointer_or_null pa
                            ∧ is_pointer_or_null pb ∧ tc_val (tptr Tvoid) v0 ∧
                              key_in_range x1 (x0, r).1 = true) &&
                          data_at Ews t_struct_tree (vint x1, (v, (pa, pb))) tp *
                          malloc_token Ews t_struct_tree tp *
                          |> ltree g ga lsh1 gsh1 pa locka *
                          |> ltree g gb lsh1 gsh1 pb lockb) *
                      my_half g_in gsh (x0, r) *
                      field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p1 *
                      |> lock_inv lsh2 lock_in (node_lock_inv gsh g p1 g_in lock_in);
                    data_at Ews t_struct_pn (p1, p1) nb;
                    my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                    data_at sh (tptr t_struct_tree_t) np b;
                    field_at sh t_struct_tree_t (DOT _lock) (ptr_of lock) np;
                    lock_inv sh lock (node_lock_inv (Share.split gsh1).1 g np g_root lock);
                    malloc_token Ews t_struct_pn nb)).
        + destruct H3 as ( ?  & v2 & g21 & g22 & ?).
          unfold node_lock_inv_new, tree_rep_R.
          rewrite -> if_false; auto.
          simpl in *.
          Intros g1 g2 x1 v1 p1' p2' l1 l2.
          forward.
          forward.
          forward.
          Exists g1 g2 x1 v1 p1' p2' l1 l2.
          entailer !.
        + (* contradiction, since  Int.one = Int.zero *)
          pose proof Int.one_not_zero; contradiction.
        + autorewrite with norm.
          destruct H3 as ( ? & v2 & g21 & g22 & ?).
          Intros g1 g2 x1 v1 p1' p2' l1 l2.
          forward.
          forward.
          simpl in H5. rewrite H5 in H4. injection H4.
          intros. subst x1. subst v2. subst g21. subst g22.
          unfold Q1.
          simpl.
          gather_SEP AS (my_half g_in _ _) (in_tree g  _).
          viewshift_SEP 0 (Q *
                    (EX n1 n2 : number,
                      !!(key_in_range x (n1, n2) = true)
                      && my_half g_in gsh (n1, n2, Some (Some(x, v, g1, g2))) * in_tree g g_in)).
          {
            go_lower.
            eapply sync_commit_gen1.
            intros. iIntros "H".
            iDestruct "H" as "[H1 H2]".
            iModIntro.
            iPoseProof (tree_rep_insert x1 g g_root g_in with "[H1 H2]") as "Hadd".
            iSplitL "H2"; auto.
            iDestruct "Hadd" as ((n1, n2) o0) "([Hmy H1] & H2)".
            iExists (n1,n2,Some o0).
            iSplitL "H1". iFrame.
            iPoseProof (bi.and_elim_l with "H2") as "H3".
            iPoseProof (bi.and_elim_r with "H3") as "Hnew".
            iIntros "H". iDestruct "H" as %Hsub.
            iMod "Hnew".
            iSpecialize ("Hnew" $! g1 g2).
            iModIntro.
            iExists (n1, n2, Some (Some (x, v, g1, g2))).
            apply node_info_incl' in Hsub as [? Heq].
            rewrite H5 in Heq.
            inv Heq.
            iExists (n1, n2, Some (Some (x, v, g1, g2))).
            logic_to_iris.
            instantiate (1 := v).
            instantiate (1 := x).
            iSplit.
            {
              iPureIntro. intros ? Hincl.
              hnf. simpl. destruct (range_incl_join _ _ _ Hincl).
              simpl in *; subst. split; [|reflexivity].
              split.
              { symmetry.
                rewrite puretree.merge_comm; apply merge_range_incl'; auto.
              }
              destruct b0, Hincl as [_ Hincl]; simpl in Hincl. inv Hincl; try constructor.
              simpl. inv H16.
            }
            iIntros "(H1 & H2)".
            iSpecialize ("Hnew" $! v1 with "[$H2 $Hmy]").
            iSplit; auto.
            {
              iPureIntro.
              split; [reflexivity|].
              eapply key_in_range_incl; eassumption.
            }
            iModIntro.
            iDestruct "Hnew" as "($ & H3)".
            iSplit; [iExists tt; auto|].
            iExists n1, n2; iFrame.
            iSplit; last done; iPureIntro.
            eapply key_in_range_incl; eassumption.
          }
          Intros n1 n2.
          unfold ltree.
          Intros.
          forward_call release_self (lsh2, lock_in,
                      node_lock_inv_pred gsh g p1 g_in (ptr_of lock_in)).
          {
            unfold node_lock_inv.
            cancel.
            unfold node_lock_inv_pred at 4, sync_inv.
            Exists (n1, n2, Some(Some (x, v, g1, g2))).
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
        unfold nodebox_rep, ltree, node_lock_inv.
        entailer !.
        Exists np.
        entailer !.
   }
Qed.
