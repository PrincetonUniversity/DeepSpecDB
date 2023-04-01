Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.puretree.
Require Import bst.bst_template_giveup.
Require Import bst.giveup_lib.
Require Import bst.giveup_traverse.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

(* Write insert_spec following the template style.
We need to write some specs of helper functions: insertOp, traverse and findnext
1) insert_spec:
           ∀ t. <bst_ref p | bst t>  insert2 (treebox t, int x, void *value)
                <t'. bst_ref p | bst t' ∧ insert t k v = t' >
2) insertOp_spec:
          {N /\  x \in range} insertOp(pn *pn, int x, void *value)
          {t'. N ∧ t' = (<[x:=k]> t) }
3) traverse_spec:
          < ...  | bst t> traverse(pn *pn, int x, void *value)
          <v. bst t /\ lock_inv >
4) findnext_spec:
          {x \in range  /\ ...} findNext(pn *pn, int x, void *value)
          {v. ((v = 1 /\ ....) \/ (v = 0 /\  ...)) /\  ... } *)

(* insert spec *)
Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * globals * gname * gname))
  OBJ M INVS ∅
  WITH b, sh, lock, x, gv, g, g_root
  PRE [ tptr (tptr t_struct_tree_t), tint ]
    PROP (writable_share sh; and (Z.le Int.min_signed x) (Z.le x Int.max_signed))
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST[ tptr tvoid ]
  EX ret: val,
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
    (!! (ret = match M !! x with Some v => v | None => nullval end) && tree_rep g g_root M).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; inrange_spec; lookup_spec;
     traverse_spec; findnext_spec; treebox_new_spec]).

(* Proving lookup function satisfies spec *)
Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward_call (t_struct_pn, gv).
  Intros nb.
  Intros lsh.
  forward.
  forward.
  sep_apply in_tree_duplicate.
  set (AS := atomic_shift _ _ _ _ _).
  set Q1:= fun (b : ( bool * (val * (share * (gname * node_info))))%type) =>
              if b.1 then AS else AS.
  (* traverse(pn, x, value) *)
  forward_call (nb, np, lock, x, nullval, gv, g, g_root, Q1).
  {
    Exists Vundef. entailer !.
    iIntros "(((H1 & H2) & H3) & H4)". iCombine "H2 H1 H3 H4" as "H".
    iVST.
    apply sepcon_derives; [| cancel_frame].
    iIntros "AU".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "[Hm HClose]".
    iModIntro. iExists _. iFrame.
    iSplit; iFrame.
    iIntros "H1".
    iSpecialize ("HClose" with "H1"). auto.
    iDestruct "HClose" as "[HClose _]".
    iIntros (pt) "[H _]".
    iMod ("HClose" with "H") as "H".
    iModIntro.
    unfold Q1.
    destruct (decide (pt.1 = true)). { rewrite e; iFrame. }
    { apply not_true_is_false in n; rewrite n; iFrame. }
  }
  Intros pt.
  destruct pt as (fl & (p & (gsh & (g_in & r)))).
  simpl in H5.
  destruct fl.
  destruct H5 as (HGh & HP).
  - unfold Q1.
    forward_if(
        PROP ( )
          LOCAL (temp _v nullval; temp _t'2 Vtrue; temp _t'7 np; temp _pn__2 nb; gvars gv;
            temp _t b; temp _x (vint x))
          SEP (AS * mem_mgr gv * 
               data_at Ews t_struct_pn (p, p) nb * in_tree g g_in p r.1.1.2 *
               in_tree g g_root np lock * malloc_token Ews t_struct_pn nb *
               data_at sh (tptr t_struct_tree_t) np b *
               field_at lsh t_struct_tree_t (DOT _lock) lock np * 
               node_lock_inv_pred g p g_in r)).
    + pose proof (Int.one_not_zero); easy.
    + simpl. forward. entailer !.
    + unfold node_lock_inv_pred, node_rep, tree_rep_R.
      rewrite -> if_true by auto.
      Intros.
      forward.
      (* alloc a pointer of lock for pointer p*)
      gather_SEP AS (in_tree g g_in p _).
      viewshift_SEP 0 (AS * (in_tree g g_in p r.1.1.2) * (EX lsh, !!(readable_share lsh) &&
                       field_at lsh t_struct_tree_t (DOT _lock) r.1.1.2 p)).
      { go_lower. apply lock_alloc. }
      Intros lsh1.
      forward.
      forward_call (r.1.1.2, Q nullval).
      {
        iIntros "(((((((((((((((AU & H1) & H2) & H3) & H4) & H5) & H6) & H7) & H8) & H9) & G1) & G2) & G3) & G4) & G5) & _)".
        iCombine "AU H1 H2" as "HH1".
        iCombine "G1 G2 H9 G3 G4 G5" as "HH2".
        iCombine "HH1 HH2" as "HH3".
        iVST.
        rewrite <- 5sepcon_assoc; rewrite <- sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & (#H1 & H2)) & (H3 & (H4 & (H5 & (H6 & (H7 & _))))))"
        ; iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iDestruct "Hm" as (tg p1 lk1) "((%K3 & K4) & K5)".
        destruct K3 as (K31 & K32 & K33 & K34).
        iPoseProof (node_exist_in_tree g (find_ghost_set tg g_root p1 lk1) p 
                         with "[H1 K5]") as "%Hy". 
        { iFrame "H1". iFrame. }
        iPoseProof (ghost_tree_rep_public_half_ramif _ _ _ _ _ _ (Neg_Infinity, Pos_Infinity)
                                                         with "[$K4]") as "GT"; try eauto.
        iDestruct "GT" as (r1 a) "((%GT1 & GT2) & GT3)".
        iPoseProof (public_agree g_in r (r1, Some a) with "[$GT2 $H5]") as "%Hx".
        iSpecialize ("GT3" with "GT2"). 
        iAssert (tree_rep g g_root m) with "[GT3 K5]" as "Hm".
        {
          iExists _, _, _. iFrame.
          iSplit. iPureIntro; try done. done.
        }
        iPoseProof (tree_rep_insert m g g_root g_in p r.1.1.2 x nullval nullval nullval nullval nullval nullval with "[$Hm $H1]") as "InvLock".
        iDestruct "InvLock" as (R O) "((K1 & K2) & K3)".
        iDestruct "K2" as (lsh2) "(% & (K2 & KInv))".
        iDestruct "KInv" as (bl) "(KAt & KInv)".
        destruct bl.
        ++ iExists (). iFrame "KAt".
           iSplit.
           {
             iIntros "H".
             iFrame.
             iAssert (ltree g g_in p r.1.1.2 (node_lock_inv_pred g p g_in (R, Some O)))
               with "[H K2]" as "HInv".
             { iExists _. iSplit; try done. iFrame "K2". iExists true. iFrame. }
             iSpecialize ("K3" with "[$HInv $K1]").
             iDestruct "K3" as "(K3 & _)".
             iSpecialize ("HClose" with "K3").
             iFrame.
           }
           iIntros (_) "(H & _)".
           iDestruct "K3" as "[_ K3]".
           iPoseProof (public_agree g_in _ _ with "[$K1 $H5]") as "%Hz".
           destruct r.
           inversion Hz; subst.
           (* join lsh1 with lsh2 = Lsh *)
           destruct H10 as (Hf & Hrs).
           iPoseProof (lock_join with "[$H2 $K2]") as "K2"; try iSplit; auto.
           iDestruct "K2" as (Lsh) "(% & K2)".
           (* done pushing back pointer of lock into ltree *)
           iAssert (ltree g g_in p R.1.2 (node_lock_inv_pred g p g_in (R, Some O)))
             with "[H3 H4 H5 H6 H7 K2 H]" as "LT".
           { 
             iExists Lsh. iFrame. iSplit; try done.
             iExists false; iFrame "H1 H H3 H4 H5 H6 H7".
             iSplit. try done. 
             unfold tree_rep_R. rewrite -> if_true; auto.
           }
           simpl.
            unfold ltree.
            iSpecialize ("K3" with "[$K1 $LT]").
            iDestruct "K3" as "(K3 & _)".
            iDestruct "HClose" as "(_ & HClose)".
            iSpecialize ("HClose" $! nullval).
            iApply "HClose".
            iFrame.
            iSplit.
            iPureIntro.
            simpl in K34.
            inv Hx; subst.
            erewrite -> (range_info_not_in_gmap _ _ r1.1 r1.2 (Neg_Infinity, Pos_Infinity)); eauto.
            simpl in HGh.
            rewrite HGh in GT1.
            destruct r1; try eauto. done.
         ++ (* contradiction *)
           unfold node_lock_inv_pred at 1.
           iDestruct "KInv" as "(? & KInv)".
           unfold node_rep.
           iDestruct "KInv" as "((((((? & KInv) & ?) & ?) & ?) & ?) & ?)".
           iPoseProof (field_at_conflict Ews t_struct_tree_t (DOT _t) p
                      with "[$H3 $KInv]") as "HF"; eauto; simpl; lia.
      }
     (* free *)
     forward_call (t_struct_pn, nb, gv).
     { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto; cancel. }
     forward.
     unfold nodebox_rep.
     Exists nullval np lsh. entailer !.
  - simpl in H2.
    unfold Q1.
    destruct H5 as ( ?  & v2 & g21 & g22 & ?).
    simpl.
    forward_if (
        PROP ( )
     LOCAL (temp _v v2;temp _t'2 Vfalse; temp _t'7 np; temp _pn__2 nb; gvars gv; temp _t b; 
     temp _x (vint x))
     SEP (AS; mem_mgr gv; seplog.emp; data_at Ews t_struct_pn (p, p) nb; in_tree g g_in p r.1.1.2;
     my_half g_in Tsh r *
       (!! (repable_signed (number2Z r.1.2.1)
          ∧ repable_signed (number2Z r.1.2.2) ∧ is_pointer_or_null r.1.1.2) &&
          field_at Ews t_struct_tree_t (DOT _t) r.1.1.1 p * 
     field_at Ews t_struct_tree_t (DOT _min) (vint (number2Z r.1.2.1)) p *
     field_at Ews t_struct_tree_t (DOT _max) (vint (number2Z r.1.2.2)) p *
     malloc_token Ews t_struct_tree_t p * in_tree g g_in p r.1.1.2 *
     (EX (ga gb : gname) (x0 : Z) (v0 pa pb locka lockb : val),
       !! (r.2 = Some (Some (x0, v0, ga, gb))
           ∧ Int.min_signed ≤ x0 ≤ Int.max_signed
             ∧ is_pointer_or_null pa
               ∧ is_pointer_or_null locka
                 ∧ is_pointer_or_null pb
                   ∧ is_pointer_or_null lockb ∧ tc_val (tptr Tvoid) v0 ∧ key_in_range x0 r.1.2 = true) &&
     data_at Ews t_struct_tree (vint x0, (v0, (pa, pb))) r.1.1.1 *
     malloc_token Ews t_struct_tree r.1.1.1 * in_tree g ga pa locka * in_tree g gb pb lockb *
     in_tree g g_root np lock * malloc_token Ews t_struct_pn nb * data_at sh (tptr t_struct_tree_t) np b* 
     field_at lsh t_struct_tree_t (DOT _lock) lock np)))).
    + unfold node_lock_inv_pred, node_rep, tree_rep_R.
      rewrite -> if_false; auto.
      simpl in H1, H2, H3, H4. simpl.
      Intros g1' g2' x1 v1' p1 p2 lock1 lock2.
      forward. forward. forward.
      Exists g1' g2' x1 v1' p1 p2 lock1 lock2.
      entailer !. apply derives_refl.
    + pose proof Int.one_not_zero; easy.
    + Intros g1 g2 x1 v1 p1 p2 lock1 lock2.
      forward.
      gather_SEP AS (in_tree g g_in p _).
      viewshift_SEP 0 (AS * (in_tree g g_in p r.1.1.2) * (EX lsh, !!(readable_share lsh) &&
                       field_at lsh t_struct_tree_t (DOT _lock) r.1.1.2 p)).
      { go_lower. apply lock_alloc. }
      Intros lsh1.
      forward.
      forward_call (r.1.1.2, Q v2).
      {
        iIntros "(((((((((((((((((((AU & H1) & H2) & H3) & _) & H4) & H5) & H6) & H7) & H8) & H9) & G1) & G2) & G3) & G4) & G5) & G6) & G7) & G8) & G9)".
        iCombine "AU H1 H2 H5 H6 H7 H8 H9 G2 G3 G4 G5" as "HH".
        iVST.
        rewrite <- 6sepcon_assoc; rewrite <- sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "(AU & (#HT & (H1 & (H2 & (H3 & (H4 & (H5 & (H6 & (H7 & (H8 & (#HT1 & #HT2)))))))))))"; iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iDestruct "Hm" as (tg pn lkn) "((%K3 & K4) & K5)".
        destruct K3 as (K31 & K32 & K33 & K34).
        iPoseProof (node_exist_in_tree g (find_ghost_set tg g_root pn lkn) p 
                         with "[K5]") as "%Hy". 
        { iFrame "HT". iFrame. }
        iPoseProof (ghost_tree_rep_public_half_ramif _ _ _ _ _ _ (Neg_Infinity, Pos_Infinity)
                                                         with "[$K4]") as "GT".
        { apply Hy. }
        iDestruct "GT" as (r1 a) "((%GT1 & GT2) & GT3)".
        iPoseProof (public_agree g_in r (r1, Some a) with "[$GT2 $H2]") as "%Hx".
        iSpecialize ("GT3" with "GT2"). 
        iAssert (tree_rep g g_root m) with "[GT3 K5]" as "Hm".
        {
          unfold tree_rep.
          iExists _, _, _. iFrame.
          iSplit. iPureIntro; try auto. done.
        }
        iPoseProof (tree_rep_insert m g g_root g_in p r.1.1.2 x v2 p1 p2 lock1 lock2 nullval with "[$Hm $HT]") as "InvLock".
        iDestruct "InvLock" as (R O) "((K1 & K2) & K3)".
        iDestruct "K2" as (lsh2) "(% & (K2 & KInv))".
        iDestruct "KInv" as (bl) "(KAt & KInv)".
        destruct bl.
        + iExists ().
          iFrame "KAt".
          iSplit.
          { iIntros "H". iFrame.
            iAssert (ltree g g_in p r.1.1.2 (node_lock_inv_pred g p g_in (R, Some O)))
              with "[H K2]" as "HInv".
            { iExists _; iSplit; iFrame; try done. iExists true; iFrame. }
            iSpecialize ("K3" with "[$HInv $K1]").
            iDestruct "K3" as "(K3 & _)".
            iSpecialize ("HClose" with "K3"); auto.
          }
          iIntros (_) "(H & _)".
          iDestruct "K3" as "[_ K3]".
          iDestruct "HClose" as "(_ & HClose)".
          iSpecialize ("HClose" $! v2).
          iApply "HClose".
          iPoseProof (public_agree g_in r (R, Some O) with "[$K1 $H2]") as "%Hz".
          destruct r.
          inversion Hz; subst.
          rewrite H6 in H10.
          inversion H10; subst x1 v2 g21 g22.
          destruct H15 as (Hf & Hrs).
          (* join lsh1 with lsh2 = Lsh *)
          iPoseProof (lock_join with "[$H1 $K2]") as "K2"; try iSplit; auto.
           iDestruct "K2" as (Lsh) "(% & K2)".
           (* done pushing back pointer of lock into ltree *)
           iAssert (ltree g g_in p (R, Some O).1.1.2 (node_lock_inv_pred g p g_in (R, Some O)) )
             with "[H2 H3 H4 H5 H6 H7 H8 K2 H]" as "LT".
           {
             iExists Lsh; iFrame. iSplit; try done.
             iExists false. iFrame "HT H H2 H3 H4 H5 H6". 
             iSplit; try done.
             unfold tree_rep_R.
             rewrite -> if_false; auto.
             iExists g1, g2, x, v1, p1, p2, lock1, lock2.
             iFrame "HT1 HT2 H7 H8".
             iPureIntro.
             repeat (split; auto).
           }
           iSpecialize ("K3" with "[$K1 $LT]").
           iDestruct "K3" as "(K3 & _)".
           iFrame.
           simpl.
           iPureIntro.
           simpl in K34.
           inversion Hx; subst.
           simpl in H6.
           rewrite H6 in GT1.
           rewrite (range_info_in_gmap x v1 g1 g2 tg r1 (Neg_Infinity, Pos_Infinity)); auto.
        + unfold node_lock_inv_pred at 1, node_rep.
          iDestruct "KInv" as "(? & KInv)".
          iDestruct "KInv" as "((((((? & KInv) & ?) & ?) & ?) & ?) & ?)".
          iPoseProof (field_at_conflict Ews t_struct_tree_t (DOT _t) p
                      with "[$H3 $KInv]") as "HF"; try easy; auto.
     }
     (* free *)
     forward_call (t_struct_pn, nb, gv).
     { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
     forward.
     unfold nodebox_rep, ltree.
     Exists v2 np lsh.
     entailer !.  by iIntros "_".
Qed.
