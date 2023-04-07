Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template_giveup.
Require Import bst.giveup_lib.
Require Import bst.giveup_traverse.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

(* Spec of insertOp function *)
Definition insertOp_spec :=
  DECLARE _insertOp
    WITH b: val, sh: share, x: Z, v: val, p: val, tp: val, min: Z, max: Z, gv: globals
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v )
  PARAMS (b; Vint (Int.repr x); v)
  GLOBALS (gv)
  SEP (mem_mgr gv;
       data_at sh (t_struct_pn) (p, p) b;
       field_at Ews t_struct_tree_t (DOT _t) tp p;
       field_at Ews t_struct_tree_t (DOT _min) (Vint (Int.repr min)) p;
       field_at Ews t_struct_tree_t (DOT _max) (Vint (Int.repr max)) p )
  POST[ tvoid ]
  EX (pnt p1' p2' : val) (lock1 lock2 : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       data_at sh t_struct_pn (p, p) b;
       field_at Ews t_struct_tree_t (DOT _t) pnt p;
       malloc_token Ews t_struct_tree pnt;
       malloc_token Ews t_struct_tree_t p1'; malloc_token Ews t_struct_tree_t p2';
       atomic_int_at Ews (vint 0) lock1; atomic_int_at Ews (vint 0) lock2;
       data_at Ews t_struct_tree (vint x, (v, (p1', p2'))) pnt;
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock2, (vint x, vint max))) p2';
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock1, (vint min, vint x))) p1';
       field_at Ews t_struct_tree_t (DOT _min) (vint min) p;
       field_at Ews t_struct_tree_t (DOT _max) (vint max) p).

(* insert spec *)
Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * val * globals * gname * gname))
  OBJ M INVS ∅
  WITH b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_tree_t), tint, tptr tvoid ]
    PROP (writable_share sh; and (Z.le Int.min_signed x) (Z.le x Int.max_signed); is_pointer_or_null v)
    PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root (<[x:=v]>M)).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec; traverse_spec; insert_spec; treebox_new_spec]).

(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
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
  forward. forward. forward. forward. forward. forward. forward. forward.
  Exists pnt p1' p2' lock1 lock2.
  entailer !.
Qed.

(* Proving insert function satisfies spec *)
Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
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
  forward_call (nb, np, lock, x, v, gv, g, g_root, Q1).
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
  simpl in H6.
  destruct fl.
  destruct H6 as (HGh & HP).
  - unfold Q1.
    forward_if(
        PROP ( )
        LOCAL (temp _t'2 Vtrue; temp _t'7 np; temp _pn__2 nb; gvars gv;
               temp _t b; temp _x (vint x); temp _value v)
        SEP (AS * mem_mgr gv * EX pt: (val * (val * (val * (val * val)))),
              !!(pt.1 <> nullval /\ (repable_signed (number2Z r.1.2.1)
          ∧ repable_signed (number2Z r.1.2.2) ∧ is_pointer_or_null r.1.1.2)) &&
          data_at Ews t_struct_pn (p, p) nb * in_tree g g_root np lock * 
          field_at Ews t_struct_tree_t (DOT _t) (pt.1) p * malloc_token Ews t_struct_tree pt.1 * 
          malloc_token Ews t_struct_tree_t pt.2.1 * malloc_token Ews t_struct_tree_t pt.2.2.1 * 
          atomic_int_at Ews (vint 0) pt.2.2.2.1 * atomic_int_at Ews (vint 0) pt.2.2.2.2 *
          data_at Ews t_struct_tree (vint x, (v, (pt.2.1, pt.2.2.1))) pt.1 * 
          data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (pt.2.2.2.2, (vint x, vint (number2Z r.1.2.2)))) pt.2.2.1 * 
          data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (pt.2.2.2.1, (vint (number2Z r.1.2.1), vint x))) pt.2.1 *
         field_at Ews t_struct_tree_t (DOT _min) (vint (number2Z r.1.2.1)) p *
         field_at Ews t_struct_tree_t (DOT _max) (vint (number2Z r.1.2.2)) p *
         in_tree g g_in p r.1.1.2 * my_half g_in Tsh r * malloc_token Ews t_struct_tree_t p *
         in_tree g g_in p r.1.1.2 * tree_rep_R r.1.1.1 r.1.2 r.2 g * malloc_token Ews t_struct_pn nb *
         data_at sh (tptr t_struct_tree_t) np b *
         field_at lsh t_struct_tree_t (DOT _lock) lock np)).
    + pose proof (Int.one_not_zero); easy.
    + simpl.
      forward_call(nb, Ews, x, v, p, r.1.1.1, (number2Z r.1.2.1), (number2Z r.1.2.2), gv).
      { unfold node_lock_inv_pred, node_rep. entailer !. }
      Intros pt.
      destruct pt as ((((pnt & p1) & p2) & lock1) & lock2).
      Exists (pnt, (p1, (p2, (lock1, lock2)))).
      entailer !. apply derives_refl.
    + Intros pt.
      destruct pt as (pnt & (p1 & (p2 & (lock1 & lock2)))).
      simpl.
      forward.
      gather_SEP AS (in_tree g g_in p _).
      viewshift_SEP 0 (AS * (in_tree g g_in p r.1.1.2) * (EX lsh, !!(readable_share lsh) &&
                       field_at lsh t_struct_tree_t (DOT _lock) r.1.1.2 p)).
      { go_lower. apply lock_alloc. }
      assert_PROP (field_compatible t_struct_tree_t [] p1) by entailer !.
      assert_PROP (field_compatible t_struct_tree_t [] p2) by entailer !.
      assert_PROP(is_pointer_or_null lock1) by entailer !.
      assert_PROP(is_pointer_or_null lock2) by entailer !.
      Intros lsh1.
      forward.
      forward_call (r.1.1.2, Q).
      {
        iIntros "(((((((((((((((((((((((AU & H1) & H2) & H3) & H4) & H5) & H6) & H7) & H8) & H9) & G1) & G2) & G3) & G4) & G5) & G6) & G7) & G8) & G9) & K1) & K2) & K3) & K4) & K5)".
        iCombine "AU H1 H2 H6 G8 G9 H7 G6 G7 G3" as "HH1".
        iCombine "G1 G2 H8 H9 G4 G5" as "HH2".
        iCombine "HH1 HH2" as "HH3".
        iVST.
        rewrite <- 7sepcon_assoc; rewrite <- sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & (#H1 & (H2 & (H3 & (H4 & (H5 & (H6 & (H7 & (H8 & H9))))))))) & (G1 & (G2 & (G3 & (G4 & (G5 & G6))))))"; iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iPoseProof (tree_rep_insert _ g g_root g_in p r.1.1.2 with "[$Hm $H1]") as "InvLock".
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
             { iExists _. iSplit. done. iFrame "K2". iExists true. iFrame. }
             iSpecialize ("K3" with "[$HInv $K1]").
             iDestruct "K3" as "(K3 & _)".
             iSpecialize ("HClose" with "K3").
             iFrame.
           }
           iIntros (_) "(H & _)".
           iDestruct "K3" as "[[> K3 _] _]".
           iDestruct "K3" as (g1 g2) "((((K4 & K5) & #K6) & #K7) & K8)".
           instantiate (1 := lock2). instantiate (1 := p2).
           instantiate (1 := lock1). instantiate (1 := p1).
           iPoseProof (public_update g_in r (R, Some O) (pnt, r.1.1.2, r.1.2, Some (Some (x, v, g1, g2))) with "[$H4 $K1]") as "(% & > (H4 & K1))".
           destruct r.
           inversion H16; subst; simpl.
           destruct H15 as (Hf & Hrs).
           (* join lsh1 with lsh2 = Lsh *)
           iPoseProof (lock_join with "[$H2 $K2]") as "K2"; try iSplit; auto.
           iDestruct "K2" as (Lsh) "(% & K2)".
           iAssert(ltree g g_in p g0.1.2
                     (node_lock_inv_pred g p g_in (pnt, g0.1.2, g0.2, Some (Some (x, v, g1, g2)))))
           with "[H H3 H4 H5 H6 H7 H8 H9 K2 ]" as "LT".
           {
             iApply (non_null_ltree g g_in p _ Lsh pnt p1 p2 lock1 lock2 g1 g2); eauto.
             iFrame. iFrame "H1 K6 K7". }
           iAssert(ltree g g1 p1 lock1
               (node_lock_inv_pred g p1 g1 (nullval, lock1, (g0.2.1, Finite_Integer x), Some None)))
           with "[K4 G1 G3 G6]" as "LT1".
           { iApply (null_ltree g g1 p1 lock1 _); eauto; iFrame; iFrame "K6". }
           iAssert(ltree g g2 p2 lock2
            (node_lock_inv_pred g p2 g2 (nullval, lock2, (Finite_Integer x, g0.2.2), Some None)))
           with "[K5 G2 G4 G5]" as "LT2".
           { iApply (null_ltree g g2 p2 lock2 _); eauto; iFrame; iFrame "K7". }
           iSpecialize ("K8" with "[$K1 $LT $LT1 $LT2]").
           iPureIntro. repeat (split; auto; [inversion HGh]); auto.
           iDestruct "K8" as "(((K8 & _) & _) & _)".
           iDestruct "HClose" as "[_ HClose]".
           iSpecialize ("HClose" $! ()).
           by iMod ("HClose" with "[$K8]") as "?".
        ++ (* prove contradiction here for using exclusive field_at of 2 nodes *)
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
     entailer !.
     unfold nodebox_rep.
     Exists np lsh.
     unfold tree_rep_R.
     rewrite -> if_true; auto.
     entailer !. by iIntros "_".
  - simpl in H2.
    forward_if (
        PROP ( )
          LOCAL (temp _t'2 Vfalse; temp _t'7 np; temp _pn__2 nb; gvars gv; temp _t b; 
                 temp _x (vint x); temp _value v)
          SEP (Q1 (false, (p, (gsh, (g_in, r)))); mem_mgr gv; seplog.emp;
               data_at Ews t_struct_pn (p, p) nb;
               in_tree g g_in p r.1.1.2;
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
                          ∧ is_pointer_or_null lockb ∧ tc_val (tptr Tvoid) v0
                          ∧ key_in_range x0 r.1.2 = true) &&
                        data_at Ews t_struct_tree (vint x0, (v, (pa, pb))) r.1.1.1 *
                        malloc_token Ews t_struct_tree r.1.1.1 *
                        in_tree g ga pa locka * in_tree g gb pb lockb));
               in_tree g g_root np lock; malloc_token Ews t_struct_pn nb;
               data_at sh (tptr t_struct_tree_t) np b;
               field_at lsh t_struct_tree_t (DOT _lock) lock np)).
    + unfold node_lock_inv_pred, node_rep, tree_rep_R.
      destruct H6 as (Hx & Hy).
      destruct Hy as (v1 & g1 & g2 & Hy).
      rewrite -> if_false; auto.
      Intros g1' g2' x1 v1' p1 p2 lock1 lock2.
      simpl. forward. forward. forward.
      Exists g1' g2' x1 v1' p1 p2 lock1 lock2.
      entailer !. apply derives_refl.
    + pose proof Int.one_not_zero; easy.
    + destruct H6 as ( ? & v2 & g21 & g22 & ?).
      Intros g1 g2 x1 v1 p1 p2 lock1 lock2.
      forward.
      unfold Q1.
      simpl.
      gather_SEP AS (in_tree g g_in p _).
      viewshift_SEP 0 (AS * (in_tree g g_in p r.1.1.2) * (EX lsh, !!(readable_share lsh) &&
                       field_at lsh t_struct_tree_t (DOT _lock) r.1.1.2 p)).
      { go_lower. apply lock_alloc. }
      Intros lsh1.
      forward.
      forward_call (r.1.1.2, Q).
      {
        iIntros "(((((((((((((((((((AU & H1) & H2) & H3) & _) & H4) & H5) & H6) & H7) & H8)
                & H9) & G1) & G2) & G3) & G4) & G5) & G6) & G7) & G8) & G9)".
        iCombine "AU H1 H2 H5 H6 H7 H8 H9 G2 G3 G4 G5" as "HH".
        iVST.
        rewrite <- 6sepcon_assoc; rewrite <- sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "(AU & (#HT & (H1 & (H2 & (H3 & (H4 & (H5 &
        (H6 & (H7 & (H8 & (#HT1 & #HT2)))))))))))"; iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iPoseProof (tree_rep_insert _ g g_root g_in p r.1.1.2 x v nullval p1 p2 lock1 lock2
                     with "[$Hm $HT]") as "InvLock".
        iDestruct "InvLock" as (R O) "((K1 & K2) & K3)".
        iDestruct "K2" as (lsh2) "(% & (K2 & KInv))".
        iDestruct "KInv" as (bl) "(KAt & KInv)".
        destruct bl.
        + iExists ().
          iFrame "KAt".
          iSplit.
          {
            iIntros "H". iFrame.
            iAssert (ltree g g_in p r.1.1.2 (node_lock_inv_pred g p g_in (R, Some O)))
              with "[H K2]" as "HInv".
            { iExists _; iSplit; iFrame; try done. iExists true; iFrame. }
            iSpecialize ("K3" with "[$HInv $K1]").
            iDestruct "K3" as "(K3 & _)".
            iSpecialize ("HClose" with "K3"); auto.
          }
          iIntros (_) "(H & _)".
          iDestruct "K3" as "[[_ > K3] _]".
          iSpecialize ("K3" $! g1 g2 v1).
          iPoseProof (public_update g_in r (R, Some O) (R, Some (Some (x, v, g1, g2)))
                   with "[$H2 $K1]") as "(% & >(H2 & K1))".
          (* join two field_at *)
          destruct r. inversion H17; simpl.
          rewrite H7 in H11.
          inversion H11; subst x1 v2 g21 g22.
          destruct g0. destruct p0.
          simpl.
          destruct H16 as (Hf & Hrs).
          (* lock_join lsh1 and lsh2 = Lsh *)
          iPoseProof (lock_join with "[$H1 $K2]") as "K2"; try iSplit; auto.
          iDestruct "K2" as (Lsh) "(% & K2)".
          iAssert (ltree g g_in p v2
           (node_lock_inv_pred g p g_in (v0, v2, r, Some (Some (x, v , g1, g2)))))
           with "[H K2 H2 H3 H4 H5 H6 H7 H8]" as "LT".
          {
            iApply (non_null_ltree g g_in p _ Lsh _ p1 p2 lock1 lock2 g1 g2); auto.
            iFrame. iFrame "HT HT1 HT2".
          }
          iSpecialize ("K3" with "[$K1 $LT]").
          iPureIntro; subst; repeat (split; auto; [inversion H7]); auto.
          iDestruct "K3" as "(K3 & _)".
          iDestruct "HClose" as "[_ HClose]".
          iSpecialize ("HClose" $! ()).
          iMod ("HClose" with "[$K3]") as "HClose"; auto.
        + (* proving using contradiction using exclusive of 2 nodes *)
          unfold node_lock_inv_pred at 1, node_rep.
          iDestruct "KInv" as "(? & KInv)".
          iDestruct "KInv" as "((((((? & KInv) & ?) & ?) & ?) & ?) & ?)".
          iPoseProof (field_at_conflict Ews t_struct_tree_t (DOT _t) p
                      with "[$H3 $KInv]") as "HF"; try easy; auto.
     }
     (* free *)
     forward_call (t_struct_pn, nb, gv).
     { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
     entailer !.
     Exists np lsh.
     entailer !. by iIntros "_".
Qed.
