Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
(* Require Import bst.giveup_template. temporary having it for lock - need remove*)
(* and make more general - not involving anything relate to specific templates *)
Require Import bst.puretree.
Require Import bst.data_struct.
Require Import bst.template.
(* Require Import bst.giveup_lib. *)
Require Import bst.giveup_specs.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

Section verif_template.
Context {N: NodeRep}.

Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_pn := Tstruct _pn noattr.


(*
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
*)

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t: type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ]
    EX p: _,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * val * globals * gname * gname))
  OBJ M INVS ∅
  WITH b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_node), tint, tptr tvoid ]
    PROP (writable_share sh; and (Z.le Int.min_signed x) (Z.le x Int.max_signed); is_pointer_or_null v)
    PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (CSS g g_root M)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (CSS g g_root (<[x:=v]>M)).

(* Definition spawn_spec := DECLARE _spawn spawn_spec. *)

Check NodeL.
Lemma tree_rep_insert: forall (t: gmap key val) g g_root g_in pn lock (x: Z) (v: val)
                      pnt p1 p2 lock1 lock2,
  CSS g g_root t * in_tree g g_in pn lock
  |-- EX (r : (val * val * range)) (o : option (ghost_info)),
  public_half g_in (r, Some o) * ltree pn lock (node_lock_inv_pred g pn g_in (r, Some o)) *
  (((@bupd _ (@bi_bupd_bupd _ mpred_bi_bupd))
      (EX (g1 g2: gname),
                        (my_half g1 Tsh (nullval, lock1, (r.2.1, Finite_Integer x), Some None) *
                         my_half g2 Tsh (nullval, lock2, (Finite_Integer x, r.2.2), Some None) *
                         in_tree g g1 p1 lock1 * in_tree g g2 p2 lock2) *
                         (!!(o = None /\ key_in_range x r.2 = true) &&
                         (public_half g_in ((pnt, r.1.2, r.2), Some (Some(x, v, []))) *
                         ltree pn lock (node_lock_inv_pred g pn g_in ((pnt, r.1.2, r.2), Some (Some(x, v, []))))) -*
                          CSS g g_root (<[x:=v]>t) *
                          in_tree g g_in pn lock )))%I
   && (|==> (ALL g1 g2: gname, ALL (v0: val), (!!(o = Some(x, v0, []) /\
      (key_in_range x r.2 = true)) && public_half g_in (r, Some (Some(x, v, []))) *
       ltree pn lock (node_lock_inv_pred g pn g_in (r, Some (Some(x, v, []))))
         -* CSS g g_root (<[x:=v]>t) * in_tree g g_in pn lock)))%I &&
     (* no changes *)
     (public_half g_in (r, Some o) * ltree pn lock (node_lock_inv_pred g pn g_in (r, Some o))
     -* (CSS g g_root t * in_tree g g_in pn lock))).
Admitted.

Definition iter_myhalf (lg: list gname) (lst : list (val * val)) :=
  iter_sepcon (fun '(g_in, (pt, lock)) =>  my_half g_in Tsh (pt, lock, (Finite_Integer 1, Finite_Integer 1), Some None)) (combine lg lst).

Definition iter_in_tree g (lg: list gname) (lst : list (val * val)) :=
  iter_sepcon (fun '(g_in, (pt, lock)) =>  in_tree g g_in pt lock) (combine lg lst).

Check node_info.

Definition iter_ltree g (lg: list gname) (lst : list (val * val))
  (lpt : list val) (lrg : list range) (lgh : list (option ghost_info)) := 
  iter_sepcon (fun '(g_in, (pt, lock), ppt, rg, lgh) =>  (ltree pt lock (node_lock_inv_pred g pt g_in (ppt, lock, rg, Some lgh)))) (combine (combine (combine (combine lg lst) lpt) lrg) lgh).

Lemma tree_rep_insert1: forall (t: gmap key val) g g_root g_in pn lock (x: Z) (v: val) pnt (lp: list val) (llk: list val) (lpt : list val) (lrg : list range) (lgh : list (option ghost_info)),
  CSS g g_root t * in_tree g g_in pn lock
  |-- EX (r : (val * val * range)) (o : option (ghost_info)),
  public_half g_in (r, Some o) * ltree pn lock (node_lock_inv_pred g pn g_in (r, Some o)) *
  (((@bupd _ (@bi_bupd_bupd _ mpred_bi_bupd))
      (EX (lg : list gname),
        (iter_myhalf lg (combine lp llk) *
         iter_in_tree g lg (combine lp llk)) *
                         (!!(o = Some (x, v, lp) /\ key_in_range x r.2 = true) &&
                         (public_half g_in ((pnt, r.1.2, r.2), Some (Some(x, v, lp))) *
                            ltree pn lock (node_lock_inv_pred g pn g_in ((pnt, r.1.2, r.2), Some (Some(x, v, lp)))) *
                           iter_ltree  g lg (combine lp llk) lpt lrg lgh) -*
                          CSS g g_root (<[x:=v]>t) *
                            in_tree g g_in pn lock )))%I &&
     (public_half g_in (r, Some o) * ltree pn lock (node_lock_inv_pred g pn g_in (r, Some o))
     -* (CSS g g_root t * in_tree g g_in pn lock))
     ).
Admitted.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_helper_spec; getLock_spec ; traverse_spec; insert_spec (*; treebox_new_spec *) ]).


Definition ltree_iter (lst: list (val * val * mpred)) :=
  iter_sepcon (fun '(p, lock, R) =>  (EX lsh, !!(field_compatible t_struct_node nil p /\ readable_share lsh) && seplog.emp *  (field_at Ews t_struct_node [StructField giveup_template._lock] lock p * inv_for_lock lock R))) lst.

Check node_rep.

Definition node_rep_iter g (lst : list (val * gname * node_info)) :=
    iter_sepcon (fun '(pn, g_current, r) =>
                   (!!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2)
       /\ is_pointer_or_null r.1.1.1 /\ is_pointer_or_null r.1.1.2 ) && seplog.emp * 
      field_at Ews (t_struct_node) [StructField giveup_template._t] r.1.1.1 pn *
      field_at Ews (t_struct_node) [StructField giveup_template._min] (vint (number2Z (r.1.2.1))) pn * (*min*)
      field_at Ews (t_struct_node) [StructField giveup_template._max] (vint (number2Z (r.1.2.2))) pn * (*max*)
      malloc_token Ews t_struct_node pn * in_tree g g_current pn r.1.1.2 *
      node_rep_R r.1.1.1 r.2 g)) lst.

(*
Definition node_rep  pn g g_current (r : node_info) :=
    !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2)
       /\ is_pointer_or_null r.1.1.1 /\ is_pointer_or_null r.1.1.2 ) && seplog.emp * 
      field_at Ews (t_struct_node) [StructField _t] r.1.1.1 pn *
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
      malloc_token Ews t_struct_node pn * in_tree g g_current pn r.1.1.2 *
      node_rep_R r.1.1.1 r.2 g.
 *)

Lemma test g (lg: list gname) (lst : list (val * val)) (lt : list gname) :
  lt <> [] -> iter_sepcon (fun '(g_in, (pt, lock)) =>  in_tree g g_in pt lock) (combine lg lst) = 
    iter_sepcon (fun '(g_in, (pt, lock), _) =>  in_tree g g_in pt lock) (combine (combine lg lst) lt).
Proof.
  revert lst lt.
  induction lg.
  intros.
  - done.
  - simpl.
    destruct lst.
    + done.
    + simpl.
      destruct lt.
      * simpl. 
        destruct p.
        intros. done.
      * intros.
        destruct p.
Admitted.
        

Definition iter_field lst :=
  iter_sepcon (fun '(pt, lock) => !! field_compatible giveup_lib.t_struct_node [] pt) (fst_snd_list lst).

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
  set Q1:= fun (b : ( enum * (val * (share * (gname * node_info))))%type) => AS.
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
    auto.
  }
  Intros pt.
  destruct pt as (fl & (p & (gsh & (g_in & r)))).
 (* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 *)
  simpl.
  destruct fl.
  - (* Found *)
    forward_if(
        PROP ( )
     LOCAL (temp _status (enums F); temp _t'7 np; temp _pn__2 nb; gvars gv; 
     temp _t b; temp _x (vint x); temp _value v)
     SEP (AS; mem_mgr gv;
     !! (key_in_range x r.1.2 = true
         ∧ repable_signed (number2Z r.1.2.1)
           ∧ repable_signed (number2Z r.1.2.2)
             ∧ is_pointer_or_null r.1.1.2 ∧ r.2 = Some None ∧ r.1.1.1 = nullval) && emp *
     data_at Ews t_struct_pn (p, p) nb * in_tree g g_in p r.1.1.2 * node_lock_inv_pred g p g_in r;
     in_tree g g_root np lock; malloc_token Ews t_struct_pn nb; data_at sh (tptr t_struct_node) np b;
     field_at lsh t_struct_node (DOT giveup_template._lock) lock np)); try easy.
     + Intros.
       forward.
       admit.
       (* call changeValue *)
       admit.
     + Intros. forward. admit. admit. 
       (* release(getLock(pn->n)); free *)
       admit.
  - (* Not Found *)
    unfold Q1.
    unfold post_traverse, node_lock_inv_pred, node_rep.
    Intros.
    Check post_insert_giveup2.
    
    forward_if (PROP ( )
     LOCAL (temp _status (enums NF); temp _t'7 np; temp _pn__2 nb; gvars gv; 
     temp _t b; temp _x (vint x); temp _value v)
     SEP (AS * mem_mgr gv * EX pt : val * list (val * val * val * val) * list val, 
     !! (key_in_range x r.1.2 = true /\ is_pointer_or_null p
         ∧ repable_signed (number2Z r.1.2.1)
           ∧ repable_signed (number2Z r.1.2.2) ∧ is_pointer_or_null r.1.1.2 ∧ r.1.1.1 ≠ nullval) &&
       post_insert_giveup2 p (pt.1).1 x v (number2Z r.1.2.1) (number2Z r.1.2.2) (pt.1).2 pt.2 r g *
      data_at Ews t_struct_pn (p, p) nb * my_half g_in Tsh r * in_tree g g_in p r.1.1.2 *
       malloc_token Ews t_struct_node p * in_tree g g_root np lock; malloc_token Ews t_struct_pn nb;
     data_at sh (tptr t_struct_node) np b;
     field_at lsh t_struct_node (DOT giveup_template._lock) lock np)); try easy.
    + forward. 
      (* insertOp_helper *)
      (* stt = 1 *)
      forward_call (x, 1, v, p, r.1.1.1, (number2Z r.1.2.1), (number2Z r.1.2.2),
                     r, g, gv).
      { simpl. entailer !. }
      Intros pt.
      destruct pt as (pnt & lst).
      assert ((Int.repr 1) <> (Int.repr 2)) as K; auto.
      rewrite Int.eq_false; auto.
      entailer !.
      Exists (pnt, lst).
      entailer !.
      cancel.
      by iIntros "H". 
    + Intros pt.
      destruct pt as (pnt & lst).
      simpl.
      Intros.
      forward.
      gather_SEP AS (in_tree g g_in p _).
      viewshift_SEP 0 (AS * (in_tree g g_in p r.1.1.2) * (EX lsh, !!(readable_share lsh) &&
                       field_at lsh t_struct_node (DOT giveup_template._lock) r.1.1.2 p)).
      { go_lower. apply lock_alloc. }
      (* viewshift_SEP 0 (iter_field lst). *)
     
      Intros lsh1.
      Intros.
      forward_call(p, r.1.1.2, lsh1).
      forward_call (r.1.1.2, Q).
      {
        iIntros "(((((((((((H1 & AU) & H2) & H3) & H4) & H5) & H6) & H7) & H8) & H9) & H10) & H11)".
        unfold post_insert_giveup2.
        iDestruct "H4" as "((((((((((K1 & K2) & K3) & K4) & K5) & K6) & K7) & K8) & K9) & K10) & K11)".
        (* iCombine "AU H2 H1 H7". *)
        iCombine "AU H2 H1 K9 H6 H7 K10 K11 K8" as "HH1".
        iCombine "K3 K1 K2 K4 K5 K6 K7" as "HH2".
        iCombine "HH1 HH2" as "HH3".
        iVST.
        rewrite <- 5sepcon_assoc; rewrite <- sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; 
        iIntros "((AU & (#H1 & (H2 & (H3 & (H4 & (H5 & (H6 & (H7 & H8))))))))
                  & (G1 & (G2 & (G3 & (G4 & (G5 & (G6 & G7)))))))";

        iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iPoseProof (tree_rep_insert1 _ g g_root g_in p r.1.1.2 with "[$Hm $H1]") as "InvLock".
        iDestruct "InvLock" as (R O) "((K1 & K2) & K3)".
        iDestruct "K2" as (lsh2) "(% & (K2 & KInv))".
        iDestruct "KInv" as (bl) "(KAt & KInv)".
        destruct bl.
        ++ iExists ().
           iFrame "KAt".
           iSplit.
           {
             iIntros "H".
             iFrame.
             iAssert (ltree p r.1.1.2 (node_lock_inv_pred g p g_in (R, Some O)))
               with "[H K2]" as "HInv".
             { iExists _. iSplit. done. iFrame "K2". iExists true. iFrame. }
             iSpecialize ("K3" with "[$HInv $K1]").
             simpl.
             iDestruct "K3" as "(K3 & _)".
             iSpecialize ("HClose" with "K3").
             iFrame.
           }
           iIntros (_) "(H & _)".
           iDestruct "K3" as "[> K3 _]".
           iDestruct "K3" as (lg) "(K4 & K5)".
           iPoseProof (public_update g_in r (R, Some O) (pnt.1, r.1.1.2, r.1.2, Some (Some (x, v, fst_list pnt.2))) with "[$H4 $K1]") as "(% & > (H4 & K1))".
           destruct r.
           destruct H9 as (Hf & Hrs).
           (* join lsh1 with lsh2 = Lsh *)
           iPoseProof (lock_join lsh1 lsh2 p  with "[$H2 $K2]") as "K2"; try iSplit; auto.
           iDestruct "K2" as (Lsh) "(% & K2)".
           iAssert(ltree p g0.1.2
                     (node_lock_inv_pred g p g_in (pnt.1, g0.1.2, g0.2, Some (Some (x, v, fst_list pnt.2)))))
           with "[H H8 K2 H4 H3 H5 H6 H7]" as "LT".
           {
             unfold ltree.
             iExists _. iFrame.
             iSplit. auto.
             unfold inv_for_lock.
             iExists false.
             unfold node_lock_inv_pred, node_rep.
             iFrame.
             simpl. iFrame "H1". 
             iPureIntro.
             simpl in *.
             Search "/\".
             apply conj. apply conj; auto. apply conj; auto.
             apply conj. admit. admit. done.
           }
           iDestruct "K4" as "(K41 & K42)".
           iAssert(iter_ltree g lg (fst_snd_list pnt.2) [nullval] [(g0.2.1, Finite_Integer x)] [])
             with "[K41 G1 G2 G3 G4 G5 G6 G7]"as "LT1".
           {
             unfold iter_ltree.

             Check combine (A := gname) (B := (val * val)) lg (fst_snd_list pnt.2).
             unfold fst_list, snd_list, fst_snd_list, fst_thrd_list, fst_frth_list .
             Search iter_sepcon.
             rewrite <- ! iter_sepcon_map.

             iCombine "G2 G4" as "G2".
             iPoseProof (iter_sepcon_sepcon' _  (λ x0 : val * val * val * val,
              field_at Ews giveup_lib.t_struct_node _ _ _) with "[G2]") as "G21"; auto.
             iCombine "G5 G6" as "G5".
             iPoseProof (iter_sepcon_sepcon' (λ x0 : val * val * val * val,
              field_at Ews giveup_lib.t_struct_node _ _ _) with "[G5]") as "G51"; auto.
             iCombine "G21 G51" as "G21".
             iPoseProof (iter_sepcon_sepcon' (λ x0 : val * val * val * val,
               malloc_token Ews giveup_lib.t_struct_node _ * _ _ _) with "[G21]") as "G21"; auto.
             iCombine "G21 G1" as "G21".
             iPoseProof (iter_sepcon_sepcon' _ (λ x0 : val * val * val * val, 
               atomic_int_at Ews _ _) with "[G21]") as "G21"; auto.
             simpl.
             Check fst_list pnt.2.
             unfold ltree.
             Search iter_sepcon derives.
             iAssert (iter_sepcon (λ pt, EX lsh0 : share,
                       !! (field_compatible giveup_lib.t_struct_node [] pt ∧
                             readable_share lsh0)) (fst_list pnt.2)) as "H".
             {
               Search iter_sepcon.
               
             Search iter_sepcon.
             Search field_compatible.
             
             rewrite <- iter_sepcon_sepcon' in "G2".
             Search iter_sepcon.
             unfold iter_sepcon.


             rewrite <- iter_sepcon_sepcon'.
             
             destruct (combine lst (map (λ '(x0, _, _, _), x0) pnt.2)).
             admit.
             simpl in *.
             destruct p0.
             simpl in *.
             list (val * val)
             list (gname)
             (gname * val * val) rather than (gname * (val * val))
             
             rewrite iter_sepcon_sepcon'. 

             
             unfold fst_snd_list 
             unfold node_rep.
             simpl.
             remember (combine (B := option ghost_info)(combine (combine (combine lg (fst_snd_list lst)) [nullval]) [(g0.2.1, Finite_Integer x)]) []) as l.
             
             
           (*
             node_rep =
λ (N : NodeRep) (pn : val) (g g_current : gname) (r : node_info),
  !! (repable_signed (number2Z r.1.2.1)
      ∧ repable_signed (number2Z r.1.2.2) ∧ is_pointer_or_null r.1.1.1 ∧ is_pointer_or_null r.1.1.2) &&
  emp * field_at Ews giveup_lib.t_struct_node (DOT giveup_template._t) r.1.1.1 pn *
  field_at Ews giveup_lib.t_struct_node (DOT giveup_template._min) (vint (number2Z r.1.2.1)) pn *
  field_at Ews giveup_lib.t_struct_node (DOT giveup_template._max) (vint (number2Z r.1.2.2)) pn *
  malloc_token Ews giveup_lib.t_struct_node pn * in_tree g g_current pn r.1.1.2 *
  node_rep_R r.1.1.1 r.2 g


            *)
           
           admit. 
        ++ (* contradiction *)
          admit.
      }
      forward_call (t_struct_pn, nb, gv).
      { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto; cancel. }
      entailer !.
      unfold nodebox_rep.
      Exists np lsh.
      entailer !.
      













      
        unfold post_insert_giveup2.
        cancel.
        entailer !. unfold node_lock_inv_pred. cancel.
        unfold node_rep.
        unfold node_lock_inv_pred. cancel.
        unfold node_rep. 
        entailer !. admit.
        unfold post_insert_giveup2.
        entailer !. 
        assert (pt.1 =  r.1.1.1). admit.
        subst.
        
        Unshelve.
        entailer !.
        entailer !.
        iIntros.
       
        


          WITH x: Z, stt: Z, v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals

      
    admit.
  - (* Null *)
    admit.

   
Admitted.
