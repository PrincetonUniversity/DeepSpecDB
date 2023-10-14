Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.give_up_template.
Require Import bst.puretree.
Require Import bst.dataStruct.
Require Import bst.giveup_lib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Context {N: NodeRep}.

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; !!( key_in_range x (((pt.2.2.2).2).1).2 = true ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.1) ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.2) /\
                         is_pointer_or_null ((((pt.2.2.2).2).1).1).2
                       /\ (if Val.eq (enums pt.1) (enums NN) then
                            pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                          else ((((pt.2.2.2).2).1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp; 
        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b;
        in_tree g pt.2.2.2.1 pt.2.1 ((((pt.2.2.2).2).1).1).2;
       node_lock_inv_pred g pt.2.1 pt.2.2.2.1 (pt.2.2.2).2



  )| (CSS g g_root M).

Check enums _.
(* t_struct_node represents for the generic-struct rather specific-data-structure *)
(* Spec of inrange function *)
Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, p: val, min: Z, max : Z, sh: share, gv: globals
  PRE [ tptr t_struct_node, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
          PARAMS (p; Vint (Int.repr x)) GLOBALS (gv)
          SEP (
              field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p)
  POST [ tint ]
  EX (succ: bool),
         PROP (match succ with
               | true => (and (Z.lt min x) (Z.lt x max))
               | false => (or (Z.le x min) (Z.le max x))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (
             field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p).

Lemma node_rep_saturate_local r p g g_current:
  node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof. unfold node_rep; entailer !. Qed.
Global Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer t g g_current p: node_rep p g g_current t |-- valid_pointer p.
Proof.
  unfold node_rep.
  Intros.
  iIntros "(((((H & ?) & ?) & ?) & ?) & ?)".
  iPoseProof (field_at_valid_ptr0 with "H") as "H"; try auto; simpl; try lia.
  iVST. entailer !.
Qed.
Global Hint Resolve node_rep_valid_pointer : valid_pointer.


(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r : node_info, g: gname, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP ((* data_at sh (t_struct_tree_t) (p, n) b *)
            node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_node) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_node) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_node) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p).

(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inRange inRange_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP ()
              LOCAL (temp _t'1 (if andb (min <? x) (x <? max)
                                then Val.of_bool true
                                else Val.of_bool false);
                     temp _t'2 (vint min); gvars gv; temp _p p; temp _x (vint x))
     SEP (field_at sh t_struct_node (DOT _min) (vint min) p;
     field_at sh t_struct_node (DOT _max) (vint max) p)).
  - repeat forward. entailer !.
     destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      apply Z.le_ge in H8.
      destruct (zlt x max); [try easy | auto].
  - forward.
    destruct (Z.ltb_spec min x); try rep_lia.
    entailer !.
  - forward_if; forward.
    + assert (((min <? x) && (x <? max))%bool = true) as Hx.
      { destruct((min <? x) && (x <? max))%bool; easy. }
      Exists true. entailer !.
    + assert (((min <? x) && (x <? max))%bool = false) as Hy.
      { destruct ((min <? x) && (x <? max))%bool; easy. }
      Exists false. entailer !.
Qed.


(* traverse invariants *)
Definition traverse_inv (b: val) (n pnN': val) (sh: share)
                        (x : Z) (v: val) (g_root: gname) (lock: val) gv
                        (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (pnN p: val) (gN_in: gname) (lockN_in: val),
            PROP ()
            LOCAL (temp _p pnN'; temp _flag (vint 2); temp _pn__2 b; temp _x (vint x);
                   (* temp _value v; *) gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 in_tree g gN_in pnN lockN_in; in_tree g g_root pnN' lock;
                 !!(is_pointer_or_null lockN_in) && seplog.emp; AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred g p g_in r *
  (!!(key_in_range x r.1.2 = true /\ r.2 = Some None /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  (* node_lock_inv_pred_1 g p g_in r x * *) (* modify it later*)
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; findnext_spec; 
                             inRange_spec; traverse_spec ]).

Axiom node_rep_R_saturate_local: forall t p g_children g,
  node_rep_R p t g_children g |-- !! is_pointer_or_null p.
Global Hint Resolve node_rep_R_saturate_local: saturate_local.

Axiom node_rep_R_valid_pointer: forall t tp g_children g,
  node_rep_R tp t g_children g |-- valid_pointer tp.

Global Hint Resolve node_rep_R_valid_pointer : valid_pointer.

(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
  forward.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  (* New pt: bool * (val * (share * (gname * node_info))) *)
  forward_loop (traverse_inv b n n Ews x v g_root lock gv inv_names g AS)
    break: (*consider to remove gsh *)
    (EX (flag: enum) (q : val) (gsh: share) (g_in: gname) (r: node_info),
     PROP() LOCAL(temp _flag (enums flag))
     SEP((match flag with
            | F => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NF => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NN => ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 = nullval) && seplog.emp)) end) *
                       Q (flag, (q, (gsh, (g_in, r)))) * mem_mgr gv)).
  - unfold traverse_inv.
    Exists n p g_root lock. sep_apply in_tree_duplicate. entailer !. 
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn p1 g_in lock_in.
    gather_SEP AS (in_tree g g_in pn lock_in).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in) *
                          (EX lsh, !!(readable_share lsh) &&
                                     field_at lsh t_struct_node (DOT _lock) lock_in pn)).
    { go_lower. apply lock_alloc. }
    Intros lsh.
    forward.
    forward.
    sep_apply in_tree_duplicate.
    (* acquire(pn->n->lock); *)
    forward_call acquire_inv_atomic (lock_in,
        AS  * (EX R, node_lock_inv_pred g pn g_in R)  ).
    {
      iIntros "[[[[[[HITlkin HITlkin1] HAS] H4] H5] HITlkin2] H7]".
      iCombine "HITlkin HAS" as "HITlkin".
      iCombine "HITlkin HITlkin1 H4 H5 HITlkin2 H7" as "HITAS".
      iVST.
      apply sepcon_derives; [| cancel_frame].
      unfold atomic_shift. iIntros "AU". iAuIntro; unfold atomic_acc; simpl.
      iDestruct "AU" as "[#HITlkin AU]".
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      iPoseProof (in_tree_inv g g_in g_root with "[$HITlkin $Hm]") as "InvLock".
      iDestruct "InvLock" as "(InvLock & _)".
      iDestruct "InvLock" as (r) "[H1 H2]".
      iExists _. iFrame.
      iSplit; iFrame.
      iIntros "H1".
      iSpecialize ("H2" with "H1").
      iFrame "HITlkin".
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2"); auto.
      iIntros (m') "((H1 & H1') & _)".
      iSpecialize ("H2" with "H1").
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2").
      iMod ("HClose").
      iFrame "HClose". by iExists _.
    }
    Intros r.
    forward.
    forward.
    unfold node_lock_inv_pred, node_rep.
    Intros.
    forward.
    (* inrange function *)
    forward_call(x, pn, (number2Z r.1.2.1), (number2Z r.1.2.2), Ews, gv).
    Intros succ1.
    assert_PROP(is_pointer_or_null r.1.1.1). entailer !.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if. 
      (* prove r.1.1.2 = lock_in *)
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
           !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct H12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NN, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NN, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      (*proving it satisfies with the post condition of traverse *)
      Intros y.
      forward.
      Exists NN pn Ews g_in r.
      unfold traverse_inv_1.
      unfold node_lock_inv_pred, node_rep.
      entailer !. admit. 
      by iIntros "(H & _)". 
      forward.
      assert_PROP(field_compatible t_struct_pn (DOT _n) b). entailer !.
      (* findNext *)
      forward_call(x, pn, (field_address t_struct_pn [StructField _n] b),
                   pn, r, g, Ews, gv).
      { unfold_data_at (data_at Ews t_struct_pn _ b); cancel. }
      {
        Intros succ.
        (* assert_PROP(r.1.1.1 <> nullval) by entailer !. *)
        destruct succ.1.1; last first.
        Intros. 
        * (* NN => succ.1.2 = succ.2  *)
          (* not found and find the next point *)
          forward.
          forward_if.
          easy. (* contradiction *)
          forward_if.
          easy. (* contradiction *)
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          forward.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower.
            apply push_lock_back; auto.  }
          (* make in_tree of next node : in_tree g succ.2 pnext lknext *)
          Intros.
          gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
          viewshift_SEP 0 (EX g_in1 lock1, AS * (node_lock_inv_pred g pn g_in r ) *
                                           (in_tree g g_in1 succ.2 lock1)).
          {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iMod "AU" as (m) "[Hm HClose]".
            Check ghost_update_step.
            iPoseProof (ghost_update_step g g_in g_root pn succ.1.2 lock_in m r
                         with "[$H $Hm $HNode $H2 $H3 $H4 $H5 $H6]") as (g_in1 lock1) "((Inv & H1) & H2)".
            { rewrite <- Hlk. iFrame "H". done. }
            iExists g_in1, lock1.
            iSpecialize ("HClose" with "H1").
            rewrite H11.
            by iFrame "Inv H2".
          }
          (*Now we have in_tree g succ.2 pnext lknext *)
          Intros gnext lknext.
          Search is_pointer_or_null.
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((HAS & H1) & H2) & H3) & H4) & H5) & H6) & H7)".
            iCombine "HAS H1 H3 H2 H4 H5 H6 H7" as "Hnode_inv_pred".
            iVST.
            rewrite <- H11.
            rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            unfold atomic_shift;
              iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
            iMod "AU" as (m) "[Hm HClose]".
            iModIntro.
            iExists tt.
            iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
            { rewrite Hlk. iFrame "H1 H2". }
            iDestruct "HI1" as "(HI1' & HI1)".
            rewrite Hlk.
            iFrame "HI1' HI1".
            iSplit.
            {
              iIntros "(Hnode_Iinv & InvLock)".
              iSpecialize ("HI2" with "InvLock").
              iDestruct "HClose" as "[HClose _]".
              iFrame "Hnode_Iinv".
              iSpecialize ("HClose" with "HI2").
              iFrame.
            }
            iIntros (_) "(H & _)".
            iSpecialize ("HI2" with "H").
            iDestruct "HClose" as "[HClose _]". 
            by iSpecialize ("HClose" with "HI2").
         }
         (* proving |--  traverse_inv *)
         unfold traverse_inv.
         Exists succ.1.2 pn gnext lknext.
         entailer !. admit.
         unfold_data_at (data_at Ews t_struct_pn _ b).
         cancel.
       * (* NF case *)
         forward.
         forward_if.
         forward.
         easy.
         forward_if.
         gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
         assert_PROP (r.1.1.2 = lock_in) as Hlk.
         { sep_apply in_tree_equiv; entailer !. }
         Intros.
         rewrite Hlk.
         (* push back lock into invariant *)
         gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
         viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
         {
           go_lower.
           iIntros "((AU & #H) & H1)".
           iMod "AU" as (m) "[Hm HClose]".
           iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
           iDestruct "InvLock" as "(_ & InvLock)".
           iDestruct "InvLock" as (R) "[H1' H2']".
           unfold ltree.
           iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
           iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NF, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NF, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      Exists  (NF, (succ.1.2 , (Ews, (g_in, r)))).
      simpl.
      unfold node_lock_inv_pred, node_rep.
      simpl.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      by iIntros "_".
      (* contradiction *)
      easy.
    * forward.
      forward_if.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (F, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (F, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      Exists  (F, (succ.1.2 , (Ews, (g_in, r)))).
      simpl.
      unfold node_lock_inv_pred, node_rep.
      simpl.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      by iIntros "_".
      (* contradiction *)
      easy.
    }
    easy.
  + forward_if.
    easy.
    forward.
    forward.
    gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
    assert_PROP (r.1.1.2 = lock_in) as Hlk.
    { sep_apply in_tree_equiv; entailer !. }
    rewrite Hlk.
    Intros.
      (* push back lock into invariant *)
    gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
    { go_lower; apply push_lock_back; auto. }
    Intros.
    gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
    viewshift_SEP 0 (AS * (node_lock_inv_pred g pn g_in r )).
    {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iFrame.
            rewrite <- Hlk. iFrame "H". done.
    }
    forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
    {
        lock_props.
        iIntros "(((((HAS & H1) & H2) & H3) & H4) & H5)".
        iCombine "HAS H1 H2 H3 H4 H5" as "Hnode_inv_pred".
        iVST.
        rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iExists tt.
        iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
        { rewrite Hlk. iFrame "H1 H2". }
          iDestruct "HI1" as "(HI1' & HI1)".
          rewrite Hlk.
          iFrame "HI1' HI1".
          iSplit.
          {
            iIntros "(Hnode_Iinv & InvLock)".
            iSpecialize ("HI2" with "InvLock").
            iDestruct "HClose" as "[HClose _]".
            iFrame "Hnode_Iinv".
            iSpecialize ("HClose" with "HI2").
              iFrame.
          }
          iIntros (_) "(H & _)".
          iSpecialize ("HI2" with "H").
          iDestruct "HClose" as "[HClose _]". 
          by iSpecialize ("HClose" with "HI2").
     }
     (* proving |--  traverse_inv *)
       forward.
       unfold traverse_inv.
       Exists n pn g_root lock.
       sep_apply (in_tree_duplicate g g_root n).
       entailer !.
   
       
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       + simpl.
         autorewrite with norm.
         forward.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl. entailer !. 
       + forward.
         Exists (false, (pn, (gsh, (g_in, r)))).
         simpl.
         unfold node_lock_inv_pred_1, node_rep_1 at 1, tree_rep_R_1 at 1.
         Intros g1 g2 v1 p1 p2 l1 l2.
         rewrite H7.
         entailer !.
         exists v1, g1, g2; auto.
         unfold node_lock_inv_pred, node_rep, tree_rep_R.
         rewrite -> if_false; auto.
         simpl.
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
