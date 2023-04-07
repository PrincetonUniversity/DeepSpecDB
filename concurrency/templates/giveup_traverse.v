Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template_giveup.
Require Import bst.giveup_lib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

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

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Definition tree_rep_1 p (sh :share):= EX (tp pa pb vp: val) (xp : Z),
  field_at sh (t_struct_tree_t) [StructField _t] tp p *
  data_at sh t_struct_tree (Vint (Int.repr xp), (vp, (pa, pb))) tp *
  (!!(is_pointer_or_null pa /\ is_pointer_or_null pb) && seplog.emp).

Definition pn_rep p n (sh : share)(pn : val) :=
  data_at sh (t_struct_pn) (p, n) pn * tree_rep_1 p sh.

Definition pn_rep_1 (g g_root: gname) (sh : share) (pn n: val) :=
  EX (p: val), data_at sh (t_struct_pn) (p, n) pn.

Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock: val) (nb : val) :=
  EX (np: val) (lsh : share),
                data_at sh (tptr (t_struct_tree_t)) np nb *
                (!!(field_compatible t_struct_tree_t nil np /\ is_pointer_or_null lock) &&
                field_at lsh t_struct_tree_t [StructField _lock] lock np) *
                in_tree g g_root np lock.

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

Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH gv: globals
  PRE [ ]
    PROP (repable_signed (number2Z Neg_Infinity) ∧
            repable_signed (number2Z Pos_Infinity))
    PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX (g g_root : gname) (v: val) (lock: val),
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (mem_mgr gv; nodebox_rep g g_root Ews lock v;
         malloc_token Ews (tptr t_struct_tree_t) v;
         tree_rep g g_root empty).

(* Spec of findnext function *)
Definition findnext_spec :=
  DECLARE _findnext
  WITH x: Z, v: val, b: val, p: val, n: val, tp: val, 
       pa: val, pb: val, px: Z, pv: val, sh: share, gv: globals
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
          PROP (writable_share sh; is_pointer_or_null pa; is_pointer_or_null pb)
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP (data_at sh (t_struct_pn) (p, n) b;
               field_at sh (t_struct_tree_t) [StructField _t] tp p;
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
  POST [ tint ]
  EX (succ: bool), EX (n' : val),
         PROP (match succ with
               | true => ((n' = pa /\ (Z.lt (Int.signed (Int.repr x)) (Int.signed (Int.repr px)))) \/
                         (n' = pb /\ (Z.lt (Int.signed (Int.repr px)) (Int.signed (Int.repr x)))))
               | false => (n' = p /\ Int.signed (Int.repr x) = Int.signed (Int.repr px))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (match succ with
             | true =>
               (data_at sh (t_struct_pn) (p, n') b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             | false =>
               (data_at sh (t_struct_pn) (p, n) b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             end).

(* Spec of inrange function *)
Definition inrange_spec :=
  DECLARE _inrange
    WITH x: Z, b: val, p: val, n: val, tp: val, min: Z, max : Z, sh: share, gv: globals
  PRE [ tptr t_struct_pn, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
          PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
          SEP (data_at sh (t_struct_pn) (p, n) b;

              field_at sh (t_struct_tree_t) [StructField _t] tp p;
              field_at sh (t_struct_tree_t) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_tree_t) [StructField _max] (Vint (Int.repr max)) p)
  POST [ tint ]
  EX (succ: bool),
         PROP (match succ with
               | true => (and (Z.lt min x) (Z.lt x max))
               | false => (or (Z.le x min) (Z.le max x))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (data_at sh (t_struct_pn) (p, n) b;
              field_at sh (t_struct_tree_t) [StructField _t] tp p;
             field_at sh (t_struct_tree_t) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_tree_t) [StructField _max] (Vint (Int.repr max)) p).

(* functions support only traverse_inv_2*)
Definition tree_rep_R_1 (tp:val) (r:(range)) (x: Z) (g_info: option (option ghost_info)) g : mpred :=
  EX (ga gb : gname), EX (v pa pb : val), EX (locka lockb : val),
     !!(g_info = Some (Some (x, v, ga, gb)) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree (Vint (Int.repr x), (v, (pa, pb))) tp *
       malloc_token Ews t_struct_tree tp *
       in_tree g ga pa locka * in_tree g gb pb lockb.

Definition node_rep_1 pn g g_current (r : node_info) (x: Z):=
  !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2)) &&
  field_at Ews (t_struct_tree_t) [StructField _t] r.1.1.1 pn *
  field_at Ews (t_struct_tree_t) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
  field_at Ews (t_struct_tree_t) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
   malloc_token Ews t_struct_tree_t pn * in_tree g g_current pn r.1.1.2 *
   tree_rep_R_1 r.1.1.1 r.1.2 x r.2 g.

Definition node_lock_inv_pred_1 g p gp a (x : Z):= my_half gp Tsh a * node_rep_1 p g gp a x.

(* Spec of traverse function *)
Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
       is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
  SEP  (mem_mgr gv;
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (tree_rep g g_root M)
  POST [ tint ]
  EX  pt: bool * (val * (share * (gname * node_info))) %type,
  PROP () (* pt: bool * (val * (share * (gname * node_info))) *)
  LOCAL (temp ret_temp (Val.of_bool pt.1))
  SEP (mem_mgr gv  ; !!( key_in_range x (((pt.2.2.2).2).1).2 = true ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.1) ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.2) /\
                         is_pointer_or_null ((((pt.2.2.2).2).1).1).2 /\
              (if pt.1 : bool
               then ((pt.2.2.2.2.2 = Some None) /\ ((((pt.2.2.2).2).1).1).1 = nullval)
               else (((((pt.2.2.2).2).1).1).1 <> nullval) /\
               (exists (v1: val) (g1 g2: gname),
                   pt.2.2.2.2.2 = Some (Some(x, v1, g1, g2))))) && seplog.emp;
                   data_at Ews t_struct_pn (pt.2.1, pt.2.1) b;
                  in_tree g pt.2.2.2.1 pt.2.1 ((((pt.2.2.2).2).1).1).2;
                  node_lock_inv_pred g pt.2.1 pt.2.2.2.1 (pt.2.2.2).2) | (tree_rep g g_root M).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; inrange_spec; traverse_spec; findnext_spec; treebox_new_spec]).

(* Proving treebox spec *)
Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv).
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv).
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (gv).
  Intros l.
  forward. forward. forward. forward.
  forward_call release_nonatomic (l).
  ghost_alloc (both_halves ((nullval, l, (Neg_Infinity, Pos_Infinity)), (Some (@None ghost_info)))).
  (* { apply @part_ref_valid. } *)
  Intros g_root.
  ghost_alloc (ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val)))
                 {[g_root := (newt, l)]}).
  Intros g.
  unfold_data_at (data_at _ _ _ newt).
  sep_apply (share_divided Ews newt l); auto.
  Intros lsh1 lsh2.
  gather_SEP (ghost_master1 _ _).
  viewshift_SEP 0 (ghost_snap (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val)))
                      {[g_root := (newt, l)]} g *
                    ghost_master (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) Tsh
                      {[g_root := (newt, l)]} g).
  { go_lower. iIntros "H". by iPoseProof (make_snap Tsh with "H") as "?". }
  forward.
  rewrite <- general_locks.both_halves_join.
  sep_apply in_tree_duplicate.
  unfold nodebox_rep, tree_rep.
  Exists g g_root p l newt lsh1 (E_ghost : @ghost_tree val) newt l.
  simpl.
  unfold ltree, inv_for_lock.
  Exists lsh2 false.
  entailer !.
  split; constructor.
  unfold node_lock_inv_pred, node_rep, tree_rep_R.
  rewrite -> if_true; auto.
  entailer !. rewrite -> sepcon_comm.
  apply derives_refl.
Qed.

(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inrange inrange_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_if ( PROP ()
     LOCAL (temp _t'1 (if andb (min <? x) (x <? max) then Val.of_bool true else Val.of_bool false);
            temp _t'3 (vint min); temp _t'2 p; gvars gv; temp _pn__2 b; temp _x (vint x))
     SEP (data_at sh t_struct_pn (p, n) b; field_at sh t_struct_tree_t (DOT _t) tp p;
          field_at sh t_struct_tree_t (DOT _min) (vint min) p;
          field_at sh t_struct_tree_t (DOT _max) (vint max) p)).
  - repeat forward. entailer !.
    destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      apply Z.le_ge in H12.
      destruct (zlt x max); [try congruence | auto].
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

Lemma node_rep_saturate_local r p g g_current: node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof. unfold node_rep; entailer !. Qed.
Global Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer t g g_current p: node_rep p g g_current t |-- valid_pointer p.
Proof.
  unfold node_rep.
  Intros.
  iIntros "(((((H & ?) & ?) & ?) & ?) & ?)";
  iPoseProof (field_at_valid_ptr0 with "H") as "H"; try auto; simpl; try lia.
  iVST. entailer !.
Qed.
Global Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_R_saturate_local t p g_children g:
  tree_rep_R p t g_children g |-- !! is_pointer_or_null p.
Proof.
  unfold tree_rep_R.
  destruct (eq_dec p nullval). entailer !.
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer t tp g_children g: tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
  unfold tree_rep_R.
  destruct (eq_dec tp nullval). entailer!.
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_valid_pointer : valid_pointer.

Ltac logic_to_iris :=
  match goal with |-context[(|==>?P)%logic] => change((|==> P)%logic) with ((|==> P)%I) end.

(* traverse invariants *)
Definition traverse_inv (b: val) (n pnN': val) (sh: share)
                        (x : Z) (v: val) (g_root: gname) (lock: val) gv
                        (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (pnN p: val) (gN_in: gname) (lockN_in: val),
            PROP ()
            LOCAL (temp _p pnN'; temp _flag (vint 1); temp _pn__2 b; temp _x (vint x);
                   temp _value v; gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 in_tree g gN_in pnN lockN_in; in_tree g g_root pnN' lock;
                 !!(is_pointer_or_null lockN_in) && seplog.emp; AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in: gname)
                          (g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred g p g_in r *
  (!!(key_in_range x r.1.2 = true /\ r.2 = Some None /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in: gname)
                          (g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred_1 g p g_in r x *
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

(* Proving traverse spec *)
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
    (EX (flag: bool) (q : val) (gsh: share) (g_in: gname) (r: node_info),
     PROP() LOCAL(temp _flag (Val.of_bool flag))
     SEP((if flag then ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 = nullval) && seplog.emp))
                 else ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 <> nullval) && seplog.emp))) *
                       Q (flag, (q, (gsh, (g_in, r)))) * mem_mgr gv)).
  - unfold traverse_inv. Exists n p g_root lock. sep_apply in_tree_duplicate. entailer !.
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn p1 g_in lock_in.
    gather_SEP AS (in_tree g g_in pn lock_in).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in) *
                          (EX lsh, !!(readable_share lsh) &&
                                     field_at lsh t_struct_tree_t (DOT _lock) lock_in pn)).
    { go_lower. apply lock_alloc. }
    Intros lsh.
    forward.
    forward.
    sep_apply in_tree_duplicate.
    (* acquire(pn->n->lock); *)
    forward_call acquire_inv_atomic (lock_in,
        AS * (EX R, node_lock_inv_pred g pn g_in R)).
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
    (* inrange function *)
    forward_call(x, b, pn, pn, r.1.1.1, (number2Z r.1.2.1), (number2Z r.1.2.2), Ews, gv).
    Intros succ1.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if.
      unfold tree_rep_R.
      rewrite -> if_true; auto.
      Intros.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      viewshift_SEP 0 (in_tree g g_in pn r.1.1.2 * in_tree g g_in pn lock_in *
                         (!!(r.1.1.2 = lock_in) && seplog.emp)).
      {
        go_lower.
        iIntros "(H1 & H2)". iPoseProof (in_tree_equiv g g_in pn with "[$H1 $H2]") as "%Hx".
        iFrame. edestruct Hx; auto.
      }
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
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
           !! (field_compatible t_struct_tree_t [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_tree_t (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          {
           iSplitL "H1".
           iFrame. iPureIntro. auto.
           iFrame. iPureIntro.
           destruct H12. auto.
          }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _.
          destruct H12.
          iFrame. iPureIntro. repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". iFrame. auto.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!( y = (true, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (true, (pn, (Ews, (g_in, r))))).
        simpl.
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm". iFrame "Hm".
        iModIntro. iExists _. by iFrame "Hm".
      }
      Intros y.
      forward.
      unfold traverse_inv_1, node_lock_inv_pred, node_rep, tree_rep_R.
      Exists true pn Ews g_in r.
      Intros.
      change emp with seplog.emp.
      rewrite -> if_true; auto.
      subst.
      destruct r.1.2.
      simpl in H5.
      go_lower.
      entailer !.
      iIntros "(H & _)". iFrame.
      unfold tree_rep_R.
      rewrite -> if_false; auto.
      Intros ga gb x0 v1 pa pb locka lockb.
      (*findNext*)
      forward_call(x, v, b, pn, pn, r.1.1.1, pa, pb, x0, v1, Ews, gv).
      {
        Intros succ.
        assert_PROP(r.1.1.1 <> nullval) by entailer !.
        destruct succ.1.
        destruct H12 as [(Hx & Hy) | Hz].
        + forward_if.
          pose proof (Int.one_not_zero). contradiction.
          (* flag = 0 *)
          Intros.
          forward.
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower; apply push_lock_back; auto. }
          sep_apply (in_tree_duplicate g ga pa locka).
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((((((((((HITlka & HITlka1) & HAS) &
                     HITlkin) & HITlkin1) & Hdtb) & Hdtpn) & Hdtpapb) & Hftmin) & Hftmax) &
                     Hmhr) & Hmlpn)  & Hmlpn') & HITlkb) & HITlkin2) & Hgv)".
            iCombine "HAS HITlkin Hmhr Hftmin Hftmax Hmlpn Hdtpn Hdtpapb
                      Hmlpn' HITlka HITlkb HITlkin1 Hdtb HITlka1 HITlkin2 Hgv"
              as "Hnode_inv_pred".
            iVST.
            rewrite Hx.
            rewrite <- 10sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            iIntros "H".
            iPoseProof (release_root with "H") as "H"; repeat done.
         }
        (* proving |--  traverse_inv *)
        Exists pa pn ga locka. entailer!. by iIntros "_".
    + (* if (_b == (0)) *)
      forward_if.
      pose proof (Int.one_not_zero); easy.
      Intros.
      forward.
      forward.
      destruct Hz as (Hz & Ht).
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      rewrite Hlk.
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      { go_lower; apply push_lock_back; auto. }
      sep_apply (in_tree_duplicate g gb pb lockb).
      Intros.
      (* _release(_t'8);) *)
      forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
      {
        lock_props.
        iIntros "(((((((((((((((HITlkb & HITlkb1) & HAS) & HITlkin) & HITlkin1) & Hdtb) & Hdtpn) & Hdtpapb) & Hftmin) & Hftmax) & Hmhr) & Hmlpn) & Hmlpn') & HITlka) & HITlkin2) & Hgv)".
        iCombine "HAS HITlkin Hmhr Hftmin Hftmax Hmlpn Hdtpn Hdtpapb  Hmlpn' HITlka HITlkb  HITlkin1 Hdtb HITlkb1 HITlkin2 Hgv" as "Hnode_inv_pred".
        iVST.
        rewrite Hz.
        rewrite <- 10sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        iIntros "H".
        iPoseProof (release_root with "H") as "H"; repeat done.
      }
      (* proving |--  traverse_inv *)
      Exists pb pn gb lockb. entailer!. by iIntros "_".
    + destruct H12 as (Hx & Hy).
      forward_if.
      assert_PROP (r.1.1.2 = lock_in) as Hlk. { sep_apply in_tree_equiv; entailer !. }
      rewrite Hlk.
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      { go_lower; apply push_lock_back; auto. }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                                (!!( y = (false, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (false, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm". iFrame "Hm".
        iModIntro.
        iExists _. by iFrame "Hm".
      }
      Intros y.
      forward.
      forward.
      unfold traverse_inv_2, node_lock_inv_pred_1, node_rep_1, tree_rep_R_1.
      Exists false pn Ews g_in r.
      subst.
      Exists ga gb v1 pa pb locka lockb.
      rewrite ! Int.signed_repr in Hy; auto.
      subst.
      entailer !. by iIntros "_".
      pose proof Int.one_not_zero; easy.
    }
    pose proof Int.one_not_zero; contradiction.
   + assert_PROP (r.1.1.2 = lock_in) as Hlk. { sep_apply in_tree_equiv; entailer !. }
     rewrite Hlk.
     assert_PROP(is_pointer_or_null r.1.1.1) by entailer !.
     gather_SEP (field_at _ t_struct_tree_t (DOT _t) _ pn)
                (field_at _ _ (DOT _min) _ pn)
                (field_at _ _ (DOT _max) _ pn)
                (malloc_token Ews t_struct_tree_t pn)
                (in_tree g g_in pn lock_in) (tree_rep_R r.1.1.1 r.1.2 r.2 g).
     viewshift_SEP 0 (node_rep pn g g_in r).
     {
       go_lower. unfold node_rep. rewrite Hlk.
       iIntros "(((((? & ?) & ?) & ?) & ?) & ?)".
       by iFrame.
     }
     Intros.
     forward_if.
     pose proof (Int.one_not_zero).
     assert (Int.zero <> Int.one); auto; easy.
     forward.
     forward.
     (* push back lock into invariant *)
     gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
     viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
     { go_lower; apply push_lock_back; auto. }
     forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
     {
       lock_props.
       iIntros "((((((HAS & HITlkin) & Hnode) & Hdtb) & Hmhr) & HITlkin1) & Hgv)".
       iCombine "HAS HITlkin Hmhr Hnode HITlkin1 Hdtb Hgv" as "Hnode_inv_pred".
       iVST.
       rewrite <- 3sepcon_assoc; rewrite <- 2sepcon_comm.
       apply sepcon_derives; [| cancel_frame].
       unfold atomic_shift; iIntros "(((AU & #HITlkin) & Hmhr) & Hnode)";
            iAuIntro; unfold atomic_acc; simpl.
       iMod "AU" as (m) "[Hm HClose]".
       iModIntro.
       iExists tt.
       iAssert (node_lock_inv_pred g pn g_in r)
                 with "[$Hmhr $Hnode]" as"Hnode_Iinv".
       iPoseProof (in_tree_inv' g g_in g_root pn lock_in _ r
                         with "[$HITlkin $Hnode_Iinv $Hm]") as "(HI1 & HI2)".
       iSplitL "HI1"; iFrame.
       iSplit.
       {
         iIntros "(Hnode_Iinv & InvLock)".
         iSpecialize ("HI2" with "InvLock").
         iDestruct "HClose" as "[HClose _]".
         iFrame.
         iSpecialize ("HClose" with "HI2"); auto.
       }
       iIntros (_) "(H & _)".
       iSpecialize ("HI2" with "H").
       iDestruct "HClose" as "[HClose _]".
       by iSpecialize ("HClose" with "HI2").
    }
    forward.
    Exists n pn g_root lock.
    sep_apply (in_tree_duplicate g g_root n).
    entailer !.
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       + forward.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl.
         entailer !.
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
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
