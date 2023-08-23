Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
(*
Require Import bst.bst_template_giveup.
Require Import bst.giveup_lib.
 *)
(*
Require Import bst.give_up_template. *)
Require Import bst.bst.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition t_struct_tree := Tstruct _node noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.
(* Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_pn := Tstruct _pn noattr. *)


Class Printable (A: Type) : Type := {
    to_string : A -> string
  }.

Check Printable nat.
Locate Nat.to_string.

#[global]Instance bool_Printable : Printable bool := {
    to_string := fun b => if b then "true" else "false" 
  }.

Compute to_string true.

Definition number2Z (x : number) : Z :=
  match x with
    | Finite_Integer y => y
    | Neg_Infinity => Int.min_signed
    | Pos_Infinity => Int.max_signed
  end.

#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition ghost_ref (g : own.gname) r1 :=
  ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) r1 g.

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.

Lemma ghost_snapshot_intree g (s : gmap gname (val * val))(pn : val)(lock: val)(g_in: gname):
    ghost_ref g s * (!! (s !! g_in = Some(pn, lock)) && seplog.emp)
                      |-- ( in_tree g g_in pn lock * ghost_ref g s).
Proof.
  unfold ghost_ref, ghost_master1, in_tree.
  iIntros "(H & (%Hx & _))".
  rewrite snap_master_join; auto.
  iFrame "H".
  iPureIntro.
  by eapply map_singleton_subseteq_l in Hx.
Qed.

Lemma node_exist_in_tree: forall g (s : gmap gname (val * val)) (pn : val) (lock: val) (g_in:gname),
    in_tree g g_in pn lock * ghost_ref g s |-- !! ( s !! g_in = Some(pn, lock)).
Proof.
 intros.
 unfold ghost_ref, in_tree.
 rewrite -> snap_master_join1.
 iIntros "(% & H)".
 iPureIntro.
 by apply map_singleton_subseteq_l.
Qed.

Class NodeRep : Type := {
  node_rep_R : val -> range -> option (option ghost_info) -> gname -> mpred
  }.
(*
Record BST : Type := {
  ga_val : gname; gb_val : gname; x_val : Z; v_val : val;
  pa_val : val; pb_val : val; locka_val : val; lockb_val : val;
  }.

Check @node_rep_R _ _ _.
Check NodeRep BST.
Check t_struct_tree.
Print  t_struct_tree.
Check Vint (Int.repr _).
 *)

Eval hnf in reptype t_struct_tree.

#[global]Instance my_specific_tree_rep : NodeRep := {
  node_rep_R := fun tp r g_info g =>
    EX (ga gb : gname), EX (x : Z),
      EX (v pa pb : val), EX (locka lockb : val),
      !!(g_info = Some (Some (x, v, ga, gb)) /\
           and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree ((Vint (Int.repr x)), (v, (pa, pb))) tp * 
       malloc_token Ews t_struct_tree tp *
       in_tree g ga pa locka * in_tree g gb pb lockb
}.



Definition node_rep pn g g_current (r : node_info) :=
  !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2) /\
    is_pointer_or_null r.1.1.2) &&
  field_at Ews (t_struct_tree_t) [StructField _t] r.1.1.1 pn *
  field_at Ews (t_struct_tree_t) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
  field_at Ews (t_struct_tree_t) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
   malloc_token Ews t_struct_tree_t pn * in_tree g g_current pn r.1.1.2 *
   node_rep_R r.1.1.1 r.1.2 r.2 g.










#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.




(*

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
*)

(*
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

 *)


(* Spec of inrange function *)
Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, p: val, n: val, tp: val, min: Z, max : Z, sh: share, gv: globals
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

(*Definition spawn_spec := DECLARE _spawn spawn_spec. *)

#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition ghost_ref (g : own.gname) r1 :=
  ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) r1 g.

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Definition tree_rep_R (tp:val) (r:(range)) (g_info: option (option ghost_info)) g : mpred :=
  if eq_dec tp nullval
  then !!(g_info = Some None) && seplog.emp
  else
  EX (ga gb : gname), EX (x : Z), EX (v pa pb : val), EX (locka lockb : val),
     !!(g_info = Some (Some (x, v, ga, gb)) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       (* data_at Ews t_struct_tree (Vint (Int.repr x), (v, (pa, pb))) tp * 
       malloc_token Ews t_struct_tree tp *  *)
       in_tree g ga pa locka * in_tree g gb pb lockb.

Definition tree_rep (g g_root: gname) (m: gmap key val) : mpred :=
   EX (* (tg : ghost_tree) *)  (p: val) (lock: val),
  seplog.emp.

Check tree_rep.

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
       is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv;
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (tree_rep g g_root M)
  POST [ tint ]
  EX  pt: bool * (val * (share * (gname * Z))) %type,
  PROP () (* pt: bool * (val * (share * (gname * node_info))) *)
  LOCAL (temp ret_temp (Val.of_bool pt.1))
  SEP (mem_mgr gv)| (tree_rep g g_root M).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
                             inRange_spec; traverse_spec ]).




(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inRange inRange_spec.
Proof.
  start_function.
  forward.
  forward_if ( PROP ()
                 LOCAL (temp _t'1 (if andb (min <? x) (x <? max) then Val.of_bool true else Val.of_bool false);
                        temp _t'2 (vint min); gvars gv; temp _p p; 
     temp _x (vint x))
     SEP (field_at sh t_struct_node (DOT _min) (vint min) p;
     field_at sh t_struct_node (DOT _max) (vint max) p)).
  - repeat forward. entailer !.
     destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      Check Z.le_ge.
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


(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
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
        iIntros "(H1 & H2)".
        iPoseProof (in_tree_equiv g g_in pn with "[$H1 $H2]") as "%Hx".
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
                               (!!(y = (true, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (true, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      forward.
      unfold traverse_inv_1, node_lock_inv_pred, node_rep, tree_rep_R.
      Exists true pn Ews g_in r.
      Intros.
      rewrite -> if_true; auto.
      subst.
      destruct r.1.2.
      simpl in H5.
      go_lower.
      entailer !.
      iIntros "(H & _)"; iFrame.
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
          pose proof (Int.one_not_zero); easy.
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
                     Hmhr) & Hmlpn) & Hmlpn') & HITlkb) & HITlkin2) & Hgv)".
            iCombine "HAS HITlkin Hmhr Hftmin Hftmax Hmlpn Hdtpn Hdtpapb
                      Hmlpn' HITlka HITlkb HITlkin1 Hdtb HITlka1 HITlkin2 Hgv"
              as "Hnode_inv_pred".
            iVST.
            rewrite Hx.
            rewrite <- 10sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            apply release_root; try repeat (split; auto); auto.
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
        apply release_root; try repeat (split; auto); auto.
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
    pose proof Int.one_not_zero; easy. 
   + assert_PROP (r.1.1.2 = lock_in) as Hlk.
     { sep_apply in_tree_equiv; entailer !. }
     rewrite Hlk.
     assert_PROP(is_pointer_or_null r.1.1.1) by entailer !.
     gather_SEP (field_at _ t_struct_tree_t (DOT _t) _ pn)
                (field_at _ _ (DOT _min) _ pn)
                (field_at _ _ (DOT _max) _ pn)
                (malloc_token Ews t_struct_tree_t pn)
                (in_tree g g_in pn lock_in) (tree_rep_R r.1.1.1 r.1.2 r.2 g).
     viewshift_SEP 0 (node_rep pn g g_in r).
     {
       go_lower.
       unfold node_rep.
       rewrite Hlk.
       iIntros "(((((? & ?) & ?) & ?) & ?) & ?)".
       by iFrame.
     }
     Intros.
     forward_if.
     pose proof (Int.one_not_zero).
     assert (Int.zero <> Int.one); try easy.
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
       iAssert (node_lock_inv_pred g pn g_in r) with "[$Hmhr $Hnode]" as"Hnode_Iinv".
       iPoseProof (in_tree_inv' g g_in g_root pn lock_in _ r
                         with "[$HITlkin $Hnode_Iinv $Hm]") as "(HI1 & HI2)".
       iSplitL "HI1"; iFrame.
       iSplit.
       {
         iIntros "(Hnode_Iinv & InvLock)".
         iSpecialize ("HI2" with "InvLock").
         iDestruct "HClose" as "[HClose _]".
         iFrame.
         by iSpecialize ("HClose" with "HI2").
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