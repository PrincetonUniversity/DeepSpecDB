Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template.
Require Import bst.bst_template_lib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.
Import FashNotation.

(*
Write insert_spec following the template style.
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
          {v. ((v = 1 /\ ....) \/ (v = 0 /\  ...)) /\  ... }
*)


Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof.
  unfold Inhabitant.
  apply empty.
Defined.

Global Instance number_inhabited: Inhabitant number.
Proof.
  unfold Inhabitant.
  apply Pos_Infinity.
Defined.

Definition tree_rep_1 p (sh :share):=
  EX (tp pa pb vp: val) (xp : Z),
  field_at sh (t_struct_tree_t) [StructField _t] tp p *
  data_at sh t_struct_tree (Vint (Int.repr xp), (vp, (pa, pb))) tp *
  (!!(is_pointer_or_null pa /\ is_pointer_or_null pb) && seplog.emp).

Definition pn_rep p n (sh : share) (pn : val) :=
  data_at sh (t_struct_pn) (p, n) pn * tree_rep_1 p sh.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

(*
x < y ==> POST: p = p' /\ n' = p->t->left
x > y ==> POST: p = p' /\ n' = p->t->right
x = y ==> POST: p = p' /\ n' = p
 *)
Definition findnext_spec :=
  DECLARE _findnext
          WITH x: Z, v: val, b: val,
               p: val, n: val, tp: val, tn: val,
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
                         (n' = pb /\ (Z.lt (Int.signed (Int.repr px))  (Int.signed (Int.repr x)))))
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


Definition pn_rep_1 (g : gname) (g_root : gname) (sh : share) (pn n: val) :=
  EX (p :val),
  data_at sh (t_struct_pn) (p, n) pn *
  my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock : lock_handle) (nb : val) :=
  EX (np: val), data_at sh (tptr (t_struct_tree_t)) np nb  *
                 ltree g g_root sh (fst (Share.split gsh1)) np lock * 
                 my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

Definition node_lock_inv_new sh g p gp (lock : lock_handle) tp r :=
   (field_at Ews t_struct_tree_t (DOT _t) tp p *
    malloc_token Ews t_struct_tree_t p *  in_tree g gp * tree_rep_R tp r.1 r.2 g  ) *
    my_half gp sh r *
    field_at lsh2 t_struct_tree_t [StructField _lock] (ptr_of lock) p *
    |> lock_inv lsh2 lock (node_lock_inv sh g p gp lock).

Definition node_lock_inv' sh g p gp lock :=
  (node_lock_inv_pred sh g p gp (ptr_of lock)) *
    lock_inv lsh2 lock (node_lock_inv sh g p gp lock).

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType (val * val * share * lock_handle * Z *
                                        val * globals * gname * gname))
          OBJ M INVS ∅
  WITH  b, n, sh, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP ( writable_share sh;
       and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
       is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
  SEP  (mem_mgr gv; node_lock_inv' (Share.split gsh1).1 g n g_root lock;
       pn_rep_1 g g_root Ews b n) | (tree_rep g g_root M)
  POST[ tint ]
  EX pt : bool * (val * (val * (lock_handle * (share * (gname * node_info)))))%type,
  PROP ()
       (* (false, (p1, (pt, ( lock_in, (gsh, (g_in, r)))))) *)
       LOCAL (temp ret_temp (Val.of_bool pt.1))
        SEP (mem_mgr gv; !!(key_in_range x (pt.2.2.2.2.2.2).1 = true ∧
              (if (fst pt) : bool
               then ((pt.2.2.2.2.2.2).2 = Some None /\ pt.2.2.1 = nullval)
               else (pt.2.2.1 <> nullval /\
               (exists (v1: val) (g1 g2: gname),
                   (pt.2.2.2.2.2.2).2 = Some (Some(x, v1, g1, g2)))))) && seplog.emp;
             (node_lock_inv_new (pt.2.2.2.2.1) g (pt.2.1)
                                             (pt.2.2.2.2.2.1)
                                             (pt.2.2.2.1)
                                             (pt.2.2.1)
                                             (pt.2.2.2.2.2.2) *
                        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b *
                        my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None))
             )
       | (tree_rep g g_root M).

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

Program Definition insert_spec :=
  DECLARE _insert2
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

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; free_atomic_spec;
     surely_malloc_spec; traverse_spec; insertOp_spec; insert_spec; findnext_spec;
                            spawn_spec ]).

Lemma node_rep_saturate_local:
   forall r p g g_current, node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof.
  intros.
  rewrite node_rep_def. Intros tp. entailer!.
Qed.
Global Hint Resolve node_rep_saturate_local: saturate_local.
Lemma node_rep_valid_pointer:
  forall t g g_current p, node_rep p g g_current t |-- valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp. sep_apply field_at_valid_ptr0; auto. entailer!.
Qed.
Global Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_R_saturate_local:
   forall t p g_children g, tree_rep_R p t g_children g |-- !! is_pointer_or_null p.
Proof.
intros. unfold tree_rep_R. change emp with seplog.emp.
destruct (eq_dec p nullval). entailer !.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
  intros. unfold tree_rep_R. change emp with seplog.emp.
  destruct (eq_dec tp nullval). entailer!.
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_valid_pointer : valid_pointer.
Lemma ltree_saturate_local:
  forall g g_root lsh gsh p lock, ltree g g_root lsh gsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Global Hint Resolve ltree_saturate_local: saturate_local.

Ltac logic_to_iris :=
  match goal with |-context[(|==> ?P)%logic] => change ((|==> P)%logic) with ((|==> P)%I) end.

(* proving findnext spec *)
Lemma findNext: semax_body Vprog Gprog f_findnext findnext_spec.
Proof.
  start_function.
  (* int y = pn->p->t->key *)
  forward. (* t1 = pn->p *)
  forward. (* t2 = t1->t *)
  forward. (* y = t2-> key*)
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    forward. (* t1 = pn->p *)
    forward. (* t2 = t1->t *)
    forward. (* t3 = t2->left *)
    forward.
    forward.
    Exists true. Exists pa.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists true. Exists pb.
    entailer !.
    forward.
    Exists false. Exists p.
    entailer !.
Qed.

Definition traverse_inv (b : val) (lock: val)
             (sh: share) (x: Z) (v: val) (g_root: gname)
             gv (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (r : node_info) (pnN : val) (gN_in : gname) (lockN_in : lock_handle) (gsh : share),
            PROP (key_in_range x (fst r) = true)
                 LOCAL (temp _flag (vint 1); temp _pn__2 b;
                       temp _x (vint x); temp _value v; gvars gv)
                 SEP (pn_rep_1 g g_root sh b pnN;
                     (*pn->n*)
                     node_rep pnN g gN_in r;
                     field_at lsh2 t_struct_tree_t [StructField _lock] (ptr_of lockN_in) pnN;
                     my_half gN_in gsh r;
                     |> lock_inv lsh2 lockN_in (node_lock_inv gsh g pnN gN_in lockN_in);
                     AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b: val) (p: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: lock_handle) (gsh: share) (sh: share) (r: node_info) (x: Z) :=
  data_at sh (t_struct_pn) (p, p) b *
  my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None) *
  field_at Ews t_struct_tree_t (DOT _t) nullval p *
  malloc_token Ews t_struct_tree_t p * in_tree g g_in *
  field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p *
  my_half g_in gsh r * (!!(key_in_range x r.1 = true /\ r.2 = Some None) && emp) *
  lock_inv lsh2 lock_in (node_lock_inv gsh g p g_in lock_in).

Definition traverse_inv_2 (b: val) (p: val) (tp: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: lock_handle) (gsh: share) (sh: share) (r: node_info) (x: Z):=
  EX (v1: val) (pa: val) (pb: val) (ga: gname) (gb: gname) (locka lockb: lock_handle),
  data_at sh (t_struct_pn) (p, p) b *
  field_at Ews t_struct_tree_t (DOT _t) tp p *
  data_at Ews t_struct_tree (vint x, (v1, (pa, pb))) tp *
  my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None) *
  malloc_token Ews t_struct_tree_t p *
  in_tree g g_in * malloc_token Ews t_struct_tree tp *
  ltree g ga lsh1 gsh1 pa locka * ltree g gb lsh1 gsh1 pb lockb *
  field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p *
  my_half g_in gsh r *
    (!!(key_in_range x r.1 = true ∧ r.2 = Some (Some (x, v1, ga, gb)) ∧
        (Int.min_signed ≤ x ≤ Int.max_signed)%Z /\
          is_pointer_or_null pa /\ is_pointer_or_null pb /\ is_pointer_or_null v1) && emp) *
  lock_inv lsh2 lock_in (node_lock_inv gsh g p g_in lock_in).

(*Proving traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  unfold pn_rep_1, ltree.
  Intros p.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  forward_loop (traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS)
               break:
    (EX (flag : bool) (q: val) (pt: val) (gsh: share) (g_in: gname)
       (lock_in : lock_handle) (r : node_info),
                PROP() LOCAL(temp _flag (Val.of_bool flag))
                      SEP((if flag
                          then ((traverse_inv_1 b q g g_root g_in lock_in gsh Ews r x) *
                                  (!!(pt = nullval) && emp))
                          else ((traverse_inv_2 b q pt g g_root g_in lock_in gsh Ews r x) *
                                  (!!(pt <> nullval) && emp))) *
                           Q (flag, (q, (pt, (lock_in, (gsh, (g_in, r)))))) * mem_mgr gv)).
  - (*pre-condition*)
    unfold traverse_inv, node_lock_inv'.
    unfold node_lock_inv at 1.
    unfold node_lock_inv_pred at 1.
    unfold sync_inv.
    Intro r.
    destruct r as [p1 o1].
    sep_apply (my_half_range_inf g_root
                                 (Share.split gsh1).1 (Share.split gsh1).2 p1
               (Neg_Infinity, Pos_Infinity)).
    Exists (Neg_Infinity, Pos_Infinity, o1) n g_root lock (fst (Share.split gsh1)).
    rewrite node_rep_def.
    Intros tp.
    unfold node_lock_inv.
    rewrite node_rep_def.
    Exists tp.
    unfold pn_rep_1.
    Exists p.
    unfold ltree.
    unfold node_lock_inv.
    entailer !.
    sep_apply (range_incl_tree_rep_R tp p1 (Neg_Infinity, Pos_Infinity) o1 g); auto.
  - (*go deeply into loop*)
    unfold traverse_inv.
    Intros r pn g_in lock_in gsh.
    (* rewrite node_rep_def.*)
    unfold pn_rep_1, tree_rep_1.
    Intros p1.
    (* pn->p = pn->n; *)
    forward.
    forward.
    forward.
    rewrite node_rep_def.
    Intros tp.
    assert_PROP(is_pointer_or_null tp) by entailer !.
    unfold tree_rep_R.
    forward.
    change emp with seplog.emp.
    (* if *)
    forward_if.
    + (* if (pn->p->t == NULL) *)
      destruct (eq_dec tp nullval).
      entailer !.
      Intros ga gb x0 v1 pa pb locka lockb.
      entailer !.
    + rewrite H3. (*  Q (true, (p1, (p1, (lock_in, (gsh, g_in))))) *)
      gather_SEP AS (my_half g_in _ _) (in_tree g _).
      viewshift_SEP 0 (EX y, Q y *
                               (!!( y = (true, (pn, (nullval, (lock_in, (gsh, (g_in, r)))))))
                                    && (in_tree g g_in * my_half g_in gsh r))).
      {
        go_lower.
        apply sync_commit_same.
        intro t. unfold tree_rep at 1. Intros tg.
        sep_apply node_exist_in_tree; Intros.
        sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H8).
        Intros r0.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists r0. unfold public_half'; cancel.
        apply imp_andp_adjoint.
        Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists (true, (pn, (nullval, (lock_in, (gsh, (g_in, r))))));  simpl; entailer !.
        unfold tree_rep.
        Exists tg.
        cancel.
        rewrite <- wand_twice.
        sep_apply wand_frame_elim.
        sep_apply wand_frame_elim''.
        entailer !.
      }
      forward. (*break*)
      erewrite eq_dec_refl.
      Intros pt1.
      unfold traverse_inv_1.
      Exists true pn nullval gsh g_in lock_in r.
      entailer !.
    + (* if (pn->p->t != NULL) *)
      rewrite -> if_false by auto.
      Intros ga gb x0 v1 pa pb locka lockb.
      forward_call(x, v, b, pn, pn, tp, tp, pa, pb, x0, v1, Ews, gv).
      {
        Intros succ.
        forward_if.
        (* flag = 0 *)
        forward.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (EX y, Q y *
                               (!!( y = (false, (pn, (tp, (lock_in, (gsh, (g_in, r)))))))
                                    && (in_tree g g_in * my_half g_in gsh r))).
        {
          go_lower.
          apply sync_commit_same.
          intro t. unfold tree_rep at 1. Intros tg.
          sep_apply node_exist_in_tree; Intros.
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H14).
          Intros r0.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists r0. unfold public_half'; cancel.
          apply imp_andp_adjoint.
          Intros.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists (false, (pn, (tp, (lock_in, (gsh, (g_in, r))))));  simpl; entailer !.
          unfold tree_rep. Exists tg.
          cancel.
          rewrite <- wand_twice.
          sep_apply wand_frame_elim.
          sep_apply wand_frame_elim''.
          entailer !.
        }
        (*break*)
        forward.
        (* will need to provide PROP(...) RETURN(...) SEP(...) *)
        {
          destruct succ as (succ & n').
          simpl in H7, H8.
          destruct succ.
          destruct H8 as [Hpa | Hpb];
          apply Int.one_not_zero in H9; contradiction.
          Intros pt1.
          (* n' = pn *)
          destruct H8 as (Hpn & Hpx).
          Exists false pn tp gsh g_in lock_in r.
          unfold traverse_inv_2.
          Exists v1 pa pb ga gb locka lockb.
          rewrite ! Int.signed_repr in Hpx; subst; auto.
          entailer !.
          cancel.
        }
        (* b != 0 *)
        destruct succ as (succ & n').
        destruct succ.
        destruct H8 as [Hpa | Hpb].
        * unfold ltree.
          destruct Hpa as (Hpa & Hx).
          simpl in Hpa.
          simpl.
          Intros.
          forward.
          subst n'.
          forward.
          (*acquire*)
          forward_call acquire_inv_simple (lsh1, locka, node_lock_inv gsh1 g pa ga locka).
          Intros.
          forward.
          gather_SEP (lock_inv lsh1 locka (node_lock_inv gsh1 g pa ga locka))
            (node_lock_inv gsh1 g pa ga locka).
          unfold node_lock_inv at 1.
          unfold node_lock_inv at 1.
          sep_apply self_part_eq.
          assert (lsh2 <> Share.bot).
          { apply readable_not_bot. apply readable_lsh2. }
          auto.
          unfold node_lock_inv_pred at 3.
          unfold sync_inv.
          Intros a.
          rewrite node_rep_def.
          Intros tp1.
          forward.
          gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half ga gsh1 a); unfold AS.
          viewshift_SEP 0 (atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
                             (λ (M : gmap key val) (_ : bool *
                                       (val * (val * (lock_handle * (share * (gname * node_info)))))),
               fold_right_sepcon [tree_rep g g_root M]) 
                             Q * my_half g_in gsh r *
                             (EX ba, !! (less_than_equal ba r.1.1 = true /\
                range_incl a.1 (ba, Finite_Integer x0) = true) &&
            (in_tree g g_in * my_half ga gsh1 (ba, Finite_Integer x0, a.2)))).
          {
            go_lower.
            apply (in_tree_left_range (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (*release*)
          forward_call release_self (lsh2, lock_in,
                    node_lock_inv_pred gsh g pn g_in (ptr_of lock_in)).
          {
            unfold node_lock_inv.
            cancel.
            unfold node_lock_inv_pred at 4.
            unfold sync_inv.
            Exists r.
            rewrite node_rep_def.
            Exists tp.
            cancel.
            unfold tree_rep_R at 2.
            rewrite -> if_false; auto.
            Exists ga gb x0 v1 pa pb locka lockb.
            unfold ltree at 1. entailer !.
            repeat rewrite later_sepcon.
            entailer !.
            unfold node_lock_inv.
            cancel.
            unfold ltree.
            unfold node_lock_inv.
            entailer !.
            repeat rewrite later_sepcon.
            entailer !.
          }
          (* proving |--  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS *)
          unfold traverse_inv.
          Exists (ba, Finite_Integer x0, a.2) pa ga locka gsh1.
          unfold node_lock_inv.
          rewrite node_rep_def.
          Exists tp1.
          unfold AS; entailer!.
          {
            unfold key_in_range in *.
            apply andb_true_intro.
            split; simpl.
            - destruct r as ((?, ?), ?).
              apply andb_prop in H1 as [].
              apply (less_than_equal_less_than_trans ba n0 (Finite_Integer x)); auto.
            - apply Zaux.Zlt_bool_true.
              rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          unfold pn_rep_1.
          Exists pn.
          entailer !.
          apply range_incl_tree_rep_R; auto.
       * unfold ltree.
         destruct Hpb as (Hpb & Hx).
         simpl in Hpb.
         simpl.
         Intros.
         forward.
         subst n'.
         forward.
         (*acquire*)
         forward_call acquire_inv_simple (lsh1, lockb, node_lock_inv gsh1 g pb gb lockb).
         Intros.
         forward. 
         gather_SEP (lock_inv lsh1 lockb (node_lock_inv gsh1 g pb gb lockb))
            (node_lock_inv gsh1 g pb gb lockb).
         unfold node_lock_inv at 1.
         unfold node_lock_inv at 1.
         sep_apply self_part_eq.
         assert (lsh2 <> Share.bot). 
         { apply readable_not_bot. 
           apply readable_lsh2.
         }
         auto.
         unfold node_lock_inv_pred at 3.
         unfold sync_inv.
         Intros a.
         rewrite node_rep_def.
         Intros tp1.
         forward.
         gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half gb gsh1 a); unfold AS.
         viewshift_SEP 0 (
             atomic_shift (λ M : gmap key val, tree_rep g g_root M) ⊤ ∅ (λ (M : gmap key val) (_ : bool *
                                       (val * (val * (lock_handle * (share * (gname * node_info)))))),
               fold_right_sepcon [tree_rep g g_root M])  Q *
                      my_half g_in gsh r *
                      (EX ta : number,
                       !! (less_than_equal r.1.2 ta = true
                           ∧ range_incl a.1 (Finite_Integer x0, ta) = true) &&
                       (in_tree g g_in * my_half gb gsh1 (Finite_Integer x0, ta, a.2)))).
         {
           go_lower.
           apply (in_tree_right_range (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (*release*)
          forward_call release_self (lsh2, lock_in,
                    node_lock_inv_pred gsh g pn g_in (ptr_of lock_in)).
          {
            unfold node_lock_inv.
            cancel.
            unfold node_lock_inv_pred at 4.
            unfold sync_inv.
            Exists r.
            rewrite node_rep_def.
            Exists tp.
            cancel.
            unfold tree_rep_R at 2.
            rewrite -> if_false; auto.
            Exists ga gb x0 v1 pa pb locka lockb.
            unfold ltree at 1. entailer !.
            repeat rewrite later_sepcon.
            entailer !.
            unfold node_lock_inv.
            cancel.
            unfold ltree.
            unfold node_lock_inv.
            entailer !.
            repeat rewrite later_sepcon.
            entailer !.
          }
          (* proving |--  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS *)
          unfold  traverse_inv.
          Exists (Finite_Integer x0, ba, a.2) pb gb lockb gsh1.
          unfold node_lock_inv.
          rewrite node_rep_def.
          Exists tp1.
          unfold AS; entailer!.
          {
            unfold key_in_range in *.
            apply andb_true_intro.
            split; simpl.
            - apply Zaux.Zlt_bool_true.
              rewrite ! Int.signed_repr in Hx; by rep_lia.
            - destruct r as ((?, ?), ?).
              apply andb_prop in H1 as [].
              apply (less_than_less_than_equal_trans (Finite_Integer x) n1 ba); auto.
          }
          unfold pn_rep_1.
          Exists pn.
          entailer !.
          apply range_incl_tree_rep_R; auto.
        * (* b == 0*)
          apply repr_inj_unsigned' in H9; rep_lia.
    }
  - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
    Intros flag.
    Intros p1 pt gsh g_in lock_in r.
    forward.
    unfold traverse_inv_1, traverse_inv_2, node_lock_inv_new.
    destruct flag.
    Intros. (* will have key_in_range x r.1 = true for post condition*)
    + (* flag = 1 *)
      Intros.
      Exists (true, (p1, (nullval, (lock_in, (gsh , (g_in, r)))))).
      simpl in *.
      unfold tree_rep_R.
      erewrite eq_dec_refl. (* will have key_in_range x r.1 = true *)
      change emp with seplog.emp.
      entailer !.
    + (* flag = 0*)
      Intros v1 pa pb ga gb locka lockb.
      Intros.
      Exists (false, (p1, (pt, (lock_in, (gsh, (g_in, r)))))).
      simpl in *.
      change emp with seplog.emp.
      entailer !.
      exists v1, ga, gb; auto.
      unfold tree_rep_R.
      destruct (eq_dec).
      * contradiction.
      * Exists ga gb x v1 pa pb locka lockb.
        unfold node_lock_inv; entailer !.
Qed.

Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  Check node_lock_inv.
  start_function.
  change emp with seplog.emp.
  Intros.
   (* (false, (p1, (pt, ( lock_in, (gsh, (g_in, r)))))) *)
  Intros.
  forward_call (t_struct_tree_t, gv).
  Intros p1'.
  forward_call (t_struct_tree_t, gv).
  Intros p2'.
  forward.
  (* unfold_data_at (data_at _ _ _ p1'). *)
  assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer!.
  forward. (* p1->t=NULL *)
  (* unfold_data_at (data_at _ _ _ p2'). *)
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

Lemma make_lock_inv_0_self : forall v N R sh1 sh2, sh1 <> Share.bot -> sepalg.join sh1 sh2 Ews ->
    (atomic_int_at Ews (vint 0) v * R) |-- @fupd mpred (bi_fupd_fupd(BiFUpd := mpred_bi_fupd)) ⊤ ⊤ (EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv sh1 h (R * self_part sh2 h)).
Proof.
  intros.
  iIntros "[a R]".
  iDestruct (atomic_int_isptr with "a") as %Ha.
  iMod (own_alloc(RA := VST.concurrency.cancelable_invariants.share_ghost) with "[$]")
      as (g) "g"; first done.
  setoid_rewrite (own_op(RA := VST.concurrency.cancelable_invariants.share_ghost) _ _ _ _ _ H0);
    iDestruct "g" as "[g1 g2]".
  iMod (inv_alloc with "[a R g2]") as "I";
      [| iExists (v, N, g); unfold lock_inv; simpl; iFrame; auto].
  iIntros "!>"; unfold inv_for_lock.
  iLeft; iExists false; iFrame; auto.
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert2 insert_spec.
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
      unfold pn_rep_1.
      unfold node_lock_inv'.
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
          instantiate (1:= v).
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
        (* erewrite <-  field_at_share_join; eauto. *)
        unfold_data_at (data_at _ _ _ p1').
        unfold_data_at (data_at _ _ _ p2').
        (*already added *)
        assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer !.
        assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer !.
        (**)
        setoid_rewrite <- field_at_share_join with (p:= p1') at 2 ; eauto.
        setoid_rewrite <- field_at_share_join with (p:= p2') at 2 ; eauto.
        unfold tree_rep_R.
        rewrite -> if_true; auto.
        eapply derives_trans. apply fupd_frame_r.
        apply  fupd_mono.
        (* do Iris here to have pieces of things we need *)
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
          iFrame.
          rewrite node_rep_def.
          iExists nullval.
          unfold tree_rep_R.
          rewrite -> if_true; auto.
          iFrame; done.
        }
        iAssert (node_lock_inv_pred gsh1 g p2' g2 lock2) with "[G11x G11z G6 H6 H8]" as "HRLock2".
        {
          unfold node_lock_inv_pred, sync_inv; auto.
          iFrame.
          iExists (Finite_Integer x, n2, Some None).
          iFrame.
          rewrite node_rep_def.
          iExists nullval.
          unfold tree_rep_R.
          rewrite -> if_true; auto.
          iFrame; done.
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
          { apply readable_not_bot, readable_lsh1. }
          eapply lsh1_lsh2_join.
          eapply derives_trans, fupd_mono with
          (P := EX h : lock_handle, !! (ptr_of h = lock1 ∧ name_of h = nroot.@"Nlock1") &&
                                      lock_inv lsh1 h (node_lock_inv_pred gsh1 g p1' g1 lock1 *
                                                         self_part lsh2 h)).
          entailer !.
          iIntros  "H".
          iDestruct "H" as (l1) "H".
          iExists l1.
          unfold node_lock_inv.
          Intros. iVST.
          rewrite pull_left_special0.
          entailer !.
          Intros. iVST.
          eapply derives_trans.
          apply make_lock_inv_0_self with (sh1 := lsh1) (sh2 := lsh2) (N := nroot .@ "Nlock2").
          { apply readable_not_bot, readable_lsh1. }
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
          entailer !.
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
        iApply (bi.later_sep_1).
        iModIntro.
        Intros. iVST.
        destruct H1x.
        destruct H2x.
        rewrite H4.
        rewrite H16.
        entailer !.
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
          unfold node_lock_inv_pred at 2.
          unfold sync_inv.
          destruct r2 as [p o].
          simpl in H7, H10.
          destruct p as [n1 n2].
          Exists (n1, n2, Some (Some(x1, v1, g1, g2))).
          rewrite node_rep_def.
          Exists tp2; cancel.
          unfold tree_rep_R. 
          assert_PROP (tp2 <> nullval) by entailer!.
          rewrite -> if_false by auto.
          Exists g1 g2 x1 v1 p1' p2' l1 l2.
          unfold ltree.
          entailer !.
          rewrite <- later_sepcon.
          eapply derives_trans;
              [|apply sepcon_derives, derives_refl; apply now_later].
          entailer !.
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
                    (EX n1 n2:number,
                      !!(key_in_range x (n1,n2) = true) 
                      && my_half g_in gsh (n1,n2,Some (Some(x,v,g1,g2))) * in_tree g g_in)).
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
            iExists (n1,n2, Some (Some(x,v,g1,g2))).
            apply node_info_incl' in Hsub as [? Heq].
            rewrite H5 in Heq.
            inv Heq.
            iExists (n1,n2, Some (Some (x,v,g1,g2))).
            logic_to_iris.
            instantiate (1 := v).
            instantiate (1:= x).
            iSplit.
            {
              iPureIntro. intros ? Hincl.
              hnf. simpl. destruct (range_incl_join _ _ _ Hincl).
              simpl in *; subst. split; [|reflexivity].
              split.
              { symmetry.
                rewrite puretree.merge_comm; apply merge_range_incl'; auto. }
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
          entailer !.
          unfold node_lock_inv_pred at 4.
          unfold sync_inv.
          Exists (n1, n2, Some(Some (x, v, g1, g2))).
          rewrite node_rep_def.
          Exists tp; cancel.
          unfold tree_rep_R.
          rewrite -> if_false by auto.
          Exists g1 g2 x v p1' p2' l1 l2.
          unfold ltree.
          entailer !.
          rewrite <- later_sepcon;
            eapply derives_trans;
            [|apply sepcon_derives, derives_refl; apply now_later].
          entailer !.
        }
        forward_call (t_struct_pn, nb, gv).
        { assert_PROP (nb <> nullval) by entailer !. rewrite if_false; auto. cancel. }
        unfold nodebox_rep.
        entailer !.
        Exists np.
        cancel.
        unfold ltree, node_lock_inv.
        entailer !.
      }
Qed.
