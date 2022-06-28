Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template.
Require Import bst.bst_template_lib.
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

(*change M into t *)


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

(*
 findnext_spec:
          {x \in range  /\ ...} findNext(pn *pn, int x, void *value)
          {v. ((v = 1 /\ ....) \/ (v = 0 /\  ...)) /\  ... }
 *)

Definition tree_rep_1 p (sh :share):=
  EX (tp pa pb vp: val) (xp : Z),
  field_at sh (t_struct_tree_t) [StructField _t] tp p *
  data_at sh t_struct_tree (Vint (Int.repr xp), (vp, (pa, pb))) tp *
  (!!(is_pointer_or_null pa /\ is_pointer_or_null pb) && emp).

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

(*
traverse_spec:
          < ...  | bst t> traverse(pn *pn, int x, void *value)
          <v. bst t /\ lock_inv >
*)

Definition pn_rep_1 (g : gname) (g_root : gname) (sh : share) (pn n: val) :=
  EX (p :val),
  data_at sh (t_struct_pn) (p, n) pn *
  my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock : val) (nb : val) :=
  EX (np: val), data_at sh (tptr (t_struct_tree_t)) np nb *
                ltree g g_root sh (fst (Share.split gsh1)) np lock *
                my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

Definition node_lock_inv_new sh g p gp lock tp r :=
   (field_at Ews t_struct_tree_t (DOT _t) tp p *
    malloc_token Ews t_struct_tree_t p * in_tree g gp * tree_rep_R tp r.1 r.2 g) *
    my_half gp sh r *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
    malloc_token Ews tlock lock *
    |> lock_inv lsh2 lock (node_lock_inv sh g p gp lock).

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType (val * val * share * val  * Z *
                                        val * globals * gname * gname))
          OBJ M INVS base.empty base.top
  WITH  b, n, sh, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP ( writable_share sh;
       and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
       is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
  SEP  (mem_mgr gv; node_lock_inv (Share.split gsh1).1 g n g_root lock;
       pn_rep_1 g g_root Ews b n) | (tree_rep g g_root M)
  POST[ tint ]
  EX pt : bool * ( val * (val * (val * (share * (gname * node_info)) )))%type,
  PROP ()
       (* (false, (p1, (pt, ( lock_in, (gsh, (g_in, r)))))) *)
       LOCAL (temp ret_temp (Val.of_bool pt.1))
        SEP (mem_mgr gv; !!(key_in_range x (pt.2.2.2.2.2.2).1 = true ∧
              (if (fst pt) : bool
               then ((pt.2.2.2.2.2.2).2 = Some None /\ pt.2.2.1 = nullval)
               else (pt.2.2.1 <> nullval /\
               (exists (v1: val) (g1 g2: gname),
                   (pt.2.2.2.2.2.2).2 = Some (Some(x, v1, g1, g2)))))) && emp;
             (node_lock_inv_new (pt.2.2.2.2.1) g (pt.2.1)
                                             (pt.2.2.2.2.2.1)
                                             (pt.2.2.2.1)
                                             (pt.2.2.1)
                                             (pt.2.2.2.2.2.2) *
                        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b *
                        my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None))
             )
       | (tree_rep g g_root M).


Program Definition insertOp_spec :=
  DECLARE _insertOp
          ATOMIC TYPE (rmaps.ConstType (bool * val * val * val * share * gname * node_info *
                                       val *  share  * Z *  val * globals * gname * gname))
          OBJ M INVS base.empty base.top
   WITH fl, p, pt, lock_in, gsh, g_in, r, b, sh, x, v, gv, g , g_root
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP ( readable_share sh; and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
         is_pointer_or_null v )
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP  (mem_mgr gv;
                 !!(fl = true /\ key_in_range x r.1 = true ∧
                    r.2 = Some None /\ pt = nullval) && emp;
                    (node_lock_inv_new gsh g p g_in lock_in pt r *
                     data_at Ews t_struct_pn (p, p) b *
                     my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None)))
                | (tree_rep g g_root M)
  POST[ tvoid ]
  PROP ()
        LOCAL ()
        SEP (mem_mgr gv;
             EX pt : bool * (val * (val * (val * (share * (gname * node_info)))))%type,
                 !!( pt.1 = true /\ pt.2.2.1 <> nullval) &&
                   emp * (node_lock_inv_new (pt.2.2.2.2.1) g (pt.2.1)
                                             (pt.2.2.2.2.2.1)
                                             (pt.2.2.2.1)
                                             (pt.2.2.1)
                                             (pt.2.2.2.2.2.2)   *
                        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b *
                        my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None)))
            | (tree_rep g g_root (<[x:=v]>M)).


Program Definition insert_spec :=
  DECLARE _insert2
  ATOMIC TYPE (rmaps.ConstType (val *  share * val * Z * val * globals * gname * gname))
  OBJ M INVS base.empty base.top
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

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.


Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec; surely_malloc_spec; insert_spec; insertOp_spec; traverse_spec; findnext_spec;
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
intros. unfold tree_rep_R. destruct (eq_dec p nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec tp nullval). entailer!.
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

(* invariants for traverse *)
Definition traverse_inv (b : val) (lock: val)
             (sh: share) (x: Z) (v: val) (g_root: gname)
             gv (inv_names : invG) (g : gname) AS : environ -> mpred :=
  (EX (r : node_info) (pnN : val) (gN_in : gname) (lockN_in : val) (gsh : share),
            PROP (key_in_range x (fst r) = true)
                 LOCAL (temp _flag (vint 1); temp _pn__2 b;
                       temp _x (vint x); temp _value v; gvars gv)
                 SEP (pn_rep_1 g g_root sh b pnN;
                     (*pn->n*)
                     node_rep pnN g gN_in r;
                     field_at lsh2 t_struct_tree_t [StructField _lock] lockN_in pnN;
                     my_half gN_in gsh r; malloc_token Ews tlock lockN_in;
                     |> lock_inv lsh2 lockN_in (node_lock_inv gsh g pnN gN_in lockN_in);
                     AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b: val) (p: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: val) (gsh: share) (sh: share) (r: node_info) (x: Z) :=
  data_at sh (t_struct_pn) (p, p) b *
  my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None) *
  field_at Ews t_struct_tree_t (DOT _t) nullval p *
  malloc_token Ews t_struct_tree_t p * in_tree g g_in *
  field_at lsh2 t_struct_tree_t (DOT _lock) lock_in p *
  my_half g_in gsh r * (!!(key_in_range x r.1 = true /\ r.2 = Some None) && emp) *
  malloc_token Ews tlock lock_in * lock_inv lsh2 lock_in (node_lock_inv gsh g p g_in lock_in).

Definition traverse_inv_2 (b: val) (p: val) (tp: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: val) (gsh: share) (sh: share) (r: node_info) (x: Z):=
  EX (v1: val) (pa: val) (pb: val) (ga: gname) (gb: gname) (locka: val) (lockb: val),
  data_at sh (t_struct_pn) (p, p) b *
  field_at Ews t_struct_tree_t (DOT _t) tp p *
  data_at Ews t_struct_tree (vint x, (v1, (pa, pb))) tp *
  my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None) *
  malloc_token Ews t_struct_tree_t p *
  in_tree g g_in * malloc_token Ews t_struct_tree tp *
  ltree g ga lsh1 gsh1 pa locka * ltree g gb lsh1 gsh1 pb lockb *
  field_at lsh2 t_struct_tree_t (DOT _lock) lock_in p *
  my_half g_in gsh r *
    (!!(key_in_range x r.1 = true ∧ r.2 = Some (Some (x, v1, ga, gb)) ∧
        (Int.min_signed ≤ x ≤ Int.max_signed)%Z /\
          is_pointer_or_null pa /\ is_pointer_or_null pb /\ is_pointer_or_null v1) && emp) *
  malloc_token Ews tlock lock_in *
  lock_inv lsh2 lock_in (node_lock_inv gsh g p g_in lock_in).

(*Proving traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  unfold pn_rep_1, ltree.
  Intros p.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  forward_loop (traverse_inv b lock Ews x v g_root gv inv_names g AS)
               break:
    (EX (flag : bool) (q: val) (pt: val) (gsh: share) (g_in: gname) (lock_in : val) (r : node_info),
                PROP() LOCAL(temp _flag (Val.of_bool flag))
                      SEP((if flag
                          then ((traverse_inv_1 b q g g_root g_in lock_in gsh Ews r x) *
                                  (!!(pt = nullval) && emp))
                          else ((traverse_inv_2 b q pt g g_root g_in lock_in gsh Ews r x) *
                                  (!!(pt <> nullval) && emp))) *
                           Q (flag, (q, (pt, (lock_in, (gsh, (g_in, r)))))) * mem_mgr gv)).
  - (*pre-condition*)
    unfold traverse_inv.
    unfold node_lock_inv at 1.
    rewrite selflock_eq.
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
    (* if *)
    forward_if.
    + (* if (pn->p->t == NULL) *)
      destruct (eq_dec tp nullval).
      entailer !.
      Intros ga gb x0 v1 pa pb locka lockb.
      entailer !.
    + rewrite H3.
      (*  Q (true, (p1, (p1, (lock_in, (gsh, g_in))))) *)
      gather_SEP AS (my_half g_in _ _) (in_tree g _).
      viewshift_SEP 0 (EX y, Q y * (!!( y = (true, (pn, (nullval, (lock_in, (gsh, (g_in, r)))))))
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
        simpl in *.
        destruct succ.
        destruct H8 as [Hpa | Hpb].
        * unfold ltree.
          destruct Hpa as (Hpa & Hx).
          Intros.
          forward.
          subst n'.
          forward.
          (*acquire*)
          forward_call (locka, lsh1, node_lock_inv gsh1 g pa ga locka).
          unfold node_lock_inv at 2.
          rewrite selflock_eq.
          unfold node_lock_inv_pred at 1.
          unfold sync_inv at 1.
          Intros a.
          rewrite node_rep_def.
          Intros tp1.
          forward.
          forward.
          gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half ga gsh1 a); unfold AS.
          sep_apply (
              in_tree_left_range (bool * (val * (val * (val * (share * (gname *
                                 (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * (share * (gname *
                                 (range * option (option ghost_info))))))))),
              tree_rep g g_root M * emp) Q x x0 g g_root inv_names v1 g_in ga gb).
          rewrite ! Int.signed_repr in Hx; by rep_lia.
          Intros ba.
          (*release*)
          forward_call (lock_in, lsh2,
                        node_lock_inv_pred gsh g pn g_in lock_in,
                        node_lock_inv gsh g pn g_in lock_in).
          {
            lock_props.
            unfold node_lock_inv at 4.
            fold (node_lock_inv gsh1 g pa ga locka).
            rewrite selflock_eq.
            unfold node_lock_inv_pred at 1.
            unfold sync_inv at 1.
            Exists r.
            rewrite node_rep_def.
            Exists tp; cancel.
            unfold tree_rep_R at 2.
            rewrite -> if_false by auto.
            Exists ga gb x0 v1 pa pb locka lockb.
            unfold ltree at 1; entailer !.
            repeat rewrite later_sepcon.
            entailer !.
            unfold node_lock_inv at 3.
            unfold ltree.
            entailer !.
            repeat rewrite later_sepcon.
            cancel.
          }
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
          Intros.
          forward.
          subst n'.
          forward.
          (*acquire*)
          forward_call (lockb, lsh1, node_lock_inv gsh1 g pb gb lockb).
          unfold node_lock_inv at 2.
          rewrite selflock_eq.
          unfold node_lock_inv_pred at 1.
          unfold sync_inv at 1.
          Intros a.
          rewrite node_rep_def.
          Intros tp1.
          forward.
          forward.
          gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half gb gsh1 a); unfold AS.
          sep_apply (in_tree_right_range (bool * (val * (val * (val * (share * (gname *
                                         (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * (share * (gname *
                                         (range * option (option ghost_info))))))))),
              tree_rep g g_root M * emp) Q x x0 g g_root inv_names v1 g_in ga gb).
          rewrite ! Int.signed_repr in Hx; by rep_lia.
          Intros ba.
          (*release*)
          forward_call (lock_in, lsh2,
                        node_lock_inv_pred gsh g pn g_in lock_in,
                        node_lock_inv gsh g pn g_in lock_in).
          {
            lock_props.
            unfold node_lock_inv at 4.
            fold (node_lock_inv gsh1 g pb gb lockb).
            rewrite selflock_eq.
            unfold node_lock_inv_pred at 1.
            unfold sync_inv at 1.
            Exists r.
            rewrite node_rep_def.
            Exists tp; cancel.
            unfold tree_rep_R at 2.
            rewrite -> if_false by auto.
            Exists ga gb x0 v1 pa pb locka lockb.
            unfold ltree at 1; entailer !.
            repeat rewrite later_sepcon.
            entailer !.
            unfold node_lock_inv at 3.
            unfold ltree.
            entailer !.
            repeat rewrite later_sepcon.
            cancel.
          }
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
    unfold traverse_inv_1, traverse_inv_2; unfold node_lock_inv_new.
    destruct flag.
    Intros. (* will have key_in_range x r.1 = true for post condition*)

    + (* flag = 1 *)
      Intros.
      Exists (true, (p1, (nullval, (lock_in, (gsh , (g_in, r)))))).
      simpl in *.
      unfold tree_rep_R.
      erewrite eq_dec_refl. (* will have key_in_range x r.1 = true *)
      entailer !.
    + (* flag = 0*)
      Intros v1 pa pb ga gb locka lockb.
      Intros.
      Exists (false, (p1, (pt, (lock_in, (gsh, (g_in, r)))))).
      simpl in *.
      entailer !.
      exists v1, ga, gb; auto.
      unfold tree_rep_R.
      destruct (eq_dec).
      * contradiction.
      * Exists ga gb x v1 pa pb locka lockb.
        unfold node_lock_inv; entailer !.
Qed.


(* proving insertOp function *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  set (AS := atomic_shift _ _ _ _ _).
  Intros.
  simpl.
  unfold node_lock_inv_new.
  subst pt.
  unfold tree_rep_R.
  destruct (eq_dec nullval nullval); last contradiction.
  Intros.
  forward_call (t_struct_tree_t, gv).
  Intros p1'.
  forward_call (t_struct_tree_t, gv).
  Intros p2'.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer!.
  simpl.
  forward. (* p1->t=NULL *)
  assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer!.
  simpl.
  forward_call (tlock, gv).
  { simpl. rewrite Z.max_r. repeat (split; auto); rep_lia. rep_lia. }
  Intros l1.
  unfold tlock.
  destruct r as [p1 o].
  destruct p1.
  simpl in H3; subst.
  gather_SEP AS (my_half g_in _  _)  (in_tree g  _).
  viewshift_SEP 0
    ( Q
      * (EX g1 g2:gname, EX n1 n2:number,
           (!!(key_in_range x (n1,n2) = true) &&
              my_half g_in gsh (n1, n2, Some (Some(x,v,g1,g2))) *
              in_tree g g_in *
              my_half g1 gsh1 (n1, Finite_Integer x, Some (@None ghost_info)) *
              my_half g2 gsh1 (Finite_Integer x, n2, Some (@None ghost_info)) *
              in_tree g g1 * in_tree g g2))).
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
      { symmetry; rewrite merge_comm; apply merge_range_incl'; auto. }
      destruct Hincl as [_ Hincl]; simpl in Hincl.
      inv Hincl; try constructor.
      inv H10.
    }
    iIntros "(H1 & H2)".
    instantiate (1 := x).
    instantiate (1:= v).
    iSpecialize ("H" with "[$H2 $Hmy]").
    iSplit; auto.
    {
      iPureIntro.
      split; auto.
      eapply key_in_range_incl; eassumption. }
      iDestruct "H" as "(((((? & ?) & ?) & ?) & ?) & ?)".
      iModIntro. rewrite exp_sepcon1; iExists tt.
      rewrite !exp_sepcon2; iExists g1.
      rewrite !exp_sepcon2; iExists g2.
      rewrite !exp_sepcon2; iExists r.1.
      rewrite !exp_sepcon2; iExists r.2; destruct r; iFrame.
      iPureIntro; split; auto.
      eapply key_in_range_incl; eassumption.
    }
    Intros g1 g2 n1 n2.
    Typeclasses eauto:= 2.
    forward_call (l1, Ews, node_lock_inv gsh1 g p1' g1 l1).
    forward. (*p1->lock = l1*)
    rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
    Typeclasses eauto:= 6.
    forward_call (l1, lsh2, node_lock_inv_pred gsh1 g p1' g1 l1, node_lock_inv gsh1 g p1' g1 l1).
    { lock_props.
      unfold node_lock_inv at 4.
      rewrite selflock_eq .
      unfold node_lock_inv_pred at 1.
      unfold sync_inv at 1.
      Exists (n1, Finite_Integer x, Some (@None ghost_info)).
      rewrite node_rep_def.
      Exists nullval.
      unfold_data_at (data_at _ _ _ p1').
      erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
      unfold tree_rep_R.
      simpl.
      unfold node_lock_inv at 2. entailer!.
    }
    forward_call (tlock, gv).
    { simpl.  rewrite Z.max_r. repeat (split; auto); rep_lia. rep_lia. }
    Intros l2.
    forward_call (l2, Ews, (node_lock_inv gsh1 g p2' g2 l2)).
    forward. (*p2->lock = l2*)
    rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
    forward_call (l2, lsh2, node_lock_inv_pred gsh1 g p2' g2 l2, node_lock_inv gsh1 g p2' g2 l2).
    { lock_props.
      unfold node_lock_inv at 5.
      rewrite selflock_eq .
      unfold node_lock_inv_pred at 1.
      unfold sync_inv at 1.
      Exists (Finite_Integer x,n2,Some (@None ghost_info)).
      rewrite node_rep_def.
      Exists nullval.
      unfold_data_at (data_at _ _ _ p2').
      erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
      unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!.
    }
    forward_call (t_struct_tree, gv).
    Intros p'.
    repeat forward.
    unfold node_lock_inv_new.
    (* (false, (p1, (pt, ( lock_in, (gsh, (g_in, r)))))) *)
    Exists (true, (p, (p', (lock_in, (gsh, (g_in, (n1, n2, Some (Some (x, v, g1, g2))) )))))) .
    entailer !.
    unfold tree_rep_R.
    assert_PROP (p' <> nullval) by entailer!.
    rewrite -> if_false.
    Exists g1 g2 x v p1' p2' l1 l2.
    unfold ltree.
    entailer !.
    rewrite <- later_sepcon.
    setoid_rewrite sepcon_comm at 1.
    setoid_rewrite sepcon_comm at 3.
    setoid_rewrite sepcon_comm at 6.
    rewrite <- sepcon_assoc.
    rewrite <- sepcon_assoc.
    rewrite <- sepcon_assoc.
    apply now_later.
    auto.
Qed.

(* proving insert function *)
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
  Check λ M : gmap key val, tree_rep g g_root M.
  forward_call (lock, sh, (node_lock_inv (fst (Share.split gsh1)) g np g_root lock)).
  set Q1:= fun (b : (bool * ( val * (val * (val * (share * (gname * node_info))))))%type) =>
              if b.1
              then AS
              else AS.
  (* traverse(pn, x, value) *)
   forward_call (nb, np, sh,  lock, x, v, gv, g, g_root, Q1, inv_names).
   {
     unfold AS, pn_rep_1.
     Exists Vundef.
     entailer !.
     rewrite !sepcon_assoc sepcon_comm.
     rewrite !sepcon_assoc sepcon_comm.
     rewrite ->  sepcon_assoc; apply sepcon_derives; [|cancel].
     iIntros "AS".
     unfold atomic_shift.
     iAuIntro.
     rewrite /atomic_acc /=.
     iMod "AS" as (m) "Hm".
     iDestruct "Hm" as "[H1 H2]".
     iModIntro.
     iExists m.
     iFrame "H1".
     iSplit; iFrame.
     { iApply bi.and_elim_l; iFrame. }
     {
       iPoseProof (bi.and_elim_l with "H2") as "H2".
       iIntros (pt) "[H H1]".
       iMod ("H2" with "H") as "H".
       iModIntro.
       unfold Q1.
       destruct (decide (pt.1 = true)).
       { rewrite e; iFrame. }
       { apply not_true_is_false in n; rewrite n; iFrame. }
     }
   }
   Intros pt.
   destruct pt as (fl & (p1 & (tp & (lock_in & (gsh & (g_in & (x0 & r))))))).
   simpl in H2, H3.
   destruct fl.
   - destruct H3.
     subst tp.
     forward_if (PROP ( )
                 LOCAL (temp _t'2 Vtrue; temp _t'8 lock; temp _t'7 np; temp _t'9 np;
                        temp _pn__2 nb; gvars gv; temp _t b; temp _x (vint x); temp _value v)
                 SEP (Q; mem_mgr gv;
                      EX pt : bool * (val * (val * (val * (share * (gname * node_info))))),
                      !! (pt.1 = true  /\ pt.2.2.1 <> nullval) && emp *
                         (node_lock_inv_new pt.2.2.2.2.1 g pt.2.1
                           pt.2.2.2.2.2.1 pt.2.2.2.1 pt.2.2.1 pt.2.2.2.2.2.2 *
                         data_at Ews t_struct_pn (pt.2.1, pt.2.1) nb *
                         my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None) *
                         data_at sh (tptr t_struct_tree_t) np b *
                         field_at sh t_struct_tree_t (DOT _lock) lock np *
                         lock_inv sh lock (node_lock_inv (Share.split gsh1).1 g np g_root lock) *
                         malloc_token Ews t_struct_pn nb))).
     + contradiction.
     + (* insertOp(pn, x, value) *)
       forward_call(true, p1, nullval, lock_in, gsh, g_in, (x0, r),
                     nb, sh, x, v, gv, g , g_root, Q , inv_names).
       {
         Intros.
         entailer !.
         unfold Q1.
         simpl.
         unfold AS.
         rewrite !sepcon_assoc.
         apply sepcon_derives; [|cancel].
         iIntros "AS".
         unfold atomic_shift.
         iAuIntro.
         rewrite /atomic_acc /=.
         iMod "AS" as (x1) "Hm".
         iModIntro.
         iDestruct "Hm" as "[H1 H2]".
         iExists x1.
         iFrame "H1".
         iSplit.
         { iApply bi.and_elim_l. iFrame. }
         { iPoseProof (bi.and_elim_r with "H2") as "H2". iFrame. }
      }
      unfold Q1.
      Intros pt.
      destruct pt as (fl2 & (p2 & (tp2 & (lock_in2 & (gsh2 & (g_in2 & r2)))))).
      entailer !.
      Exists (fl2, (p2, (tp2, (lock_in2, (gsh2, (g_in2, r2)))))).
      entailer !.
      cancel.
    + unfold node_lock_inv_new.
      Intros pt.
      destruct pt as (fl2 & (p2 & (tp2 & (lock_in2 & (gsh2 & (g_in2 & r2)))))).
      simpl.
      simpl in H4, H5.
      forward.
      forward.
      (* _release2(_t'4) *)
      unfold tree_rep_R.
      rewrite if_false; auto.
      Intros g1 g2 x1 v1 p1' p2' l1 l2.
      (*  (_release2(_t'4); *)
      forward_call (lock_in2, lsh2, node_lock_inv_pred gsh2 g p2 g_in2 lock_in2,
                     node_lock_inv gsh2 g p2 g_in2 lock_in2).
      {
        lock_props.
        unfold node_lock_inv at 3.
        rewrite selflock_eq.
        unfold node_lock_inv_pred at 1.
        unfold sync_inv at 1.
        destruct r2 as [p o].
        simpl in H6, H9.
        destruct p as [n1 n2].
        Exists (n1, n2, Some (Some(x1, v1, g1, g2))).
        rewrite node_rep_def.
        unfold node_lock_inv.
        Exists tp2; cancel.
        unfold tree_rep_R. 
        assert_PROP (tp2 <> nullval) by entailer!.
        rewrite -> if_false by auto.
        Exists g1 g2 x1 v1 p1' p2' l1 l2.
        unfold ltree.
        entailer !.
        rewrite <- later_sepcon;
          eapply derives_trans;
          [|apply sepcon_derives, derives_refl; apply now_later].
        entailer !.
     }
     gather_SEP Q (my_half _ _ _).
     forward_call (t_struct_pn, nb, gv).
     {
       assert_PROP (nb <> nullval) by entailer !.
       rewrite if_false; auto.
       cancel.
     }
     unfold nodebox_rep.
     entailer !.
     Exists np.
     unfold ltree, node_lock_inv.
     entailer !.
   - (* (_t'6->_value) = _value;) *)
     forward_if (
         PROP ( )
           LOCAL (temp _t'2 Vfalse; temp _t'8 lock; temp _t'7 np; temp _t'9 np; temp _pn__2 nb;
                  gvars gv; temp _t b; temp _x (vint x); temp _value v)
           SEP (Q1 (false, (p1, (tp, (lock_in, (gsh, (g_in, (x0, r))))))); mem_mgr gv; emp;
                field_at Ews t_struct_tree_t (DOT _t) tp p1 *
                  malloc_token Ews t_struct_tree_t p1 * in_tree g g_in *
                  (EX (ga gb : gname) (x1 : Z) (v0 pa pb locka lockb : val),
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
                  field_at lsh2 t_struct_tree_t (DOT _lock) lock_in p1 *
                  malloc_token Ews tlock lock_in *
                  |> lock_inv lsh2 lock_in (node_lock_inv gsh g p1 g_in lock_in);
                data_at Ews t_struct_pn (p1, p1) nb;
                my_half g_root (Share.split gsh1).2 (Neg_Infinity, Pos_Infinity, None);
                data_at sh (tptr t_struct_tree_t) np b;
                field_at sh t_struct_tree_t (DOT _lock) lock np;
                lock_inv sh lock (node_lock_inv (Share.split gsh1).1 g np g_root lock);
                malloc_token Ews t_struct_pn nb)).
     + destruct H3 as ( ?  & v2 & g21 & g22 & ?).
       unfold node_lock_inv_new.
       unfold tree_rep_R.
       rewrite -> if_false by auto.
       simpl in *.
       Intros g1 g2 x1 v1 p1' p2' l1 l2.
       forward.
       forward.
       forward.
       Exists g1 g2 x1 v1 p1' p2' l1 l2.
       entailer !.
     + (* contradiction, since  Int.one = Int.zero *)
       pose proof Int.one_not_zero; contradiction.
     + unfold node_lock_inv_new, tree_rep_R.
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
          iPoseProof (tree_rep_insert with "[$H1 $H2]") as "Hadd". 
          iDestruct "Hadd" as ((n1, n2) o0) "([Hmy H1] & H2)".
          iExists (n1,n2,Some o0).
          iFrame.
          iPoseProof (bi.and_elim_l with "H2") as "H3".
          iPoseProof (bi.and_elim_r with "H3") as "Hnew".
          iIntros "H"; iDestruct "H" as %Hsub.
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
            split. { symmetry; rewrite merge_comm; apply merge_range_incl'; auto. }
            destruct b0, Hincl as [_ Hincl]; simpl in Hincl. inv Hincl; try constructor.
            simpl. inv H14.
          }
          iIntros "(H1 & H2)".
          iSpecialize ("Hnew" with "[$H2 $Hmy]").
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
      forward_call (lock_in, lsh2,
                     node_lock_inv_pred gsh g p1 g_in lock_in,
                     node_lock_inv gsh g p1 g_in lock_in).
      {
        lock_props.
        unfold node_lock_inv at 3.
        rewrite selflock_eq.
        unfold node_lock_inv_pred at 1, sync_inv at 1.
        Exists (n1, n2, Some(Some (x, v, g1, g2))).
        rewrite node_rep_def.
        Exists tp; cancel.
        unfold tree_rep_R.
        rewrite -> if_false by auto.
        Exists g1 g2 x v p1' p2' l1 l2.
        unfold node_lock_inv; entailer!.
      }
      forward_call (t_struct_pn, nb, gv).
      {
       assert_PROP (nb <> nullval) by entailer !.
       rewrite if_false; auto.
       cancel.
      }
      unfold nodebox_rep.
      entailer !.
      Exists np.
      unfold ltree, node_lock_inv.
      entailer !.
Qed.


