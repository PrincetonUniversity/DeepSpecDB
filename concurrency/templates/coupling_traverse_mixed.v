Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.mixed_mode.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import VST.atomics.verif_lock_atomic.
From refinedc.project.rc.bst_template_coupling Require Import generated_code generated_spec.
Require Import bst.coupling_lib_mixed.
Require Import VST.floyd.library.
From iris.algebra Require Import auth gset.

Section proof.
  Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct threads._atom_int noattr)}
    `{!inG Σ (ext_order.inclR (authR (gsetUR gname)))} `{!inG Σ (frac_auth.frac_authR nodeR)}.

Definition tree_rep_1 p (sh :share):=
  ∃ (tp pa pb vp: val) (xp : Z),
  field_at sh (t_struct_tree_t) [StructField _t] tp p ∗
  data_at sh t_struct_tree (Vint (Int.repr xp), (vp, (pa, pb))) tp ∗
  (⌜is_pointer_or_null pa /\ is_pointer_or_null pb⌝ ∧ emp).

Definition pn_rep p n (sh : share) (pn : val) :=
  data_at sh (t_struct_pn) (p, n) pn ∗ tree_rep_1 p sh.

(* import findnext's spec from RefinedCC *)
Lemma findnext_defined : exists b, Genv.find_symbol (globalenv prog) _findnext = Some b /\
  Genv.find_funct_ptr (globalenv prog) b = Some (Internal f_findnext).
Proof.
  setoid_rewrite Genv.find_funct_ptr_iff.
  by apply Genv.find_def_symbol.
Qed.

Definition findnext_address : address := (proj1_sig (find_symbol_funct_ptr_ex_sig _ _ _ _ findnext_defined), 0%Z).

Definition findnext_spec := (_findnext, funtype_to_funspec _ f_findnext
  (λ '(ppn, n, k, v, l, r, lock, x), [type.adr2val ppn; Vint (Int.repr x)]) type_of_findnext).

Definition pn_rep_1 (g : gname) (g_root : gname) (sh : share) (pn n: val) :=
  ∃ (p :val),
  data_at sh (t_struct_pn) (p, n) pn ∗
  my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None).

(* sh for field_at, ish for lock_inv, and gsh for node_lock_inv *)
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (sh' : Qp) (lock : lock_handle) (nb : val) :=
  ∃ (np: val), data_at sh (tptr (t_struct_tree_t)) np nb  ∗
                 ltree g g_root sh sh' (1/4) np lock ∗
                 my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None).

Definition node_lock_inv_new sh g p gp (lock : lock_handle) tp r :=
   (field_at Ews t_struct_tree_t (DOT _t) tp p ∗
    malloc_token Ews t_struct_tree_t p ∗ in_tree g gp ∗ tree_rep_R tp r.1 r.2 g) ∗
    my_half gp sh r ∗
    field_at lsh2 t_struct_tree_t [StructField _lock] (ptr_of lock) p ∗
    ▷ lock_inv (1/2) lock (node_lock_inv sh g p gp lock).

Definition node_lock_inv' sh g p gp lock :=
  (node_lock_inv_pred sh g p gp (ptr_of lock)) ∗
    lock_inv (1/2) lock (node_lock_inv sh g p gp lock).

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (ConstType (val * val * share * lock_handle * Z *
                                        val * globals * gname * gname))
          OBJ M INVS ∅
  WITH  b, n, sh, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
  PROP ( writable_share sh;
       and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed));
       is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
  SEP  (mem_mgr gv; node_lock_inv' (1/4) g n g_root lock;
       pn_rep_1 g g_root Ews b n) | (tree_rep g g_root M)
  POST[ tint ]
  ∃ pt : bool * (val * (val * (lock_handle * (Qp * (gname * (range * excl' (option ghost_info)))))))%type,
  PROP ()
       (* (false, (p1, (pt, ( lock_in, (gsh, (g_in, r)))))) *)
       RETURN (Val.of_bool pt.1)
        SEP (mem_mgr gv; ⌜key_in_range x (pt.2.2.2.2.2.2).1 = true ∧
              (if (fst pt) : bool
               then ((pt.2.2.2.2.2.2).2 = Excl' None /\ pt.2.2.1 = nullval)
               else (pt.2.2.1 <> nullval /\
               (exists (v1: val) (g1 g2: gname),
                   (pt.2.2.2.2.2.2).2 = Excl' (Some(x, v1, g1, g2)))))⌝ ∧ emp;
             (node_lock_inv_new (pt.2.2.2.2.1) g (pt.2.1)
                                             (pt.2.2.2.2.2.1)
                                             (pt.2.2.2.1)
                                             (pt.2.2.1)
                                             (pt.2.2.2.2.2.2) ∗
                        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b ∗
                        my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None))
             )
       | (tree_rep g g_root M).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     traverse_spec; findnext_spec; spawn_spec ]).

Lemma node_rep_saturate_local:
   forall r p g g_current, node_rep p g g_current r ⊢ ⌜is_pointer_or_null p⌝.
Proof.
  intros.
  rewrite node_rep_def.
  Intros tp. entailer!.
Qed.
Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer:
  forall t g g_current p, node_rep p g g_current t ⊢ valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp. sep_apply field_at_valid_ptr0; auto. entailer!.
Qed.
Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_R_saturate_local:
   forall t p g_children g, tree_rep_R p t g_children g ⊢ ⌜is_pointer_or_null p⌝.
Proof.
  intros.
  unfold tree_rep_R.
  destruct (eq_dec p nullval). entailer !.
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g ⊢ valid_pointer tp.
Proof.
  intros. unfold tree_rep_R.
  destruct (eq_dec tp nullval). entailer!.
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Hint Resolve tree_rep_R_valid_pointer : valid_pointer.

Lemma ltree_saturate_local:
  forall g g_root lsh ish gsh p lock, ltree g g_root lsh ish gsh p lock ⊢ ⌜isptr p⌝.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Hint Resolve ltree_saturate_local: saturate_local.

Definition traverse_inv (b : val) (lock: val)
             (sh: share) (x: Z) (v: val) (g_root: gname)
             gv (g : gname) AS : environ -> mpred :=
  (∃ (r : node_info) (pnN : val) (gN_in : gname) (lockN_in : lock_handle) (gsh : Qp),
            PROP (key_in_range x (fst r) = true)
                 LOCAL (temp _flag (vint 1); temp _pn__2 b;
                       temp _x (vint x); temp _value v; gvars gv)
                 SEP (pn_rep_1 g g_root sh b pnN;
                     (*pn->n*)
                     node_rep pnN g gN_in r;
                     field_at lsh2 t_struct_tree_t [StructField _lock] (ptr_of lockN_in) pnN;
                     my_half gN_in gsh r;
                     ▷ lock_inv (1/2) lockN_in (node_lock_inv gsh g pnN gN_in lockN_in);
                     AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b: val) (p: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: lock_handle) (gsh: Qp) (sh: share) (r: node_info) (x: Z) :=
  data_at sh (t_struct_pn) (p, p) b ∗
  my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None) ∗
  field_at Ews t_struct_tree_t (DOT _t) nullval p ∗
  malloc_token Ews t_struct_tree_t p ∗ in_tree g g_in ∗
  field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p ∗
  my_half g_in gsh r ∗ (⌜key_in_range x r.1 = true /\ r.2 = Excl' None⌝ ∧ emp) ∗
  lock_inv (1/2) lock_in (node_lock_inv gsh g p g_in lock_in).

Definition traverse_inv_2 (b: val) (p: val) (tp: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: lock_handle) (gsh: Qp) (sh: share) (r: node_info) (x: Z):=
  ∃ (v1: val) (pa: val) (pb: val) (ga: gname) (gb: gname) (locka lockb: lock_handle),
  data_at sh (t_struct_pn) (p, p) b ∗
  field_at Ews t_struct_tree_t (DOT _t) tp p ∗
  data_at Ews t_struct_tree (vint x, (v1, (pa, pb))) tp ∗
  my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None) ∗
  malloc_token Ews t_struct_tree_t p ∗
  in_tree g g_in ∗ malloc_token Ews t_struct_tree tp ∗
  ltree g ga lsh1 (1/2) (1/2) pa locka ∗ ltree g gb lsh1 (1/2) (1/2) pb lockb ∗
  field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p ∗
  my_half g_in gsh r ∗
    (⌜key_in_range x r.1 = true ∧ r.2 = Excl' (Some (x, v1, ga, gb)) ∧
        (Int.min_signed ≤ x ≤ Int.max_signed)%Z /\
          is_pointer_or_null pa /\ is_pointer_or_null pb /\ is_pointer_or_null v1⌝ ∧ emp) ∗
  lock_inv (1/2) lock_in (node_lock_inv gsh g p g_in lock_in).

(*Proving traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  unfold pn_rep_1, ltree.
  Intros p.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  forward_loop (traverse_inv b (ptr_of lock) Ews x v g_root gv g AS)
               break:
    (∃ (flag : bool) (q: val) (pt: val) (gsh: Qp) (g_in: gname)
       (lock_in : lock_handle) (r : node_info),
                PROP() LOCAL(temp _flag (Val.of_bool flag))
                      SEP((if flag
                          then ((traverse_inv_1 b q g g_root g_in lock_in gsh Ews r x) ∗
                                  (⌜pt = nullval⌝ ∧ emp))
                          else ((traverse_inv_2 b q pt g g_root g_in lock_in gsh Ews r x) ∗
                                  (⌜pt <> nullval⌝ ∧ emp))) ∗
                           Q (flag, (q, (pt, (lock_in, (gsh, (g_in, r)))))) ∗ mem_mgr gv)).
  - (*precondition*)
    unfold traverse_inv, node_lock_inv', node_lock_inv at 1, node_lock_inv_pred at 1, sync_inv.
    Intro r.
    destruct r as [p1 o1].
    sep_apply (my_half_range_inf g_root (1/4) (1/4) p1
               (Neg_Infinity, Pos_Infinity)).
    Exists (Neg_Infinity, Pos_Infinity, o1) n g_root lock (1/4)%Qp.
    rewrite node_rep_def.
    Intros tp.
    unfold node_lock_inv.
    rewrite node_rep_def.
    Exists tp.
    unfold pn_rep_1.
    Exists p.
    entailer !.
    sep_apply (range_incl_tree_rep_R tp p1 (Neg_Infinity, Pos_Infinity) o1 g); auto.
  - (*go deeply into loop*)
    unfold traverse_inv.
    Intros r pn g_in lock_in gsh.
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
    + rewrite H3. (*  Q (true, (p1, (p1, (lock_in, (gsh, g_in))))) *)
      gather_SEP AS (my_half g_in _ _) (in_tree g _).
      viewshift_SEP 0 (∃ y, Q y ∗
                               (⌜ y = (true, (pn, (nullval, (lock_in, (gsh, (g_in, r))))))⌝
                                    ∧ (in_tree g g_in ∗ my_half g_in gsh r))).
      { go_lowerx.
        rewrite sep_emp.
        apply sync_commit_same.
        intro t.
        unfold tree_rep at 1.
        Intros tg.
        sep_apply node_exist_in_tree; Intros.
        sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H19).
        Intros r0.
        rewrite -bupd_intro.
        Exists r0. unfold public_half'; cancel.
        apply bi.wand_intro_r.
        Intros.
        rewrite -bupd_intro.
        apply bi.wand_intro_r.
        rewrite -bupd_intro.
        Exists (true, (pn, (nullval, (lock_in, (gsh, (g_in, r))))));  simpl; entailer !.
        unfold tree_rep.
        Exists tg.
        cancel.
        iIntros "(? & H & $ & ? & ?)".
        iPoseProof ("H" with "[$]") as "$".
        iStopProof; entailer !.
        apply bi.affinely_elim_emp. }
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
        viewshift_SEP 0 (∃ y, Q y ∗
                               (⌜ y = (false, (pn, (tp, (lock_in, (gsh, (g_in, r))))))⌝
                                    ∧ (in_tree g g_in ∗ my_half g_in gsh r))).
        { go_lower.
          apply sync_commit_same.
          intro t.
          unfold tree_rep at 1.
          Intros tg.
          sep_apply node_exist_in_tree; Intros.
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H14).
          Intros r0.
          eapply derives_trans; [|apply bupd_intro].
          Exists r0. unfold public_half'; cancel.
          apply imp_andp_adjoint.
          Intros.
          eapply derives_trans; [|apply bupd_intro].
          rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply bupd_intro].
          Exists (false, (pn, (tp, (lock_in, (gsh, (g_in, r)))))); simpl; entailer !.
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
        { destruct succ as (succ & n').
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
        ∗ unfold ltree.
          destruct Hpa as (Hpa & Hx).
          simpl in Hpa.
          simpl.
          Intros.
          forward.
          subst n'.
          forward.
          (*acquire*)
          forward_call acquire_inv_simple (gsh1, locka, node_lock_inv gsh1 g pa ga locka).
          Intros.
          forward.
          gather_SEP (lock_inv gsh1 locka (node_lock_inv gsh1 g pa ga locka))
            (node_lock_inv gsh1 g pa ga locka).
          unfold node_lock_inv at 1.
          unfold node_lock_inv at 1.
          sep_apply self_part_eq.
          apply readable_not_bot.
          apply readable_gsh2.
          unfold node_lock_inv_pred at 3, sync_inv.
          Intros a.
          rewrite node_rep_def.
          Intros tp1.
          forward.
          gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half ga gsh1 a); unfold AS.
          viewshift_SEP 0 (atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
                             (λ (M : gmap key val) (_ : bool ∗
                                       (val ∗ (val ∗ (lock_handle ∗ (share ∗ (gname ∗ node_info)))))),
               fold_right_sepcon [tree_rep g g_root M])
                             Q ∗ my_half g_in gsh r ∗
                             (∃ ba, ⌜(less_than_equal ba r.1.1 = true /\
                range_incl a.1 (ba, Finite_Integer x0) = true⌝ ∧
            (in_tree g g_in ∗ my_half ga gsh1 (ba, Finite_Integer x0, a.2)))).
          {
            go_lower.
            apply (in_tree_left_range (bool ∗ (val ∗ (val ∗ (val ∗ namespace ∗ gname ∗ (share ∗ (gname ∗
                                 (range ∗ option (option ghost_info))))))))
            (λ M (_ : (bool ∗ (val ∗ (val ∗ (val ∗ namespace ∗ gname ∗ (share ∗ (gname ∗
                                 (range ∗ option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (∗release∗)
          forward_call release_self (gsh2, lock_in, node_lock_inv_pred gsh g pn g_in (ptr_of lock_in)).
          {
            unfold node_lock_inv.
            cancel.
            unfold node_lock_inv_pred at 4, sync_inv.
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
            unfold ltree, node_lock_inv.
            entailer !.
            repeat rewrite later_sepcon.
            entailer !.
          }
          (∗ proving ⊢  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS ∗)
          unfold traverse_inv.
          Exists (ba, Finite_Integer x0, a.2) pa ga locka gsh1.
          unfold node_lock_inv.
          rewrite node_rep_def.
          Exists tp1.
          unfold AS; entailer!.
          {
            unfold key_in_range in ∗.
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
       ∗ unfold ltree.
         destruct Hpb as (Hpb & Hx).
         simpl in Hpb.
         simpl.
         Intros.
         forward.
         subst n'.
         forward.
         (∗acquire∗)
         forward_call acquire_inv_simple (gsh1, lockb, node_lock_inv gsh1 g pb gb lockb).
         Intros.
         forward.
         gather_SEP (lock_inv gsh1 lockb (node_lock_inv gsh1 g pb gb lockb))
            (node_lock_inv gsh1 g pb gb lockb).
         unfold node_lock_inv at 1.
         unfold node_lock_inv at 1.
         sep_apply self_part_eq.
         apply readable_not_bot.
         apply readable_gsh2.
         unfold node_lock_inv_pred at 3.
         unfold sync_inv.
         Intros a.
         rewrite node_rep_def.
         Intros tp1.
         forward.
         gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half gb gsh1 a); unfold AS.
         viewshift_SEP 0 (
             atomic_shift (λ M : gmap key val, tree_rep g g_root M) ⊤ ∅ (λ (M : gmap key val) (_ : bool ∗
                                       (val ∗ (val ∗ (lock_handle ∗ (share ∗ (gname ∗ node_info)))))),
               fold_right_sepcon [tree_rep g g_root M])  Q ∗
                      my_half g_in gsh r ∗
                      (∃ ta : number,
                       ⌜(less_than_equal r.1.2 ta = true
                           ∧ range_incl a.1 (Finite_Integer x0, ta) = true) ∧
                       (in_tree g g_in ∗ my_half gb gsh1 (Finite_Integer x0, ta, a.2)))).
         {
           go_lower.
           apply (in_tree_right_range (bool ∗ (val ∗ (val ∗ (val ∗ namespace ∗ gname ∗ (share ∗ (gname ∗
                                 (range ∗ option (option ghost_info))))))))
            (λ M (_ : (bool ∗ (val ∗ (val ∗ (val ∗ namespace ∗ gname ∗ (share ∗ (gname ∗
                                 (range ∗ option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (∗release∗)
          forward_call release_self (gsh2, lock_in, node_lock_inv_pred gsh g pn g_in (ptr_of lock_in)).
          {
            unfold node_lock_inv.
            cancel.
            unfold node_lock_inv_pred at 4, sync_inv.
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
            unfold ltree, node_lock_inv.
            entailer !.
            repeat rewrite later_sepcon.
            entailer !.
          }
          (∗ proving ⊢  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS ∗)
          unfold  traverse_inv.
          Exists (Finite_Integer x0, ba, a.2) pb gb lockb gsh1.
          unfold node_lock_inv.
          rewrite node_rep_def.
          Exists tp1.
          unfold AS; entailer!.
          {
            unfold key_in_range in ∗.
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
        ∗ (∗ b == 0∗)
          apply repr_inj_unsigned' in H9; rep_lia.
    }
  - (∗ semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION ∗)
    Intros flag.
    Intros p1 pt gsh g_in lock_in r.
    forward.
    unfold traverse_inv_1, traverse_inv_2, node_lock_inv_new.
    destruct flag.
    Intros. (∗ will have key_in_range x r.1 = true for post condition∗)
    + (∗ flag = 1 ∗)
      Intros.
      Exists (true, (p1, (nullval, (lock_in, (gsh , (g_in, r)))))).
      simpl in ∗.
      unfold tree_rep_R.
      erewrite eq_dec_refl. (∗ will have key_in_range x r.1 = true ∗)
      entailer !.
    + (∗ flag = 0∗)
      Intros v1 pa pb ga gb locka lockb.
      Intros.
      Exists (false, (p1, (pt, (lock_in, (gsh, (g_in, r)))))).
      simpl in H2, H4. simpl.
      entailer !.
      exists v1, ga, gb; auto.
      unfold tree_rep_R.
      destruct (eq_dec).
      ∗ contradiction.
      ∗ Exists ga gb x v1 pa pb locka lockb.
        entailer !.
Qed.
