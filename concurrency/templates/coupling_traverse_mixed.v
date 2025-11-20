Require Import Coq.Program.Equality.
Require Import VST.concurrency.conclib.
From VST.typing Require Import type own singleton struct adequacy.
Require Import VST.floyd.proofauto.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.mixed_mode.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.atomics.general_locks.
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
  (λ '(ppn, n, k, v, l, r, x), [type.adr2val ppn; Vint (Int.repr x)]) type_of_findnext).

Lemma convert_tree : forall a k v l r,
  repable_signed k → is_pointer_or_null v →
  a ◁ᵥ|t_struct_tree| (k, v, l, r) @ tree ⊣⊢ <affine> ⌜a = (vint k, (v, (adr2val l, adr2val r)))⌝.
Proof.
  intros.
  rewrite tree_unfold /= /struct /ty_own_val_at {1}/ty_own_val.
  iSplit.
  - iIntros "(% & %Hcty & % & _ & H)".
    destruct a as (?, (?, (?, ?))).
    dependent destruction Hcty; simpl.
    iDestruct "H" as "(Hk & Hv & Hl & Hr)".
    iDestruct "Hk" as (? (j & Hj1 & Hj2)) "Hk".
    destruct j as [|[|[|[|]]]]; inv Hj1; inv Hj2.
    setoid_rewrite unfold_int_type; last done; iDestruct "Hk" as %->.
    iDestruct "Hv" as (? (j & Hj1 & Hj2)) "Hv".
    destruct j as [|[|[|[|]]]]; inv Hj1; inv Hj2.
    setoid_rewrite unfold_value_ptr_type; last done; iDestruct "Hv" as %->.
    iDestruct "Hl" as (? (j & Hj1 & Hj2)) "Hl".
    destruct j as [|[|[|[|]]]]; inv Hj1; inv Hj2.
    setoid_rewrite unfold_value_ptr_type; last done; iDestruct "Hl" as %->.
    iDestruct "Hr" as (? (j & Hj1 & Hj2)) "Hr".
    destruct j as [|[|[|[|]]]]; inv Hj1; inv Hj2.
    setoid_rewrite unfold_value_ptr_type; last done; iDestruct "Hr" as %->.
    done.
  - iIntros (->).
    iExists _, eq_refl.
    iSplit.
    { iPureIntro.
      split3; last split; intros ?; rewrite /repinject //=; auto. }
    iSplit; first done; simpl.
    iSplitL; [|iSplitL; [|iSplitL]]; iExists _.
    + iSplit; first by iPureIntro; exists O.
      by iApply unfold_int_type.
    + iSplit; first by iPureIntro; exists 1.
      by iApply unfold_value_ptr_type.
    + iSplit; first by iPureIntro; exists 2.
      by iApply unfold_value_ptr_type.
    + iSplit; first by iPureIntro; exists 3.
      by iApply unfold_value_ptr_type.
Qed.

Lemma convert_pn : forall a k (v l r : val) n, repable_signed k →
  is_pointer_or_null v → isptr l → isptr r → is_pointer_or_null n →
  a ◁ᵥ|tptr t_struct_pn| to_address a @ &own ((Some (k, v, to_address l, to_address r), n) @ pn) ⊣⊢
  (∃ p : val, data_at Tsh t_struct_pn (p, n) a ∗ ∃ pt : val, data_at Tsh (tptr t_struct_tree) pt p ∗
              data_at Tsh t_struct_tree (vint k, (v, (l, r))) pt).
Proof.
  intros.
  rewrite unfold_own_type //.
  rewrite bi.pure_True // bi.True_and.
  setoid_rewrite pn_unfold; rewrite /= /struct; simpl_type.
  iSplit.
  - iIntros "(%a' & ? & % & %Hcty & % & _ & H)".
    destruct a'; dependent destruction Hcty.
    iDestruct "H" as "(Hp & Hn)".
    iDestruct "Hp" as (? (j & Hj1 & Hj2)) "Hp".
    destruct j as [|[|]]; inv Hj1; inv Hj2.
    rewrite {1}/frac_ptr {1}/ty_of_rty; simpl_type.
    iDestruct "Hp" as (?) "Hp".
    rewrite /frac_ptr_type; simpl_type.
    iDestruct "Hp" as "(%Hy & Hp)"; rewrite /repinject /= in Hy; subst.
    rewrite {1}/optional.optionalO; simpl_type.
    rewrite {1}/first_field; simpl_type.
    iDestruct "Hp" as (? [=] ?) "Hp"; subst.
    iDestruct (ty_deref _ (tptr _) MCNone with "Hp") as (?) "(Hp & Hv)"; first done.
    setoid_rewrite (unfold_own_type0 t_struct_tree); last done.
    iDestruct "Hv" as "(% & Hpt & Hv)"; rewrite convert_tree //.
    iDestruct "Hv" as %->.
    rewrite {4}/data_at /field_at /at_offset /=.
    rewrite !to_address_eq //; iFrame.
    iExists x; rewrite isptr_offset_val_zero //; iFrame; iSplit; last done.
    iDestruct "Hn" as (? (j & Hj1 & Hj2)) "Hn".
    destruct j as [|[|]]; inv Hj1; inv Hj2.
    rewrite unfold_value_ptr_type //.
    iDestruct "Hn" as %->; done.
  - iIntros "(%p & Ha & % & Hp & Hpt)".
    iDestruct (data_at_local_facts with "Ha") as %(_ & Ha); iFrame "Ha".
    iExists _, eq_refl; do 2 (iSplit; first done).
    iSplitL.
    + iExists _; iSplit; first by iPureIntro; exists O.
      rewrite {1}/ty_of_rty; simpl_type.
      iExists (to_address p).
      rewrite /frac_ptr; simpl_type.
      rewrite {1}/data_at /field_at /at_offset.
      iDestruct "Hp" as (Hp) "Hp".
      assert (isptr p) by by destruct Hp.
      rewrite isptr_offset_val_zero //.
      rewrite to_address_eq //; iSplit; first done.
      rewrite /optional.optionalO; simpl_type.
      rewrite /first_field; simpl_type.
      iExists _; iSplit; first done; simpl.
      rewrite /has_layout_loc to_address_eq //; iSplit; first done.
      rewrite /ty_of_rty; simpl_type.
      iExists (to_address pt); iApply (ty_ref _ _ MCNone with "[] [Hp]").
      3: { rewrite /type.mapsto to_address_eq //. }
      { done. }
      { rewrite /has_layout_loc to_address_eq //. }
      setoid_rewrite unfold_own_type; last done.
      iSplit; first done; iFrame.
      iApply convert_tree; try done.
      rewrite !to_address_eq //.
    + iExists _; iSplit; first by iPureIntro; exists 1.
      rewrite unfold_value_ptr_type //.
Qed.

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
   (field_at Tsh t_struct_tree_t (DOT _t) tp p ∗
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
       pn_rep_1 g g_root Tsh b n) | (tree_rep g g_root M)
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
                        data_at Tsh t_struct_pn (pt.2.1, pt.2.1) b ∗
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

Opaque field_at.

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
  destruct (eq_dec p nullval). { entailer !. }
  Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g ⊢ valid_pointer tp.
Proof.
  intros. unfold tree_rep_R.
  destruct (eq_dec tp nullval). { entailer!. }
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
  field_at Tsh t_struct_tree_t (DOT _t) nullval p ∗
  malloc_token Ews t_struct_tree_t p ∗ in_tree g g_in ∗
  field_at lsh2 t_struct_tree_t (DOT _lock) (ptr_of lock_in) p ∗
  my_half g_in gsh r ∗ (⌜key_in_range x r.1 = true /\ r.2 = Excl' None⌝ ∧ emp) ∗
  lock_inv (1/2) lock_in (node_lock_inv gsh g p g_in lock_in).

Definition traverse_inv_2 (b: val) (p: val) (tp: val) (g: gname) (g_root: gname) (g_in: gname)
                          (lock_in: lock_handle) (gsh: Qp) (sh: share) (r: node_info) (x: Z):=
  ∃ (v1: val) (pa: val) (pb: val) (ga: gname) (gb: gname) (locka lockb: lock_handle),
  data_at sh (t_struct_pn) (p, p) b ∗
  field_at Tsh t_struct_tree_t (DOT _t) tp p ∗
  data_at Tsh t_struct_tree (vint x, (v1, (pa, pb))) tp ∗
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

(* Should we make a hook for the simplifications, or maybe declare the specs with a tactic that simplifies them? *)
Ltac match_postcondition ::=
unfold atomic_spec_post', atomic_spec_post0, rev_curry, tcurry, tcurry_rev, tcurry_rev';
fix_up_simplified_postcondition;
cbv beta iota zeta; unfold_post;
constructor; let rho := fresh "rho" in intro rho; cbn [fn_params_post' fn_params_post_void monPred_at postassert_of assert_of ofe_mor_car];
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite monPred_at_exist;
tryif apply bi.exist_proper
 then (intros ?vret;
          generalize rho; rewrite -local_assert; apply PROP_RETURN_SEP_ext';
          [reflexivity | | reflexivity];
          (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be (temp ret_temp ...), but it is not"))
 else fail "The funspec of the function should have a POSTcondition that starts
with an existential, that is,  ∃ _:_, PROP...LOCAL...SEP".

(*Proving traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  unfold pn_rep_1, ltree.
  Intros p.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  forward_loop (traverse_inv b (ptr_of lock) Tsh x v g_root gv g AS)
               break:
    (∃ (flag : bool) (q: val) (pt: val) (gsh: Qp) (g_in: gname)
       (lock_in : lock_handle) (r : node_info),
                PROP() LOCAL(temp _flag (Val.of_bool flag))
                      SEP((if flag
                          then ((traverse_inv_1 b q g g_root g_in lock_in gsh Tsh r x) ∗
                                  (⌜pt = nullval⌝ ∧ emp))
                          else ((traverse_inv_2 b q pt g g_root g_in lock_in gsh Tsh r x) ∗
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
      { entailer !. }
      Intros ga gb x0 v1 pa pb locka lockb.
      entailer !.
    + rewrite H3. (*  Q (true, (p1, (p1, (lock_in, (gsh, g_in))))) *)
      gather_SEP AS (my_half g_in _ _) (in_tree g _).
      viewshift_SEP 0 (∃ y, Q y ∗ (⌜y = (true, (pn, (nullval, (lock_in, (gsh, (g_in, r))))))⌝
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
        Exists (true, (pn, (nullval, (lock_in, (gsh, (g_in, r)))))); simpl; entailer!.
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
      assert_PROP (isptr b) by entailer!.
      assert_PROP (isptr pa) by entailer!.
      assert_PROP (isptr pb) by entailer!.
      assert_PROP (isptr pn) by entailer!.
      forward_call (to_address b, pn, x0, v1, to_address pa, to_address pb, x).
      { rewrite to_address_eq //; entailer!!. }
      { simpl.
        rewrite to_address_eq // convert_pn //; auto.
        rewrite unfold_int_type //.
        Exists pn tp; cancel.
        rewrite bi.pure_True // bi.affinely_True_emp sep_emp.
        rewrite field_at_data_at' /= isptr_offset_val_zero //.
        Intros; cancel. }
      { simpl.
        Intros ? a; destruct a as (succ, nn); simpl.
        rewrite /val_type /= unfold_bool_type -bi.persistent_and_affinely_sep_l /bi_affinely; Intros; subst.
        rewrite fold_own_type to_address_eq //; setoid_rewrite convert_pn; [|auto..].
        2: { destruct succ; last by destruct H12; subst; auto.
             destruct H12 as [[-> _] | [-> _]]; rewrite to_address_eq //. }
        Intros pn' tp'.
        forward_if.
        (* flag = 0 *)
        forward.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (∃ y, Q y ∗ (⌜y = (false, (pn, (tp, (lock_in, (gsh, (g_in, r))))))⌝
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
          { go_lowerx.
            apply (in_tree_left_range (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (*release*)
          forward_call release_self (gsh2, lock_in, node_lock_inv_pred gsh g pn g_in (ptr_of lock_in)).
          { unfold node_lock_inv.
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
          (* proving ⊢  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS *)
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
             atomic_shift (λ M : gmap key val, tree_rep g g_root M) ⊤ ∅ (λ (M : gmap key val) (_ : bool *
                                       (val * (val * (lock_handle * (share * (gname * node_info)))))),
               fold_right_sepcon [tree_rep g g_root M]) Q ∗
                      my_half g_in gsh r ∗
                      (∃ ta : number,
                       ⌜(less_than_equal r.1.2 ta = true
                           ∧ range_incl a.1 (Finite_Integer x0, ta) = true) ∧
                       (in_tree g g_in ∗ my_half gb gsh1 (Finite_Integer x0, ta, a.2)))).
         { go_lowerx.
           apply (in_tree_right_range (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))
            (λ M (_ : (bool * (val * (val * (val * namespace * gname * (share * (gname *
                                 (range * option (option ghost_info))))))))),
              fold_right_sepcon [tree_rep g g_root M]) Q x x0 g g_root v1 g_in ga gb).
            auto. auto. rewrite ! Int.signed_repr in Hx; by rep_lia.
          }
          Intros ba.
          (*release*)
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
          (* proving ⊢  traverse_inv b (ptr_of lock) Ews x v g_root gv inv_names g AS *)
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
      entailer !.
    + (* flag = 0*)
      Intros v1 pa pb ga gb locka lockb.
      Intros.
      Exists (false, (p1, (pt, (lock_in, (gsh, (g_in, r)))))).
      simpl in H2, H4. simpl.
      entailer !.
      exists v1, ga, gb; auto.
      unfold tree_rep_R.
      destruct (eq_dec).
      * contradiction.
      * Exists ga gb x v1 pa pb locka lockb.
        entailer !.
Qed.
