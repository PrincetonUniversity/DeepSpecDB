Require Import Coq.Sets.Ensembles.
Require Import Coq.micromega.Lia.
Require Import VST.progs.conclib.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import bst.puretree.
Require Import bst.bst_conc_cglock.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Fixpoint tree_rep (t: @tree val) (p: val): mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
   EX pa:val, EX pb:val,
                    malloc_token Ews t_struct_tree p *
                    data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
                    tree_rep a pa * tree_rep b pb
 end.

Instance tree_ghost: Ghost := discrete_PCM (@tree val).

Notation tree_info := (@G tree_ghost).

Definition treebox_rep (t: @tree val) (b: val) :=
  EX p: val, data_at Ews (tptr t_struct_tree) p b * tree_rep t p.

Definition node_lock_inv g lock np :=
  (EX tr, my_half g Tsh tr *
          treebox_rep tr (field_address t_struct_tree_t [StructField _t] np)) *
  malloc_token Ews tlock lock * malloc_token Ews t_struct_tree_t np.

Definition nodebox_rep (g : gname)
           (sh : share) (lock : val) (nb: val) :=
  EX np: val,
     data_at sh (tptr t_struct_tree_t) np nb *
     field_at sh t_struct_tree_t [StructField _lock] lock np *
     lock_inv sh lock (node_lock_inv g lock np).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
  WITH t:type, gv: globals
  PRE [ _n OF tuint ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    LOCAL (temp _n (Vint (Int.repr (sizeof t))); gvars gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid ] EX p:_,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * globals * gname))
  OBJ BST INVS base.empty base.top
  WITH b, sh, lock, x, gv, g
  PRE [_t OF (tptr (tptr t_struct_tree_t)), _x OF tint]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed)
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!! sorted_tree BST && public_half g BST)
  POST [tptr Tvoid]
   EX ret: val,
   PROP ()
   LOCAL (temp ret_temp ret)
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
         (!! (sorted_tree BST /\ ret = lookup nullval x BST) && public_half g BST).

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * val * globals * gname))
  OBJ BST INVS base.empty base.top
  WITH b, sh, lock, x, v, gv, g
  PRE [_t OF (tptr (tptr t_struct_tree_t)), _x OF tint, _value OF (tptr tvoid)]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed;
        is_pointer_or_null v)
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!! sorted_tree BST && public_half g BST)
  POST [tvoid]
   PROP ()
   LOCAL ()
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!! sorted_tree (insert x v BST) && public_half g (insert x v BST)).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: @tree val, x: Z, vx: val, tb: @tree val, y: Z, vy: val,
              tc: @tree val, b: val, l: val, pa: val, r: val
  PRE  [ __l OF (tptr (tptr t_struct_tree)),
        _l OF (tptr t_struct_tree),
        _r OF (tptr t_struct_tree)]
    PROP(Int.min_signed <= x <= Int.max_signed; is_pointer_or_null vx)
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (data_at Ews (tptr t_struct_tree) l b;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (pa, r))) l;
         malloc_token Ews t_struct_tree l; tree_rep ta pa; tree_rep (T tb y vy tc) r)
  POST [ Tvoid ]
    EX pc: val,
    PROP (Int.min_signed <= y <= Int.max_signed; is_pointer_or_null vy)
    LOCAL()
    SEP (data_at Ews (tptr t_struct_tree) r b;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (l, pc))) r;
         malloc_token Ews t_struct_tree r; tree_rep (T ta x vx tb) l; tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: @tree val, x: Z, v: val, tb: @tree val, b: val, p: val, gv: globals
  PRE  [ _t OF (tptr (tptr (t_struct_tree)))]
    PROP(Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) v)
    LOCAL(temp _t b; gvars gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_struct_tree) p b;
         malloc_token Ews t_struct_tree p;
         field_at Ews t_struct_tree [StructField _key] (Vint (Int.repr x)) p;
         field_at Ews t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv; treebox_rep (pushdown_left ta tb) b).

Program Definition delete_spec :=
 DECLARE _delete
 ATOMIC TYPE (rmaps.ConstType (_ * _ * _ * _ * _ * _))
         OBJ BST INVS base.empty base.top
 WITH b, x, lock, gv, sh, g
 PRE  [ _t OF (tptr (tptr t_struct_tree_t)), _x OF tint]
    PROP (Int.min_signed <= x <= Int.max_signed; readable_share sh)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!!(sorted_tree BST) && public_half g BST)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!!(sorted_tree (delete x BST)) && public_half g (delete x BST)).

Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH gv: globals
  PRE  [  ]
    PROP () LOCAL (gvars gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX v:val, EX lock:val, EX g:gname,
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (mem_mgr gv; nodebox_rep g Ews lock v;
        malloc_token Ews (tptr t_struct_tree_t) v;
        public_half g E).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t: @tree val, p: val, gv: globals
  PRE  [ _p OF (tptr t_struct_tree) ]
       PROP() LOCAL(temp _p p; gvars gv) SEP (mem_mgr gv; tree_rep t p)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH lock: val, b: val, gv: globals, g: gname
  PRE  [ _b OF (tptr (tptr t_struct_tree_t)) ]
       PROP()
       LOCAL(gvars gv; temp _b b)
       SEP (mem_mgr gv; nodebox_rep g Ews lock b;
           malloc_token Ews (tptr t_struct_tree_t) b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).

Definition tree_inv g g1 g2 :=
  EX (b: bool) (v: val) (l1 l2 : list (key * val)),
  ghost_var gsh1 (b, v) g1 * ghost_var gsh1 (l1 ++ l2) g2 *
  public_half g (insert_seq_opt b v l1 l2).

Definition thread_lock_R sh lock g g1 b (gv: globals) :=
  ghost_var gsh2 (true, (gv ___stringlit_1)) g1 * mem_mgr gv *
  data_at sh (tptr (tptr (t_struct_tree_t))) b (gv _tb) *
  data_at Ers (tarray tschar 16)
          (map (Vint oo cast_int_int I8 Signed)
               [Int.repr 79; Int.repr 78; Int.repr 69;
               Int.repr 95; Int.repr 70; Int.repr 82;
               Int.repr 79; Int.repr 77; Int.repr 95;
               Int.repr 84; Int.repr 72; Int.repr 82;
               Int.repr 69; Int.repr 65; Int.repr 68;
               Int.repr 0]) (gv ___stringlit_1) * nodebox_rep g sh lock b.

Definition thread_lock_inv sh lock g g1 b gv lockt :=
  selflock (thread_lock_R sh lock g g1 b gv) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : iname * gname * gname * gname * share * val * val * globals * invG
    PRE [ _args OF (tptr tvoid) ]
         let '(i, g1, g2, g, sh, lock, b, gv, inv_names) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (invariant i (tree_inv g g1 g2); ghost_var gsh2 (false, nullval) g1;
               mem_mgr gv; data_at sh (tptr (tptr (t_struct_tree_t))) b (gv _tb);
               data_at Ers (tarray tschar 16)
                       (map (Vint oo cast_int_int I8 Signed)
                            [Int.repr 79; Int.repr 78; Int.repr 69;
                            Int.repr 95; Int.repr 70; Int.repr 82;
                            Int.repr 79; Int.repr 77; Int.repr 95;
                            Int.repr 84; Int.repr 72; Int.repr 82;
                            Int.repr 69; Int.repr 65; Int.repr 68;
                            Int.repr 0]) (gv ___stringlit_1);
               nodebox_rep g sh lock b;
               lock_inv sh (gv _thread_lock)
                        (thread_lock_inv sh lock g g1 b gv (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP ().

Definition main_spec :=
  DECLARE _main
          WITH gv : globals
                      PRE  [] main_pre prog tt nil gv
                      POST [ tint ] main_post prog nil gv.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
                          freelock2_spec; freelock_spec; release2_spec;
                          surely_malloc_spec;
                          lookup_spec; insert_spec;
                          turn_left_spec; pushdown_left_spec; delete_spec;
                          treebox_new_spec; tree_free_spec; treebox_free_spec;
                          spawn_spec; thread_func_spec; main_spec]).

Lemma field_at_value_eq : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject (nested_field_type t gfs) v1 <> Vundef ->
  repinject (nested_field_type t gfs) v2 <> Vundef ->
  type_is_by_value (nested_field_type t gfs) = true ->
  type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold field_at, at_offset; Intros.
  rewrite !by_value_data_at_rec_nonvolatile; auto.
  sep_apply mapsto_value_eq; Intros; apply prop_right.
  set (t' := nested_field_type t gfs) in *.
  pose proof (f_equal (valinject t') H6) as Heq.
  rewrite !valinject_repinject in Heq; auto.
Qed.

Lemma data_at_value_eq : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject t v1 <> Vundef -> repinject t v2 <> Vundef ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |-- !!(v1 = v2).
Proof. intros; unfold data_at; apply field_at_value_eq; auto. Qed.

Lemma nodebox_rep_share_join : forall g (sh1 sh2 sh : share) (lock : val) (nb : val),
    readable_share sh1 -> readable_share sh2 -> sepalg.join sh1 sh2 sh ->
    nodebox_rep g sh1 lock nb * nodebox_rep g sh2 lock nb = nodebox_rep g sh lock nb.
Proof.
  intros. unfold nodebox_rep. apply pred_ext.
  - Intros np1 np2. assert_PROP (np1 <> Vundef) by entailer!.
    assert_PROP (np2 <> Vundef) by entailer!.
    sep_apply data_at_value_eq; Intros; subst. Exists np2.
    rewrite <- (data_at_share_join sh1 sh2 sh), <- (field_at_share_join sh1 sh2 sh),
    <- (lock_inv_share_join sh1 sh2 sh); auto. cancel.
  - Intros np; Exists np np.
    rewrite <- (data_at_share_join sh1 sh2 sh), <- (field_at_share_join sh1 sh2 sh),
    <- (lock_inv_share_join sh1 sh2 sh); auto. cancel.
Qed.

Lemma tree_rep_saturate_local:
   forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof. destruct t; simpl; intros. entailer!. Intros pa pb. entailer!. Qed.
Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof. intros. destruct t; simpl; normalize; auto with valid_pointer. Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Lemma node_lock_exclusive : forall g lock np,
    exclusive_mpred (node_lock_inv g lock np).
Proof.
  intros. unfold node_lock_inv. unfold exclusive_mpred. unfold treebox_rep.
  Intros tr1 tr2 tp1 tp2. sep_apply field_at_conflict; auto.
  rewrite sepcon_comm. rewrite sepcon_FF. auto.
Qed.
Hint Resolve node_lock_exclusive.

Lemma tree_rep_nullval: forall t, tree_rep t nullval |-- !! (t = E).
Proof.
  intros. destruct t; [entailer! |].
  simpl tree_rep. Intros pa pb. entailer!.
Qed.
Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_spec: forall (t: @tree val) (b: val),
  treebox_rep t b =
  EX p: val,
  match t with
  | E => !!(p=nullval) && data_at Ews (tptr t_struct_tree) p b
  | T l x v r => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      data_at Ews (tptr t_struct_tree) p b * malloc_token Ews t_struct_tree p *
      field_at Ews t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      field_at Ews t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  unfold treebox_rep at 1. f_equal. extensionality p.
  destruct t; simpl.
  - apply pred_ext; entailer!.
  - unfold treebox_rep. apply pred_ext; entailer!.
    + Intros pa pb. Exists pb pa. unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]). cancel.
    + Intros pa pb. Exists pb pa. unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]). cancel.
Qed.

Lemma bst_left_entail: forall (t1 t1' t2: @tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Ews (tptr t_struct_tree) p b * malloc_token Ews t_struct_tree p *
  data_at Ews t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  rewrite <- wand_sepcon_adjoint.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p'.
  Exists p' p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': @tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Ews (tptr t_struct_tree) p b * malloc_token Ews t_struct_tree p *
  data_at Ews t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.
  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.

Lemma insert_tree_inv_shift1: forall {inv_names : invG} i g g1 g2 l k v,
    invariant i (tree_inv g g1 g2) *
    ghost_var gsh2 l g2 |--
              atomic_shift (λ BST : tree, !! sorted_tree BST && public_half g BST) ∅ ⊤
              (λ (BST : tree) (_ : ()),
               fold_right_sepcon
                 [!! sorted_tree (insert k v BST) && public_half g (insert k v BST)])
              (λ _ : (), ghost_var gsh2 (l ++ [(k, v)]) g2).
Proof.
  intros; apply inv_atomic_shift; auto. 1: apply empty_subseteq.
  unfold tree_inv. iIntros "t". iDestruct "t" as (b) ">t".
  iDestruct "t" as (v0) "t". iDestruct "t" as (l1 l2) "[[g1 g2] t]". iModIntro.
  iExists (insert_seq_opt b v0 l1 l2). rewrite sepcon_comm sepcon_andp_prop. iSplit.
  - iApply (prop_right with "t"). apply insert_seq_opt_sorted.
  - iFrame. iSplit.
    + iIntros "[% c] !>". iExists b, v0, l1, l2. iModIntro. iFrame.
    + iIntros (_) "(>g & [% c] & _)".
      iPoseProof (ghost_var_inj (A := list (key * val)) with "[$g2 $g]") as "%";
        auto with share; subst l.
      iMod (ghost_var_update with "[g2 g]") as "g2". {
        rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[g2 $]".
      iExists b, v0, l1, (l2 ++ [(k, v)]). iModIntro. iModIntro.
      rewrite insert_seq_opt_assoc. rewrite <- app_assoc. iFrame.
Qed.

Lemma insert_tree_inv_shift2: forall {inv_names : invG} i g g1 g2 (v1 v2: val),
    invariant i (tree_inv g g1 g2) *
    ghost_var gsh2 (false, v1) g1 |--
              atomic_shift (λ BST : tree, !! sorted_tree BST && public_half g BST) ∅ ⊤
              (λ (BST : tree) (_ : ()),
               fold_right_sepcon
                 [!! sorted_tree (insert 1 v2 BST) && public_half g (insert 1 v2 BST)])
              (λ _ : (), ghost_var gsh2 (true, v2) g1).
Proof.
  intros; apply inv_atomic_shift; auto. 1: apply empty_subseteq.
  unfold tree_inv. iIntros "t". iDestruct "t" as (b) ">t".
  iDestruct "t" as (v0) "t". iDestruct "t" as (l1 l2) "[[g1 g2] t]". iModIntro.
  iExists (insert_seq_opt b v0 l1 l2). rewrite sepcon_comm sepcon_andp_prop. iSplit.
  - iApply (prop_right with "t"). apply insert_seq_opt_sorted.
  - iFrame. iSplit.
    + iIntros "[% c] !>". iExists b, v0, l1, l2. iModIntro. iFrame.
    + iIntros (_) "(>g & [% c] & _)".
      iPoseProof (ghost_var_inj (A := (bool * val)) with "[$g1 $g]") as "%";
        auto with share. inv H0.
      iMod (ghost_var_update with "[g1 g]") as "g1". {
        rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g1" as "[g1 $]".
      iExists true, v2, (l1 ++ l2), nil. iModIntro. iModIntro.
      simpl insert_seq_opt. rewrite insert_seq_assoc app_nil_r. iFrame.
Qed.

Lemma thread_inv_exclusive : forall sh lock g g1 b gv lockt,
    readable_share sh -> exclusive_mpred (thread_lock_inv sh lock g g1 b gv lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R. apply exclusive_sepcon1. apply exclusive_sepcon1.
  apply exclusive_sepcon2. apply data_at_exclusive; auto. simpl; lia.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS. unfold abbreviate.
  forward. (* _l = &_thread_lock; *)
  unfold nodebox_rep.
  Intros np.
  forward. (* _t'1 = _tb; *)
  assert_PROP (is_pointer_or_null (gv ___stringlit_1)) by entailer!.
  assert (Int.min_signed ≤ 1 ∧ 1 ≤ Int.max_signed) by (compute; split; intro; easy).
  forward_call (b, sh, lock, 1, (gv ___stringlit_1), gv, g,
                ghost_var gsh2 (true, gv ___stringlit_1) g1, inv_names). {
    sep_apply (insert_tree_inv_shift2 i g g1 g2 nullval (gv ___stringlit_1)).
    unfold nodebox_rep. Exists np. entailer!. }
  forward_call (gv _thread_lock, sh, thread_lock_R sh lock g g1 b gv,
                thread_lock_inv sh lock g g1 b gv (gv _thread_lock)). {
    lock_props. unfold thread_lock_inv at 2. unfold thread_lock_R.
    rewrite selflock_eq. unfold thread_lock_inv, thread_lock_R. entailer!. }
  forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  rewrite <- (emp_sepcon (mem_mgr _)); Intros.
  viewshift_SEP 0 (EX inv_names : invG, wsat) by (go_lower; apply make_wsat).
  Intros inv_names.
  ghost_alloc (ghost_var Tsh (false, nullval)). Intro g1.
  ghost_alloc (ghost_var Tsh (@nil (key * val))). Intro g2.
  rewrite <- 2 (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros.
  forward_call (gv). (* _t'1 = _treebox_new([]); *)
  Intros v. destruct v as [[b lock] g]. simpl fst. simpl snd.
  forward. (* _tb = _t'1;   *)
  forward. (* _t_lock = &_thread_lock; *)
  forward. (* _t'6 = _tb; *)
  assert (readable_share Ews) by apply writable_readable, writable_Ews.
  assert_PROP (is_pointer_or_null (gv ___stringlit_2)) by entailer!.
  assert (Int.min_signed ≤ 3 ∧ 3 ≤ Int.max_signed) by (compute; split; intro; easy).
  gather_SEP wsat (ghost_var gsh1 _ g1) (ghost_var gsh1 _ g2) (public_half _ _).
  viewshift_SEP 0 (EX i, |> (wsat * invariant i (tree_inv g g1 g2))). {
    go_lower. rewrite !sepcon_assoc. apply make_inv'. unfold tree_inv.
    Exists false nullval (@nil (key * val)) (@nil (key * val)).
    simpl insert_seq_opt. simpl app. cancel. } Intros i.
  rewrite invariant_dup; Intros.
  forward_call (b, Ews, lock, 3, (gv ___stringlit_2), gv, g,
                ghost_var gsh2 [(3, (gv ___stringlit_2))] g2, inv_names). {
    sep_apply (insert_tree_inv_shift1 i g g1 g2 [] 3 (gv ___stringlit_2)).
    simpl app. apply sepcon_derives; [apply derives_refl | cancel]. }
  forward. (* _t'5 = _tb; *)
  assert_PROP (is_pointer_or_null (gv ___stringlit_3)) by entailer!.
  assert (Int.min_signed ≤ 1 ∧ 1 ≤ Int.max_signed) by (compute; split; intro; easy).
  rewrite invariant_dup; Intros.
  forward_call (b, Ews, lock, 1, (gv ___stringlit_3), gv, g,
                ghost_var gsh2 [(3, (gv ___stringlit_2));
                                (1, (gv ___stringlit_3))] g2, inv_names). {
    sep_apply (insert_tree_inv_shift1 i g g1 g2 [(3, (gv ___stringlit_2))]
                                     1 (gv ___stringlit_3)).
    simpl app. apply sepcon_derives; [apply derives_refl | cancel]. }
  forward. (* _t'4 = _tb;  *)
  assert_PROP (is_pointer_or_null (gv ___stringlit_4)) by entailer!.
  assert (Int.min_signed ≤ 4 ∧ 4 ≤ Int.max_signed) by (compute; split; intro; easy).
  rewrite invariant_dup; Intros.
  forward_call (b, Ews, lock, 4, (gv ___stringlit_4), gv, g,
                ghost_var gsh2 [(3, (gv ___stringlit_2));
                                (1, (gv ___stringlit_3));
                                (4, (gv ___stringlit_4))] g2, inv_names). {
    sep_apply (insert_tree_inv_shift1
                 i g g1 g2 [(3, gv ___stringlit_2); (1, gv ___stringlit_3)]
                 4 (gv ___stringlit_4)).
    simpl app. apply sepcon_derives; [apply derives_refl | cancel]. }
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gv _thread_lock, Ews,
                thread_lock_inv sh1 lock g g1 b gv (gv _thread_lock)).
  rewrite invariant_dup; Intros.
  forward_spawn _thread_func nullval (i, g1, g2, g, sh1, lock, b, gv, inv_names). {
    rewrite <- (lock_inv_share_join sh1 sh2 Ews); auto.
    rewrite <- (data_at_share_join sh1 sh2 Ews); auto.
    rewrite <- (nodebox_rep_share_join g sh1 sh2 Ews); auto. entailer!. }
  forward.
  sep_apply (create_mem_mgr gv).
  assert_PROP (is_pointer_or_null (gv ___stringlit_5)) by entailer!.
  rewrite invariant_dup; Intros.
  forward_call (b, sh2, lock, 1, (gv ___stringlit_5), gv, g,
                ghost_var gsh2 [(3, (gv ___stringlit_2));
                                (1, (gv ___stringlit_3));
                                (4, (gv ___stringlit_4));
                                (1, (gv ___stringlit_5))] g2, inv_names). {
    sep_apply (insert_tree_inv_shift1
                 i g g1 g2 [(3, gv ___stringlit_2); (1, gv ___stringlit_3);
                            (4, gv ___stringlit_4)]
                 1 (gv ___stringlit_5)).
    simpl app. apply sepcon_derives; [apply derives_refl | cancel]. }
  forward_call (gv _thread_lock, sh2,
                thread_lock_inv sh1 lock g g1 b gv (gv _thread_lock)).
  unfold thread_lock_inv at 2. rewrite selflock_eq. Intros.
  forward_call (gv _thread_lock, Ews, sh1, thread_lock_R sh1 lock g g1 b gv,
                thread_lock_inv sh1 lock g g1 b gv (gv _thread_lock)). {
    lock_props. unfold thread_lock_inv.
    rewrite <- (lock_inv_share_join sh1 sh2 Ews); auto. entailer!. }
  unfold thread_lock_R. Intros.
  gather_SEP (nodebox_rep g sh1 _ _) (nodebox_rep g sh2 _ _).
  rewrite (nodebox_rep_share_join g sh1 sh2 Ews lock b); auto.
  gather_SEP (data_at sh1 _ _ _) (data_at sh2 _ _ _).
  rewrite (data_at_share_join sh1 sh2 Ews); auto.
  forward.
  forward_call (lock, b, gv, g).
  forward.
Qed.

Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward.
  forward.
  forward_call (lock, Ews, node_lock_inv g lock np).
  forward_call (lock, Ews, node_lock_inv g lock np). (* _freelock(_l); *)
  - lock_props.
  - unfold node_lock_inv. unfold treebox_rep. Intros tr p.
    change (tptr t_struct_tree) with
        (nested_field_type t_struct_tree_t [StructField _t]).
    rewrite <- field_at_data_at.
    forward. (* _p = (_tgp -> _t); *)
    forward_call (tr, p, gv). (* _tree_free(_p); *)
    gather_SEP (my_half _ _ _).
    viewshift_SEP 0 (emp). { go_lower. apply own_dealloc. }
    forward_call (t_struct_tree_t, np, gv). (* _free(_tgp); *)
    + if_tac; entailer!.
      unfold_data_at_ np.
      unfold_data_at (data_at Ews t_struct_tree_t _ np). cancel.
    + forward_call (tlock, lock, gv). (* _free(_l); *)
      * if_tac; entailer!.
      * forward_call (tptr t_struct_tree_t, b, gv).
        -- if_tac; entailer!.
        -- entailer!.
Qed.

Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  forward_if.
  - destruct t; simpl tree_rep. 1: Intros; contradiction.
    Intros pa pb.
    forward.
    forward.
    forward_call (t_struct_tree, p, gv).
    + rewrite if_false; auto. entailer!.
    + forward_call (t1, pa, gv).
      forward_call (t2, pb, gv).
      entailer!.
  - forward. subst.
    sep_apply tree_rep_nullval. Intros. subst. simpl tree_rep. entailer!.
Qed.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv). 1: split; simpl; [rep_omega | auto].
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv). 1: split; simpl; [rep_omega | auto].
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (tarray (tptr tvoid) 2, gv).
  1: split; simpl; [ unfold Z.max; simpl; rep_omega | auto].
  Intros l. (* lock_t *l *)
  ghost_alloc (both_halves E). 1: apply @part_ref_valid.
  Intros g'. rewrite <- both_halves_join.
  forward_call (l, Ews, node_lock_inv g' l newt). Intros.
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  forward_call (l, Ews, node_lock_inv g' l newt).
  - lock_props.
    unfold node_lock_inv. Exists (@E val).
    unfold_data_at (data_at Ews t_struct_tree_t _ _).
    unfold treebox_rep. Exists (vint 0).
    change (tptr t_struct_tree) with
        (nested_field_type t_struct_tree_t [StructField _t]).
    rewrite <- field_at_data_at. cancel. unfold tree_rep. entailer!.
  - forward. Exists p l g'. unfold nodebox_rep. Exists newt. entailer!.
Qed.

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (t, gv). Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
  - if_tac. subst p. entailer!. entailer!.
  - forward_call tt. contradiction.
  - if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Definition pushdown_left_inv (b_res: val)
           (t_res: @tree val) (gv: globals) : environ -> mpred :=
  EX b: val, EX ta: @tree val, EX x: Z, EX v: val, EX tb: @tree val,
  PROP  ()
  LOCAL (temp _t b; gvars gv)
  SEP   (mem_mgr gv; treebox_rep (T ta x v tb) b;
        (treebox_rep (pushdown_left ta tb) b -* treebox_rep t_res b_res)).

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (pushdown_left_inv b (pushdown_left ta tb) gv).
  - (* Precondition *)
    unfold pushdown_left_inv. Exists b ta x v tb. entailer!.
    apply derives_trans with (treebox_rep (T ta x v tb) b).
    2: cancel; apply -> wand_sepcon_adjoint; cancel.
    rewrite (treebox_rep_spec (T ta x v tb)). Exists p. entailer!.
  - (* Loop body *)
    unfold pushdown_left_inv. clear x v H H0. Intros b0 ta0 x vx tbc0.
    unfold treebox_rep at 1. Intros p0.
    forward. (* p = *t; *)
    simpl tree_rep. Intros pa pbc.
    forward. (* q = p->right *)
    forward_if.
    + subst. assert_PROP (tbc0 = E) by entailer!. subst.
      forward. (* q = p->left *)
      forward. (* *t=q *)
      forward_call (t_struct_tree, p0, gv). (* _free(_p); *)
      1: if_tac; entailer!.
      forward. (* return *)
      simpl tree_rep. simpl pushdown_left. cancel.
      apply modus_ponens_wand'. Exists pa. entailer!.
    + destruct tbc0 as [| tb0 y vy tc0]. 1: simpl tree_rep; Intros; easy.
      forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc).
      (* _turn_left(_t, _p, _q); *)
      Intros pc.
      forward. (* _t = &(_q -> _left); *)
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0.
      gather_SEP (data_at Ews _ _ b0) (malloc_token _ _ _). Intros.
      Opaque tree_rep. entailer!. Transparent tree_rep.
      apply RAMIF_PLAIN.trans'. now apply bst_left_entail.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  simpl tree_rep.
  Intros pb pc.
  forward. (* mid=r->left *)
  forward. (* l->right=mid *)
  forward. (* r->left=l *)
  forward. (* _l = r *)
  Exists pc.
  entailer!.
  simpl tree_rep.
  Exists pa pb.
  entailer!.
Qed.

Definition lookup_inv (b: val) (lock:val) (sh: share) (x: Z) gv (inv_names : invG)
           (Q : val -> mpred) (g:gname) (np tp: val)
           (root_t: tree_info) : environ -> mpred :=
  (EX tn: val, EX t : tree_info,
   PROP (lookup nullval x t = lookup nullval x root_t)
   LOCAL (temp _p tn; temp _tgt np; temp _t b; temp _l lock;
          temp _x (vint x); gvars gv)
   SEP (data_at sh (tptr t_struct_tree_t) np b;
       field_at sh t_struct_tree_t [StructField _lock] lock np;
       lock_inv sh lock (node_lock_inv g lock np);
       my_half g Tsh root_t; field_at Ews t_struct_tree_t [StructField _t] tp np;
       malloc_token Ews t_struct_tree_t np;
       tree_rep t tn; malloc_token Ews tlock lock;
       tree_rep t tn -* tree_rep root_t tp;
       atomic_shift
         (λ BST : tree, !! sorted_tree BST && public_half g BST) ∅ ⊤
         (λ (BST : tree) (ret : val),
          fold_right_sepcon
            [!! (sorted_tree BST ∧ ret = lookup nullval x BST) && public_half g BST])
         Q; mem_mgr gv))%assert.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. unfold treebox_rep. Intros a tp.
  change (tptr t_struct_tree) with
      (nested_field_type t_struct_tree_t [StructField _t]).
  rewrite <- field_at_data_at.
  forward. (* _p = (_tgt -> _t); *)
  forward_while (lookup_inv b lock sh x gv inv_names Q g np tp a).
  (* while (_p != (tptr tvoid) (0)) { *)
  - unfold lookup_inv. Exists tp a. entailer!. apply -> wand_sepcon_adjoint. cancel.
  - entailer!.
  - destruct t; unfold tree_rep at 1; fold tree_rep. 1: normalize. Intros pa pb.
    forward. (* _y = (_p -> _key); *)
    forward_if; [|forward_if].
    + forward. Exists (pa, t1). simpl fst. simpl snd. entailer!.
      * rewrite <- H0; simpl. rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''. apply -> wand_sepcon_adjoint. simpl.
        Exists pa pb. entailer!.
    + forward. Exists (pb, t2). simpl fst. simpl snd. entailer!.
      * rewrite <- H0. simpl. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''. apply -> wand_sepcon_adjoint. simpl.
        Exists pa pb. entailer!.
    + assert (x = k) by lia. subst x. clear H H3 H4. forward.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
      viewshift_SEP 0 (EX y, Q y * (!! (y = v) && (my_half g Tsh a))). {
        go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (ret : val),
                                     !! (sorted_tree BST ∧ ret = lookup nullval k BST)
                                     && public_half g BST * emp) Q *
                       my_half g Tsh a)).
        apply sync_commit_same. intro t. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists t. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H3; auto. subst t.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists v.
        entailer!. rewrite <- H0. simpl.
        now do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). } Intros y. subst y.
      forward_call (lock, sh, node_lock_inv g lock np).
      * assert (Frame =
                [Q v; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t [StructField _lock] lock np]);
          subst Frame; [ reflexivity | clear H].
        lock_props. unfold node_lock_inv. unfold treebox_rep. Exists a tp.
        rewrite (field_at_data_at Ews _ _ _ _). simpl nested_field_type.
        simpl fold_right_sepcon. cancel.
        apply modus_ponens_wand'. simpl. Exists pa pb. entailer!.
      * forward. Exists v. unfold nodebox_rep. Exists np. entailer!.
  - subst tn. sep_apply tree_rep_nullval. Intros. subst t. simpl in H0.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
    viewshift_SEP 0 (EX y, Q y * (!! (y = nullval) && (my_half g Tsh a))). {
      go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (ret : val),
                                     !! (sorted_tree BST ∧ ret = lookup nullval x BST)
                                     && public_half g BST * emp) Q *
                       my_half g Tsh a)).
        apply sync_commit_same. intro tr. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H2; auto. subst tr.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists nullval.
        entailer!. } Intros y. subst y.
    forward_call (lock, sh, node_lock_inv g lock np).
    + assert (Frame =
              [Q nullval; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
               field_at sh t_struct_tree_t [StructField _lock] lock np]);
        subst Frame; [ reflexivity | clear H1].
      lock_props. unfold node_lock_inv. unfold treebox_rep. Exists a tp.
      rewrite (field_at_data_at Ews _ _ _ _). simpl nested_field_type.
      simpl fold_right_sepcon. cancel. apply modus_ponens_wand.
    + forward. Exists nullval. unfold nodebox_rep. Exists np. entailer!.
Qed.

Definition insert_inv (b: val) (lock:val) (sh: share) (x: Z) (v: val)
           gv (inv_names : invG) (Q: mpred) (g:gname) (np: val)
           (root_t: tree_info) : environ -> mpred :=
  (EX tn: val, EX t : tree_info,
   PROP ()
   LOCAL (temp _tr tn; temp _tgt np; temp _t b; temp _l lock;
          temp _x (vint x); temp _value v; gvars gv)
   SEP (data_at sh (tptr t_struct_tree_t) np b;
       field_at sh t_struct_tree_t [StructField _lock] lock np;
       lock_inv sh lock (node_lock_inv g lock np);
       my_half g Tsh root_t;
       malloc_token Ews t_struct_tree_t np;
       treebox_rep t tn; malloc_token Ews tlock lock;
       treebox_rep (insert x v t) tn -* treebox_rep (insert x v root_t)
                   (field_address t_struct_tree_t [StructField _t] np);
       atomic_shift
         (λ BST : tree, !! sorted_tree BST && public_half g BST)
         ∅ ⊤
         (λ (BST : tree) (_ : ()),
          fold_right_sepcon
            [!! sorted_tree (insert x v BST) && public_half g (insert x v BST)])
         (λ _ : (), Q); mem_mgr gv))%assert.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. unfold treebox_rep. Intros tr tp.
  forward. (* _tr = &(_tgt -> _t); *)
  forward_loop (insert_inv b lock sh x v gv inv_names Q g np tr).
  - unfold insert_inv. Exists (field_address t_struct_tree_t [StructField _t] np) tr.
    entailer!. unfold treebox_rep at 1.
    Exists tp. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - unfold insert_inv. Intros tn t. unfold treebox_rep at 1. Intros p.
    forward. (* _p = *_tr; *)
    forward_if. (* if (_p == (tptr tvoid) (0)) { *)
    + subst p.
      forward_call (t_struct_tree, gv); [simpl; repeat (split; auto); rep_omega|].
      Intros p'.
      forward. (* *_tr = _p; *)
      forward. (* (_p -> _key) = _x; *)
      forward. (* (_p -> _value) = _value; *)
      forward. (* (_p -> _left) = (tptr tvoid) (0); *)
      forward. (* (_p -> _right) = (tptr tvoid) (0); *)
      assert_PROP (t = E) by entailer!. subst t. simpl tree_rep. Intros.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
      viewshift_SEP 0 (Q * my_half g Tsh (insert x v tr)). {
        go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (_ : ()),
                                     !! sorted_tree (insert x v BST) &&
                                     @public_half tree_ghost g (insert x v BST) * emp)
                                    (λ _ : (), Q) * my_half g Tsh tr)).
        apply sync_commit_gen1. intros tr1. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr1. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H2; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (insert x v tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply insert_sorted. }
      forward_call (lock, sh, node_lock_inv g lock np). (* _release(_l); *)
      * assert (Frame =
                [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t [StructField _lock] lock np]);
          subst Frame; [ reflexivity | clear H1].
        lock_props. unfold node_lock_inv. Exists (insert x v tr).
        simpl fold_right_sepcon. cancel. apply modus_ponens_wand'.
        unfold treebox_rep. Exists p'. simpl. Exists nullval nullval. entailer!.
      * forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
    + destruct t; simpl tree_rep. 1: normalize. Intros pa pb.
      forward. (* _y = (_p -> _key); *)
      forward_if; [|forward_if].
      * forward. (* _tr = &(_p -> _left); *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] p) t1.
        entailer!. simpl treebox_rep. rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'. now apply bst_left_entail.
      * forward. (* _tr = &(_p -> _right); *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] p) t2.
        entailer!. simpl treebox_rep. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'. now apply bst_right_entail.
      * assert (x = k) by lia. subst x. clear H2 H3 H4.
        forward. (* (_p -> _value) = _value; *)
        gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
        viewshift_SEP 0 (Q * my_half g Tsh (insert k v tr)). {
        go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (_ : ()),
                                     !! sorted_tree (insert k v BST) &&
                                     @public_half tree_ghost g (insert k v BST) * emp)
                                    (λ _ : (), Q) * my_half g Tsh tr)).
        apply sync_commit_gen1. intros tr1. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr1. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H3; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (insert k v tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply insert_sorted. }
        forward_call (lock, sh, node_lock_inv g lock np). (* _release(_l); *)
        -- assert (Frame =
                   [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                    field_at sh t_struct_tree_t [StructField _lock] lock np]);
             subst Frame; [ reflexivity | clear H2].
           lock_props. unfold node_lock_inv. Exists (insert k v tr).
           simpl fold_right_sepcon. cancel. apply modus_ponens_wand'.
           unfold treebox_rep. Exists p. simpl.
           do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). simpl tree_rep.
           Exists pa pb. entailer!.
        -- forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
Qed.

Definition delete_inv (b: val) (lock:val) (sh: share) (x: Z)
           gv (inv_names : invG) (Q: mpred) (g:gname) (np: val)
           (root_t: tree_info) : environ -> mpred :=
  (EX tn: val, EX t : tree_info,
   PROP ()
   LOCAL (temp _tr tn; temp _tgt np; temp _t b; temp _l lock;
          temp _x (vint x); gvars gv)
   SEP (data_at sh (tptr t_struct_tree_t) np b;
       field_at sh t_struct_tree_t [StructField _lock] lock np;
       lock_inv sh lock (node_lock_inv g lock np);
       my_half g Tsh root_t;
       malloc_token Ews t_struct_tree_t np;
       treebox_rep t tn; malloc_token Ews tlock lock;
       treebox_rep (delete x t) tn -* treebox_rep (delete x root_t)
                   (field_address t_struct_tree_t [StructField _t] np);
       atomic_shift
         (λ BST : tree, !! sorted_tree BST && public_half g BST)
         ∅ ⊤
         (λ (BST : tree) (_ : ()),
          fold_right_sepcon
            [!! sorted_tree (delete x BST) && public_half g (delete x BST)])
         (λ _ : (), Q); mem_mgr gv))%assert.

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. unfold treebox_rep. Intros tr tp.
  forward. (* _tr = &(_tgt -> _t); *)
  forward_loop (delete_inv b lock sh x gv inv_names Q g np tr).
  - unfold delete_inv. Exists (field_address t_struct_tree_t [StructField _t] np) tr.
    entailer!. unfold treebox_rep at 1.
    Exists tp. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - unfold delete_inv. Intros tn t. unfold treebox_rep at 1. Intros p.
    forward. (* _p = *_tr; *)
    forward_if. (* if (_p == (tptr tvoid) (0)) { *)
    + subst p. assert_PROP (t = E) by entailer!. subst t.
      simpl tree_rep. Intros. simpl delete.
      gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
      viewshift_SEP 0 (Q * my_half g Tsh (delete x tr)). {
        go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (_ : ()),
                                     !! sorted_tree (delete x BST) &&
                                     @public_half tree_ghost g (delete x BST) * emp)
                                    (λ _ : (), Q) * my_half g Tsh tr)).
        apply sync_commit_gen1. intros tr1. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr1. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H1; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (delete x tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply delete_sorted. }
      forward_call (lock, sh, node_lock_inv g lock np). (* _release(_l); *)
      * assert (Frame =
                [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t [StructField _lock] lock np]);
          subst Frame; [ reflexivity | clear H0].
        lock_props. unfold node_lock_inv. Exists (delete x tr).
        simpl fold_right_sepcon. cancel. apply modus_ponens_wand'.
        unfold treebox_rep. Exists nullval. simpl. entailer!.
      * forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
    + destruct t; simpl tree_rep. 1: normalize. Intros pa pb.
      forward. (* _y = (_p -> _key); *)
      forward_if; [|forward_if].
      * forward. (* _tr = &(_p -> _left); *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] p) t1.
        entailer!. simpl treebox_rep. rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'. now apply bst_left_entail.
      * forward. (* _tr = &(_p -> _right); *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] p) t2.
        entailer!. simpl treebox_rep. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'. now apply bst_right_entail.
      * assert (x = k) by lia. subst x. clear H1 H2 H3.
        unfold_data_at (data_at _ _ _ p).
        gather_SEP (field_at _ _ [StructField _left] _ _) (tree_rep _ pa).
        replace_SEP 0 (treebox_rep
                         t1 (field_address t_struct_tree [StructField _left] p)). {
          unfold treebox_rep; entailer!. Exists pa.
          rewrite field_at_data_at. simpl. entailer!. }
        gather_SEP (field_at _ _ [StructField _right] _ _) (tree_rep _ pb).
        replace_SEP 0 (treebox_rep
                         t2 (field_address t_struct_tree [StructField _right] p)). {
          unfold treebox_rep; entailer!. Exists pb.
          rewrite field_at_data_at. entailer!. }
        forward_call (t1, k, v, t2, tn, p, gv); [entailer! .. |].
        (* _pushdown_left(_tr); *)
        gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
        viewshift_SEP 0 (Q * my_half g Tsh (delete k tr)). {
        go_lower.
        rewrite <- (sepcon_emp
                      (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                        public_half g BST) ∅ ⊤
                                    (λ (BST : tree_info) (_ : ()),
                                     !! sorted_tree (delete k BST) &&
                                     @public_half tree_ghost g (delete k BST) * emp)
                                    (λ _ : (), Q) * my_half g Tsh tr)).
        apply sync_commit_gen1. intros tr1. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr1. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H2; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (delete k tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply delete_sorted. }
        forward_call (lock, sh, node_lock_inv g lock np). (* _release(_l); *)
        -- assert (Frame =
                   [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                    field_at sh t_struct_tree_t [StructField _lock] lock np]);
             subst Frame; [ reflexivity | clear H1].
           lock_props. unfold node_lock_inv. Exists (delete k tr).
           simpl fold_right_sepcon. cancel. apply modus_ponens_wand'.
           unfold treebox_rep. Intros p'. Exists p'. simpl.
           do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). cancel.
        -- forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
Qed.
