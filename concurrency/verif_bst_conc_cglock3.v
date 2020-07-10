Require Import Coq.Sets.Ensembles.
Require Import Coq.micromega.Lia.
Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import bst.bst_conc_cglock3.
Require Import bst.puretree.

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

Definition lookup_spec :=
 DECLARE _lookup
  WITH b: val, x: Z, t: @tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ tptr Tvoid ]
    PROP()
    LOCAL(temp ret_temp (lookup nullval x t))
    SEP (treebox_rep t b).

Program Definition lookup_conc_spec :=
  DECLARE _lookup_conc
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

Definition insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, t: @tree val, gv: globals
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP (Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
    SEP (mem_mgr gv; treebox_rep t b)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; treebox_rep (insert x v t) b).

Program Definition insert_conc_spec :=
  DECLARE _insert_conc
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

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: Z, t: @tree val, gv: globals
  PRE  [_t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP (Int.min_signed <= x <= Int.max_signed)
    LOCAL (temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP (mem_mgr gv; treebox_rep t b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv; treebox_rep (delete x t) b).

Program Definition delete_conc_spec :=
 DECLARE _delete_conc
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


Definition main_spec :=
  DECLARE _main
          WITH gv : globals
                      PRE  [] main_pre prog tt nil gv
                      POST [ tint ] main_post prog nil gv.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
                          freelock2_spec;
                          (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
                          surely_malloc_spec;
                          lookup_spec; lookup_conc_spec;
                          insert_spec; insert_conc_spec;
                          turn_left_spec; pushdown_left_spec;
                          delete_spec; delete_conc_spec;
                          (* spawn_spec; thread_func_spec; *) main_spec
       ]).

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

Definition lookup_inv (b0 p0: val) (t0: @tree val) (x: Z): environ -> mpred :=
  EX p: val, EX t: @tree val,
  PROP(lookup nullval x t = lookup nullval x t0)
  LOCAL(temp _p p; temp _x (Vint (Int.repr x)))
  SEP(data_at Ews (tptr t_struct_tree) p0 b0;
     tree_rep t p;  (tree_rep t p -* tree_rep t0 p0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros p.
  forward. (* p=*t; *)
  forward_while (lookup_inv b p t x).
  - Exists p t. entailer!.
    apply -> wand_sepcon_adjoint. cancel.
  - entailer!.
  - destruct t0; unfold tree_rep at 1; fold tree_rep. normalize.
    Intros pa pb.
    forward.
    forward_if; [ | forward_if ].
    + forward. (* p=p<-left *)
      Exists (pa,t0_1). unfold fst,snd.
      entailer!.
      * rewrite <- H0; simpl.
        rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        simpl. Exists pa pb; entailer!.
    + forward. (* p=p<-right *)
      Exists (pb,t0_2). unfold fst,snd.
      entailer!.
      * rewrite <- H0; simpl. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        simpl. Exists pa pb; entailer!.
    + assert (x=k) by omega. subst x. clear H H3 H4.
      forward. (* v=p->value *)
      forward. (* return v; *)
      unfold treebox_rep. entailer!.
      * rewrite <- H0. simpl. now do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]).
      * Exists p. cancel.
        apply modus_ponens_wand'. simpl tree_rep.
        Exists pa pb; entailer!.
  - forward. (* return NULL; *)
    entailer!. unfold treebox_rep. Exists p. cancel.
    apply modus_ponens_wand.
Qed.

Lemma malloc_token_address_eq: forall np,
    malloc_token Ews t_struct_tree_t np |--
                 !! (np = field_address t_struct_tree_t [StructField _t] np).
Proof.
  intros.
  assert_PROP (field_compatible t_struct_tree_t [StructField _t] np) by entailer!.
  assert_PROP (isptr np) by entailer!. apply prop_right. unfold field_address.
  rewrite if_true; auto. simpl. destruct np; inv H0.
  now rewrite offset_val_zero_Vptr.
Qed.

Definition insert_inv (b0: val) (t0: @tree val) (x: Z) (v: val) gv:
  environ -> mpred :=
  EX b: val, EX t: @tree val,
  PROP ()
  LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
  SEP (mem_mgr gv; treebox_rep t b;
      (treebox_rep (insert x v t) b -* treebox_rep (insert x v t0) b0)).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  forward_loop (insert_inv b t x v gv).
  - unfold insert_inv.
    Exists b t. entailer. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - unfold insert_inv.
    Intros b1 t1.
    unfold treebox_rep at 1. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + subst p1.
      forward_call (t_struct_tree, gv). 1: simpl; repeat (split; auto); rep_omega.
      Intros p'.
      forward. (* p->key=x; *)
      simpl data_at.
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      assert_PROP (t1= E) by entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp; auto.
      forward. (* *t = p; *)
      forward. (* return; *)
      cancel. apply modus_ponens_wand'. unfold treebox_rep. simpl tree_rep.
      Exists p' nullval nullval. entailer!.
    + destruct t1; simpl tree_rep. 1: normalize.
      Intros pa pb. clear H1.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      * forward. (* t=&p->left *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] p1) t1_1.
        entailer!. simpl.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail; auto.
      * forward. (* t=&p->right *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] p1) t1_2.
        entailer!. simpl. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      * assert (x=k) by omega.
        subst x.  clear H H1 H3.
        forward. (* p->value=value *)
        forward. (* return *) simpl treebox_rep.
        do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). cancel.
        apply modus_ponens_wand'.
        unfold treebox_rep. Exists p1.
        simpl tree_rep. Exists pa pb. entailer!.
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

Definition delete_inv (b0: val) (t0: @tree val) (x: Z) gv: environ -> mpred :=
  EX b: val, EX t: @tree val,
  PROP ()
  LOCAL (temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
  SEP (mem_mgr gv; treebox_rep t b;
      (treebox_rep (delete x t) b -* treebox_rep (delete x t0) b0)).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  forward_loop (delete_inv b t x gv).
  - Exists b t. entailer. cancel. rewrite <- wand_sepcon_adjoint. cancel.
  - unfold delete_inv.
    Intros b1 t1.
    unfold treebox_rep at 1. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + subst p1.
      assert_PROP (t1= E) by entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp; auto.
      forward. cancel.
      unfold treebox_rep at 1.
      apply modus_ponens_wand'.
      Exists nullval.
      simpl tree_rep.
      entailer!.
    + destruct t1; simpl tree_rep. 1: normalize.
      Intros pa pb. clear H0.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      * forward. (* t=&p->left *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _left] p1) t1_1.
        entailer!. simpl.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail; auto.
      * forward. (* t=&p->right *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _right] p1) t1_2.
        entailer!. simpl. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb. 2: now apply Z.ltb_lt.
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      * assert (x=k) by omega.
        subst x.
        unfold_data_at (data_at _ _ _ p1).
        gather_SEP (field_at _ _ [StructField _left] _ _) (tree_rep _ pa).
        replace_SEP
          0 (treebox_rep t1_1 (field_address t_struct_tree [StructField _left] p1)). {
          unfold treebox_rep; entailer!.
          Exists pa.
          rewrite field_at_data_at. simpl.
          entailer!.
        }
        gather_SEP (field_at _ _ [StructField _right] _ _) (tree_rep _ pb).
        replace_SEP
          0 (treebox_rep t1_2 (field_address t_struct_tree [StructField _right] p1)). {
          unfold treebox_rep; entailer!.
          Exists pb.
          rewrite field_at_data_at.
          entailer!.
        }
        forward_call (t1_1, k, v, t1_2, b1, p1, gv); [entailer! .. | ].
        forward. (* return *)
        simpl.
        do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). cancel.
        apply modus_ponens_wand'. auto.
Qed.

Lemma body_lookup_conc: semax_body Vprog Gprog f_lookup_conc lookup_conc_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. Intros tr.
  forward_call (field_address t_struct_tree_t [StructField _t] np, x, tr).
  - sep_apply (malloc_token_address_eq np). Intros. simpl snd. entailer!.
  - gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
    viewshift_SEP 0 (EX y, Q y * (!!(y = lookup nullval x tr) && (my_half g Tsh tr))).
    { go_lower.
      rewrite <- (sepcon_emp
                    (atomic_shift (λ BST : tree_info, !! sorted_tree BST &&
                                                      public_half g BST) ∅ ⊤
                                  (λ (BST : tree_info) (ret : val),
                                   !! (sorted_tree BST ∧ ret = lookup nullval x BST)
                                   && public_half g BST * emp) Q *
                     my_half g Tsh tr)).
        apply sync_commit_same. intro a. Intros.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists a. cancel.
        apply imp_andp_adjoint. Intros. rewrite if_true in H2; auto. subst a.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        Exists (lookup nullval x tr). entailer!. } Intros y. subst y.
    forward_call (lock, sh, node_lock_inv g lock np).
    + assert (Frame =
              [Q (lookup nullval x tr); mem_mgr gv;
               data_at sh (tptr t_struct_tree_t) np b;
               field_at sh t_struct_tree_t [StructField _lock] lock np]);
        subst Frame; [ reflexivity | clear H0].
      lock_props. unfold node_lock_inv. Exists tr.
      simpl fold_right_sepcon. cancel.
    + forward. Exists (lookup nullval x tr). unfold nodebox_rep. Exists np. entailer!.
Qed.

Lemma body_insert_conc: semax_body Vprog Gprog f_insert_conc insert_conc_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. Intros tr.
  forward_call (field_address t_struct_tree_t [StructField _t] np, x, v, tr, gv).
  - sep_apply (malloc_token_address_eq np). Intros. simpl snd. entailer!.
  - gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
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
    + assert (Frame =
                [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t [StructField _lock] lock np]);
          subst Frame; [ reflexivity | clear H1].
      lock_props. unfold node_lock_inv. Exists (insert x v tr).
      simpl fold_right_sepcon. cancel.
    + forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
Qed.

Lemma body_delete_conc: semax_body Vprog Gprog f_delete_conc delete_conc_spec.
Proof.
  start_function.
  unfold nodebox_rep. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g lock np)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. Intros tr.
  forward_call (field_address t_struct_tree_t [StructField _t] np, x, tr, gv).
  - sep_apply (malloc_token_address_eq np). Intros. simpl snd. entailer!.
  - gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
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
    + assert (Frame =
              [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
               field_at sh t_struct_tree_t [StructField _lock] lock np]);
        subst Frame; [ reflexivity | clear H0].
      lock_props. unfold node_lock_inv. Exists (delete x tr).
      simpl fold_right_sepcon. cancel.
    + forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
Qed.
