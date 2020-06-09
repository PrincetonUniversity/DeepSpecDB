Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc_cglock.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import Coq.micromega.Lia.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

  Inductive tree : Type :=
  | E : tree
  | T: tree -> key -> V -> tree -> tree.

  Inductive In (k : key) : tree -> Prop :=
  | InRoot l r x v:  (k = x) -> In k (T l x v r )
  | InLeft l r x v': In k l -> In k (T l x v' r)
  | InRight l r x v': In k r -> In k (T l x v' r).

  Definition lt (t: tree) (k: key) := forall x : key, In x t -> k < x .
  Definition gt (t: tree) (k: key) := forall x : key, In x t -> k > x .

  Inductive sorted_tree : tree -> Prop :=
  | Sorted_Empty : sorted_tree E
  | Sorted_Tree x v l r : sorted_tree l -> sorted_tree r ->
                          gt l x -> lt r x -> sorted_tree (T l x v r ).

  Definition empty_tree : tree := E.

  Fixpoint lookup (x: key) (t : tree) : V :=
    match t with
    | E => default
    | T tl k v tr => if x <? k then lookup x tl
                     else if k <? x then lookup x tr
                          else v
    end.

  Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
    match s with
    | E => T E x v E
    | T a y v' b => if  x <? y then T (insert x v a) y v' b
                    else if y <? x then T a y v' (insert x v b)
                         else T a x v b
    end.

  Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
    match bc with
    | E => a
    | T b y vy c => T (pushdown_left a b) y vy c
    end.

  Fixpoint delete (x: key) (s: tree) : tree :=
    match s with
    | E => E
    | T a y v' b => if  x <? y then T (delete x a) y v' b
                    else if y <? x then T a y v' (delete x b)
                         else pushdown_left a b
    end.

  Lemma pushdown_left_In: forall (t1 t2: tree) (x: key),
      In x (pushdown_left t1 t2) -> In x t1 \/ In x t2.
  Proof.
    intros. revert t2 H. induction t2; intros; simpl in *; auto. inv H.
    - right. now apply InRoot.
    - apply IHt2_1 in H1. destruct H1; [left | right]; auto. now apply InLeft.
    - right. now apply InRight.
  Qed.

  Lemma delete_In: forall (x: key) (t: tree) (y: key), In y (delete x t) -> In y t.
  Proof.
    intros. revert t H. induction t; intros; simpl in *; auto. destruct (x <? k).
    - inv H; try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
      apply IHt1 in H1. now apply InLeft.
    - destruct (k <? x).
      + inv H; try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
        apply IHt2 in H1. now apply InRight.
      + apply pushdown_left_In in H. destruct H; [apply InLeft | apply InRight]; easy.
  Qed.

  Lemma pushdown_left_sorted: forall (t1 t2: tree),
      sorted_tree t1 -> sorted_tree t2 -> (forall x y, In x t1 -> In y t2 -> x < y) ->
      sorted_tree (pushdown_left t1 t2).
  Proof.
    intros. revert t2 H0 H1. induction t2; intros; simpl in H0 |-* ; auto.
    inv H0. constructor; auto.
    - apply IHt2_1; auto. intros. apply H1; auto. now apply InLeft.
    - intros z ?. apply pushdown_left_In in H0. destruct H0.
      + apply Z.lt_gt, H1; auto. now apply InRoot.
      + now specialize (H8 _ H0).
  Qed.

  Lemma delete_sorted: forall (x: key) (t: tree),
      sorted_tree t -> sorted_tree (delete x t).
  Proof.
    intros. revert t H. induction t; intros; simpl; auto. inv H.
    destruct (x <? k) eqn: ?.
    - apply Z.ltb_lt in Heqb. constructor; auto. intros y ?.
      apply delete_In in H. now apply H6.
    - apply Z.ltb_ge in Heqb. destruct (k <? x) eqn: ?.
      + apply Z.ltb_lt in Heqb0. constructor; auto. intros y ?.
        apply delete_In in H. now apply H7.
      + apply pushdown_left_sorted; auto. intros y z ? ?.
        apply H6 in H. apply H7 in H0. lia.
  Qed.

  Lemma value_in_tree: forall x v k (t: tree),
      In k (insert x v t ) -> (x = k) \/ In k t.
  Proof.
    intros. induction t; simpl in H. 1: inversion H; subst; auto.
    destruct (x <? k0) eqn: Heqn.
    - inversion H; subst.
      + right. apply InRoot. auto.
      + specialize (IHt1 H1). destruct IHt1. left. auto. right. apply InLeft. auto.
      + right. apply InRight. auto.
    - destruct (k0 <? x) eqn: Heqn'.
      + inversion H; subst.
        * right. apply InRoot. auto.
        * right. apply InLeft. auto.
        * specialize (IHt2 H1). destruct IHt2. left. auto. right. apply InRight. auto.
      + assert (k0 = x).
        { apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. lia. }
        subst. right. inversion H; subst.
        * apply InRoot. auto.
        * apply InLeft. auto.
        * apply InRight. auto.
  Qed.

  Lemma insert_sorted : forall x v (t: tree),
      sorted_tree t -> sorted_tree (insert x v t).
  Proof.
    intros. induction t.
    - simpl. apply Sorted_Tree; auto; [unfold gt | unfold lt]; intros; easy.
    - simpl. destruct (x <? k)  eqn: Heqn.
      + constructor.
        * apply IHt1. inversion H; auto.
        * inversion H; auto.
        * unfold gt. intros. apply value_in_tree in H0. destruct H0. subst.
          apply Z.ltb_lt in Heqn. lia.  inversion H;subst. auto.
        * unfold lt. intros. inversion H; subst. auto.
      + destruct (k <? x) eqn: Heqn'.
        * apply Sorted_Tree.
          -- inversion H; subst. auto.
          -- apply IHt2. inversion H. auto.
          -- unfold gt. intros. inversion H; subst. auto.
          -- unfold lt. intros. apply value_in_tree in H0. destruct H0.
             ++ subst. apply Z.ltb_lt in Heqn'. lia.
             ++ inversion H; subst. auto.
        * assert (k = x).
          {apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. lia. }
          subst. apply Sorted_Tree; inversion H; subst; auto.
  Qed.

End TREES.

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
  WITH b:_, sh:_, lock:_, x:_, gv:_, g:_
  PRE [_t OF (tptr (tptr t_struct_tree_t)), _x OF tint]
   PROP (readable_share sh;
        Int.min_signed <= x <= Int.max_signed; is_pointer_or_null lock)
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
  WITH b:_, sh:_, lock:_, x:_, v:_, gv:_, g:_
  PRE [_t OF (tptr (tptr t_struct_tree_t)), _x OF tint, _value OF (tptr tvoid)]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed;
       is_pointer_or_null v; is_pointer_or_null lock )
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!! sorted_tree BST && public_half g BST)
  POST [tvoid]
   PROP ()
   LOCAL ()
   SEP (mem_mgr gv; nodebox_rep g sh lock b) |
        (!! sorted_tree (insert x v BST) && public_half g (insert x v BST)).

Definition main_spec :=
  DECLARE _main
          WITH gv : globals
                      PRE  [] main_pre prog tt nil gv
                      POST [ tint ] main_post prog nil gv.


Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
                          freelock2_spec;
                          (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
                          surely_malloc_spec;
                          lookup_spec; insert_spec;
                          (* turn_left_spec; pushdown_left_spec; delete_spec ; *)
                          (* spawn_spec; thread_func_spec; *) main_spec
       ]).

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
      * rewrite <- H1; simpl. rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''. apply -> wand_sepcon_adjoint. simpl.
        Exists pa pb. entailer!.
    + forward. Exists (pb, t2). simpl fst. simpl snd. entailer!.
      * rewrite <- H1. simpl. rewrite if_falseb. 2: apply Z.ltb_ge; lia.
        rewrite if_trueb; auto. now apply Z.ltb_lt.
      * apply RAMIF_PLAIN.trans''. apply -> wand_sepcon_adjoint. simpl.
        Exists pa pb. entailer!.
    + assert (x = k) by lia. subst x. clear H H4 H5. forward.
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
        apply imp_andp_adjoint. Intros. rewrite if_true in H4; auto. subst t.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists v.
        entailer!. rewrite <- H1. simpl.
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
  - subst tn. sep_apply tree_rep_nullval. Intros. subst t. simpl in H1.
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
        apply imp_andp_adjoint. Intros. rewrite if_true in H3; auto. subst tr.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro].
        rewrite <- wand_sepcon_adjoint.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists nullval.
        entailer!. } Intros y. subst y.
    forward_call (lock, sh, node_lock_inv g lock np).
    + assert (Frame =
              [Q nullval; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
               field_at sh t_struct_tree_t [StructField _lock] lock np]);
        subst Frame; [ reflexivity | clear H].
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
         (λ BST : verif_bst_conc_cglock2.tree, !! sorted_tree BST && public_half g BST)
         ∅ ⊤
         (λ (BST : verif_bst_conc_cglock2.tree) (_ : ()),
          fold_right_sepcon
            [!! sorted_tree (insert x v BST) && public_half g (insert x v BST)])
         (λ _ : (), Q); mem_mgr gv))%assert.

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
        apply imp_andp_adjoint. Intros. rewrite if_true in H3; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (insert x v tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply insert_sorted. }
      forward_call (lock, sh, node_lock_inv g lock np). (* _release2(_l); *)
      * assert (Frame =
                [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                 field_at sh t_struct_tree_t [StructField _lock] lock np]);
          subst Frame; [ reflexivity | clear H2].
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
      * assert (x = k) by lia. subst x. clear H3 H4 H5.
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
        apply imp_andp_adjoint. Intros. rewrite if_true in H4; auto. subst tr1.
        eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists tr tr.
        entailer!. 2: exact tt. rewrite <- wand_sepcon_adjoint.
        sep_apply (public_update g tr tr (insert k v tr)). Intros.
        apply ghost_seplog.bupd_mono. entailer!. now apply insert_sorted. }
        forward_call (lock, sh, node_lock_inv g lock np). (* _release2(_l); *)
        -- assert (Frame =
                   [Q; mem_mgr gv; data_at sh (tptr t_struct_tree_t) np b;
                    field_at sh t_struct_tree_t [StructField _lock] lock np]);
             subst Frame; [ reflexivity | clear H3].
           lock_props. unfold node_lock_inv. Exists (insert k v tr).
           simpl fold_right_sepcon. cancel. apply modus_ponens_wand'.
           unfold treebox_rep. Exists p. simpl.
           do 2 (rewrite if_falseb; [|apply Z.ltb_irrefl]). simpl tree_rep.
           Exists pa pb. entailer!.
        -- forward. (* return; *) unfold nodebox_rep. Exists np. entailer!.
Qed.
