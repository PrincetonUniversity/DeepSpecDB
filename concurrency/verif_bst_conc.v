Require Import VST.progs.conclib.
Require Import bst.bst_conc.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.



Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.
 
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

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Eval hnf in reptype (nested_field_type t_struct_tree_t [StructField _lock]).

Fixpoint tree_rep (t: tree val) (p: val) : mpred := (*tree strored in p correctly, see struct tree, representation in memory*)
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.


Definition lsh1 := fst (slice.cleave Ews).
Definition lsh2 := snd (slice.cleave Ews).

Lemma readable_lsh1 : readable_share lsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_lsh2 : readable_share lsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma lsh1_lsh2_join : sepalg.join lsh1 lsh2 Ews.
Proof.
  apply slice.cleave_join; unfold lsh1, lsh2; destruct (slice.cleave Ews); auto.
Qed.

Hint Resolve readable_lsh1 readable_lsh2 lsh1_lsh2_join.

Definition ltree tl lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (tl (p, lock))).


Definition node_rep tl (t: tree val) (np: val) : mpred :=
 match t with
 | E => !!(np=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) && EX pa : val, EX pb : val, EX locka : val, EX lockb : val,  
    data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) np * malloc_token Ews t_struct_tree np *
    |>ltree tl lsh1 pa locka * |>ltree tl lsh1 pb lockb
 end.

Definition t_lock_pred tl p (lock: val) :=
  EX t : tree val, EX tp : val, (field_at Ews (t_struct_tree_t) [StructField _t] tp p *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p * node_rep tl t tp) *
  (malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock lock).

Definition t_lock_pred' tl p lock :=
  selflock (t_lock_pred tl p lock) lsh2 lock.

Definition t_lock_pred_uncurry (tl : ((val * val) -> mpred)) := fun '(p, lock) =>
  t_lock_pred' tl p lock.

Definition t_lock_pred'' := HORec t_lock_pred_uncurry.

Definition t_lock_pred''' p lock := t_lock_pred'' (p,lock).

Definition ltree_final lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (t_lock_pred''' p lock)).

Definition node_rep' (t: tree val) (np: val) : mpred :=
 match t with
 | E => !!(np=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) && EX pa : val, EX pb : val, EX locka : val, EX lockb : val,  
    data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) np * malloc_token Ews t_struct_tree np *
    |>ltree_final lsh1 pa locka * |>ltree_final lsh1 pb lockb
 end.

Lemma ltree_eqp : forall P Q a b c,
  ALL x : _, |> (P x <=> Q x) |-- |> ltree P a b c <=> |> ltree Q a b c.
Proof.
  intros; unfold ltree.
  rewrite !later_andp; apply eqp_andp; [apply eqp_refl|].
  rewrite !later_sepcon; apply eqp_sepcon; [apply eqp_refl|].
  apply lock_inv_nonexpansive2.
Qed.

Definition t_lock_pred_final p lock := EX t : tree val, EX tp : val,
  field_at Ews t_struct_tree_t [StructField _t] tp p * field_at lsh2 t_struct_tree_t [StructField _lock] lock p * node_rep' t tp *
  (malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock lock).

Lemma eqp_subp : forall P Q, P <=> Q |-- P >=> Q.
Proof.
  intros; change (predicates_hered.derives (P <=> Q) (P >=> Q)).
  apply subtypes.eqp_subp, predicates_hered.derives_refl.
Qed.

Theorem t_lock_pred_def : forall p lock, 
  t_lock_pred''' p lock = (EX t : _, EX tp : _, field_at Ews t_struct_tree_t [StructField _t] tp p *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p * node_rep' t tp *
    (malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock lock)) *
    |> lock_inv lsh2 lock (t_lock_pred''' p lock).
Proof.
  intros.
  unfold t_lock_pred'''.
  assert (HOcontractive t_lock_pred_uncurry).
  { apply prove_HOcontractive; intros ?? (?, ?).
    unfold t_lock_pred_uncurry, t_lock_pred'.
    eapply derives_trans, eqp_subp.
    eapply derives_trans, nonexpansive_entail with (F := fun P => selflock P lsh2 v0), selflock_nonexpansive.
    unfold t_lock_pred.
    apply eqp_exp; intros t.
    apply eqp_exp; intros.
    apply eqp_sepcon, eqp_refl.
    apply eqp_sepcon; [apply eqp_refl|].
    destruct t; simpl node_rep.
    { apply eqp_refl. }
    apply eqp_andp; [apply eqp_refl|].
    repeat (apply eqp_exp; intros).
    rewrite !sepcon_assoc; apply eqp_sepcon; [apply eqp_refl|].
    apply eqp_sepcon; [apply eqp_refl|].
    apply eqp_sepcon; eapply derives_trans, ltree_eqp; apply allp_right; intros; eapply allp_left; rewrite eqp_later; apply derives_refl. }
  etransitivity; [eapply equal_f, HORec_fold_unfold; auto|].
  unfold t_lock_pred_uncurry at 1.
  unfold t_lock_pred'.
  rewrite selflock_eq.
  unfold t_lock_pred at 1.
  unfold t_lock_pred''.
  etransitivity; [|rewrite HORec_fold_unfold; auto]; reflexivity.
Qed.


Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree_t) p b.


Definition nodebox_rep (sh : share) (lock : val) (nb: val) :=
 EX np: val, data_at Ews (tptr (t_struct_tree_t)) np nb * ltree_final sh np lock (**
    (* extra piece of lock pointer *) field_at lsh2 t_struct_tree_t [StructField _lock] lock np*).

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

Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH gv: globals, u : unit
  PRE  [  ]
       PROP() LOCAL(gvars gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX v:val, EX lock:val,
    PROP()
    LOCAL(temp ret_temp v)
    SEP (mem_mgr gv; nodebox_rep lsh1 lock v;
           malloc_token Ews (tptr t_struct_tree_t) v).

(*Definition insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)); temp _value v)
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (insert x v t) b).
*)  
    
(*maybe I should add the treebox_rep in the ltree definition *)
(*NEW*)
Definition insert_spec :=
  DECLARE _insert
  WITH sh : share, lock : val,
       b: val, x: Z, v: val, t: tree val, gv : globals
  PRE [  _t OF (tptr (tptr t_struct_tree_t)), _x OF tint,
        _value OF (tptr Tvoid)  ]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
   SEP (mem_mgr gv; nodebox_rep sh lock b)
  POST [ Tvoid ]
   PROP ()
   LOCAL ()
   SEP (mem_mgr gv; nodebox_rep sh lock b).
(*Definition insert_spec prog := DECLARE (ext_link_prog prog "insert") insert_spec'.*)    

Definition lookup_spec :=
 DECLARE _lookup
  WITH sh : share, b: val, x: Z, v: val, lock : val
  PRE  [ _t OF (tptr (tptr t_struct_tree_t(*t_struct_tree*))), _x OF tint  ]
    PROP(readable_share sh; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (nodebox_rep sh lock b)
  POST [ tptr Tvoid ]
   EX ret : val,
    PROP()
    LOCAL(temp ret_temp ret)
    SEP (nodebox_rep sh lock b).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: Z, vx: val, tb: tree val, y: Z, vy: val, tc: tree val, b: val, l: val, pa: val, r: val
  PRE  [ __l OF (tptr (tptr (Tstruct _tree noattr))),
        _l OF (tptr (Tstruct _tree noattr)),
        _r OF (tptr (Tstruct _tree noattr))]
    PROP(Int.min_signed <= x <= Int.max_signed; is_pointer_or_null vx)
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (data_at Tsh (tptr t_struct_tree) l b;
         data_at Tsh t_struct_tree (Vint (Int.repr x), (vx, (pa, r))) l;
         tree_rep ta pa;
         tree_rep (T tb y vy tc) r)
  POST [ Tvoid ] 
    EX pc: val,
    PROP(Int.min_signed <= y <= Int.max_signed; is_pointer_or_null vy)
    LOCAL()
    SEP (data_at Tsh (tptr t_struct_tree) r b;
         data_at Tsh t_struct_tree (Vint (Int.repr y), (vy, (l, pc))) r;
         tree_rep (T ta x vx tb) l;
         tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: Z, v: val, tb: tree val, b: val, p: val
  PRE  [ _t OF (tptr (tptr (Tstruct _tree noattr)))]
    PROP(Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) v)
    LOCAL(temp _t b)
    SEP (data_at Tsh (tptr t_struct_tree) p b;
         field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p;
         field_at Tsh t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: Z, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (delete x t) b).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH sh: share, lock: val, p: val
  PRE  [ _p OF (tptr t_struct_tree) ]
       PROP() LOCAL(temp _p p) SEP (ltree_final Ews p lock)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP ().

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH sh: share, lock: val, b: val
  PRE  [ _b OF (tptr (tptr t_struct_tree)) ]
       PROP() LOCAL(temp _b b) SEP (nodebox_rep Ews lock b; malloc_token Ews (tptr t_struct_tree_t) b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP ().


Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.*)

(*no freelock_spec, spawn_spec, freelock2_spec, release2_spec*)
Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
    surely_malloc_spec; treebox_new_spec;
    tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec
  ]).

Lemma node_rep_saturate_local:
   forall t p, node_rep' t p |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!.
Intros pa pb locka lockb. entailer!.
Qed.

Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer:
  forall t p, node_rep' t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve node_rep_valid_pointer: valid_pointer.

Lemma ltree_final_saturate_local:
  forall lsh p lock, ltree_final lsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree_final; entailer!.
Qed.
Hint Resolve ltree_final_saturate_local: saturate_local.

(*Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree_t) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

Definition insert_inv (b0: val) (t0: tree val) (x: Z) (v: val): environ -> mpred :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(treebox_rep t b;  (treebox_rep (insert x v t) b -* treebox_rep (insert x v t0) b0)). (* b0 which points to t0 which is the entire tree *)
*)

Definition insert_inv (b0: val) (lsh0 : share) (lock0 : val) (t0: tree val) (x: Z) (v: val) gv: environ -> mpred :=
  EX p: val, EX lock: val,
  PROP()
  LOCAL(temp _l lock; temp _tgt p; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
  SEP(mem_mgr gv; |>lock_inv lsh2 lock (t_lock_pred''' p lock); t_lock_pred_final p lock;
      nodebox_rep lsh0 lock0 b0).


Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros. Check RAMIF_PLAIN.solve.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp. auto.
  + rewrite emp_sepcon. auto.
Qed.

Lemma node_rep_nullval: forall t,
  node_rep' t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl node_rep'.
  Intros pa pb locka lockb. entailer!.
Qed.

Hint Resolve node_rep_nullval: saturate_local.

(*Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- nodebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.*)

(*Lemma bst_left_entail: forall sh1 lock1 p1 b1 pa tp locka,
  lock_inv sh1 lock1 (t_lock_pred''' p1 lock1) *
  data_at Ews (tptr t_struct_tree_t) p1 b1 *
  field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1
  |-- data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
    ltree_final sh1 pa locka *
    (data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
     ltree_final sh1 pa locka -*
     data_at Ews (tptr t_struct_tree_t) p1 b1 *
     field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1 *
     lock_inv sh1 lock1 (t_lock_pred''' p1 lock1)).
Proof.
  intros.
  unfold ltree_final at 1; entailer!.
  { admit. }
  unfold_data_at (data_at _ _ _ b1). Check field_at_data_at.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  Check wand_sepcon_adjoint.
  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  node_rep t1 p1 * node_rep t2 p2
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
*)
Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; omega)
                          | rewrite if_falseb by (apply Z.ltb_ge; omega)].

Lemma t_lock_exclusive : forall p l,
  exclusive_mpred (t_lock_pred''' p l).
Proof.
  intros. rewrite t_lock_pred_def.
  eapply derives_exclusive, exclusive_sepcon1 with 
  (P := EX tp : _, field_at Ews t_struct_tree_t [StructField _t] tp p)
  (Q:= EX t0 : tree val, EX tp : val, _ * node_rep t_lock_pred'' t0 tp * malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock l * _).
  - unfold t_lock_pred_final. Intros t0 tp. Exists tp. cancel. Exists t0 tp. apply derives_refl.
  - apply ex_field_at_exclusive; auto.
    simpl. omega.
Qed.
Hint Resolve t_lock_exclusive.

Lemma t_lock_rec : forall p l,
  rec_inv lsh2 l (t_lock_pred_final p l) (t_lock_pred''' p l).
Proof.
  intros; apply t_lock_pred_def.
Qed.
Hint Resolve t_lock_rec.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (tarray (tptr tvoid) 2, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros l. (* lock_t *l *)
  forward_call (l, Ews, t_lock_pred''' newt l).
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
  forward_call (l, lsh2, t_lock_pred_final newt l, t_lock_pred''' newt l).
  { lock_props.
    rewrite t_lock_pred_def at 3.
    Exists (E : tree val) (vint 0). unfold_data_at (data_at Ews t_struct_tree_t _ _).
    unfold node_rep'. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
    entailer!. }
  forward.
  Exists p l.
  unfold nodebox_rep.
  unfold ltree_final.
  Exists newt.
  entailer!.
Qed.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof. 
  start_function. rename H into Hx.
  unfold nodebox_rep; Intros p.
  forward.
  unfold ltree_final; Intros.
  forward.
  forward_call (lock, sh, t_lock_pred''' p lock).
  rewrite t_lock_pred_def at 2; Intros t tp.
  forward.

(* unfold data_at.
  unfold field_at; Intros. simpl. unfold at_offset. rewrite offset_val_force_ptr, isptr_force_ptr by apply H.
  rename H into FCb.
  unfold data_at_rec. simpl. forward.
 2: apply H.
Search force_ptr. simpl. Search offset_val 0. simpl. forward. (* unfold_data_at 1%nat. (data_at _ _ _ _).*)
Search field_at.
unfold_data_at at 1.
  forward. entailer.
  eapply semax_pre; [ 
    | apply (semax_loop _ (insert_inv b sh lock t x v) (insert_inv b sh lock t x v) )]. 
  * (* Precondition *)
    unfold insert_inv. 
    Exists b lock sh. entailer!. apply wand_refl_cancel_right.
  * (* Loop body *)
    unfold insert_inv.
    Intros b1 lock1 sh1.
    forward. (* Sskip *)
    unfold nodebox_rep at 1. Intros p1.
    forward. (* tgt=*t; *)
      unfold ltree_final. entailer!.
    unfold ltree_final. Intros.  
    (*assert_PROP
    (offset_val 4 p1 = field_address (tlock) [StructField _lock] p1).
      1: entailer!. rewrite field_address_offset.
         autorewrite with norm. unfold offset_val.*)
    forward. (* l=tgt->lock *)
      1: rewrite lock_inv_isptr. entailer!.
    forward_call(lock1, sh1, t_lock_pred''' sh1 p1 lock1).   (* acquire(l) *) 
    rewrite t_lock_pred_def at 2.  unfold t_lock_pred', t_lock_pred.
    Intros t1 tp.  
    forward. (*p=tgt->t*)
    forward_if.
    + (* then clause *)
      subst tp.
      Time forward_call (sizeof t_struct_tree_t).
        1: simpl. rep_omega.
      Intros p1'. 
      rewrite memory_block_data_at_ by auto.
      Time forward_call (sizeof t_struct_tree_t). 
        1: simpl. rep_omega.
      Intros p2'.
      rewrite memory_block_data_at_ by auto.
      forward. (* p1->t=NULL *)
      simpl.
      forward. (* p1->t=NULL *)
      simpl. 
      forward_call (sizeof tlock).
        1: simpl. rep_omega.
      Intros l1.
*)
Admitted.

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep; Intros p.
  forward.
  unfold ltree_final; Intros.
  forward.
  forward_call (lock, sh, t_lock_pred''' p lock).
  eapply semax_pre; [
    | apply (semax_loop _ (insert_inv b sh lock t x v gv) (insert_inv b sh lock t x v gv) )].
  * (* Precondition *)
    unfold insert_inv.
    rewrite t_lock_pred_def at 2; Intros t0 tp.
    Exists p lock.
    unfold ltree_final; entailer!.
    unfold nodebox_rep, t_lock_pred_final.
    Exists p t0 tp; unfold ltree_final; entailer!.
  * (* Loop body *)
    unfold insert_inv.
    Intros p1 lock1.
    forward. (* Sskip *)
    unfold t_lock_pred_final; Intros t1 tp.
    forward. (*p=tgt->t*)
    forward_if.
    + (* then clause *)
      subst tp.
      forward_call (t_struct_tree_t, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p1'.
      forward_call (t_struct_tree_t, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p2'.
      forward. (* p1->t=NULL *)
      simpl.
      forward. (* p1->t=NULL *)
      simpl. 
      forward_call (tlock, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros l1.
      forward_call(l1, Ews, t_lock_pred''' p1' l1). 
      forward. (*p1->lock = l1*) 
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      forward_call(l1, lsh2, t_lock_pred_final p1' l1, t_lock_pred''' p1' l1).
      { lock_props.
        rewrite t_lock_pred_def at 3. Exists (E : tree val) (vint 0).
        unfold_data_at 2%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
         simpl. entailer!. }
      deadvars.
      forward_call (tlock, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros l2.
      forward_call(l2, Ews, t_lock_pred''' p2' l2). 
      forward. (*p2->lock = l2*)
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      forward_call(l2, lsh2, t_lock_pred_final p2' l2, t_lock_pred''' p2' l2).
      { lock_props.
        rewrite t_lock_pred_def at 3. Exists (E : tree val) (vint 0).
        unfold_data_at 1%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
        simpl. entailer!. }
      forward_call (t_struct_tree, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p'.
      forward. (* tgt->t=p; *)  
      forward. (* p->key=x; *)
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      assert_PROP (t1= (@E _)) by entailer!.
      subst t1. simpl node_rep.
      assert_PROP (field_compatible t_struct_tree_t [] p1) by entailer!.
      forward_call(lock1, lsh2, t_lock_pred_final p1 lock1, t_lock_pred''' p1 lock1).
      { lock_props.
        setoid_rewrite t_lock_pred_def at 4.
        Exists (T E x v E) p'. cancel. simpl. Exists p1' p2' l1 l2. unfold ltree_final. entailer!.
        rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
        entailer!.
        { rewrite field_compatible_cons in H6, H8; destruct H6, H8; auto. } }
      forward. (* return; *)
    + (* else clause *)
      destruct t1.
      { simpl node_rep'. normalize. }
      simpl node_rep'.
      Intros pa pb locka lockb.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        rewrite (field_at_data_at _ _ [StructField _left]); simpl.
        assert_PROP (field_compatible t_struct_tree [StructField _left] tp) by entailer!.
        rewrite field_compatible_field_address by auto.
        unfold ltree_final at 1; Intros.
        forward.
        forward_call (locka, lsh1, t_lock_pred''' pa locka).
        rewrite t_lock_pred_def at 2.
        Intros ta tpa.
        forward_call(lock1, lsh2, t_lock_pred_final p1 lock1, t_lock_pred''' p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 4. Exists (T t1_1 k v0 t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree_final; entailer!.
          unfold_data_at (data_at _ _ _ tp); cancel.
          rewrite (field_at_data_at _ _ [StructField _left]), field_compatible_field_address by auto; simpl; cancel.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        Exists pa locka.
        unfold ltree_final; entailer!.
        unfold t_lock_pred_final.
        Exists ta tpa; cancel.
      - (* Inner if, second branch:  k<x *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        rewrite (field_at_data_at _ _ [StructField _left]); simpl.
        assert_PROP (field_compatible t_struct_tree [StructField _left] tp) by entailer!.
        rewrite field_compatible_field_address by auto.
        unfold ltree_final at 2; Intros.
        forward.
        forward_call (lockb, lsh1, t_lock_pred''' pb lockb).
        rewrite t_lock_pred_def at 2.
        Intros tb tpb.
        forward_call(lock1, lsh2, t_lock_pred_final p1 lock1, t_lock_pred''' p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 4. Exists (T t1_1 k v0 t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree_final; entailer!.
          unfold_data_at (data_at _ _ _ tp); cancel.
          rewrite (field_at_data_at _ _ [StructField _left]), field_compatible_field_address by auto; simpl; cancel.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        Exists pb lockb.
        unfold ltree_final; entailer!.
        unfold t_lock_pred_final.
        Exists tb tpb; cancel.
      - (* x = k *)
        forward.
        forward_call(lock1, lsh2, t_lock_pred_final p1 lock1, t_lock_pred''' p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 2. Exists (T t1_1 k v t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree_final; entailer!.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        forward.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize.
Qed.
