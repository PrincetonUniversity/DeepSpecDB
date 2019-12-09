Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc.
Require Import VST.atomics.general_locks.


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


Definition lsh1 := fst (slice.cleave Ews).
Definition lsh2 := snd (slice.cleave Ews).

Definition sh1 := fst (slice.cleave lsh1).
Definition sh2 := snd (slice.cleave lsh1).

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

Lemma readable_sh1 : readable_share sh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_sh2 : readable_share sh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma sh1_sh2_join : sepalg.join sh1 sh2 lsh1.
Proof.
  apply slice.cleave_join; unfold sh1, sh2; destruct (slice.cleave Ews); auto.
Qed.

Hint Resolve readable_sh1 readable_sh2 sh1_sh2_join.

Definition node_rep_r R arg : mpred := let '(np, t) := arg in
 EX tp:val,
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * 
 match t with
 | E => !!(tp=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa : val, EX pb : val, EX locka : val, EX lockb : val, EX ga : gname, EX gb : gname,
    data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp *
    |>lock_inv lsh1 locka (sync_inv(A := tree val) ga (uncurry R pa)) *
    |>lock_inv lsh1 lockb (sync_inv(A := tree val) gb (uncurry R pb))
 end.

Definition node_rep_closed := HORec node_rep_r.

Definition node_rep np t := node_rep_closed (np, t).

(*Definition tree_rep (tp:val) (t: tree val) :=
match t with
 | E => !!(tp=nullval) && seplog.emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
EX pa : val, EX pb : val, EX locka : val, EX lockb : val, EX ga : gname, EX gb : gname,
    data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp *
    |>lock_inv' locka ga a (node_rep pa) * |>lock_inv' lockb gb b (node_rep pb) 
   end.

 Lemma node_rep_def : forall np t, node_rep np t =
     EX tp:val, (field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np *
     tree_rep tp t.
Proof.
  intros.
  unfold node_rep, node_rep_closed.
  etransitivity; [eapply equal_f, HORec_fold_unfold|]; auto.
  clear.
  apply prove_HOcontractive; intros ?? (?, ?).
  unfold node_rep_r.
  apply subp_exp; intros.
  apply subp_sepcon; [apply subp_refl|].
  destruct t.
  { apply subp_refl. }
  apply subp_andp; [apply subp_refl|].
  repeat (apply subp_exp; intros).
  rewrite !sepcon_assoc; apply subp_sepcon; [apply subp_refl|].
  apply subp_sepcon; [apply subp_refl|].
  unfold lock_inv'.
  rewrite !later_orp !later_sepcon.
  apply subp_sepcon; apply subp_orp; repeat apply subp_sepcon; try apply subp_refl.
  * eapply allp_left.
    rewrite fash_andp; apply andp_left1, derives_refl.
  * eapply allp_left.
    rewrite fash_andp; apply andp_left1, derives_refl.
Qed.*)

(* node_rep should be similar to the one from verif_bst_conc.v, but takes t : tree as an argument. *)
Definition ltree (g:gname) sh p lock := lock_inv sh lock (sync_inv g (node_rep p)).

Definition nodebox_rep (g : gname) (sh : share) (lock : val) (nb: val) :=
 EX np: val, data_at sh (tptr (t_struct_tree_t)) np nb * ltree g sh np lock.

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

(* for each node:
lock_inv sh lock (sync_inv gn (node_rep p))

Fixpoint tree_rep g (t: tree val) : mpred :=
 match t with
 | E => emp
 | T a x v b => public_half g (T a x v b) * EX ga gb, tree_rep ga a * tree_rep gb b
 end. *)

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType ( val * val * share *  val * Z *val *globals * gname)) OBJ BST INVS empty top
  WITH  b: _, np: _,  sh: _, lock : _,  x: _, v: _, gv : _ , g: _
  PRE [  _t OF (tptr (tptr t_struct_tree_t)), _x OF tint,  _value OF (tptr tvoid)  ]
          PROP (  readable_share sh; Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v; is_pointer_or_null lock)
          LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
          SEPS  (mem_mgr gv; nodebox_rep g sh lock b) | (tree_rep g BST)
  POST[ tvoid  ]
  EX b0: unit,
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep g sh lock b) | (tree_rep g (insert x v BST)).
   

Program Definition lookup_spec :=
 DECLARE _lookup
   ATOMIC TYPE (rmaps.ConstType ( val * val *  Z * share * val  * gname)) OBJ BST INVS empty top
  WITH  b: _, np : _,  x: _, sh:_, lock : _, g: _
  PRE  [ _t OF (tptr (tptr t_struct_tree_t(*t_struct_tree*))), _x OF tint  ]
    PROP(readable_share sh; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEPS (nodebox_rep sh lock np b) | ( ltree  BST g  lock np)   
  POST [ tptr Tvoid ]
   EX ret : val,
    PROP ()
    LOCAL(temp ret_temp ret)
    SEP (!! (ret =  lookup(Vint (Int.repr x))  x  BST) && nodebox_rep sh lock np b;  ltree  BST g  lock np  ).
    
Program Definition treebox_free_spec :=
 DECLARE _treebox_free
   ATOMIC TYPE (rmaps.ConstType ( val* val * val * share * globals  * gname)) OBJ BST INVS empty top
  WITH  lock: _, b:_,np:_, sh:_, gv: _, g:_
  PRE  [ _b OF (tptr (tptr t_struct_tree_t)) ]
       PROP(readable_share sh) 
       LOCAL(gvars gv; temp _b b) 
           SEPS (mem_mgr gv; nodebox_rep sh lock np b; malloc_token Ews (tptr t_struct_tree_t) b) | ( ltree  BST g  lock np)   
  POST [ Tvoid ]
  EX t : unit,
    PROP()
    LOCAL()
    SEP (mem_mgr gv).
    
 Program Definition tree_free_spec :=
 DECLARE _tree_free
   ATOMIC TYPE (rmaps.ConstType ( val * val  * share * globals  * gname)) OBJ BST INVS empty top
  WITH lock: _, np: _, sh:_, gv : _, g: _
  PRE  [ _p OF (tptr t_struct_tree_t) ]
       PROP(readable_share sh) 
       LOCAL(gvars gv; temp _p np) 
       SEPS (mem_mgr gv)|(ltree  BST g  lock np)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).
 
 Program Definition delete_spec :=
 DECLARE _delete
    ATOMIC TYPE (rmaps.ConstType ( val * val * val * Z  * share   * gname)) OBJ BST INVS empty top
      WITH lock: _, b: _, np: _, x: _, sh:_,  g: _
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP( readable_share sh ; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEPS (nodebox_rep sh lock np b) | ( ltree  BST g  lock np)   
  POST [ Tvoid ] 
  EX t: unit,
    PROP()
    LOCAL()
    SEP (nodebox_rep sh lock np b; ltree  (delete x  BST) g  lock np).
    
 Program Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH gv: globals, sh: share , g: gname
   PRE  [ ]
     PROP(readable_share sh)
     LOCAL(gvars gv)
     SEP (mem_mgr gv)
  
  POST [ tptr (tptr t_struct_tree_t) ]
    EX b:val, EX np:val, EX lock:val,
    PROP()
    LOCAL(temp ret_temp b)
    SEP (mem_mgr gv; nodebox_rep sh lock np b; ltree  E g  lock np;
           malloc_token Ews (tptr t_struct_tree_t) b). 
    
Definition turn_left_spec :=
 DECLARE _turn_left
  WITH b: val, l: val, tl: val, x: Z, vx: val, tll: val, r: val, tr: val, y: Z, vy: val, mid: val, trr: val
  PRE  [ __l OF (tptr (tptr t_struct_tree_t)),
        _tgl OF (tptr t_struct_tree_t),
        _tgr OF (tptr t_struct_tree_t)]
    PROP (is_pointer_or_null mid)
    LOCAL (temp __l b; temp _tgl l; temp _tgr r)
    SEP (data_at Ews (tptr t_struct_tree_t) l b;
         field_at Ews (t_struct_tree_t) [StructField _t] tl l;
         field_at Ews (t_struct_tree_t) [StructField _t] tr r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, r))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (mid, trr))) tr)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at Ews (tptr t_struct_tree_t) r b;
         field_at Ews (t_struct_tree_t) [StructField _t] tl l;
         field_at Ews (t_struct_tree_t) [StructField _t] tr r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, mid))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (l, trr))) tr).




(* Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH b: val, p: val, tp: val, lockp: val, 
       x: Z, vx: val, locka: val, lockb: val, ta: val, tb: val,
       gv: globals
  PRE  [ _t OF (tptr (tptr t_struct_tree_t))]
    PROP ()
    LOCAL (temp _t b; gvars gv)
    SEP (mem_mgr gv;
(*          nodebox_rep Ews lockp b *)
         data_at Ews (tptr t_struct_tree_t) p b;
         field_at Ews t_struct_tree_t [StructField _t] tp p;
(*          field_at Ews t_struct_tree_t [StructField _lock] lockp p; *)
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (ta, tb))) tp;
         ltree Ews p lockp;
         ltree lsh1 ta locka;
         ltree lsh1 tb lockb;
         malloc_token Ews t_struct_tree tp;
         malloc_token Ews tlock lockp;
         malloc_token Ews t_struct_tree_t p
         (* nodebox_rep Ews locka ta;
         nodebox_rep Ews lockb tb *))
  POST [ Tvoid ]
    EX b: val,
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv;
         nodebox_rep lsh1 locka b
         (* data_at Ews (tptr t_struct_tree_t) p b;
         field_at Ews t_struct_tree_t [StructField _t] ta p; *)
         (* field_at Ews t_struct_tree_t [StructField _lock] lockp p; *)
         (* ltree Ews p lockp;
         ltree Ews ta locka;
         ltree Ews tb lockb *)
         (* nodebox_rep Ews locka ta;
         nodebox_rep Ews lockb tb *)). *)


(* Definition delete_spec :=
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
 *)(* 
Definition tree_free_spec :=
 DECLARE _tree_free
  WITH lock: val, p: val, gv : globals
  PRE  [ _p OF (tptr t_struct_tree_t) ]
       PROP() 
       LOCAL(gvars gv; temp _p p) 
       SEP (mem_mgr gv;
            ltree lsh1 p lock)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH lock: val, b: val, gv: globals
  PRE  [ _b OF (tptr (tptr t_struct_tree_t)) ]
       PROP() 
       LOCAL(gvars gv; temp _b b) 
       SEP (mem_mgr gv; nodebox_rep lsh1 lock b;
              (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) b;
              malloc_token Ews (tptr t_struct_tree_t) b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).
    
Definition thread_lock_R sh lock np gv:=
   (mem_mgr gv*
   data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb)*
   data_at Ers (tarray tschar 16)
   (map (Vint oo cast_int_int I8 Signed)
   [Int.repr 79; Int.repr 78; Int.repr 69;
   Int.repr 95; Int.repr 70; Int.repr 82;
   Int.repr 79; Int.repr 77; Int.repr 95;
   Int.repr 84; Int.repr 72; Int.repr 82;
   Int.repr 69; Int.repr 65; Int.repr 68; 
   Int.repr 0]) (gv ___stringlit_1)*
   nodebox_rep sh lock np).

Definition thread_lock_inv sh1 lsh2 np gv lockb lockt :=
  selflock (thread_lock_R sh1 lockb np gv) lsh2 lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * val * val * globals
    PRE [ _args OF (tptr tvoid) ]
         let '(sh, lock, np, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   ( mem_mgr gv; 
                 data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb);
                 data_at Ers (tarray tschar 16)
                 (map (Vint oo cast_int_int I8 Signed)
                 [Int.repr 79; Int.repr 78; Int.repr 69;
                 Int.repr 95; Int.repr 70; Int.repr 82;
                 Int.repr 79; Int.repr 77; Int.repr 95;
                 Int.repr 84; Int.repr 72; Int.repr 82;
                 Int.repr 69; Int.repr 65; Int.repr 68; 
                 Int.repr 0]) (gv ___stringlit_1);
                 nodebox_rep sh1 lock np;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh1 sh np gv lock (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP ().
 *)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt nil gv
  POST [ tint ] main_post prog nil gv.


Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec ).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.*)

(*no freelock_spec, spawn_spec, freelock2_spec, release2_spec*)
Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
    surely_malloc_spec;
(*     tree_free_spec; treebox_free_spec; *)
    insert_spec; (* lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec ;
    spawn_spec; thread_func_spec;  *)main_spec 
  ]).


Lemma node_rep_saturate_local:
   forall t p, node_rep p t |-- !! is_pointer_or_null p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp; entailer!.
Qed.

Hint Resolve node_rep_saturate_local: saturate_local.


Lemma node_rep_valid_pointer:
  forall t p, node_rep p t |-- valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp; entailer!.
Qed.

Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_saturate_local:
   forall t p, tree_rep p t |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!. 
Intros pa pb locka lockb ga gb. entailer!.
Qed.

Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t tp, tree_rep tp t |-- valid_pointer tp.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed. 

Hint Resolve tree_rep_valid_pointer : valid_pointer.

(*
Lemma ltree_saturate_local:
  forall lsh p lock, ltree lsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Hint Resolve ltree_saturate_local: saturate_local. *)

(*
 My comment 
 Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree_t) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.
*)
Notation ghost_ref_tree t g := ( ghost_reference (P:=discrete_PCM _) t g ).

Definition insert_inv (b0: val) (tp0:val)  (lsh0 : share) (lock0 : val) (x: Z) (v: val) gv (t: tree val) (inv_names : invG) (Q : () -> mpred) ( g:gname) : environ -> mpred :=
  PROP()
  LOCAL(temp _l lock0; temp _tgt tp0; temp _x (Vint (Int.repr x)); temp _value v; gvars gv)
  SEP(mem_mgr gv;   nodebox_rep lsh0 lock0 tp0 b0; 
  atomic_shift (λ a : tree val, lock_inv' lock0 g a (node_rep tp0)) ∅ ⊤
  (λ (t : tree val) (_ : ()),
     mem_mgr gv *
     (nodebox_rep lsh0 lock0 tp0 b0 * (ltree (insert x v t) g lock0 tp0 * seplog.emp))) Q *
ghost_ref_tree t g * node_rep tp0 t).

(*
Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp. auto.
  + rewrite emp_sepcon. auto.
Qed.

Lemma node_rep_nullval: forall t,
  node_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl node_rep.
  Intros pa pb locka lockb. entailer!.
Qed.

Hint Resolve node_rep_nullval: saturate_local. *)

(*Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- nodebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.*)

(*Lemma bst_left_entail: forall sh1 lock1 p1 b1 pa tp locka,
  lock_inv sh1 lock1 (t_lock_pred p1 lock1) *
  data_at Ews (tptr t_struct_tree_t) p1 b1 *
  field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1
  |-- data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
    ltree sh1 pa locka *
    (data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
     ltree sh1 pa locka -*
     data_at Ews (tptr t_struct_tree_t) p1 b1 *
     field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1 *
     lock_inv sh1 lock1 (t_lock_pred p1 lock1)).
Proof.
  intros.
  unfold ltree at 1; entailer!.
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

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  Intros. 
  simpl.
  unfold nodebox_rep at 2.
  Intros.
  forward.
  forward.
  forward_call  [tree val : Type; unit : Type] acquire_inv(lock,g, (node_rep np),
    (λ (t : tree val) (_ : ()), mem_mgr gv *
               ( nodebox_rep sh lock np b *
               (ltree (insert x v t) g lock np * seplog.emp))), Q , inv_names ).
               {   unfold ltree at 1. cancel. }
  Intros BST.
   eapply semax_pre; [
    | apply (semax_loop _ (insert_inv b np sh lock x v gv BST inv_names Q g) (insert_inv b np sh lock  x v gv BST inv_names Q g) )]. 
  * (* Precondition *)
    unfold insert_inv.
    unfold nodebox_rep at 2.
    Intros.
     entailer!. 
  * (* Loop body *)
    unfold insert_inv.
    Intros.
    forward. (* Sskip *)
    rewrite node_rep_def. 
    Intros tp.
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
      { simpl. rewrite Z.max_r. repeat (split; auto); rep_omega. rep_omega. }
      Intros l1.
      unfold tlock.
      forward_call [tree val : Type] makelock_inv (l1, BST, node_rep np).   
      Intro g0.
      Intros.    
      forward. (*p1->lock = l1*) 
(*       rewrite <- (lock_inv_share_join lsh1 lsh2) by auto. *)
      forward_call [tree val : Type; tree val : Type] release_inv (l1, g, BST, node_rep np, fun (n n' : tree val) => emp,
    (fun (_ : tree val) => emp), inv_names).
Admitted.
  (*     {  lock_props. 
        rewrite t_lock_pred_def at 3. Exists (E : tree val) (vint 0).
        unfold_data_at 2%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
         simpl. entailer!. }
      deadvars.
      forward_call (tlock, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros l2.
      forward_call(l2, Ews, t_lock_pred p2' l2). 
      forward. (*p2->lock = l2*)
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      forward_call(l2, lsh2, t_lock_pred_base p2' l2, t_lock_pred p2' l2).
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
      forward_call(lock1, lsh2, t_lock_pred_base p1 lock1, t_lock_pred p1 lock1).
      { lock_props.
        setoid_rewrite t_lock_pred_def at 4.
        Exists (T E x v E) p'. cancel. simpl. Exists p1' p2' l1 l2. unfold ltree. entailer!.
        rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
        entailer!.
        { rewrite field_compatible_cons in H6, H8; destruct H6, H8; auto. } }
      forward. (* return; *)
    + (* else clause *)
      destruct t1.
      { simpl node_rep. normalize. }
      simpl node_rep.
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
        unfold ltree at 1; Intros.
        forward.
        forward_call (locka, lsh1, t_lock_pred pa locka).
        rewrite t_lock_pred_def at 2.
        Intros ta tpa.
        forward_call(lock1, lsh2, t_lock_pred_base p1 lock1, t_lock_pred p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 4. Exists (T t1_1 k v0 t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree; entailer!.
          unfold_data_at (data_at _ _ _ tp); cancel.
          rewrite (field_at_data_at _ _ [StructField _left]), field_compatible_field_address by auto; simpl; cancel.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        Exists pa locka.
        unfold ltree; entailer!.
        unfold t_lock_pred_base.
        Exists ta tpa; cancel.
      - (* Inner if, second branch:  k<x *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        rewrite (field_at_data_at _ _ [StructField _left]); simpl.
        assert_PROP (field_compatible t_struct_tree [StructField _left] tp) by entailer!.
        rewrite field_compatible_field_address by auto.
        unfold ltree at 2; Intros.
        forward.
        forward_call (lockb, lsh1, t_lock_pred pb lockb).
        rewrite t_lock_pred_def at 2.
        Intros tb tpb.
        forward_call(lock1, lsh2, t_lock_pred_base p1 lock1, t_lock_pred p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 4. Exists (T t1_1 k v0 t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree; entailer!.
          unfold_data_at (data_at _ _ _ tp); cancel.
          rewrite (field_at_data_at _ _ [StructField _left]), field_compatible_field_address by auto; simpl; cancel.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        Exists pb lockb.
        unfold ltree; entailer!.
        unfold t_lock_pred_base.
        Exists tb tpb; cancel.
      - (* x = k *)
        forward.
        forward_call(lock1, lsh2, t_lock_pred_base p1 lock1, t_lock_pred p1 lock1).
        { lock_props.
          setoid_rewrite t_lock_pred_def at 2. Exists (T t1_1 k v t1_2) tp.
          cancel. simpl. Exists pa pb locka lockb.
          unfold ltree; entailer!.
          rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later].
          cancel. }
        forward.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize.
Qed. *)


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
  exclusive_mpred (t_lock_pred p l).
Proof.
  intros. rewrite t_lock_pred_def.
  eapply derives_exclusive, exclusive_sepcon1 with 
  (P := EX tp : _, field_at Ews t_struct_tree_t [StructField _t] tp p)
  (Q:= EX t0 : tree val, EX tp : val, _ * node_rep t0 tp * malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock l * _).
  - unfold t_lock_pred_base. Intros t0 tp. Exists tp. cancel. Exists t0 tp. apply derives_refl.
  - apply ex_field_at_exclusive; auto.
    simpl. omega.
Qed.
Hint Resolve t_lock_exclusive.

Lemma t_lock_rec : forall p l,
  rec_inv lsh2 l (t_lock_pred_base p l) (t_lock_pred p l).
Proof.
  intros; apply t_lock_pred_def.
Qed.
Hint Resolve t_lock_rec.


Lemma thread_inv_exclusive : forall sh1 lsh2 nb gv lockb lockt,
  exclusive_mpred (thread_lock_inv sh1 lsh2 nb gv lockb lockt).
Proof.
  intros; apply selflock_exclusive. unfold thread_lock_R. apply exclusive_sepcon1. apply exclusive_sepcon1.
  apply exclusive_sepcon2. apply data_at_exclusive. auto. simpl. omega.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
start_function.
forward. 
unfold nodebox_rep.
Intros np0.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_1)). { entailer!. }
forward_call(sh1,lock,np,1,gv ___stringlit_1,gv).
 * unfold nodebox_rep. Exists np0. entailer!.
 * split. auto. split. rep_omega. auto.
 * forward_call (gv _thread_lock, sh, thread_lock_R sh1 lock np gv, thread_lock_inv sh1 sh np gv lock (gv _thread_lock)).
    { lock_props. unfold thread_lock_inv, thread_lock_R. rewrite selflock_eq at 2. entailer!. }
    forward.
Qed.

Lemma ltree_share_join : forall (sh1 sh2 sh : share) (p : val) (lock : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
  ltree sh1 p lock * ltree sh2 p lock = ltree sh p lock.
Proof.
  intros; unfold ltree.
  rewrite sepcon_andp_prop, sepcon_andp_prop', <- andp_assoc, andp_dup; f_equal.
  rewrite <- sepcon_assoc, (sepcon_assoc (field_at _ _ _ _ _)), (sepcon_comm (lock_inv _ _ _)), <- sepcon_assoc.
  erewrite field_at_share_join by eauto.
  rewrite sepcon_assoc.
  erewrite lock_inv_share_join by eauto; reflexivity.
Qed.

(* for conclib *)
Lemma field_at_value_cohere : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p, readable_share sh1 ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |--
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v1 p.
Proof.
  intros; unfold field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.

Lemma field_at_value_eq : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject (nested_field_type t gfs) v1 <> Vundef -> repinject (nested_field_type t gfs) v2 <> Vundef ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold field_at, at_offset; Intros.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
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
Proof.
  intros; unfold data_at; apply field_at_value_eq; auto.
Qed.

Lemma nodebox_rep_share_join : forall (sh1 sh2 sh : share) (lock : val) (nb : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
       nodebox_rep sh1 lock nb * nodebox_rep sh2 lock nb = nodebox_rep sh lock nb.
Proof.
  intros; unfold nodebox_rep.
  apply pred_ext.
  - Intros np1 np2.
    assert_PROP (np1 <> Vundef) by entailer!.
    assert_PROP (np2 <> Vundef) by entailer!.
    sep_apply data_at_value_eq; Intros; subst.
    erewrite data_at_share_join, ltree_share_join by eauto.
    Exists np2; auto.
  - Intros np; Exists np np.
    erewrite <- data_at_share_join, <- (ltree_share_join sh3 sh4); eauto; cancel.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
forward_call(gv).
Intros vret.
forward.
forward.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_2)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),3,gv ___stringlit_2,gv).
 { split3. auto. rep_omega. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_3)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),1,gv ___stringlit_3,gv).
 { split3. auto. rep_omega. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_4)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),4,gv ___stringlit_4,gv).
 { split3. auto. rep_omega. auto. }
forward_call ((gv _thread_lock), Ews, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)). 
forward_spawn _thread_func nullval (lsh2,(snd vret),(fst vret), gv).
 { erewrite <- lock_inv_share_join; try apply lsh1_lsh2_join; auto.
   erewrite <- nodebox_rep_share_join; try apply sh1_sh2_join; auto.
   erewrite <- data_at_share_join; try apply lsh1_lsh2_join; auto.
    entailer!. }
assert_PROP ( is_pointer_or_null (gv ___stringlit_5)). { entailer!. }
forward.
sep_apply (create_mem_mgr gv).
forward_call(sh2,(snd vret), (fst vret),1,gv ___stringlit_5,gv).
 { split3. auto. rep_omega. auto. }
forward_call ((gv _thread_lock), lsh1, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
unfold thread_lock_inv at 2. rewrite selflock_eq. Intros.

forward_call ((gv _thread_lock), Ews, lsh2, thread_lock_R sh1 (snd vret) (fst vret) gv, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
{ lock_props. unfold thread_lock_inv. erewrite <- (lock_inv_share_join _ _ Ews); try apply lsh1_lsh2_join; auto. entailer!. }
forward.
forward_call((snd vret), (fst vret), gv).
 { unfold thread_lock_R. erewrite <- (nodebox_rep_share_join _ _ lsh1) ; try apply sh1_sh2_join; auto.
entailer!. }
forward.
Qed.

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (
    EX b : val,
    PROP ()
    LOCAL (temp _t b; gvars gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_struct_tree_t) p b;
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        data_at Ews t_struct_tree (vint x, (vx, (ta, tb))) tp; 
        ltree Ews p lockp;
        ltree lsh1 ta locka; ltree lsh1 tb lockb;
        malloc_token Ews t_struct_tree tp;
        malloc_token Ews tlock lockp;
        malloc_token Ews t_struct_tree_t p))%assert.
  Exists b. entailer!. admit.
  clear b. Intros b.
  forward.
  unfold ltree at 1; Intros.
  forward.
  forward.
  forward.
  unfold ltree at 2; Intros.
  forward.
  forward_call (lockb, lsh1, t_lock_pred tb lockb).
  rewrite t_lock_pred_def at 2. Intros tbv tbp.
  forward.
  forward_if.
  { forward.
    forward.
    forward_call (t_struct_tree, tp, gv).
    { if_tac; entailer!. }
    forward_call (lockp, Ews, lsh2, t_lock_pred_base p lockp, t_lock_pred p lockp).
    { lock_props. }
    forward_call (tlock, lockp, gv).
    { if_tac; entailer!. }
    forward_call (t_struct_tree_t, p, gv).
    { if_tac. entailer!.
      unfold_data_at (data_at_ Ews t_struct_tree_t p).
      entailer!. }
    forward_call (lockb, Ews, lsh2, t_lock_pred_base tb lockb, t_lock_pred tb lockb).
    { lock_props.
      rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
      entailer!. }
    forward_call (tlock, lockb, gv).
    { if_tac; entailer!. }
    forward_call (t_struct_tree_t, tb, gv).
    { if_tac. entailer!.
      unfold_data_at (data_at_ Ews t_struct_tree_t tb).
      cancel.
      erewrite <- (field_at_share_join _ _ Ews _ [StructField _lock]) by eauto.
      entailer!. }
    forward.
    { unfold nodebox_rep.
      Exists (b) (ta).
      entailer!.
      unfold node_rep. Intros. cancel. } }
  unfold node_rep at 1.
  destruct tbv eqn:E.
  { Intros. contradiction. }
  { Intros tbl tbr ltbl ltbr.
    (* hoist_later_in_pre. *)
    (* assert_PROP (isptr tbl). {
      entailer!.
    } *)
    forward_call (b, p, tp, x, vx, ta, tb, tbp, k, v, tbl, tbr).
    { admit. }
    forward. simpl.
    forward_call (lockb, lsh2, t_lock_pred_base tb lockb, t_lock_pred tb lockb).
    { lock_props.
      rewrite t_lock_pred_def at 3.
      cancel.
      Exists (tbv) (tbp).
      unfold node_rep.
      rewrite E.
      entailer!.
      Exists (p) (tbr) (lockp) (ltbr).
      entailer!.
      unfold ltree at 3.
      rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
      erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
      entailer!.
      SearchAbout later sepcon.
      rewrite later_sepcon.
      entailer!. }
    Exists (offset_val 8 tbp).
    entailer!.
    unfold ltree at 2 3.
    entailer!.
Admitted.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  { entailer!. }
Qed.

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
  forward_call (l, Ews, t_lock_pred newt l).
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
  forward_call (l, lsh2, t_lock_pred_base newt l, t_lock_pred newt l).
  { lock_props.
    rewrite t_lock_pred_def at 3.
    Exists (E : tree val) (vint 0). unfold_data_at (data_at Ews t_struct_tree_t _ _).
    unfold node_rep. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
    entailer!. }
  forward.
  Exists p l.
  unfold nodebox_rep.
  unfold ltree.
  Exists newt.
  entailer!.
  erewrite <- data_at_share_join by eauto; cancel.
Qed.

Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function. simpl.
  unfold ltree; Intros.
  forward.
  forward_call (lock, lsh1, t_lock_pred p lock).
  rewrite t_lock_pred_def at 2.
  Intros treeval tp.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _p tp; temp _l lock; gvars gv; temp _tgp p)
    SEP (lock_inv lsh1 lock (t_lock_pred p lock);
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        field_at lsh2 t_struct_tree_t [StructField _lock] lock p;
        malloc_token Ews t_struct_tree_t p; malloc_token Ews tlock lock;
        lock_inv lsh2 lock (t_lock_pred p lock); mem_mgr gv;
        field_at lsh1 t_struct_tree_t [StructField _lock] lock p)).
  { unfold node_rep. destruct treeval.
    { Intros. contradiction. }
    { Intros pa pb locka lockb.
      forward. (* p->left *)
      forward. (* p -> right *)
      forward_call (t_struct_tree, tp, gv).
      { if_tac.
        - contradiction.
        - entailer!. }
      unfold ltree at 1; Intros.
      forward_call (locka, pa, gv).
      { unfold ltree at 2. entailer!. }
      forward_call (lockb, pb, gv).
      entailer!. }}
  { forward.
    entailer!.
    unfold node_rep.
    destruct treeval; Intros.
    - cancel.
    - Intros pa pb locka lockb.
      entailer!. }
  forward_call (lock, Ews, lsh2, t_lock_pred_base p lock, t_lock_pred p lock).
  { lock_props.
    rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
    entailer!. }
  forward_call (tlock, lock, gv).
  { if_tac.
    - entailer!.
    - entailer!. }
  forward_call (t_struct_tree_t, p, gv).
  { if_tac.
    - entailer!.
    - entailer!.
      unfold_data_at_ p.
      unfold_data_at (data_at Ews t_struct_tree_t _ p).
      rewrite <- (field_at_share_join lsh2 lsh1 Ews t_struct_tree_t [StructField _lock] _ p) by eauto.
      cancel. }
    forward.
  
Qed.

Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward.
  forward_call (lock, np, gv).
  forward_call (tptr t_struct_tree_t, b, gv).
  { destruct (eq_dec b nullval).
    { entailer!. }
    { erewrite <- (data_at__share_join _ _ Ews) by eauto; entailer!. }}
  forward.
Qed.

Lemma node_rep_D {TR p} (P: p<>nullval) :
  node_rep TR p |-- (EX l k v r, !!(TR = T l k v r) && node_rep TR p).
Proof.
destruct TR as [ | l k v r]; simpl; Intros. contradiction.
Exists l k v r. entailer!.
Qed.

(*Variant of t_lock_pred but without the |> lock_inv lsh2 lock (t_lock_pred p lock) term*)
Definition tlp TR (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt * 
  node_rep TR p * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

(*Version of tlp that existentially quantifies over the semantic tree*)
Definition tlp' (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt * 
  (EX TR, node_rep TR p) * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

Definition lookup_inv (*TR*) b lsh0 lock0 (x:Z): environ -> mpred :=
  EX p: val, EX tgt:val, EX lock:val,
  PROP() 
  LOCAL(temp _p p; temp _l lock; temp _x (Vint (Int.repr x)))
  SEP (|>lock_inv lsh2 lock (t_lock_pred tgt lock); 
       tlp' (* TR*) p tgt lock;  nodebox_rep lsh0 lock0 b).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof. 
  start_function. rename H into Hx.
  unfold nodebox_rep; Intros tgt.
  forward. deadvars.
  unfold ltree; Intros. rename H into FC_tgt. rewrite lock_inv_isptr; Intros.
  forward.

  (*aquire(l)*)
  forward_call (lock, sh, t_lock_pred tgt lock). 
  rewrite t_lock_pred_def at 2. Intros TREE1 p.
  forward. (*p=tgt->t*)
  deadvars. 

  forward_while (lookup_inv (*TREE1*) b sh lock x).
  + Exists p tgt lock. entailer. 
    unfold tlp' at 1. cancel. Exists TREE1; cancel.
    unfold nodebox_rep. Exists tgt; cancel.
    unfold ltree. entailer!.

  + unfold tlp'; try Intros TR. entailer!.
  + clear TREE1. unfold tlp'; Intros TR.
    clear FC_tgt tgt p. rename p0 into p. rename tgt0 into tgt.
    sep_apply (@node_rep_D TR p HRE); Intros l k v r; subst. simpl; Intros pa pb locka lockb.
    rename H into K. 
    forward.
    forward_if.
    - rename H into HK. 
      forward. forward.
      unfold ltree at 1; Intros. rename H into FC_pa.
      forward. deadvars.
      
      (*aquire(l)*)
      forward_call (locka, lsh1, t_lock_pred pa locka).
      rewrite t_lock_pred_def at 2. Intros pa_T pa_t.

      forward. (*p=tgt->t*)

      (*release*)
      forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
      { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] locka pa;
                  node_rep pa_T pa_t; malloc_token Ews t_struct_tree_t pa;
                  malloc_token Ews tlock locka; lock_inv lsh2 locka (t_lock_pred pa locka);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pa_t pa]); 
          subst Frame; [ reflexivity | clear H].
        lock_props.
        setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
        (*Parameter TR1: tree val.
          Parameter TR2: tree val.*)
        Exists (T (*TR1*)l k v (*TR2*)r) p.
        cancel. unfold node_rep.
        Exists pa pb locka lockb; entailer!.
        unfold ltree; entailer!.
        rewrite later_sepcon. eapply derives_trans.
        2: apply sepcon_derives, derives_refl; try apply now_later.
        cancel. }
      Exists ((pa_t, pa), locka); entailer!.
      unfold tlp'; cancel. Exists pa_T; cancel.

    - rename H into XK.
      forward_if.
      * rename H into KX. forward. forward. 
        unfold ltree at 2; Intros. rename H into FC_pb.
        forward. deadvars.

        (*aquire(l)*)
        forward_call (lockb, lsh1, t_lock_pred pb lockb).
        rewrite t_lock_pred_def at 2. Intros pb_T pb_t.

        forward. (*p=tgt->t*)

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] lockb pb;
                  node_rep pb_T pb_t; malloc_token Ews t_struct_tree_t pb;
                  malloc_token Ews tlock lockb; lock_inv lsh2 lockb (t_lock_pred pb lockb);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pb_t pb]);
            subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
          (*Parameter TR4: tree val.
            Parameter TR5: tree val.*)
          Exists (T (*TR4*)l k v (*TR5*)r) p.
          cancel. unfold node_rep. 
          Exists pa pb locka lockb. entailer!.
          unfold ltree; entailer.
          rewrite later_sepcon. eapply derives_trans.
          2: apply sepcon_derives, derives_refl; try apply now_later.
          cancel. }
        Exists ((pb_t, pb), lockb). entailer!.
        unfold tlp'. cancel. Exists pb_T; cancel.
      * rename H into KX. 
        forward.

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
          (*Parameter TR6: tree val.
            Parameter TR7: tree val.*)
          Exists (T (*TR6*)l k v (*TR7*)r) p.
          cancel. unfold node_rep.
          Exists pa pb locka lockb. entailer!. }
        forward. Exists v; entailer!.
  + subst. unfold tlp'; simpl; Intros. Intros TR.

    (*release*)
    forward_call(lock0, lsh2, t_lock_pred_base tgt0 lock0, t_lock_pred tgt0 lock0).
    { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
      lock_props.
      setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
      Exists (@E val) nullval; simpl. entailer!. simpl; entailer!. }
    forward. Exists (vint 0); entailer!.
Qed.

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



