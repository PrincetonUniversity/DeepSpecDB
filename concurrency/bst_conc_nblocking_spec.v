Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc_nblocking.
Require Import bst.bst_conc_lemmas.
Require Import VST.atomics.general_locks.
Require Import VST.atomics.SC_atomics.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.iter_sepcon.

 Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition atomic_ptr := Tstruct _atom_ptr noattr.
Variable atomic_ptr_at : share -> val -> val -> mpred.
Hypothesis atomic_ptr_at__ : forall sh v p, atomic_ptr_at sh v p |-- atomic_ptr_at sh Vundef p.
Definition t_struct_tree := Tstruct _tree noattr.

Section Specifications.

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

Fixpoint ghost_tree_rep (t: @ ghost_tree val ) (nb:val) (g_current:gname) (g:gname) range : mpred := 
 match t, range with
 | E_ghost , _ => atomic_ptr_at Ews nullval nb * ghost_master1 (ORD := range_order)  (range,  (@None ghost_info)) g_current 
 | (T_ghost a ga lp x v b gb rp ), (l, r) =>  EX tp, EX sh, !!(readable_share sh) && atomic_ptr_at Ews tp nb * data_at sh t_struct_tree (Vint (Int.repr x),(v,(lp,rp))) tp * ghost_master1 (ORD := range_order)  (range,  (@Some ghost_info (x,v,ga,gb))) g_current * in_tree ga (l, Finite_Integer x) lp g * in_tree gb ( Finite_Integer x, r) rp g *  ghost_tree_rep a  lp ga g (l, Finite_Integer x) * ghost_tree_rep b rp gb g (Finite_Integer x, r)
 end.

Definition tree_rep2 (g:gname) (g_root: gname) (nb:val) (sh:share) (t: @tree val  ) : mpred := EX (tg:ghost_tree), !! (find_pure_tree tg = t) && ghost_tree_rep tg  nb g_root g (Neg_Infinity, Pos_Infinity) 
                                                                                                                                 * bst_conc_lemmas.ghost_ref g (find_ghost_set tg g_root ( Neg_Infinity, Pos_Infinity) nb).

Definition nodebox_rep (sh : share) (nb: val) (g_root: gname) (g:gname)  :=  EX tp:val, EX lp: list val,  atomic_ptr_at sh tp nb * iter_sepcon ( fun p => EX sh1:share, data_at_ sh1 t_struct_tree p ) lp * in_tree g_root (Neg_Infinity, Pos_Infinity) nb g.
 

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType ( val * share * Z * val * globals*gname* gname)) OBJ BST INVS base.empty base.top
  WITH  b, sh, x, v, gv, g, g_root
  PRE [  _tb OF (tptr atomic_ptr), _x OF tint,  _value OF (tptr tvoid) ]
          PROP (readable_share sh;Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v )
          LOCAL (temp _tb b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv )
          SEP  (mem_mgr gv; nodebox_rep sh b g_root g ) | (!!(sorted_tree BST)&&tree_rep2 g g_root b sh  BST )
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep sh b g_root g) | (!!(sorted_tree (bst_conc_lemmas.insert x v BST))&&tree_rep2 g g_root  b sh (bst_conc_lemmas.insert x v BST) ). 

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType ( val * share* Z * globals * gname * gname))
         OBJ BST INVS base.empty base.top
  WITH b, sh, x, gv, g, g_root
  PRE [_tb OF (tptr atomic_ptr), _x OF tint]
    PROP (
          Int.min_signed <= x <= Int.max_signed)
    LOCAL (temp _tb b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP  (mem_mgr gv; nodebox_rep sh b g_root g) |
  (!! sorted_tree BST && tree_rep2 g g_root b sh BST)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep sh b g_root g) |
        (!! (sorted_tree BST /\ ret = (bst_conc_lemmas.lookup nullval x BST)) && tree_rep2 g g_root b sh BST).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt nil gv
  POST [ tint ] main_post prog nil gv.
  
  Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition atomic_load_ptr_spec := DECLARE _atomic_load_ptr (atomic_load_ptr_spec atomic_ptr atomic_ptr_at).
Definition atomic_store_ptr_spec := DECLARE _atomic_store_ptr (atomic_store_ptr_spec atomic_ptr atomic_ptr_at).
Definition atomic_CAS_ptr_spec := DECLARE _atomic_CAS_ptr (atomic_CAS_ptr_spec atomic_ptr atomic_ptr_at).
Definition make_atomic_ptr_spec := DECLARE _make_atomic_ptr ( make_atomic_ptr_spec atomic_ptr atomic_ptr_at).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
    surely_malloc_spec; 
    atomic_load_ptr_spec;
    atomic_store_ptr_spec;
    atomic_CAS_ptr_spec;
    make_atomic_ptr_spec;
    (* treebox_new_spec; *)
    insert_spec;
    lookup_spec;
    spawn_spec;
    main_spec 
  ]).
  End Specifications.

  