Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
(* Require Import bst.giveup_template. temporary having it for lock - need remove*)
(* and make more general - not involving anything relate to specific templates *)
Require Import bst.puretree.
Require Import bst.data_struct.
Require Import bst.template.
Require Import bst.giveup_lib.
Require Import bst.giveup_specs.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

Section verif_template.
Context {N: NodeRep}.
(*
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
*)

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t: type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ]
    EX p: _,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).
(*
Definition insertOp_spec :=
  DECLARE _insertOp
    WITH b: val, sh: share, x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, gv: globals
  PRE [ tptr tvoid, tint, tptr tvoid, tint ]
  PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       (* data_at sh (t_struct_pn) (p, p) b; *)
       field_at Ews t_struct_node (DOT _t) tp p;
       field_at Ews t_struct_node (DOT _min) (Vint (Int.repr min)) p;
       field_at Ews t_struct_node (DOT _max) (Vint (Int.repr max)) p )
  POST[ tvoid ]
  EX (pnt : val) (pnl: list val) (lkl: list val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (* data_at sh t_struct_pn (p, p) b; *)
       field_at Ews t_struct_node (DOT _t) pnt p;
       malloc_token Ews t_struct_node pnt;
       iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) pnl;
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) lkl;
(*
       data_at Ews t_struct_tree (vint x, (v, (p1', p2'))) pnt;
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock2, (vint x, vint max))) p2';
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock1, (vint min, vint x))) p1';
*)
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p).
*)

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * val * globals * gname * gname))
  OBJ M INVS ∅
  WITH b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_node), tint, tptr tvoid ]
    PROP (writable_share sh; and (Z.le Int.min_signed x) (Z.le x Int.max_signed); is_pointer_or_null v)
    PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (CSS g g_root M)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (CSS g g_root (<[x:=v]>M)).

(* Definition spawn_spec := DECLARE _spawn spawn_spec. *)

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; (* insertOp_spec; *) traverse_spec; insert_spec (*; treebox_new_spec *) ]).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward_call (t_struct_pn, gv).
  Intros nb.
  Intros lsh.
  forward. 
  forward.
  sep_apply in_tree_duplicate.
  set (AS := atomic_shift _ _ _ _ _).
  set Q1:= fun (b : ( enum * (val * (share * (gname * node_info))))%type) => AS.
  (* traverse(pn, x, value) *)
  forward_call (nb, np, lock, x, v, gv, g, g_root, Q1).
  {
    Exists Vundef. entailer !.
    iIntros "(((H1 & H2) & H3) & H4)". iCombine "H2 H1 H3 H4" as "H".
    iVST.
    apply sepcon_derives; [| cancel_frame].
    iIntros "AU".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "[Hm HClose]".
    iModIntro. iExists _. iFrame.
    iSplit; iFrame.
    iIntros "H1".
    iSpecialize ("HClose" with "H1"). auto.
    iDestruct "HClose" as "[HClose _]".
    iIntros (pt) "[H _]".
    iMod ("HClose" with "H") as "H".
    iModIntro.
    unfold Q1.
    auto.
  }
  Intros pt.
  destruct pt as (fl & (p & (gsh & (g_in & r)))).
  destruct fl.
  (* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 *)
  destruct (Val.eq (enums F) (vint 2)); auto.
  simpl.
  - easy.
  - simpl.
    unfold post_traverse.
    unfold node_lock_inv_pred.
    Intros.
    forward_if(
        PROP ( )
     LOCAL (temp _status (Vint Int.zero); temp _t'7 np; temp _pn__2 nb; gvars gv; 
     temp _t b; temp _x (vint x); temp _value v)
     SEP (Q1 (F, (p, (gsh, (g_in, r)))); mem_mgr gv; emp; data_at Ews t_struct_pn (p, p) nb;
     in_tree g g_in p r.1.1.2; my_half g_in Tsh r; node_rep p g g_in r; in_tree g g_root np lock;
     malloc_token Ews t_struct_pn nb; data_at sh (tptr t_struct_node) np b;
     field_at lsh t_struct_node (DOT giveup_template._lock) lock np)).
    + forward.
      entailer !. (* is_pointer_or_null p *) admit.
      admit.
    + easy.
    + forward. admit. simpl. admit.


      admit.
  - simpl.
    forward_if(
      PROP ( )
     LOCAL (temp _status (Vint Int.one); temp _t'7 np; temp _pn__2 nb; gvars gv; 
     temp _t b; temp _x (vint x); temp _value v)
     SEP (Q1 (NF, (p, (gsh, (g_in, r)))); mem_mgr gv; post_traverse nb x g NF p gsh g_in r;
     in_tree g g_root np lock; malloc_token Ews t_struct_pn nb; data_at sh (tptr t_struct_node) np b;
     field_at lsh t_struct_node (DOT giveup_template._lock) lock np)).
    + easy.
    + forward.
      entailer !. (*is_pointer_or_null p *) admit.
      destruct (Val.eq (enums NF) (enums NN)); eauto.
      ** easy.
      ** (* call insert_Op_helper *)
        assert_PROP(is_pointer_or_null r.1.1.1). entailer !. 
        admit.
        unfold node_lock_inv_pred.
        unfold node_rep.
        (* r.1.1.1 ≠ nullval *)
        admit.
    + forward.
      entailer !.  (*is_pointer_or_null p *) admit.
      destruct (Val.eq (enums NF) (enums NN)); eauto.
      ** easy.
      ** admit.
  - simpl.
    forward_if (
        PROP ( )
     LOCAL (temp _status (vint 2); temp _t'7 np; temp _pn__2 nb; gvars gv; 
     temp _t b; temp _x (vint x); temp _value v)
     SEP (Q1 (NN, (p, (gsh, (g_in, r)))); mem_mgr gv; post_traverse nb x g NN p gsh g_in r;
     in_tree g g_root np lock; malloc_token Ews t_struct_pn nb; data_at sh (tptr t_struct_node) np b;
     field_at lsh t_struct_node (DOT giveup_template._lock) lock np)).
    + easy.
    + forward.
      entailer !.  (*is_pointer_or_null p *) admit.
      destruct (Val.eq (enums NN) (enums NN)); eauto.
      ** (* r.1.1.1 = nullval *)
        (* call insert_Op_helper *)
        unfold node_lock_inv_pred, node_rep.








        
        admit.
      ** easy.
    + forward.
      entailer !.  (*is_pointer_or_null p *) admit.
      

Admitted.
