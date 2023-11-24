Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.give_up_template.
Require Import bst.puretree.
Require Import bst.dataStruct.
Require Import bst.template.
Require Import bst.giveup_lib.
Require Import bst.giveup_traverse.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock: val) (nb : val) :=
  EX (np: val) (lsh : share),
                data_at sh (tptr (t_struct_node)) np nb *
                (!!(field_compatible t_struct_node nil np /\ is_pointer_or_null lock) &&
                field_at lsh t_struct_node [StructField _lock] lock np) *
                in_tree g g_root np lock.

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
     surely_malloc_spec; insertOp_spec; traverse_spec; insert_spec (*; treebox_new_spec *) ]).

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
  Check enum.
  set (AS := atomic_shift _ _ _ _ _).
  set Q1:= fun (b : ( enum * (val * (share * (gname * node_info))))%type) => AS.
  (* traverse(pn, x, value) *)
  forward_call (nb, np, lock, x, v, gv, g, g_root, Q1).
  {
    Exists Vundef. entailer !.
    iIntros "(((H1 & H2) & H3) & H4)".
    iCombine "H2 H1 H3 H4" as "H".
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
  simpl in H6.
  destruct fl.
  (* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 *)
  destruct (Val.eq (enums F) (vint 2)); auto.
  - easy.
  - admit.
  - destruct (Val.eq (enums NF) (vint 2)); eauto.
    + easy.
    + admit.
  - destruct (Val.eq (enums NN) (vint 2)); eauto.
    + admit.
    + easy.

Admitted.