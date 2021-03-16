Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc.
Require Import VST.atomics.general_locks.
Require Import bst.flows.
Require Import bst.inset_flows.
Require Import bst.keys_ghost.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Instance val_dec: EqDecision val.
Proof. hnf. apply Val.eq. Qed.

Instance val_countable: Countable val.
Proof. admit. Admitted.

Definition pc_flowint := @flowintR val _ _ nat nat_ccm.

Definition pc_flowint_ghost := @flowintGhost val _ _ nat nat_ccm.

Definition inset_flowint := inset_flowint val Z.

Definition inset_flowint_ghost := @flowintGhost val _ _ (@K_multiset Z _ _) _.

Instance bst_ghost: Ghost := prod_PCM pc_flowint_ghost inset_flowint_ghost.

Instance state_ghost: Ghost := ref_PCM bst_ghost.

Definition bst_content_t := gmap Z val.

Definition global_inv (Ipc: pc_flowint) (Iset: inset_flowint)
           (root: val) (KS: gset Z): Prop :=
  ✓ Ipc /\ ✓ Iset /\ (forall n, n <> root -> inf Ipc n = 0) /\ (inf Ipc root = 1) /\
  (forall n, out Ipc n = 0) /\ (forall n, n <> root -> inf Iset n = ∅) /\
  (dom_ms (inf Iset root) = KS) /\ (forall n, out Iset n = ∅) /\
  (domm Ipc = domm Iset).

Definition node_rep (sh: share) (g gc: gname) (np: val): mpred :=
  EX p: val,
  (field_at Ews (t_struct_tree_t) [StructField _t] p np) *
   malloc_token Ews t_struct_tree_t np *
  (if eq_dec p nullval then emp else
  EX (Icn: pc_flowint) (Isn: inset_flowint) (k: Z) (v: val),
  EX (pa pb: val),
  (!!(domm Icn = {[np]} /\ domm Icn = {[np]} /\
      (forall p', inf Icn p' = 0 \/ inf Icn p' = 1) /\
      (forall p', out Icn p' = 0 \/ out Icn p' = 1)) &&
   data_at Ews t_struct_tree (Vint (Int.repr k), (v, (pa, pb))) p *
   ghost_part sh ((Icn, Isn): @G bst_ghost) g *
   ghost_part sh (gset_to_keys {[k]} :@G keysGhost) gc))%logic.

Definition cont_to_keys (cont: bst_content_t): @G keysGhost :=
  gset_to_keys (dom (gset Z) cont).

Definition bst_tree (root: val) (cont: bst_content_t) (g gc: gname): mpred :=
  EX np: val, EX Ipc: pc_flowint, EX Iset: inset_flowint,
    !!(global_inv Ipc Iset np (dom (gset Z) cont)) &&
    data_at Ews (tptr (t_struct_tree_t)) np root *
    ghost_reference ((Ipc, Iset): @G bst_ghost) g *
    ghost_reference (cont_to_keys cont) gc *
    (EX l:
       (list (share * val)),
       !!(sepalg_list.list_join Share.bot (map fst l) Ews /\ NoDup (map snd l) /\
          (forall n, n ∈ domm Ipc <-> In n (map snd l))) &&
       iter_sepcon
         (fun sv => EX lock,
                    field_at Ews t_struct_tree_t [StructField _lock] lock (snd sv) *
                    malloc_token Ews tlock lock *
                    lock_inv Ews lock (node_rep (fst sv) g gc (snd sv))) l).

Local Open Scope Z_scope.

Global Obligation Tactic := atomic_nonexpansive_tac.

Program Definition delete_spec :=
 DECLARE _delete
 ATOMIC TYPE (rmaps.ConstType (val * Z * _ * _ * _))
         OBJ BST INVS base.empty base.top
 WITH b, x, gv, g, gc
 PRE  [ tptr (tptr t_struct_tree_t), tint]
    PROP (Int.min_signed <= x <= Int.max_signed)
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP (mem_mgr gv) | (bst_tree b BST g gc)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv) | (bst_tree b (delete x BST) g gc).

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
                 delete_spec
  ]).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
Abort.
