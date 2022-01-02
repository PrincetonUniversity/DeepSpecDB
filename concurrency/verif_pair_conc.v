Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import bst.pair_conc.
Import FashNotation.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_pair := Tstruct _Pair noattr.
Definition t_struct_pair_impl := Tstruct _PairImpl noattr.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition release_spec := DECLARE _release release_spec.
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition pair_impl := (Z * nat)%type.

#[local] Instance pair_impl_ghost : Ghost := exclusive_PCM pair_impl.

Notation pair_impl_info := (@G pair_impl_ghost).

Definition pair_impl_state (p: val) (g: gname) (pair_impl: pair_impl_info): mpred :=
  EX content : Z, EX version: nat,
  !! (pair_impl = Some (content, version)) &&
    (field_at Ews t_struct_pair_impl (DOT _data) (vint content) p *
       field_at Ews t_struct_pair_impl (DOT _version) (vint version) p).

Definition pair_impl_rep (p: val) (g: gname) (sh: share) lock :=
  field_at sh t_struct_pair_impl (DOT _lock) lock p *
    malloc_token sh tlock lock *
    lock_inv sh lock (sync_inv g Tsh (pair_impl_state p)).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vint (Int.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition pair_rep (g: gname) (value: Z) (version: nat) :=
  public_half g (Some (value, version)).

Definition pair_new_spec :=
  DECLARE _pair_new
    WITH gv: globals, value: Z
    PRE [tint]
      PROP ()
      PARAMS (vint value)
      GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [tptr t_struct_pair_impl]
      EX p: val, EX lock:val,  EX g: gname,
      PROP ()
      LOCAL (temp ret_temp p)
      SEP (mem_mgr gv; pair_impl_rep p g Ews lock;
           malloc_token Ews t_struct_pair_impl p;
           pair_rep g value O).

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
                           freelock_spec; freelock2_spec; spawn_spec;
                           surely_malloc_spec;
                           pair_new_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (t, gv).
  Intros p.
  forward_if (p <> nullval).
  - if_tac; entailer!.
  - forward_call 1. contradiction.
  - forward. rewrite -> if_false by auto; entailer!.
  - forward. rewrite -> if_false by auto. Exists p; entailer!.
Qed.

Lemma body_pair_new: semax_body Vprog Gprog f_pair_new pair_new_spec.
Proof.
  start_function.
  forward_call (t_struct_pair_impl, gv).
  Intros p.
  forward_call (tlock, gv). { vm_compute; split; intro; easy. }
  Intros lock.
  ghost_alloc (both_halves (Some (value, O))). { apply @part_ref_valid. }
  Intros g. rewrite <- both_halves_join. Intros.
  forward_call (lock, Ews, (sync_inv g Tsh (pair_impl_state p))).
  forward.
  forward.
  forward.
  forward_call (lock, Ews, (sync_inv g Tsh (pair_impl_state p))). {
    lock_props. unfold sync_inv, pair_impl_state.
    Exists (Some (value, O)) value O. entailer !.
    unfold_data_at (data_at Ews _ _ _). cancel. }
  forward.
  Exists p lock g. entailer !. unfold pair_impl_rep. cancel.
Qed.
