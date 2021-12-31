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
Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition pair_impl := (Z * nat)%type.

#[local] Instance pair_impl_ghost : Ghost := exclusive_PCM pair_impl.

Notation pair_impl_info := (@G pair_impl_ghost).

Definition pair_impl_state (p: val) (g: gname) (pair_impl: pair_impl_info): mpred :=
  EX content : Z, EX version: nat,
  !! (pair_impl = Some (content, version)) &&
    (field_at Ews t_struct_pair_impl [StructField _data] (vint content) p *
       field_at Ews t_struct_pair_impl [StructField _version] (vint version) p).

Definition pair_impl_rep (p: val) (g: gname) (sh: share) lock :=
  field_at Ews t_struct_pair_impl [StructField _lock] lock p *
    lock_inv sh lock (sync_inv g sh (pair_impl_state p)).

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

(* Definition pair_new_spec := *)
(*   DECLARE _pair_new, *)
(*     WITH gv: globals, *)
(*       PRE [], *)
(*       PROP (), *)
(*       PARAMS (), *)
(*       GLOBALS (gv), *)
(*       SEP (mem_mgr gv), *)
(*       POST [tptr t_struct_pair_impl], *)
(*       PROP (), *)
(*       LOCAL (temp ret_temp v), *)
(*       SEP (mem_mgr gv) *)

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
                           freelock2_spec; spawn_spec; surely_malloc_spec]).

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
