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

Definition pair_rep (g: gname) (impl: pair_impl) :=
  public_half g (Some impl).

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
           pair_rep g (value, O)).

Definition pair_free_spec :=
  DECLARE _pair_free
    WITH gv: globals, pa_iml: pair_impl, p: val, lock:val, g: gname
    PRE [tptr t_struct_pair_impl]
      PROP ()
      PARAMS (p)
      GLOBALS (gv)
      SEP (mem_mgr gv; pair_impl_rep p g Ews lock;
           malloc_token Ews t_struct_pair_impl p;
           pair_rep g pa_iml)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (mem_mgr gv).

Definition change_pair (p: pair_impl) (v: Z): pair_impl :=
  match p with (value, version) => (v, S version) end.

Program Definition write_spec :=
 DECLARE _write
  ATOMIC TYPE (rmaps.ConstType _) OBJ impl INVS empty top
  WITH sh, g, gv, lock, p, value
  PRE [tptr t_struct_pair_impl, tint]
       PROP  (readable_share sh)
       PARAMS (p; vint value)
       GLOBALS (gv)
       SEP (pair_impl_rep p g sh lock) | (pair_rep g impl)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (pair_impl_rep p g sh lock) | (pair_rep g (change_pair impl value)).

Definition pair_snap_rep (ga gb: gname) (pairsnap: (pair_impl * pair_impl)%type) :=
  pair_rep ga (fst pairsnap) * pair_rep gb (snd pairsnap).

Program Definition read_pair_spec :=
 DECLARE _read_pair
  ATOMIC TYPE (rmaps.ConstType _) OBJ pairsnap INVS empty top
  WITH sh, gv, ga, gb, locka, lockb, pa, pb
  PRE [tptr t_struct_pair_impl, tint]
       PROP  (readable_share sh)
       PARAMS (pa; pb)
       GLOBALS (gv)
       SEP (pair_impl_rep pa ga sh locka; pair_impl_rep pb gb sh lockb) |
           (pair_snap_rep ga gb pairsnap)
  POST [ tptr t_struct_pair ]
         EX p: val,
         PROP ()
         LOCAL (temp ret_temp p)
         SEP (data_at_ Ews (tptr t_struct_pair) p;
              pair_impl_rep pa ga sh locka; pair_impl_rep pb gb sh lockb) |
             (pair_snap_rep ga gb pairsnap).


Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
                           freelock_spec; freelock2_spec; spawn_spec;
                           surely_malloc_spec; pair_new_spec; pair_free_spec;
                           read_pair_spec; write_spec]).

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

Lemma body_pair_free: semax_body Vprog Gprog f_pair_free pair_free_spec.
Proof.
  start_function.
  unfold pair_impl_rep. Intros.
  forward.
  forward_call (lock, Ews, sync_inv g Tsh (pair_impl_state p)).
  gather_SEP (pair_rep _ _).
  viewshift_SEP 0 emp. {
    go_lower. unfold pair_rep. iIntros "H". iMod (own_dealloc with "H"); auto. }
  forward_call (lock, Ews, sync_inv g Tsh (pair_impl_state p)). {
    lock_props. }
  assert_PROP (lock <> nullval) by entailer !.
  forward_call (tlock, lock, gv). {
    rewrite if_false; auto. entailer !. } clear .
  assert_PROP (p <> nullval) by entailer !.
  unfold sync_inv. Intros a. unfold pair_impl_state. Intros content version.
  gather_SEP (my_half _ _ _).
  viewshift_SEP 0 emp. {
    go_lower. iIntros "H". iMod (own_dealloc with "H"); auto. }
  gather_SEP (field_at Ews t_struct_pair_impl (DOT _data) _ _)
             (field_at Ews t_struct_pair_impl (DOT _version) _ _)
             (field_at Ews t_struct_pair_impl (DOT _lock) _ _).
  replace_SEP 0 (data_at Ews t_struct_pair_impl
                         (lock, (vint content, vint version)) p). {
    entailer !. unfold_data_at  (data_at Ews _ _ _). cancel. }
  forward_call (t_struct_pair_impl, p, gv). {
    rewrite if_false; auto. sep_apply (data_at_data_at_). cancel. }
  entailer !.
Qed.

Lemma body_write: semax_body Vprog Gprog f_write write_spec.
Proof.
  start_function.
  unfold pair_impl_rep. Intros.
  forward.
  forward_call (lock, sh, sync_inv g Tsh (pair_impl_state p)).
  unfold sync_inv at 2. Intros a. unfold pair_impl_state at 2.
  Intros content version. subst a.
  forward.
  forward.
  forward.
  rewrite add_repr.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (Q * my_half g Tsh (Some (value, S version))). {
    go_lower.
    rewrite <- (sepcon_emp
               (atomic_shift (λ impl : pair_impl, pair_rep g impl) ∅ ⊤
                             (λ (impl : pair_impl) (_ : ()),
                               pair_rep g (change_pair impl value) * emp)
                             (λ _ : (), Q) *
                  (@my_half pair_impl_ghost g Tsh (Some (content, version))))).
    apply sync_commit_gen1. intros pair1. Intros.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    unfold pair_rep. Exists (Some pair1). cancel. rewrite if_true; auto.
    apply imp_andp_adjoint. Intros. inversion H. subst pair1. clear H.
    cbn [change_pair]. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (Some (content, version)) (Some (content, version)). entailer !.
    2: exact tt. rewrite <- wand_sepcon_adjoint.
    sep_apply (public_update g (Some (content, version)) (Some (content, version))
                             (Some (value, S version))). Intros.
    apply ghost_seplog.bupd_mono. entailer!. }
  forward_call (lock, sh, sync_inv g Tsh (pair_impl_state p)). {
    lock_props. unfold sync_inv. Exists (Some (value, S version)).
    unfold pair_impl_state. Exists value (S version).
    replace (vint (version + 1)) with (vint (S version)). 2: do 2 f_equal; lia.
    entailer !. }
  unfold pair_impl_rep. entailer !.
Qed.
