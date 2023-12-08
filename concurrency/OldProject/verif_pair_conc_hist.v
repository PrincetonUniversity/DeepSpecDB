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

Section HIST_GHOST.

  Definition pair_impl := (Z * nat)%type.
  (* Definition hist_item := (pair_impl * pair_impl)%type. *)

  (* Definition hist_item_valid (it: hist_item): Prop := *)
  (*   it.1.2 = it.2.2 \/ S it.1.2 = it.2.2. *)

  Definition pair_hist := nat -> option pair_impl.

  (* Definition state_at (h: hist) (t: nat): option pair_impl := *)
  (*   match h t with *)
  (*   | None => None *)
  (*   | Some (p1, p2) => Some p2 *)
  (*   end. *)

  Definition newest_state (h: pair_hist) (p: pair_impl) :=
    exists t, h t = Some p /\ forall t', h t' ≠ None -> (t' <= t)%nat.

  (* Lemma state_compatible: forall h1 h2, *)
  (*     compatible h1 h2 -> *)
  (*     forall t p, state_at h1 t = Some p -> state_at (map_add h1 h2) t = Some p. *)
  (* Proof. *)
  (*   unfold state_at. intros. rewrite map_add_comm; auto. *)
  (*   destruct (h1 t) eqn:?H. 2: inversion H0. symmetry in H. *)
  (*   eapply compatible_k in H1; eauto. now rewrite H1. *)
  (* Qed. *)

  Definition hist_valid (h: pair_hist) := forall t1 t2 p1 p2,
      h t1 = Some p1 -> h t2 = Some p2 ->
      (p1.2 = p2.2 -> p1.1 = p2.1) /\ (t1 <= t2 -> (p1.2 <= p2.2)%nat).

  #[global] Instance hist_Sep: @sepalg.Sep_alg pair_hist map_disj_join.
  Proof.
    exists (fun _ => empty_map); intros; auto.
    repeat red. intros. destruct (t k); auto.
  Defined.

  #[global] Instance hist_Perm: @sepalg.Perm_alg pair_hist map_disj_join.
  Proof.
    constructor; intros.
    - extensionality k. specialize (H k); specialize (H0 k).
      destruct (x k), (y k); try congruence; contradiction.
    - apply map_disj_join_spec in H as []; apply map_disj_join_spec in H0 as []; subst.
      rewrite map_add_assoc. eexists; rewrite !map_disj_join_spec; repeat split.
      + eapply disjoint_incl; eauto. rewrite map_add_comm.
        * apply map_incl_add.
        * apply disjoint_compatible; auto.
      + apply disjoint_add; auto. eapply disjoint_incl; eauto. apply map_incl_add.
    - rewrite map_disj_join_spec in H. rewrite map_disj_join_spec. destruct H. split.
      + now symmetry.
      + rewrite map_add_comm; auto. apply disjoint_compatible. now symmetry.
    - extensionality k; specialize (H k); specialize (H0 k).
      destruct (a k), (b k); auto.
      + destruct (a' k); [contradiction | auto].
      + destruct (a' k); [contradiction | auto].
      + destruct (b' k); [contradiction | auto].
  Qed.

  #[global, program] Instance pair_impl_ghost: Ghost :=
    { valid := hist_valid; Join_G := map_disj_join }.
  Next Obligation.
    - intros. specialize (H0 t1 t2 p1 p2). rewrite map_disj_join_spec in H.
      destruct H. apply disjoint_compatible in H. subst x. symmetry in H.
      eapply compatible_k in H1, H2; eauto. rewrite map_add_comm in H1, H2; auto.
      specialize (H0 H1 H2). destruct H0. now apply H0.
    - intros. specialize (H0 t1 t2 p1 p2). rewrite map_disj_join_spec in H.
      destruct H. apply disjoint_compatible in H. subst x. symmetry in H.
      eapply compatible_k in H1, H2; eauto. rewrite map_add_comm in H1, H2; auto.
      specialize (H0 H1 H2). destruct H0. now apply H4.
  Qed.

End HIST_GHOST.

Notation pair_impl_info := (@G pair_impl_ghost).

Definition pair_impl_state (p: val) (g: gname) (hist: pair_impl_info): mpred :=
  EX content : Z, EX version: nat,
  !! (newest_state hist (content, version)) &&
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

Definition pair_rep (g: gname) (hist: pair_impl_info) :=
  public_half g hist.

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
      PROP (valid (ghosts.singleton O (value, O)))
      LOCAL (temp ret_temp p)
      SEP (mem_mgr gv; pair_impl_rep p g Ews lock;
           malloc_token Ews t_struct_pair_impl p;
           pair_rep g (ghosts.singleton O (value, O))).

Definition pair_free_spec :=
  DECLARE _pair_free
    WITH gv: globals, pa_hist: pair_impl_info, p: val, lock:val, g: gname
    PRE [tptr t_struct_pair_impl]
      PROP ()
      PARAMS (p)
      GLOBALS (gv)
      SEP (mem_mgr gv; pair_impl_rep p g Ews lock;
           malloc_token Ews t_struct_pair_impl p;
           pair_rep g pa_hist)
    POST [tvoid]
      PROP ()
      LOCAL ()
      SEP (mem_mgr gv).

Program Definition write_spec :=
 DECLARE _write
  ATOMIC TYPE (rmaps.ConstType _) OBJ hist INVS empty top
  WITH sh, g, gv, lock, p, value
  PRE [tptr t_struct_pair_impl, tint]
       PROP  (readable_share sh)
       PARAMS (p; vint value)
       GLOBALS (gv)
       SEP (pair_impl_rep p g sh lock) | (pair_rep g hist)
  POST [ tvoid ]
         EX ph: (pair_impl * pair_hist)%type,
         PROP ()
         LOCAL ()
         SEP (pair_impl_rep p g sh lock) | (!! (ph.1.1 = value /\
                                                add_events hist [ph.1] ph.2) &&
                                              pair_rep g ph.2).

Definition pair_snap_rep (ga gb: gname)
           (pairsnap: (pair_impl_info * pair_impl_info)%type) :=
  pair_rep ga (fst pairsnap) * pair_rep gb (snd pairsnap).

Definition pair_snap_rep_match (pairsnap: (pair_impl_info * pair_impl_info)%type)
           (pp: (Z * Z)%type): Prop :=
  exists p1 p2, newest_state pairsnap.1 p1 /\ newest_state pairsnap.2 p2 /\
                  p1.1 = pp.1 /\ p2.1 = pp.2.

Program Definition read_pair_spec :=
 DECLARE _read_pair
  ATOMIC TYPE (rmaps.ConstType _) OBJ pairsnap INVS empty top
  WITH sh, gv, ga, gb, locka, lockb, pa, pb
  PRE [tptr t_struct_pair_impl, tptr t_struct_pair_impl]
       PROP  (readable_share sh)
       PARAMS (pa; pb)
       GLOBALS (gv)
       SEP (mem_mgr gv; pair_impl_rep pa ga sh locka; pair_impl_rep pb gb sh lockb) |
           (pair_snap_rep ga gb pairsnap)
  POST [ tptr t_struct_pair ]
         EX pab: (val * (Z * Z))%type,
         PROP ()
         LOCAL (temp ret_temp (fst pab))
         SEP (mem_mgr gv;
              data_at Ews t_struct_pair
                      (vint (fst (snd pab)), vint (snd (snd pab))) (fst pab);
              malloc_token Ews t_struct_pair (fst pab);
              pair_impl_rep pa ga sh locka; pair_impl_rep pb gb sh lockb) |
    (!! pair_snap_rep_match pairsnap pab.2 && pair_snap_rep ga gb pairsnap).

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

Lemma newest_singleton: forall p t, newest_state (ghosts.singleton t p) p.
Proof.
  intros. red. exists t. split.
  - unfold ghosts.singleton. rewrite if_true; auto.
  - intros. unfold ghosts.singleton in H. destruct (eq_dec t' t). 2: tauto.
    subst. lia.
Qed.

Lemma valid_singleton: forall p (t: nat), valid (ghosts.singleton t p).
Proof.
  intros. red. unfold pair_impl_ghost. repeat intro. unfold ghosts.singleton in H, H0.
  destruct (eq_dec t1 t). 2: inversion H. subst t1. inversion H. subst p1.
  destruct (eq_dec t2 t). 2: inversion H0. subst t2. inversion H0. subst p2.
  split; intros; auto; lia.
Qed.

Lemma body_pair_new: semax_body Vprog Gprog f_pair_new pair_new_spec.
Proof.
  start_function.
  forward_call (t_struct_pair_impl, gv).
  Intros p.
  forward_call (tlock, gv). { vm_compute; split; intro; easy. }
  Intros lock.
  ghost_alloc (both_halves (ghosts.singleton O (value, O))). { apply @part_ref_valid. }
  Intros g. rewrite <- both_halves_join. Intros.
  forward_call (lock, Ews, (sync_inv g Tsh (pair_impl_state p))).
  forward.
  forward.
  forward.
  forward_call (lock, Ews, (sync_inv g Tsh (pair_impl_state p))). {
    lock_props. unfold sync_inv, pair_impl_state.
    Exists (ghosts.singleton O (value, O)) value O. entailer !.
    1: apply newest_singleton. unfold_data_at (data_at Ews _ _ _); cancel. }
  forward. pose proof (valid_singleton (value, O) O).
  Exists p lock g. entailer !. unfold pair_impl_rep, pair_rep. cancel.
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
  unfold sync_inv at 2. Intros h. unfold pair_impl_state at 2.
  Intros content version.
  forward.
  forward.
  forward.
  rewrite add_repr.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (EX ph, Q ph * (!! (ph.1 = (value, S version) /\
                                        newest_state ph.2 (value, S version)) &&
                                    my_half g Tsh ph.2)). {
    go_lower.
    rewrite <- (sepcon_emp
                  (atomic_shift (λ hist : pair_impl_info, pair_rep g hist) ∅ ⊤
         (λ (hist : pair_impl_info) (ph : Z * nat * (nat → option pair_impl)),
            !! (ph.1.1 = value ∧ add_events hist [ph.1] ph.2) && pair_rep g ph.2 * emp)
         Q * my_half g Tsh h)).
    apply sync_commit_gen. intros h1.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    unfold pair_rep. Exists h1. cancel. rewrite if_true; auto.
    apply imp_andp_adjoint. Intros. subst h1.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists h h. entailer !. rewrite <- wand_sepcon_adjoint.
    destruct H as [newt [? ?]].
    remember (map_upd h (S newt) (value, S version)) as h'.
    assert (add_events h [(value, S version)] h'). {
      subst h'. apply add_events_1. red. intros. apply H0 in H1. lia. }
    assert (newest_state h' (value, S version)). {
      subst h'. exists (S newt). split.
      - unfold map_upd. rewrite if_true; auto.
      - intros. unfold map_upd in H2. destruct (eq_dec t' (S newt)).
        1: subst; lia. apply H0 in H2. lia. }
    sep_apply (public_update g h h h'). Intros. apply ghost_seplog.bupd_mono.
    Exists ((value, S version), h'). simpl. entailer!. }
  Intros ph. destruct ph as [pS h'].
  forward_call (lock, sh, sync_inv g Tsh (pair_impl_state p)). {
    lock_props. unfold sync_inv. Exists h'. simpl in H0, H1.
    unfold pair_impl_state. Exists value (S version).
    replace (vint (version + 1)) with (vint (S version)). 2: do 2 f_equal; lia.
    subst pS. simpl. entailer !. }
  unfold pair_impl_rep. Exists (pS, h'). entailer !.
Qed.

Lemma body_read_pair: semax_body Vprog Gprog f_read_pair read_pair_spec.
Proof.
  start_function.
  forward_call(t_struct_pair, gv).
  Intros result. unfold fold_right_sepcon.
  forward_loop (PROP ( )
     LOCAL (temp _result result; gvars gv; temp _a pa; temp _b pb)
     SEP (mem_mgr gv; malloc_token Ews t_struct_pair result;
     data_at_ Ews t_struct_pair result;
     atomic_shift
       (λ pairsnap : pair_impl_info * pair_impl_info, pair_snap_rep ga gb pairsnap) ∅
       ⊤
       (λ (pairsnap : pair_impl_info * pair_impl_info) (pab : val * (Z * Z)),
          !! pair_snap_rep_match pairsnap pab.2 && pair_snap_rep ga gb pairsnap * emp)
       Q; pair_impl_rep pa ga sh locka; pair_impl_rep pb gb sh lockb)). 1: auto.
  unfold pair_impl_rep at 1. Intros.
  forward.
  forward_call (locka, sh, sync_inv ga Tsh (pair_impl_state pa)).
  unfold sync_inv at 2. Intros ha. unfold pair_impl_state at 2. Intros da va.
  forward.
  forward.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (atomic_shift (λ pairsnap : pair_impl_info * pair_impl_info, pair_snap_rep ga gb pairsnap) ∅ ⊤
            (λ (pairsnap : pair_impl_info * pair_impl_info) (pab : val * (Z * Z)),
               !! pair_snap_rep_match pairsnap pab.2 && pair_snap_rep ga gb pairsnap * emp) Q * my_half ga Tsh ha * (!!(exists t, ha t = Some (da, va)) && emp)). {
    go_lower.
    rewrite <-
            (sepcon_emp
               (atomic_shift
    (λ pairsnap : pair_impl_info * pair_impl_info, pair_snap_rep ga gb pairsnap) ∅ ⊤
    (λ (pairsnap : pair_impl_info * pair_impl_info) (pab : val * (Z * Z)),
       !! pair_snap_rep_match pairsnap pab.2 && pair_snap_rep ga gb pairsnap * emp) Q *
                  my_half ga Tsh ha)) at 1.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    apply sync_rollback. intros. destruct x as [pair1 pair2].
    eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists pair1.
    rewrite if_true; auto. unfold pair_snap_rep. simpl fst. simpl snd.
    unfold pair_rep at 1. cancel. apply imp_andp_adjoint. Intros. subst pair1.
    rewrite <- wand_sepcon_adjoint.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro]. unfold pair_rep at 2.
    entailer !. destruct H as [t [? ?]]. now exists t. } Intros.
  forward_call (locka, sh, sync_inv ga Tsh (pair_impl_state pa)). {
    lock_props. unfold sync_inv. Exists ha. unfold pair_impl_state.
    Exists da va. entailer !. }

Abort.
