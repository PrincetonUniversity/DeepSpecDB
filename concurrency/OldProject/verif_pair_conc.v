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

Section FAILED_ATTEMPTS.
  #[local] Definition join_pair_impl (a b: pair_impl): option pair_impl :=
  match a, b with
    | (c1, v1), (c2, v2) =>
        if (v1 <? v2)%nat then Some (c2, v2)
        else if (v2 <? v1)%nat then Some (c1, v1)
             else if ((c1 =? c2) && (v1 =? v2)%nat)%bool then Some (c1, v1)
                  else None
    end.

  #[local] Instance pair_impl_join: sepalg.Join pair_impl :=
    fun a b c => join_pair_impl a b = Some c.

  #[local] Instance pair_impl_perm: sepalg.Perm_alg pair_impl.
  Proof.
    constructor; intros.
    - repeat red in H, H0. rewrite H in H0. inversion H0. auto.
    - repeat red in H, H0. unfold join_pair_impl in H, H0. destruct a, b, c, d, e.
      destruct (n <? n0)%nat eqn:?H.
      + destruct (n2 <? n1)%nat eqn:?H.
        * inversion H; subst. inversion H0; subst.
          exists (z3, n3). split; repeat red; simpl. 1: rewrite H2; auto.
          rewrite !Nat.ltb_lt in H1 H2. assert (n < n3)%nat by lia.
          rewrite <- Nat.ltb_lt in H3. rewrite H3. auto.
        * destruct (n1 <? n2)%nat eqn:?H.
          -- inversion H; subst. inversion H0; subst. exists (z3, n3).
             split; repeat red; simpl.
             ++ rewrite H2. rewrite H3. auto.
             ++ rewrite H1. auto.
          -- inversion H; subst. destruct ((z2 =? z1) && (n2 =? n1)%nat)%bool eqn:?H.
             2: inversion H0. inversion H0; subst. exists (z3, n3).
             split; repeat red; simpl.
             ++ rewrite H2. rewrite H3. rewrite H4. auto.
             ++ rewrite H1. auto.
      + destruct (n0 <? n)%nat eqn:?H.
        * inversion H; subst. destruct (n2 <? n1)%nat eqn:?H.
          -- inversion H0; subst. exists (z3, n3). split; repeat red; simpl.
             2: rewrite H3; auto. rewrite Nat.ltb_ge in H1. rewrite Nat.ltb_lt in H3.
             assert (n0 < n3)%nat by lia. rewrite <- Nat.ltb_lt in H4.
             rewrite H4; auto.
          -- destruct (n1 <? n2)%nat eqn:?H.
             ++ inversion H0; subst. apply Nat.ltb_lt in H4, H2. admit.
             ++ destruct ((z2 =? z1) && (n2 =? n1)%nat)%bool eqn:?H. 2: inversion H0.
                inversion H0; subst. exists (z3, n3). rewrite andb_true_iff in H5.
                destruct H5. rewrite Nat.eqb_eq in H6. subst. rewrite Z.eqb_eq in H5.
                subst. split; repeat red; simpl. 1: rewrite H2; auto.
                rewrite Nat.ltb_irrefl. rewrite Z.eqb_refl. rewrite Nat.eqb_refl.
                simpl. auto.
        * destruct ((z =? z0) && (n =? n0)%nat)%bool eqn:?H. 2: inversion H.
          inversion H; subst. apply andb_true_iff in H3. destruct H3.
          apply Z.eqb_eq in H3. subst. apply Nat.eqb_eq in H4. subst.
          destruct (n0 <? n1)%nat eqn:?H.
          -- inversion H0; subst. exists (z3, n3).
             split; repeat red; simpl; rewrite H3; auto.
          -- destruct (n1 <? n0)%nat eqn:?H.
             ++ inversion H0; subst. exists (z3, n3). split; repeat red; simpl.
                ** rewrite H3. rewrite H4. auto.
                ** rewrite H1. rewrite Nat.eqb_refl. rewrite Z.eqb_refl. now simpl.
             ++ destruct ((z0 =? z1) && (n0 =? n1)%nat)%bool eqn:?H. 2: inversion H0.
                inversion H0; subst. apply andb_true_iff in H5. destruct H5.
                apply Z.eqb_eq in H5. apply Nat.eqb_eq in H6. subst.
                exists (z1, n1). split; repeat red; simpl; rewrite H1;
                  rewrite Nat.eqb_refl; rewrite Z.eqb_refl; simpl; auto.
    - unfold sepalg.join, pair_impl_join, join_pair_impl in *. destruct a, b, c.
      destruct (n <? n0)%nat eqn:?H.
      + inversion H; subst. rewrite Nat.ltb_lt in H0.
        assert ((n1 <? n)%nat = false). { rewrite Nat.ltb_ge. lia. } rewrite H1. auto.
      + destruct (n0 <? n)%nat eqn:?H; auto.
        destruct ((z =? z0) && (n =? n0)%nat)%bool eqn:?H. 2: inversion H.
        rewrite andb_true_iff in H2. destruct H2. rewrite Z.eqb_eq in H2.
        rewrite Nat.eqb_eq in H3. subst. rewrite Z.eqb_refl. rewrite Nat.eqb_refl.
        simpl. auto.
    - destruct a, a', b, b'. repeat red in H, H0. simpl in *.
      destruct (n <? n0)%nat eqn:?H.
      + inversion H; subst. destruct (n1 <? n2)%nat eqn:?H.
        * inversion H0; subst. rewrite !Nat.ltb_lt in H1, H2. lia.
        * destruct (n2 <? n1)%nat eqn:?H.
          -- inversion H0; subst; auto.
          -- destruct ((z1 =? z2) && (n1 =? n2)%nat)%bool; inversion H0; auto.
      + destruct (n0 <? n)%nat eqn:?H. 1: inversion H; auto.
        destruct ((z =? z0) && (n =? n0)%nat)%bool; inversion H; auto.
Abort.

End FAILED_ATTEMPTS.

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
    (!! (fst (snd pab) = fst (fst pairsnap) /\ snd (snd pab) = fst (snd pairsnap)) &&
       pair_snap_rep ga gb pairsnap).

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
    apply sync_commit_gen1. intros pair1.
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

Lemma body_read_pair: semax_body Vprog Gprog f_read_pair read_pair_spec.
Proof.
  start_function.
  forward_call(t_struct_pair, gv).
  Intros result. unfold fold_right_sepcon.
  forward_loop (PROP ( )
     LOCAL (temp _result result; gvars gv; temp _a pa; temp _b pb)
     SEP (mem_mgr gv; malloc_token Ews t_struct_pair result;
     data_at_ Ews t_struct_pair result;
     atomic_shift (λ pairsnap : pair_impl * pair_impl, pair_snap_rep ga gb pairsnap) ∅
       ⊤
       (λ (pairsnap : pair_impl * pair_impl) (pab : val * (Z * Z)),
          !! (pab.2.1 = pairsnap.1.1 ∧ pab.2.2 = pairsnap.2.1) &&
          pair_snap_rep ga gb pairsnap * emp) Q; pair_impl_rep pa ga sh locka;
     pair_impl_rep pb gb sh lockb)).
  1: auto.
  unfold pair_impl_rep at 1. Intros.
  forward.
  forward_call (locka, sh, sync_inv ga Tsh (pair_impl_state pa)).
  unfold sync_inv at 2. Intros a. unfold pair_impl_state at 2. Intros da va. subst a.
  forward.
  forward.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (EX pab, Q pab * (!! (pab.2.1 = da) &&
                                      my_half ga Tsh (Some (da, va)))). {
    go_lower.
    rewrite <-
            (sepcon_emp
               (atomic_shift (λ pairsnap : pair_impl * pair_impl,
                                 pair_snap_rep ga gb pairsnap)
                             ∅ ⊤
                             (λ (pairsnap : pair_impl * pair_impl)
                                (pab : val * (Z * Z)),
                               !! (pab.2.1 = pairsnap.1.1 ∧ pab.2.2 = pairsnap.2.1) &&
                                 pair_snap_rep ga gb pairsnap * emp) Q *
                  @my_half pair_impl_ghost ga Tsh (Some (da, va)))).
    apply sync_commit_same. intros. destruct x as [pair1 pair2].
    eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists (Some pair1).
    rewrite if_true; auto. unfold pair_snap_rep. simpl fst. simpl snd.
    unfold pair_rep at 1. cancel. apply imp_andp_adjoint. Intros. inversion H.
    subst pair1. clear H. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    rewrite <- wand_sepcon_adjoint.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro]. simpl fst.
    Exists (pa, (da, pair2.1)). simpl. entailer !. }
Abort.
