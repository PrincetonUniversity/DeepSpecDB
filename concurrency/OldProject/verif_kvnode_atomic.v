Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import bst.kvnode.
Import FashNotation.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tnode := Tstruct _node noattr.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition release_spec := DECLARE _release release_spec.
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition SIZE: Z := 8.

Definition data_log := nat -> option Z.

Definition version_ghost: Ghost := snap_PCM (ORD := max_order).

Definition data_log_ghost: Ghost :=
  snap_PCM (ORD := @fmap_order nat _ _ (@discrete_order Z)).

Definition ghost_log := ghost_master (ORD := @fmap_order nat _ _ (@discrete_order Z)).
Definition ghost_lsnap := ghost_snap (ORD := @fmap_order nat _ _ (@discrete_order Z)).
Definition ghost_version := ghost_master (ORD := max_order).
Definition ghost_vsnap := ghost_snap (ORD := max_order).

Definition log_max (l: data_log) (v: nat): Prop :=
  l v <> None /\ forall v', (v < v')%nat -> l v' = None.

Definition log_latest (l: data_log) (v: nat) (value: Z): Prop :=
  l v = Some value /\ log_max l v.

Definition version_state (p: val) (g: gname) (version: (@G version_ghost)): mpred :=
  !!(version.1 = Tsh) && field_at Ews tnode (DOT _version) (vint version.2) p.

Definition version_rep (p: val) (g: gname) (sh: share) lock :=
  field_at sh tnode (DOT _vlock) lock p *
    malloc_token sh tlock lock *
    lock_inv sh lock (sync_inv g Tsh (version_state p)).

Definition single_data_state sh loc (g: gname)
           (log: (@G data_log_ghost)): mpred :=
  EX d : Z, EX v: nat,
        !! (log.1 = Tsh /\ repable_signed d /\ log_latest log.2 v d) &&
          data_at sh tint (vint d) loc.

Definition single_data_rep loc lock_loc lock lg sh: mpred :=
  data_at sh (tptr tlock) lock lock_loc *
    lock_inv sh lock
             (sync_inv lg Tsh (single_data_state sh loc)).

Definition node_state sh vp vlock vg locs lock_locs locks lgs :=
  !! (Zlength locs = SIZE /\ Zlength locks = SIZE) &&
    version_rep vp vg sh vlock *
    iter_sepcon (fun i => single_data_rep
                         (Znth i locs)
                         (field_address0 (tarray tlock SIZE) (SUB i) lock_locs)
                         (Znth i locks) (Znth i lgs) sh) (upto (Z.to_nat SIZE)).

Definition log_halves (version: (@G version_ghost)) lgs (logs: list (@G data_log_ghost)) i :=
  !! (if Nat.even version.2 then log_max (Znth i logs).2 version.2
      else exists v, (v >= version.2 - 1)%nat /\ log_max (Znth i logs).2 v) &&
  public_half (Znth i lgs) (Znth i logs).

Definition public_state vg lgs (version: (@G version_ghost))
           (logs: list (@G data_log_ghost)): mpred :=
  public_half vg version *
    iter_sepcon (log_halves version lgs logs) (upto (Z.to_nat SIZE)).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
             complete_legal_cosu_type t = true;
             natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p).

Definition node_new_spec :=
  DECLARE _node_new
  WITH gv: globals, v_addr: val, values: list Z
  PRE [tptr tint]
  PROP (Zlength values = SIZE; Forall repable_signed values)
  PARAMS (v_addr)
  GLOBALS (gv)
  SEP (mem_mgr gv; data_at Ews (tarray tint SIZE) (map (fun z => vint z) values) v_addr)
  POST [tptr tnode]
  EX p: val, EX vp: val, EX vlock: val, EX vg: gname, EX locs: list val,
  EX lock_locs: val, EX locks: list val, EX lgs: list gname,
  PROP ()
  RETURN (p)
  SEP (mem_mgr gv; malloc_token Ews tnode p;
       data_at Ews (tarray tint SIZE) (map (fun z => vint z) values) v_addr;
       data_at Ews tnode (vp, (vint 0, (lock_locs, Znth 0 locs))) p;
       node_state Ews vp vlock vg locs lock_locs locks lgs;
       public_state vg lgs (Tsh, O) (map (fun v => (Tsh, ghosts.singleton O v)) values)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
                           freelock_spec; freelock2_spec; spawn_spec; node_new_spec;
                           surely_malloc_spec]).

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

Lemma body_node_new: semax_body Vprog Gprog f_node_new node_new_spec.
Proof.
  start_function.
  forward_call (tnode, gv).
  Intros p.
  forward_call (tlock, gv). { vm_compute; split; intro; easy. }
  Intros vlock.
  ghost_alloc (both_halves (P := version_ghost) (Tsh, O)). { apply @part_ref_valid. }
  Intros vg. rewrite <- both_halves_join. Intros.
  forward_call (vlock, Ews, (sync_inv vg Tsh (version_state p))).
  forward_call (tarray tlock SIZE, gv). { vm_compute; split; congruence. }
  Intros lock_locs.
  forward_call (tarray tint SIZE, gv). { vm_compute; split; congruence. }
  Intros locs.
  freeze FR := (mem_mgr _) (malloc_token _ _ _) (malloc_token _ _ _)
                           (malloc_token _ _ _) (malloc_token _ _ _)
                           (lock_inv _ _ _) (my_half _ _ _) (public_half _ _)
                           (data_at_ Ews tnode p).
  forward_for_simple_bound SIZE
     (EX i: Z, EX locks: list (reptype tlock),
      PROP (Zlength locks = i)
      LOCAL (temp _data locs; temp _locks lock_locs; temp _l vlock;
             temp _result p; gvars gv; temp _values v_addr)
      SEP (FRZL FR;
           data_at Ews (tarray tint SIZE)
                   ((map (fun z => vint z) (sublist.sublist 0 i values)) ++
                     Zrepeat Vundef (SIZE - i)) locs;
           data_at Ews (tarray tlock SIZE) (locks ++ Zrepeat [Vundef; Vundef] (SIZE - i)) lock_locs;
           data_at Ews (tarray tint SIZE) (map (λ z : Z, vint z) values) v_addr)).
  1: unfold SIZE; rep_lia.
  - rewrite !data_at__eq. Exists (@nil (list val)). entailer !.
  - ghost_alloc (both_halves (P := prod_PCM version_ghost data_log_ghost)
                             ((Tsh, O), (Tsh, ghosts.singleton O (Znth i values)))). {
      apply @part_ref_valid. }
    Intros lgi. rewrite <- both_halves_join. Intros.
    assert_PROP (isptr lock_locs) by (entailer !).
    assert_PROP (field_compatible0 (tarray tlock SIZE) (SUB i) lock_locs). { entailer!. }
    assert_PROP (field_compatible0 (tarray tint SIZE) (SUB i) locs). { entailer!. }
    forward_call (field_address0 (tarray tlock SIZE) (SUB i) lock_locs, Ews,
                   (sync_inv lgi Tsh
                             (single_data_state Ews (field_address0 (tarray tint SIZE) (SUB i) locs)))).
    + entailer !. simpl. destruct lock_locs; inversion H3. simpl.
      unfold field_address0. rewrite if_true; auto. simpl. do 3 f_equal. remember (Zlength locks).
      unfold Ptrofs.of_ints. rewrite Int.signed_repr. 2: unfold SIZE in H1; rep_lia.
      rewrite Z.max_r. 2: lia. rewrite ptrofs_mul_repr. f_equal.
    + rewrite (split2_data_at_Tarray_app i); auto. 2: apply Zlength_Zrepeat; lia.
      assert (SIZE - i = 1 + (SIZE - i - 1)) by lia. rewrite H6.
      rewrite <- (Zrepeat_app _ _ [Vundef; Vundef]); [|lia..]. rewrite <- H6.
      rewrite (split2_data_at_Tarray_app 1 (SIZE - i)). 2, 3: apply Zlength_Zrepeat; lia.
      assert (Zrepeat [Vundef; Vundef] 1 = [[Vundef; Vundef]]) by easy. rewrite H6.
      rewrite (data_at_singleton_array_eq _ tlock [Vundef; Vundef]); auto.
      rewrite data_at__eq. entailer !.
    + unfold SIZE in *. forward. forward.
      forward_call (field_address0 (tarray tlock SIZE) (SUB i) lock_locs, Ews,
                     (sync_inv lgi Tsh (single_data_state Ews (field_address0 (tarray tint SIZE) (SUB i) locs)))). {
        lock_props. unfold sync_inv, single_data_state.
        Exists ((Tsh, O), (Tsh, ghosts.singleton O (Znth i values))). simpl.
        Exists O. Exists (Znth i values). rewrite !H2.
        replace (1 + (8 - i - 1) - 1) with (8 - i - 1) by lia.
        replace (1 + (8 - i - 1)) with (8 - i) by lia.
        entailer !.
        - split.
          + rewrite List.Forall_forall in H0. apply H0. apply Znth_In. lia.
          + red. unfold ghosts.singleton. split.
            * destruct (eq_dec O O); auto. congruence.
            * intros. destruct (eq_dec v' O); auto. lia.
        - rewrite upd_Znth_app2; rewrite Zlength_map; autorewrite with sublist. 2: lia.
          rewrite upd_Znth_unfold. 2: rewrite Zlength_Zrepeat; lia. autorewrite with sublist.
          remember (Zlength locks) as i.
          assert (Zlength [vint (Znth i values)] = 1) by (unfold Zlength; simpl; lia).
          rewrite (split2_data_at_Tarray_app i).
          2: rewrite Zlength_map; autorewrite with sublist; auto.
          2: { rewrite Zlength_app. rewrite Zlength_Zrepeat; try lia. rewrite H2. lia. }
          rewrite (split2_data_at_Tarray_app 1); auto. 2: rewrite Zlength_Zrepeat; lia.
          rewrite (data_at_singleton_array_eq _ tint (vint (Znth i values))); auto. entailer !. }



Qed.
