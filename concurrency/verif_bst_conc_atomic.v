Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_conc.
Import FashNotation.

Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

 (* trees labeled with ghost names *)

Inductive ghost_tree: Type :=
 | E_ghost : ghost_tree
 | T_ghost : ghost_tree ->gname -> key -> V  -> ghost_tree -> gname -> ghost_tree.

Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 r g2 x v :
       (k = x) -> In_ghost k (T_ghost l g1 x v r g2 )
  | InLeft_ghost l g1 r g2 x v' :
      In_ghost k l -> In_ghost k (T_ghost l g1 x v' r g2)
  | InRight_ghost l g1 r g2 x v' :
      In_ghost k r -> In_ghost k (T_ghost l g1 x v' r g2).

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k < x .
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k > x .

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
| Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
| Sorted_Ghost_Tree x v l g1 r g2 (Hsortedl : sorted_ghost_tree l) (Hsortedr : sorted_ghost_tree r)
  (Hgtl : gt_ghost l x) (Hltr : lt_ghost r x) : sorted_ghost_tree (T_ghost l g1 x v r g2 ).

Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree) (g1:gname) (g2:gname) : ghost_tree :=
match s with
| E_ghost => T_ghost E_ghost g1 x v E_ghost g2
| T_ghost a ga y v' b gb => if  x <? y then T_ghost (insert_ghost x v a g1 g2) ga y v' b gb
                       else if (y <? x) then T_ghost a ga y v' (insert_ghost x v b g1 g2) gb else T_ghost a ga x v b gb
end.

End TREES.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Definition lsh1 := fst (slice.cleave Ews).
Definition lsh2 := snd (slice.cleave Ews).

Definition sh1 := fst (slice.cleave lsh1).
Definition sh2 := snd (slice.cleave lsh1).

Lemma readable_lsh1 : readable_share lsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_lsh2 : readable_share lsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma lsh1_lsh2_join : sepalg.join lsh1 lsh2 Ews.
Proof.
  apply slice.cleave_join; unfold lsh1, lsh2; destruct (slice.cleave Ews); auto.
Qed.

Global Hint Resolve readable_lsh1 readable_lsh2 lsh1_lsh2_join : core.

Lemma readable_sh1 : readable_share sh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_sh2 : readable_share sh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma sh1_sh2_join : sepalg.join sh1 sh2 lsh1.
Proof.
  apply slice.cleave_join; unfold sh1, sh2; destruct (slice.cleave Ews); auto.
Qed.

Global Hint Resolve readable_sh1 readable_sh2 sh1_sh2_join : core.

Program Instance range_ghost : Ghost :=
  { G := range; valid g := True; Join_G a b c := c = merge_range a b }.
Next Obligation.
  exists (fun _ => (Pos_Infinity,Neg_Infinity)).
  + intros; hnf.
      destruct t; auto.
  + auto.
Defined.
Next Obligation.
 + intros; hnf in *. subst; auto.
 + intros; hnf in *. exists (merge_range b c); split; hnf. auto. rewrite H0. rewrite H. apply merge_assoc.
 + intros; hnf in *. rewrite merge_comm. apply H.
 + intros; hnf in *.
    symmetry in H; apply merge_range_incl in H.
    symmetry in H0; apply merge_range_incl in H0.
    apply range_incl_antisym; auto.
Qed.

Instance bst_ghost : Ghost := ref_PCM range_ghost.

Definition ghost_ref g r1 := ghost_reference(P := set_PCM) r1 g.

Definition in_tree g r1 := EX sh: share, ghost_part(P := set_PCM) sh (Ensembles.Singleton r1) g.

Definition finite (S : Ensemble gname) := exists m, forall x, Ensembles.In S x -> (x <= m)%nat.

Lemma finite_new : forall S, finite S -> exists g, ~Ensembles.In S g.
Proof.
  intros ? [m ?].
  exists (Datatypes.S m); intros X.
  specialize (H _ X); lia.
Qed.

Lemma finite_add : forall S g, finite S -> finite (Add S g).
Proof.
  intros ?? [m ?].
  exists (max g m); intros ? X.
  rewrite Nat.max_le_iff.
  inv X; auto.
  inv H0; auto.
Qed.

Lemma finite_union : forall S1 S2, finite S1 -> finite S2 -> finite (Union S1 S2).
Proof.
  intros ?? [m1 H1] [m2 H2].
  exists (max m1 m2); intros ? X.
  rewrite Nat.max_le_iff.
  inv X; auto.
Qed.

Lemma finite_empty : finite Empty_set.
Proof.
  exists O; intros; inv H.
Qed.

Lemma finite_singleton : forall x, finite (Singleton x).
Proof.
  intros; exists x; intros; inv H; auto.
Qed.

Lemma in_tree_add : forall g s g1 g', ~Ensembles.In s g' -> in_tree g g1 * ghost_ref g s |-- (|==> !! (g1 <> g') && (ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
Proof.
  intros.
  unfold in_tree at 1; Intros sh; iIntros "H".
  iPoseProof (ref_sub with "H") as "%".
  rewrite ghost_part_ref_join.
  assert (Ensembles.In s g1).
  { destruct (eq_dec sh Tsh); subst.
    - constructor.
    - destruct H0 as (? & ? & ?); subst.
      repeat constructor. }
  iMod (ref_add(P := set_PCM) _ _ _ _ (Singleton g') (Add (Singleton g1) g') (Add s g') with "H") as "H".
  { repeat constructor.
    inversion 1; subst.
    inv H3; inv H4; contradiction. }
  { split; auto.
    constructor; intros ? X; inv X.
    inv H3; contradiction. }
  fold (ghost_part_ref(P := set_PCM) sh (Add (Singleton g1) g') (Add s g') g).
  rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>".
  iDestruct "H" as "[in $]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := set_PCM) sh1 sh2 sh (Singleton g1) (Singleton g')); auto.
  iDestruct "in" as "[in1 in2]". iSplit.
  * iPureIntro; intros Hcontra; subst; congruence.
  * iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  * split; auto; constructor; intros ? X; inv X.
    inv H5; inv H6; contradiction.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
Qed.

Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. Is this the right way to do it? *)
Instance node_ghost : Ghost := prod_PCM range_ghost (exclusive_PCM (option ghost_info)).

Notation node_info := (@G node_ghost).

Lemma ghost_node_alloc : forall g s g1 (a : node_info),
  finite s -> in_tree g g1 * ghost_ref g s |-- (|==> EX g', !! (¬ Ensembles.In s g' /\ g1 <> g') && (both_halves a g' * ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
Proof.
  intros.
  iIntros "r".
  iMod (own_alloc_strong(RA := ref_PCM node_ghost) (fun x => ~Ensembles.In s x)
    (Some (Tsh, a), Some a) with "[$]") as (g') "[% ?]".
  { intros l.
    destruct H as [n H].
    exists (S (max (fold_right max O l) n)).
    split.
    - intros X%own.list_max.
      pose proof (Max.le_max_l (fold_right max O l) n); lia.
    - intros X; specialize (H _ X).
      pose proof (Max.le_max_r (fold_right max O l) n); lia. }
  { apply @part_ref_valid. }
  iExists g'. iFrame.
  iMod (in_tree_add _ _ _ g' with "r") as "(% & ($ & $))"; auto.
Qed.

Lemma gsh1_not_Tsh : gsh1 <> Tsh.
Proof.
  pose proof gsh1_gsh2_join. intro. rewrite H0 in H. apply sepalg.join_comm in H.
  apply sepalg.unit_identity in H. now apply (readable_nonidentity readable_gsh2).
Qed.

Lemma gsh2_not_Tsh : gsh2 <> Tsh.
Proof.
  pose proof gsh1_gsh2_join. intro. rewrite H0 in H. apply sepalg.unit_identity in H.
  now apply (readable_nonidentity readable_gsh1).
Qed.
Global Hint Resolve gsh1_not_Tsh gsh2_not_Tsh : core.

Lemma range_incl_join: forall  (r1 r2 r3 : node_info), sepalg.join r1 r2 r3 -> range_incl r1.1 r3.1 = true /\ range_incl r2.1 r3.1 = true.
Proof.
  intros. destruct r1 as [range1 r1]. destruct r2 as [range2 r2]. destruct r3 as [range3 r3].
  hnf in H. simpl in *. destruct H. inv H; auto. split; [|rewrite merge_comm]; eapply merge_range_incl; eauto.
Qed.

(* Each lock will hold gsh1 of my_half, with gsh2 held by the invariant, allowing the lock's range to become outdated.
  The exception is the root node, which will hold some smaller fraction of gsh1, allowing clients to know that the root's range is total. *)

(* base definition for node_lock_inv_r *)
Definition node_lock_inv_r' (R : (val * (own.gname * node_info) → mpred)) sh p gp lock :=
  sync_inv gp sh (uncurry (uncurry R p)) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
  malloc_token Ews tlock lock.

Definition node_lock_inv_r (R : (val * (own.gname * node_info) → mpred)) sh p gp lock :=
      selflock (node_lock_inv_r' R sh p gp lock) lsh2 lock.

Definition ltree_r R (g_root:gname) sh gsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] lock p *
   lock_inv sh lock (node_lock_inv_r R gsh p g_root lock)).

(* Does the range ghost help at all, given that we could calculate it precisely from the nodes we've seen?
  Yes, since the nodes we've seen may change after we pass them. *)
Definition node_rep_r (g:gname) R arg : mpred := let '(np, (g_current,(r,g_info))) := arg in
EX tp:val,
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * in_tree g g_current *
if eq_dec tp nullval then !!( g_info = Some None) && emp  else
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !! (g_info = Some (Some(x,v,ga,gb)) /\ Int.min_signed <= x <= Int.max_signed /\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp  *
    |> ltree_r R ga lsh1 gsh1 pa locka * |> ltree_r R gb lsh1 gsh1 pb lockb.

Definition node_rep_closed g := HORec (node_rep_r g).

Definition node_rep np g g_current r := node_rep_closed g (np, (g_current, r)).

Definition node_lock_inv_pred sh g p gp lock :=
  sync_inv gp sh (node_rep p g) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p * malloc_token Ews tlock lock (* * malloc_token Ews t_struct_tree_t p *).
(* No malloc token for t_struct_tree_t because node_rep_r contains one *)

Definition node_lock_inv sh g p gp lock :=
  selflock (node_lock_inv_pred sh g p gp lock) lsh2 lock.

Definition public_half' (g : gname) (d : range * option (option ghost_info)) := my_half g gsh2 (fst d, None) * public_half g d.

 Fixpoint ghost_tree_rep (t: @ ghost_tree val) (g:gname) range : mpred :=
 match t, range with
 | E_ghost , _ => public_half' g (range, Some (@None ghost_info))
 | T_ghost a ga x v b gb, (l, r) => public_half' g (range, Some (Some (x,v,ga,gb))) * ghost_tree_rep a ga (l, Finite_Integer x) * ghost_tree_rep b gb (Finite_Integer x, r)
 end.

Lemma public_half_range_incl : forall g r r' o, range_incl r r' = true -> public_half' g (r, o) |-- (|==> public_half' g (r', o))%I.
Proof.
  intros.
  iIntros "H".
  iPoseProof (public_part_update with "H") as "[% $]".
  intros ? [J1 J2]; simpl in *.
  split; auto; simpl.
  hnf in J1 |- *.
  symmetry in J1; rewrite merge_comm in J1; apply merge_range_incl in J1.
  symmetry; rewrite merge_comm; apply merge_range_incl'.
  eapply range_incl_trans; eauto.
Qed.

Fixpoint find_ghost_set (t : @ghost_tree val) (g:gname) : Ensemble gname :=
  match t with
  | E_ghost => Ensembles.Singleton g
  | T_ghost a ga x v  b gb => Add  (Union (find_ghost_set a ga) (find_ghost_set b gb)) g
end.

Definition find_ghost_set' (t : @ghost_tree val) : Ensemble gname :=
  match t with
  | E_ghost => Empty_set
  | T_ghost a ga x v  b gb => Union (find_ghost_set a ga) (find_ghost_set b gb)
end.

Lemma find_ghost_set_finite : forall t g, finite (find_ghost_set t g).
Proof.
  induction t; intros; simpl.
  - apply finite_singleton.
  - apply finite_add, finite_union; auto.
Qed.

Lemma find_ghost_set_equiv : forall t g,
  find_ghost_set t g = Add (find_ghost_set' t) g.
Proof.
  intros. destruct t.
  - unfold Add; simpl. now rewrite Union_Empty.
  - simpl; auto.
Qed.

Inductive unique_gname : ghost_tree -> Prop :=
  | Unique_Empty : unique_gname E_ghost
  | Unique_Tree : forall (x : key) (v : val) (l : ghost_tree) (g1 : gname) (r : ghost_tree) (g2 : gname),
                  unique_gname l -> unique_gname r ->
                  g1 <> g2 ->
                  Intersection (find_ghost_set' l) (find_ghost_set' r) = Empty_set ->
                  ~Ensembles.In (find_ghost_set' l) g1 ->
                  ~Ensembles.In (find_ghost_set' r) g1 ->
                  ~Ensembles.In (find_ghost_set' r) g2 ->
                  ~Ensembles.In (find_ghost_set' l) g2 ->
                  unique_gname (T_ghost l g1 x v r g2).

(* turn a tree into a gmap *)
Fixpoint tree_to_gmap (t : @ghost_tree val) : gmap key val :=
  match t with
  | E_ghost => empty
  | T_ghost a ga x v b gb => base.insert x v (union (tree_to_gmap a) (tree_to_gmap b))
  end.

Definition tree_rep (g : gname) (g_root : gname)  (m: gmap key val) : mpred := EX tg : ghost_tree,
  !! (~ Ensembles.In (find_ghost_set' tg) g_root /\ unique_gname tg /\ sorted_ghost_tree tg /\ tree_to_gmap tg = m) &&
  ghost_tree_rep tg g_root (Neg_Infinity, Pos_Infinity) * ghost_ref g (find_ghost_set tg g_root).

Definition ltree (g : gname) (g_root : gname) sh gsh p lock := !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] lock p  * lock_inv sh lock (node_lock_inv gsh g p g_root lock)).

(* nodebox_rep knows that the range of the root is -infinity to +infinity, but doesn't know the data. *)
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock : val) (nb : val) :=
  EX np: val, data_at sh (tptr (t_struct_tree_t)) np nb * ltree g g_root sh (fst (Share.split gsh1)) np lock * my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

Lemma my_half_range_inf : forall g sh1 sh2 r1 r2 o,
    my_half g sh1 (r1, o) * my_half g sh2 (Neg_Infinity, Pos_Infinity, None) |--
    my_half g sh1 (r2, o) * my_half g sh2 (Neg_Infinity, Pos_Infinity, None).
Proof.
  intros.
  iIntros "H"; iPoseProof (own_valid_2 with "H") as "%".
  destruct H as ((a, ?) & [J ?] & ?); simpl in J.
  destruct a as [(?, ?)|]; try contradiction.
  destruct J as (? & ? & ? & ?).
  unfold my_half; erewrite 2 ghost_part_join with
                      (a := (Neg_Infinity, Pos_Infinity, o));
  eauto with share; repeat constructor; simpl; hnf; rewrite merge_infinity; auto.
Qed.

Definition tree_rep_R (tp:val) (r:(range)) (g_info: option (option ghost_info)) g : mpred :=
  if eq_dec tp nullval then !!(g_info = Some None) && emp else
  EX ga : gname, EX gb : gname, EX x : Z, EX v : val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !!(g_info = Some (Some(x,v,ga,gb)) /\ Int.min_signed <= x <= Int.max_signed/\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp *
     |> ltree g ga lsh1 gsh1 pa locka * |> ltree g gb lsh1 gsh1 pb lockb.

(* up *)
Lemma eqp_subp : forall P Q, P <=> Q |-- P >=> Q.
Proof.
  intros; constructor.
  apply subtypes.eqp_subp, predicates_hered.derives_refl.
Qed.

(* up *)
Lemma selflock_nonexpansive2 : forall {A} (P Q : A -> mpred) sh p x,
    (ALL x : _, |> (P x <=> Q x) |--
    |> selflock (P x) sh p <=> |> selflock (Q x) sh p).
Proof.
  intros. apply allp_left with x. rewrite <- eqp_later; apply later_derives.
  apply nonexpansive_entail with (F := fun P => selflock P sh p).
  apply selflock_nonexpansive.
Qed.

Lemma lock_inv_node_lock_inv_r_nonexpansive:
  ∀ (P Q : val * (own.gname * node_info) → mpred)
    (sh gsh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * node_info),
    |> P x <=> |> Q x
       |-- |> lock_inv sh lock (node_lock_inv_r P gsh p gp lock) >=>
           |> lock_inv sh lock (node_lock_inv_r Q gsh p gp lock).
Proof.
  intros. eapply derives_trans, eqp_subp. eapply derives_trans, lock_inv_nonexpansive2.
  apply allp_right. intros v. unfold node_lock_inv_r.
  remember (fun (M: val * (own.gname *
                           node_info) -> mpred)
                (x: gname * val) =>
              (node_lock_inv_r' M gsh (snd x) (fst x) v)) as func.
  pose proof (selflock_nonexpansive2 (func P) (func Q) lsh2 v (gp, p)).
  replace (func P (gp, p)) with (node_lock_inv_r' P gsh p gp v) in H by
    now rewrite Heqfunc.
  replace (func Q (gp, p)) with (node_lock_inv_r' Q gsh p gp v) in H by
      now rewrite Heqfunc. rewrite eqp_later. eapply derives_trans, H.
  apply allp_right. intros (?, ?). clear H. subst func. unfold fst, snd.
  unfold node_lock_inv_r'. unfold sync_inv, uncurry.
  rewrite eqp_later. repeat rewrite -> later_sepcon. erewrite !(later_exp' node_info ((Pos_Infinity, Pos_Infinity), None)); eauto.
  do 2 apply semax_conc.eqp_sepcon, semax_conc.eqp_refl.
  apply eqp_exp. intros (?, ?). apply allp_left with (v0, (g, (g0, g1))).
  rewrite <- !eqp_later. apply later_derives, semax_conc.eqp_sepcon.
  + apply derives_refl.
  + apply semax_conc.eqp_refl.
Qed.

Lemma ltree_r_nonexpansive:
  ∀ (P Q : val * (own.gname * node_info) → mpred)
    (sh gsh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * node_info),
    |> P x <=> |> Q x |-- |> ltree_r P gp sh gsh p lock >=> |> ltree_r Q gp sh gsh p lock.
Proof.
  intros. unfold ltree_r. rewrite !later_andp. apply subp_andp. 1: apply subp_refl.
  rewrite !later_sepcon. apply subp_sepcon. 1: apply subp_refl.
  apply lock_inv_node_lock_inv_r_nonexpansive.
Qed.

Lemma node_rep_def : forall np r g g_current,
    node_rep np g g_current r =
    EX tp:val, (field_at Ews (t_struct_tree_t) [StructField _t] tp np) *
               malloc_token Ews t_struct_tree_t np *  in_tree g g_current *
               tree_rep_R tp (fst r) (snd r) g.
Proof.
   intros. assert (HOcontractive (node_rep_r g)). {
    apply prove_HOcontractive. intros ?? (?, (?, (?, ?))). unfold node_rep_r.
    apply subp_exp; intros. apply subp_sepcon; [apply subp_refl|].
    destruct (eq_dec x nullval). 1: apply subp_refl. repeat (apply subp_exp; intro).
    rewrite !sepcon_assoc; apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; apply ltree_r_nonexpansive. }
  unfold node_rep, node_rep_closed.
  etransitivity; [eapply equal_f, HORec_fold_unfold|]; auto.
  unfold node_rep_r at 1. destruct r; reflexivity.
Qed.

Lemma node_lock_inv_def : forall gsh p lock g g_current,
  node_lock_inv gsh g p g_current lock =
  (EX a : node_info,
    node_rep p g g_current a * my_half g_current gsh a) *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
    malloc_token Ews tlock lock *
    |> lock_inv lsh2 lock (node_lock_inv gsh g p g_current lock).
Proof.
  intros.
  unfold node_lock_inv at 1.
  setoid_rewrite (selflock_eq) at 1.
  unfold node_lock_inv_pred at 1.
  unfold sync_inv at 1.
  unfold node_lock_inv at 1.
  reflexivity.
Qed.

Lemma node_lock_exclusive : forall sh p lock g g_current,
  exclusive_mpred (node_lock_inv sh g p g_current lock).
Proof.
  intros. rewrite node_lock_inv_def.
  eapply derives_exclusive, exclusive_sepcon1 with
  (P := field_at lsh2 t_struct_tree_t [StructField _lock] lock p)
  (Q := (EX a : node_info, node_rep p g g_current a * my_half(P := node_ghost) g_current sh a) *
         malloc_token Ews tlock lock * _).
  - Intros a. Exists a. cancel. apply derives_refl.
  - apply field_at_exclusive; auto.
    simpl. lia.
Qed.
Global Hint Resolve node_lock_exclusive : core.

Lemma node_lock_inv_rec: forall sh g p gp lock,
    rec_inv lsh2 lock (node_lock_inv_pred sh g p gp lock) (node_lock_inv sh g p gp lock).
Proof. intros. apply node_lock_inv_def. Qed.
Global Hint Resolve node_lock_inv_rec : core.

Lemma node_exist_in_tree: forall g s g_in, in_tree g g_in * ghost_ref g s |-- !! (Ensembles.In s g_in).
Proof.
intros. unfold ghost_ref, in_tree; Intros sh. rewrite ref_sub.  destruct  (eq_dec sh Tsh).
- Intros. apply log_normalize.prop_derives. intros. subst s.  apply In_singleton.
- apply log_normalize.prop_derives. intros [m H].  unfold sepalg.join in H. hnf in H. destruct H. rewrite H0. apply Union_introl. apply In_singleton.
Qed.

Lemma In_tree_to_gmap : forall x t, In_ghost x t <-> tree_to_gmap t !! x <> None.
Proof.
  induction t; simpl.
  - rewrite lookup_empty. split; [inversion 1| contradiction].
  - destruct (eq_dec k x).
    + subst; rewrite lookup_insert.
      split; [discriminate | by constructor].
    + rewrite -> lookup_insert_ne, lookup_union by auto.
      unfold union_with, option_union_with.
      split. 
      * inversion 1; subst; first contradiction.
        { apply IHt1 in H1; destruct (tree_to_gmap t1 !! x); auto; destruct (tree_to_gmap t2 !! x); auto. }
        { apply IHt2 in H1; destruct (tree_to_gmap t1 !! x); auto; destruct (tree_to_gmap t2 !! x); auto. }
      * destruct (tree_to_gmap t1 !! x) eqn: H1.
        { intros; constructor 2; apply IHt1; auto. }
        { destruct (tree_to_gmap t2 !! x); last contradiction.
          intros; constructor 3; apply IHt2; auto. }
Qed.

Lemma insert_tree_to_gmap : forall t x v g1 g2, sorted_ghost_tree t ->
  tree_to_gmap (insert_ghost x v t g1 g2) = <[x := v]>(tree_to_gmap t).
Proof.
  intros; induction t; simpl.
  - rewrite left_id; reflexivity.
  - inv H.
    destruct (x <? k) eqn: H1; [|destruct (k <? x) eqn: H2]; simpl.
    + rewrite -> IHt1 by auto. rewrite -insert_union_l; apply insert_commute; lia.
    + rewrite -> IHt2 by auto. rewrite -insert_union_r. apply insert_commute; lia.
      { specialize (Hgtl x). destruct (tree_to_gmap t1 !! x) eqn: Hx; auto.
        spec Hgtl; last lia. apply In_tree_to_gmap; rewrite Hx; auto. }
    + assert (x = k) by lia; subst.
      rewrite insert_insert; reflexivity.
Qed.

Lemma update_ghost_ref: forall g s g_in (a b : node_info), finite s -> in_tree g g_in * ghost_ref g s |--
  (|==> EX g1 g2:gname, !!((~Ensembles.In s g1) /\ (~Ensembles.In s g2) /\ (g1 <> g2)) &&
    both_halves a g1 * both_halves b g2 * ghost_ref g (Add (Add s g1) g2) *
    in_tree g g1 * in_tree g g2 * in_tree g g_in)%I .
 Proof.
  intros.
  iIntros "H".
  iDestruct "H" as "[Ha Hb]". iPoseProof (ghost_node_alloc with "[$Ha $Hb]") as ">H"; auto.
  iDestruct "H" as ((* sh3 sh4  *)g1) "[% [[[Ha Hb] Hc] Hd]]". instantiate (1:= a).
  iPoseProof( ghost_node_alloc with "[$Hb $Hc]") as ">Hnew". apply finite_add; auto.
  iDestruct "Hnew" as ((* sh5 sh6 *) g2) "[% [[[Hc Hb] He] Hf]]". instantiate (1:= b).
  iModIntro. iExists (* sh4, sh6, *) g1, g2. iFrame. iSplit; auto; iPureIntro.
  destruct H0; destruct H1 as [Hinadd ?]; repeat (split; auto).
  intro Hcontra. apply Hinadd. apply Union_introl; auto.
  intro Hcontra; subst. apply Hinadd. apply Union_intror; constructor.
Qed.

Lemma ghost_set_insert: forall x v tg g1 g2, ~In_ghost x tg -> find_ghost_set' (insert_ghost x v tg g1 g2) =  Add (Add (find_ghost_set' tg) g1) g2.
Proof.
  induction tg; intros; simpl.
  + unfold Add. rewrite Union_Empty. reflexivity.
  + destruct (x <? k) eqn:E1; [|destruct (k <? x) eqn:E2]; simpl.
    - repeat rewrite -> find_ghost_set_equiv with (g := g).
      rewrite IHtg1. unfold Add.
      remember (find_ghost_set' tg1) as a1. remember (find_ghost_set tg2 g0) as a2.
      remember (Singleton g1) as b. remember (Singleton g2) as c.
      remember (Singleton g) as d.
      rewrite -> (Union_assoc a1 b c). rewrite -> (Union_assoc a1 _ d).
      rewrite -> (Union_comm _ d). rewrite <- (Union_assoc a1 d _).
      rewrite -> (Union_assoc _ _ a2). rewrite -> (Union_comm _ a2).
      rewrite <- (Union_assoc _ a2 _). rewrite <- Union_assoc; reflexivity.
      intro Hcontra. apply H. apply InLeft_ghost; auto.
    - repeat rewrite -> find_ghost_set_equiv with (g := g0).
      rewrite IHtg2. unfold Add.
      remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set' tg2) as a2.
      remember (Singleton g1) as b. remember (Singleton g2) as c.
      remember (Singleton g0) as d.
      rewrite -> (Union_assoc _ c d).
      rewrite -> (Union_assoc a2 b _). rewrite (Union_comm b _).
      rewrite (Union_assoc c d b). rewrite <- (Union_comm _ c).
      rewrite <- (Union_assoc a2 _ c). rewrite <- (Union_assoc a2 d b).
      rewrite <- (Union_assoc a1 _ c). rewrite <- (Union_assoc a1 _ b).
      reflexivity.
      intro Hcontra. apply H. apply InRight_ghost; auto.
    - intros. assert (x = k) by lia.
      apply (InRoot_ghost x tg1 g tg2 g0 k v0) in H0. contradiction H.
Qed.

Lemma ghost_set_insert2: forall x v tg g1 g2 g_root, ~In_ghost x tg -> find_ghost_set (insert_ghost x v tg g1 g2) g_root = Add (Add (find_ghost_set tg g_root) g1) g2.
Proof.
  intros.
  rewrite !find_ghost_set_equiv ghost_set_insert; auto.
  unfold Add.
  rewrite !Union_assoc (Union_comm (Singleton _)) Union_assoc (Union_comm (Singleton _)) Union_assoc; reflexivity.
Qed.

Lemma ghost_set_insert_same: forall x v tg g1 g2, In_ghost x tg -> sorted_ghost_tree tg -> find_ghost_set' (insert_ghost x v tg g1 g2) = find_ghost_set' tg.
  induction tg; intros; simpl.
 + inv H.
 + inv H0; inv H; simpl.
    - rewrite Z.ltb_irrefl; reflexivity.
    - specialize (Hgtl _ H1). destruct (x <? k) eqn:?; try lia; simpl.
      rewrite !find_ghost_set_equiv IHtg1; auto.
    - specialize (Hltr _ H1). destruct (x <? k) eqn:?; [|destruct (k <? x) eqn:?]; try lia; simpl.
      rewrite !find_ghost_set_equiv IHtg2; auto.
Qed.

Lemma ghost_set_insert_same2: forall x v tg g1 g2 g_root, In_ghost x tg -> sorted_ghost_tree tg -> find_ghost_set (insert_ghost x v tg g1 g2) g_root =  find_ghost_set tg g_root.
Proof.
  intros.
  rewrite !find_ghost_set_equiv ghost_set_insert_same; auto.
Qed.

Inductive range_info_in_tree (ri: node_info)
          (range: range): ghost_tree -> Prop :=
| riit_none: ri = (range, Some None) -> range_info_in_tree ri range E_ghost
| riit_root: forall (l r: ghost_tree) (g1 g2: gname) k v,
    ri = (range, Some (Some (k, v, g1, g2))) ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2)
| riit_left: forall (l r: ghost_tree) (g1 g2: gname) k v,
    range_info_in_tree ri (range.1, Finite_Integer k) l ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2)
| riit_right: forall (l r: ghost_tree) (g1 g2: gname) k v,
    range_info_in_tree ri (Finite_Integer k, range.2) r ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2).

Definition empty_range rn tg r_root := range_info_in_tree (rn, Some None) r_root tg.

Lemma empty_range_E : forall r, empty_range r E_ghost r.
Proof.
  constructor; auto.
Qed.
Global Hint Resolve empty_range_E : core.

Definition keys_in_range_ghost (t : @ghost_tree val) r := forall k, In_ghost k t -> key_in_range k r = true.

Lemma keys_in_range_ghost_subtrees : forall t1 t2 g1 g2 k v r, keys_in_range_ghost (T_ghost t1 g1 k v t2 g2) r -> sorted_ghost_tree (T_ghost t1 g1 k v t2 g2) ->
  key_in_range k r = true /\ keys_in_range_ghost t1 (r.1, Finite_Integer k) /\ keys_in_range_ghost t2 (Finite_Integer k, r.2).
Proof.
  intros. inv H0. split3.
  - apply H; constructor; auto.
  - intros ??.
    specialize (H k0); spec H.
    { apply InLeft_ghost; auto. }
    apply Hgtl in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [->]; lia.
  - intros ??.
    specialize (H k0); spec H.
    { apply InRight_ghost; auto. }
    apply Hltr in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [? H1].
    simpl in *; rewrite H1; lia.
Qed.

Lemma keys_in_range_infinity : forall tg, keys_in_range_ghost tg (Neg_Infinity, Pos_Infinity).
Proof.
  intros ???; auto.
Qed.
Global Hint Resolve keys_in_range_infinity : core.

Lemma ghost_range_inside_ghost_range : forall r r_root tg, empty_range r tg r_root -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg -> range_incl r r_root = true.
Proof.
  intros; revert dependent r_root.
  induction tg; intros; inv H.
  - inv H2; apply range_incl_refl.
  - inv H3.
  - eapply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); [|auto].
    inv H1.
    eapply range_incl_trans; [apply IHtg1; eauto 1|].
    apply key_in_range_l; auto.
  - eapply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); [|auto].
    inv H1.
    eapply range_incl_trans; [apply IHtg2; eauto 1|].
    apply key_in_range_r; auto.
Qed.

Notation public_half := (public_half').

Lemma ghost_tree_insert: forall tg g_root g_in x v r_root
  (Hin : Ensembles.In (find_ghost_set tg g_root) g_in)
  (Hrange : keys_in_range_ghost tg r_root) (Hsorted : sorted_ghost_tree tg),
  ghost_tree_rep tg g_root r_root  |-- EX r : range, EX o : option ghost_info, !!(range_incl r r_root = true) && public_half g_in (r, Some o) *
  (* insert *)
  ((!! (key_in_range x r = true) --> ALL g1 g2 : gname, match o with
  | None => public_half g_in (r, Some (Some(x,v,g1,g2))) * public_half g1 (fst r, Finite_Integer x, Some (@None ghost_info)) * public_half g2 (Finite_Integer x, snd r, Some (@None ghost_info)) -*
    (!! empty_range r tg r_root && ghost_tree_rep (insert_ghost x v tg g1 g2) g_root r_root)
  | Some (x0, v0, ga, gb) => !!(x0 = x) && public_half g_in (r, Some (Some(x,v,ga,gb))) -* 
    (!! In_ghost x tg && ghost_tree_rep (insert_ghost x v tg g1 g2) g_root r_root)
  end) &&
  (* no change *)
  (public_half g_in (r, Some o) -* ghost_tree_rep tg g_root r_root)).
Proof.
  intros.
  revert dependent r_root.
  revert dependent g_root.
  induction tg; simpl; intros.
  - inv Hin. Exists r_root (@None ghost_info); entailer!.
    apply andp_right.
    * rewrite <- imp_andp_adjoint; Intros.
      apply allp_right; intro g1. apply allp_right; intro g2. rewrite <- wand_sepcon_adjoint. destruct r_root; entailer!; auto.
    * apply wand_refl_cancel_right.
  - apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
    inv Hsorted; inv Hin. destruct r_root; inv H2.
    * sep_apply IHtg1; clear IHtg1 IHtg2.
      Intros r o; Exists r o; entailer!.
      { eapply range_incl_trans; [eassumption|].
        apply key_in_range_l with (r := (_, _)); auto. }
      iIntros "[[IH root] tree2]"; iSplit.
      + iIntros "%". iDestruct "IH" as "[IH _]"; iSpecialize ("IH" with "[%]"); first done.
        iIntros (g1 g2); iSpecialize ("IH" $! g1 g2).
        assert (x <? k = true) as ->.
        { destruct r; eapply (less_than_less_than_equal_trans (Finite_Integer _) _ (Finite_Integer _)).
          unfold key_in_range in H4; apply andb_prop in H4; apply H4.
          unfold range_incl in H2; apply andb_prop in H2; apply H2. }
        destruct o as [(((?, ?), ?), ?)|].
        -- iIntros "H"; iDestruct ("IH" with "H") as "[% ?]".
           iFrame; iPureIntro.
           split; auto; apply InLeft_ghost; auto.
        -- iIntros "H"; iDestruct ("IH" with "H") as "[% ?]".
           iFrame; iPureIntro.
           split; auto; apply riit_left; auto.
      + iDestruct "IH" as "[_ IH]".
        iIntros "H"; iSpecialize ("IH" with "H"); iFrame.
    * sep_apply IHtg2; clear IHtg1 IHtg2.
      Intros r o; Exists r o. rewrite sepcon_andp_prop'; apply andp_right.
      { apply prop_right; eapply range_incl_trans; [eassumption|].
        apply key_in_range_r with (r := (_, _)); auto. }
      cancel. iIntros "[[IH root] tree1]"; iSplit.
      + iIntros "%". iDestruct "IH" as "[IH _]"; iSpecialize ("IH" with "[%]"); first done.
        iIntros (g1 g2); iSpecialize ("IH" $! g1 g2).
        assert (k <? x = true) as Hgt.
        { destruct r; eapply (less_than_equal_less_than_trans (Finite_Integer _) _ (Finite_Integer _)).
          unfold range_incl in H2; apply andb_prop in H2; apply H2.
          unfold key_in_range in H4; apply andb_prop in H4; apply H4. }
        assert (x <? k = false) as -> by lia; rewrite Hgt.
        destruct o as [(((?, ?), ?), ?)|].
        -- iIntros "H"; iDestruct ("IH" with "H") as "[% ?]".
           iFrame; iPureIntro.
           split; auto; apply InRight_ghost; auto.
        -- iIntros "H"; iDestruct ("IH" with "H") as "[% ?]".
           iFrame; iPureIntro.
           split; auto; apply riit_right; auto.
      + iDestruct "IH" as "[_ IH]".
        iIntros "H"; iSpecialize ("IH" with "H"); iFrame.
    * inv H2. Exists r_root (Some (k, v0, g, g0)).
      destruct r_root. rewrite sepcon_andp_prop'; apply andp_right.
      { apply prop_right, range_incl_refl. }
      cancel. apply andp_right.
      + rewrite <- imp_andp_adjoint; Intros.
        apply allp_right; intro g1. apply allp_right; intro g2.
        rewrite <- wand_sepcon_adjoint; Intros; entailer!.
        { apply InRoot_ghost; auto. }
        destruct (x <? x) eqn: E1; try lia.
        simpl; entailer!.
      + rewrite <- wand_sepcon_adjoint; cancel.
Qed.

Lemma key_not_exist_in_tree: forall tg r_root d x (Hempty : empty_range d tg r_root)
  (Hrange : keys_in_range_ghost tg r_root) (Hsorted : sorted_ghost_tree tg),
  key_in_range x d = true -> ~In_ghost x tg.
Proof.
  induction tg; intros.
  { intros X; inv X. }
  apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
  intros X. inv Hsorted. inv Hempty.
  - inv H4.
  - exploit IHtg1; eauto.
    apply ghost_range_inside_ghost_range in H4; auto.
    eapply key_in_range_incl in H; eauto.
    inv X; auto.
    * simpl in H; lia.
    * specialize (Hltr _ H5); simpl in H; lia.
  - exploit IHtg2; eauto.
    apply ghost_range_inside_ghost_range in H4; auto.
    eapply key_in_range_incl in H; eauto.
    inv X; auto.
    * simpl in H; lia.
    * specialize (Hgtl _ H5); simpl in H; lia.
Qed.

Lemma both_halves_join : forall g a, my_half g gsh1 a * public_half g a = both_halves a g.
Proof.
  intros; rewrite <- both_halves_join.
  unfold public_half'; erewrite <- sepcon_assoc, my_half_join; eauto with share.
  repeat constructor; hnf; simpl.
  symmetry; apply merge_id.
Qed.

Lemma empty_intersection: forall {A} S T,
  @Intersection A S T = Empty_set <-> (forall x, Ensembles.In S x -> ~Ensembles.In T x).
Proof.
  split; intros.
  + intros Hcontra. assert (Ensembles.In (Intersection S T) x) by (constructor; auto).
    rewrite H in H1; inv H1.
  + apply Extensionality_Ensembles.
    split; unfold Included; intros.
    - inv H0. apply H in H1; contradiction.
    - inv H0.
Qed.

Lemma insert_ghost_unique: forall x (v : val) tg g1 g2,
  g1 <> g2 -> ~In_ghost x tg ->
  ~Ensembles.In (find_ghost_set' tg) g1 ->
  ~Ensembles.In (find_ghost_set' tg) g2 ->
  unique_gname tg -> unique_gname (insert_ghost x v tg g1 g2).
Proof.
  induction tg; simpl; intros.
  - simpl. apply Unique_Tree; try (intros Hcontra; inv Hcontra; fail); auto.
    apply Intersection_Empty.
  - assert (¬ In_ghost x tg1) as Hntg1. {
      intros Hcontra; apply H0. apply InLeft_ghost; auto.
    }
    assert (¬ In_ghost x tg2) as Hntg2. {
      intros Hcontra; apply H0. apply InRight_ghost; auto.
    }
    assert (¬ Ensembles.In (find_ghost_set' tg1) g1) as Hnghosttg1g1. {
      intros Hcontra; apply H1; simpl. apply Union_introl.
      rewrite find_ghost_set_equiv. apply Union_introl; auto.
    }
    assert (¬ Ensembles.In (find_ghost_set' tg1) g2) as Hnghosttg1g2. {
      intros Hcontra; apply H2; simpl. apply Union_introl.
      rewrite find_ghost_set_equiv. apply Union_introl; auto.
    }
    assert (¬ Ensembles.In (find_ghost_set' tg2) g1) as Hnghosttg2g1. {
      intros Hcontra; apply H1; simpl. apply Union_intror.
      rewrite find_ghost_set_equiv. apply Union_introl; auto.
    }
    assert (¬ Ensembles.In (find_ghost_set' tg2) g2) as Hnghosttg2g2. {
      intros Hcontra; apply H2; simpl. apply Union_intror.
      rewrite find_ghost_set_equiv. apply Union_introl; auto.
    }
    simpl. inv H3. destruct (x <? k) eqn:E; [|destruct (k <? x) eqn:E2].
    + constructor; auto.
      * rewrite ghost_set_insert; auto.
        rewrite empty_intersection; rewrite -> empty_intersection in H13.
        intros ? Hin1 Hin2.
        inv Hin1.
        inv H3.
        { eapply H13; eauto. }
        { inv H4; eauto. }
        { inv H3; eauto. }
      * rewrite ghost_set_insert; auto.
        inversion 1; subst. inv H4; eauto.
        { inv H5; eauto. contradiction H1.
          constructor 1. rewrite find_ghost_set_equiv. constructor 2; constructor. }
        { inv H4; eauto. contradiction H2.
          constructor 1. rewrite find_ghost_set_equiv. constructor 2; constructor. }
      * rewrite ghost_set_insert; auto.
        inversion 1; subst. inv H4; eauto.
        { inv H5; eauto. contradiction H1.
          constructor 2. rewrite find_ghost_set_equiv. constructor 2; constructor. }
        { inv H4; eauto. contradiction H2.
          constructor 2. rewrite find_ghost_set_equiv. constructor 2; constructor. }
    + constructor; auto.
      * rewrite ghost_set_insert; auto.
        rewrite empty_intersection; rewrite -> empty_intersection in H13.
        intros ? Hin1 Hin2.
        inv Hin2.
        inv H3.
        { eapply H13; eauto. }
        { inv H4; eauto. }
        { inv H3; eauto. }
      * rewrite ghost_set_insert; auto.
        inversion 1; subst. inv H4; eauto.
        { inv H5; eauto. contradiction H1.
          constructor 1. rewrite find_ghost_set_equiv. constructor 2; constructor. }
        { inv H4; eauto. contradiction H2.
          constructor 1. rewrite find_ghost_set_equiv. constructor 2; constructor. }
      * rewrite ghost_set_insert; auto.
        inversion 1; subst. inv H4; eauto.
        { inv H5; eauto. contradiction H1.
          constructor 2. rewrite find_ghost_set_equiv. constructor 2; constructor. }
        { inv H4; eauto. contradiction H2.
          constructor 2. rewrite find_ghost_set_equiv. constructor 2; constructor. }
    + constructor; auto.
Qed.

Lemma insert_ghost_same_unique: forall x (v : val) tg g1 g2,
  In_ghost x tg -> sorted_ghost_tree tg ->
  unique_gname tg -> unique_gname (insert_ghost x v tg g1 g2).
Proof.
  induction tg; simpl; intros.
  - inv H.
  - inv H0; inv H1; inv H.
    + rewrite Z.ltb_irrefl. constructor; auto.
    + specialize (Hgtl _ H1); destruct (x <? k) eqn:E; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
    + specialize (Hltr _ H1); destruct (x <? k) eqn:E; try lia.
      destruct (k <? x) eqn:E2; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
Qed.

Lemma In_ghost_insert : forall x (v : val) k tg g1 g2, In_ghost k (insert_ghost x v tg g1 g2) -> x = k \/ In_ghost k tg.
Proof.
  induction tg; simpl; intros.
  - inv H; auto.
  - destruct (x <? k0) eqn: ?; [|destruct (k0 <? x) eqn: ?].
    * inv H.
      + right; apply InRoot_ghost; auto.
      + destruct (IHtg1 _ _ H1); auto.
        right. apply InLeft_ghost. auto.
      + right. apply InRight_ghost. auto.
    * inv H.
      + right. apply InRoot_ghost. auto.
      + right. apply InLeft_ghost. auto.
      + destruct (IHtg2 _ _ H1); auto.
        right. apply InRight_ghost. auto.
    * assert (k0 = x) by lia; subst.
      right; inv H.
      + apply InRoot_ghost. auto.
      + apply InLeft_ghost. auto.
      + apply InRight_ghost. auto.
Qed.

Lemma insert_ghost_sorted: forall x (v : val) tg g1 g2,
  sorted_ghost_tree tg -> sorted_ghost_tree (insert_ghost x v tg g1 g2).
Proof.
  induction tg; intros; simpl.
  - apply Sorted_Ghost_Tree; auto.
    unfold gt_ghost; inversion 1.
    unfold lt_ghost; inversion 1.
  - inv H. destruct (x <? k) eqn:E; [|destruct (k <? x) eqn:E2].
    + apply Sorted_Ghost_Tree; auto.
      unfold gt_ghost; intros. apply In_ghost_insert in H as [?|?]; auto; lia.
    + apply Sorted_Ghost_Tree; auto.
      unfold lt_ghost; intros. apply In_ghost_insert in H as [?|?]; auto; lia.
    + assert (k = x) by lia; subst.
      apply Sorted_Ghost_Tree; auto.
Qed.

Lemma tree_rep_insert: forall t g g_root g_in x v ,
  tree_rep g g_root t * in_tree g g_in |-- EX r, EX o, public_half g_in (r, Some o) *
  ((|==> (EX g1 g2:gname, (!!(o = None /\ key_in_range x r = true) && public_half g_in (r, Some (Some(x,v,g1,g2)))) -* tree_rep g g_root (<[x:=v]>t) * my_half g1 gsh1 (r.1, Finite_Integer x, Some (@None ghost_info)) * my_half g2 gsh1 (Finite_Integer x, r.2, Some (@None ghost_info)) *  in_tree g g_in * in_tree g g1 * in_tree g g2))%I
    && (|==> (ALL g1 g2:gname, ALL (v0:val), (!!(o = Some(x,v0,g1,g2) /\ (key_in_range x r = true)) &&  public_half g_in (r, Some (Some(x,v, g1,g2)))) -* tree_rep g g_root (<[x:=v]>t) * in_tree g g_in))%I
   && (public_half g_in (r, Some o) -* (tree_rep g g_root t * in_tree g g_in))).
Proof.
  intros.
  unfold tree_rep at 1. Intros tg.
  sep_apply node_exist_in_tree; Intros.
  rewrite -> (ghost_tree_insert tg g_root g_in x v) by auto.
  Intros r o. Exists r o. cancel.
  apply andp_right; [apply andp_right|].
  - erewrite update_ghost_ref. iIntros "(>H1 & [H2 _])". iDestruct "H1" as (g1 g2) "((((([(% & % & %) H1] & H3) & H4) & H5) & H6) & H7)".
    rewrite <- !both_halves_join. iDestruct "H1" as "(H1 & H1')". iDestruct "H3" as "(H3 & H3')". iModIntro. iExists g1. iExists g2. iIntros "([% %] & H')"; subst. iSpecialize ("H2" with "[%]"); first done.
    iSpecialize ("H2" $! g1 g2 with "[$H' $H1' $H3']").
    unfold tree_rep. rewrite !exp_sepcon1. iExists (insert_ghost x v tg g1 g2). iDestruct "H2" as "[% H2]".
    assert (~In_ghost x tg) as Hout by (eapply key_not_exist_in_tree; eauto).
    rewrite -> ghost_set_insert, ghost_set_insert2 by auto. iFrame. iSplit; auto.
      * iPureIntro; rewrite -> insert_tree_to_gmap by auto.
        repeat (split; auto).
        + rewrite -> find_ghost_set_equiv in *. intros Hcontra; inv Hcontra. inv H8; try contradiction.
          { inv H10. apply H5. constructor 2; constructor. }
          { inv H8. apply H6. constructor 2; constructor. }
        + apply insert_ghost_unique; auto.
          { intros Hcontra; contradiction H5. rewrite find_ghost_set_equiv. constructor 1; auto. }
          { intros Hcontra; contradiction H6. rewrite find_ghost_set_equiv. constructor 1; auto. }
        + apply insert_ghost_sorted; auto.
      * apply find_ghost_set_finite.
  - iIntros "((H1 & H2) & [H3 _]) !>". iIntros (g1 g2 v0) "[[% %] H]"; subst.
    iSpecialize ("H3" with "[%]"); first done. iSpecialize ("H3" $! g1 g2 with "[$H]"); first done.
    unfold tree_rep. rewrite !exp_sepcon1. iExists (insert_ghost x v tg g1 g2). iDestruct "H3" as "[% H3]". 
    rewrite -> ghost_set_insert_same, ghost_set_insert_same2 by auto. iFrame. iSplit; auto.
    iPureIntro; rewrite -> insert_tree_to_gmap by auto.
    repeat (split; auto).
    + apply insert_ghost_same_unique; auto.
    + apply insert_ghost_sorted; auto.
  - iIntros "((? & ?) & [_ H]) ?".
    unfold tree_rep.
    rewrite !exp_sepcon1; iExists tg; iFrame.
    iSplit; auto; iApply "H"; done.
Qed.

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

Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH gv: globals
  PRE  [  ]
    PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX v:val, EX lock:val, EX g:gname, EX g_root:gname,
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (mem_mgr gv; nodebox_rep g g_root lsh1 lock v;
         (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) v;
         malloc_token Ews (tptr t_struct_tree_t) v;
         tree_rep g g_root empty).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH lock: val, b: val, gv: globals, g: gname, g_root: gname, M: _
  PRE  [ tptr (tptr t_struct_tree_t) ]
       PROP ()
       PARAMS (b) GLOBALS (gv)
       SEP (mem_mgr gv; nodebox_rep g g_root lsh1 lock b;
              (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) b;
              malloc_token Ews (tptr t_struct_tree_t) b;
              tree_rep g g_root M)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH lock: val, sh : share, p: val, gv : globals, g: gname, g_root: gname
  PRE  [ tptr t_struct_tree_t ]
       PROP()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv;
            ltree g g_root lsh1 sh p lock)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH l: val, tl: val, x: Z, vx: val, tll: val,
       r: val, tr: val, y: Z, vy: val, mid: val, trr: val
  PRE  [tptr t_struct_tree_t, tptr t_struct_tree_t]
    PROP (is_pointer_or_null mid)
    PARAMS (l; r) GLOBALS ()
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tl l;
         field_at Ews (t_struct_tree_t) [StructField _t] tr r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, r))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (mid, trr))) tr)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tr l;
         field_at Ews (t_struct_tree_t) [StructField _t] tl r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, mid))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (r, trr))) tr).

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType (val *  share * val * Z * val * globals * gname * gname)) OBJ M INVS base.empty base.top
  WITH  b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_tree_t), tint, tptr tvoid ]
          PROP ( readable_share sh; Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v )
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root (<[x:=v]>M)).

Program Definition delete_spec :=
 DECLARE _delete
 ATOMIC TYPE (rmaps.ConstType (_ * _ * _ * _ * _ * _ * _))
         OBJ M INVS base.empty base.top
 WITH b, x, lock, gv, sh, g, g_root
 PRE  [ tptr (tptr t_struct_tree_t), tint]
    PROP (Int.min_signed <= x <= Int.max_signed; readable_share sh)
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root M)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep g g_root (base.delete x M)).

Time Program Definition pushdown_left_spec :=
 DECLARE _pushdown_left
 ATOMIC TYPE (rmaps.ConstType (val * val * val * share * Z * val * val * val * val * val * gname * gname * globals * range * gname * gname * gname)) OBJ M INVS base.empty base.top
 WITH p, tp, lockp, gsh,
       x, vx, locka, lockb, ta, tb,
       g, g_root, gv, r, g_del, ga, gb
  PRE [ tptr t_struct_tree_t ]
    PROP (Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) vx; key_in_range x r = true)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv;
         in_tree g g_del;
         my_half g_del gsh (r, Some (Some (x, vx, ga, gb)));
         field_at Ews t_struct_tree_t [StructField _t] tp p;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (ta, tb))) tp;
         ltree g g_del lsh2 gsh p lockp;
         ltree g ga lsh1 gsh1 ta locka;
         ltree g gb lsh1 gsh1 tb lockb;
         malloc_token Ews t_struct_tree tp;
         malloc_token Ews tlock lockp;
         malloc_token Ews t_struct_tree_t p) | (tree_rep g g_root M)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv) | (tree_rep g g_root (base.delete x M)).

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * globals * gname * gname))
         OBJ M INVS base.empty base.top
  WITH b, sh, lock, x, gv, g, g_root
  PRE [tptr (tptr t_struct_tree_t), tint]
    PROP (readable_share sh;
          Int.min_signed <= x <= Int.max_signed)
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) |
  (tree_rep g g_root M)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!! (ret = match M !! x with Some v => v | None => nullval end) && tree_rep g g_root M).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.*)

(*no freelock_spec, spawn_spec, freelock2_spec, release2_spec*)
Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
  (* acquire_spec; release_spec; makelock_spec; freelock_spec; *)
    surely_malloc_spec;
    treebox_new_spec; tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec ;
    (* spawn_spec; *) main_spec
  ]).

Lemma node_rep_saturate_local:
   forall r p g g_current, node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof.
  intros. rewrite node_rep_def. Intros tp. entailer!.
Qed.
Global Hint Resolve node_rep_saturate_local: saturate_local.


Lemma node_rep_valid_pointer:
  forall t g g_current p, node_rep p g g_current t |-- valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp. sep_apply field_at_valid_ptr0; auto. entailer!.
Qed.
Global Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_R_saturate_local:
   forall t p g_children g, tree_rep_R p t g_children g |-- !! is_pointer_or_null p.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec p nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec tp nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Global Hint Resolve tree_rep_R_valid_pointer : valid_pointer.


Lemma ltree_saturate_local:
  forall g g_root lsh gsh p lock, ltree g g_root lsh gsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Global Hint Resolve ltree_saturate_local: saturate_local.


Definition insert_inv (b: val) (lock: val) (sh: share) (x: Z) (v: val) (g_root: gname) gv (inv_names : invG) (Q : mpred) (g : gname) AS : environ -> mpred :=
(EX r : node_info, EX g_in : gname, EX lock_in : val, EX np : val, EX gsh : share,
PROP (key_in_range x (fst r) = true)
LOCAL (temp _l lock_in; temp _tgt np; temp _t b; temp _x (vint x); temp _value v; gvars gv)
SEP (nodebox_rep g g_root sh lock b;
  field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
  malloc_token Ews tlock lock_in;
  node_rep np g g_in r; my_half g_in gsh r;
 |> lock_inv lsh2 lock_in (node_lock_inv gsh g np g_in lock_in); AS; mem_mgr gv))%assert.

 Definition lookup_inv (b: val) (lock:val) (sh: share) (x: Z) gv (inv_names : invG)
           (Q : val -> mpred) (g g_root:gname) AS : environ -> mpred :=
  (EX tp: val, EX np: val, EX r : node_info, EX g_in : gname, EX lock_in : val, EX gsh : share,
   PROP (key_in_range x r.1 = true)
   LOCAL (temp _p tp; temp _l lock_in; temp _tgt np; temp _t b;
          temp _x (vint x); gvars gv)
   SEP (nodebox_rep g g_root sh lock b;
       field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np;
       |> lock_inv lsh2 lock_in (node_lock_inv gsh g np g_in lock_in);
       field_at Ews t_struct_tree_t [StructField _t] tp np;
       malloc_token Ews t_struct_tree_t np; in_tree g g_in;
       tree_rep_R tp r.1 r.2 g; my_half g_in gsh r; malloc_token Ews tlock lock_in;
       AS; mem_mgr gv))%assert.

Lemma tree_rep_R_nullval: forall t g_info g,
  tree_rep_R nullval t (g_info: option (option ghost_info)) g |-- !! (g_info = Some (@None ghost_info)).
Proof.
  intros.
  unfold tree_rep_R. simpl. entailer!.
Qed.
Global Hint Resolve tree_rep_R_nullval: saturate_local.

Lemma ghost_tree_rep_public_half_ramif: forall tg g_root r_root g_in,
    Ensembles.In (find_ghost_set tg g_root) g_in ->
    ghost_tree_rep tg g_root r_root |--
    EX r: node_info, !! (range_info_in_tree r r_root tg) &&
      (public_half g_in r * (public_half g_in r -* ghost_tree_rep tg g_root r_root)).
Proof.
  induction tg; intros; simpl in *.
  - inv H. Exists (r_root, Some (@None ghost_info)). apply andp_right.
    + apply prop_right. now constructor.
    + cancel. apply wand_refl_cancel_right.
  - destruct r_root as [l r]. inv H; inv H0.
    + specialize (IHtg1 _ (l, Finite_Integer k) _ H). sep_apply IHtg1.
      Intros r0. Exists r0. apply andp_right.
      * apply prop_right. now apply riit_left.
      * cancel. rewrite <- wand_sepcon_adjoint. cancel. apply wand_frame_elim''.
    + specialize (IHtg2 _ (Finite_Integer k, r) _ H). sep_apply IHtg2.
      Intros r0. Exists r0. apply andp_right.
      * apply prop_right. now apply riit_right.
      * cancel. rewrite <- wand_sepcon_adjoint. cancel. apply wand_frame_elim''.
    + Exists (l, r, Some (Some (k, v, g, g0))). apply andp_right.
      * apply prop_right. now apply riit_root.
      * cancel. rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma ghost_tree_rep_public_half_ramif2: forall tg g_root r_root g_in,
    Ensembles.In (find_ghost_set tg g_root) g_in ->
    ghost_tree_rep tg g_root r_root
    |--
    (EX r: range ,
           (public_half g_in (r, Some (@None ghost_info)) *
            (public_half g_in (r, Some (@None ghost_info)) -*
                         ghost_tree_rep tg g_root r_root))) ||
    (EX r: range, EX x: key, EX v: val, EX ga gb: gname,
     EX i1 i2: option ghost_info,
        ((public_half g_in (r, Some (Some (x, v, ga, gb))) *
          public_half ga ((r.1, Finite_Integer x), Some i1) *
          public_half gb ((Finite_Integer x, r.2), Some i2)) *
        ((public_half g_in (r, Some (Some (x, v, ga, gb))) *
          public_half ga ((r.1, Finite_Integer x), Some i1) *
          public_half gb ((Finite_Integer x, r.2), Some i2))
           -* ghost_tree_rep tg g_root r_root))).
Proof.
  induction tg; intros; simpl in *.
  - apply orp_right1. inv H. Exists r_root. cancel. apply wand_refl_cancel_right.
  - destruct r_root as [lroot rroot]. inv H; inv H0.
    + specialize (IHtg1 _ (lroot, Finite_Integer k) _ H). sep_apply IHtg1. clear.
      rewrite distrib_orp_sepcon. apply orp_derives.
      * Intros r. Exists r. cancel. rewrite <- wand_sepcon_adjoint.
        cancel. apply wand_frame_elim''.
      * Intros r x v0 ga gb i1 i2. Exists r x v0 ga gb i1 i2. cancel.
        rewrite <- wand_sepcon_adjoint. cancel.
        rewrite !sepcon_assoc. apply wand_frame_elim''.
    + specialize (IHtg2 _ (Finite_Integer k, rroot) _ H). sep_apply IHtg2. clear.
      rewrite distrib_orp_sepcon. apply orp_derives.
      * Intros r. Exists r. cancel. rewrite <- wand_sepcon_adjoint.
        cancel. apply wand_frame_elim''.
      * Intros r x v0 ga gb i1 i2. Exists r x v0 ga gb i1 i2. cancel.
        rewrite <- wand_sepcon_adjoint. cancel.
        rewrite !sepcon_assoc. apply wand_frame_elim''.
    + apply orp_right2. Exists (lroot, rroot) k v g g0. clear.
      destruct tg1, tg2; simpl.
      * Exists (@None ghost_info) (@None ghost_info). cancel.
        apply wand_refl_cancel_right.
      * Exists (@None ghost_info) (Some (k0, v0, g1, g2)). cancel.
        rewrite <- wand_sepcon_adjoint. cancel.
      * Exists (Some (k0, v0, g1, g2)) (@None ghost_info). cancel.
        rewrite <- wand_sepcon_adjoint. cancel.
      * Exists (Some (k0, v0, g1, g2)) (Some (k1, v1, g3, g4)). cancel.
        rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma range_info_in_tree_In: forall tg x v ga gb rn r_root,
    range_info_in_tree (rn, Some (Some (x, v, ga, gb))) r_root tg ->
    In_ghost x tg.
Proof.
  induction tg; intros.
  { inv H. inv H0. }
  inv H.
  - inv H1. now constructor 1.
  - constructor 2. eapply IHtg1; eauto.
  - constructor 3. eapply IHtg2; eauto.
Qed.

Lemma range_info_incl: forall tg o rn r_root,
  range_info_in_tree (rn, o) r_root tg -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg ->
  range_incl rn r_root = true.
Proof.
  induction 1; intros.
  - inv H. apply range_incl_refl.
  - inv H. apply range_incl_refl.
  - apply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); auto.
    inv H1.
    unfold range_incl in *; destruct rn, range; simpl in *.
    apply andb_prop in IHrange_info_in_tree as [->]; auto.
    eapply less_than_equal_trans; first eassumption.
    apply less_than_to_less_than_equal.
    apply andb_prop in H0 as [_ ?]; auto.
  - apply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); auto.
    inv H1.
    unfold range_incl in *; destruct rn, range; simpl in *.
    apply andb_prop in IHrange_info_in_tree as [? ->]; auto.
    rewrite andb_true_r.
    eapply less_than_equal_trans; last eassumption.
    apply less_than_to_less_than_equal.
    apply andb_prop in H0 as [? _]; auto.
Qed.

Lemma range_info_in_gmap: forall x v ga gb tg rn r_root,
    sorted_ghost_tree tg ->
    range_info_in_tree (rn, Some (Some (x, v, ga, gb))) r_root tg ->
    tree_to_gmap tg !! x = Some v.
Proof.
  induction tg; intros; simpl.
  { inv H0. inv H1. }
  inv H. inv H0.
  - inv H1. apply lookup_insert.
  - exploit Hgtl. { eapply range_info_in_tree_In; eauto. }
    intros; rewrite -> lookup_insert_ne by lia.
    eapply lookup_union_Some_l, IHtg1; eauto.
  - exploit Hltr. { eapply range_info_in_tree_In; eauto. }
    intros; rewrite -> lookup_insert_ne by lia.
    rewrite lookup_union_r.
    + eapply IHtg2; eauto.
    + destruct (eq_dec (tree_to_gmap tg1 !! x) None); auto.
      apply In_tree_to_gmap, Hgtl in n; lia.
Qed.

Lemma range_info_not_in_gmap: forall tg x rn r_root,
    sorted_ghost_tree tg -> key_in_range x rn = true ->
    keys_in_range_ghost tg r_root ->
    range_info_in_tree (rn, Some None) r_root tg -> tree_to_gmap tg !! x = None.
Proof.
  induction tg; intros; simpl.
  { apply lookup_empty. }
  apply keys_in_range_ghost_subtrees in H1 as (? & ? & ?); auto.
  inv H; inv H2.
  - inv H5.
  - exploit range_info_incl; eauto; intros Hrange.
    pose proof (key_in_range_incl _ _ _ H0 Hrange) as Hx.
    apply andb_prop in Hx as []; simpl in *.
    rewrite -> lookup_insert_ne by lia.
    rewrite lookup_union_None; split.
    + eapply IHtg1; eauto.
    + destruct (eq_dec (tree_to_gmap tg2 !! x) None); auto.
      apply In_tree_to_gmap, Hltr in n; lia.
  - exploit range_info_incl; eauto; intros Hrange.
    pose proof (key_in_range_incl _ _ _ H0 Hrange) as Hx.
    apply andb_prop in Hx as []; simpl in *.
    rewrite -> lookup_insert_ne by lia.
    rewrite lookup_union_None; split.
    + destruct (eq_dec (tree_to_gmap tg1 !! x) None); auto.
      apply In_tree_to_gmap, Hgtl in n; lia.
    + eapply IHtg2; eauto.
Qed.

Lemma range_incl_tree_rep_R: forall tp r1 r2 g_info g,
    range_incl r1 r2 = true ->
    tree_rep_R tp r1 g_info g |-- tree_rep_R tp r2 g_info g.
Proof.
  intros. unfold tree_rep_R. if_tac. 1: cancel. Intros ga gb x v pa pb locka lockb.
  Exists ga gb x v pa pb locka lockb. entailer!.
  destruct (key_in_range x r1) eqn: ?. 2: easy.
  eapply key_in_range_incl; eauto.
Qed.

Lemma node_info_incl: forall a b c,
    @sepalg.join node_info (@Join_G node_ghost) a b c ->
    range_incl (fst a) (fst c) = true /\ match a.2 with Some x => c.2 = Some x | _ => True end.
Proof.
  intros.
  destruct (range_incl_join _ _ _ H); split; auto.
  destruct a, c, H; simpl in *.
  inv H2; auto.
  - destruct g2; auto.
  - inv H5.
Qed.

Lemma node_info_incl': forall sh a c,
    (if eq_dec sh Tsh then a = c else exists b, @sepalg.join node_info (@Join_G node_ghost) a b c) ->
    range_incl (fst a) (fst c) = true /\ match a.2 with Some x => c.2 = Some x | _ => True end.
Proof.
  intros; if_tac in H.
  { subst a; destruct c.2; auto. }
  destruct H; eapply node_info_incl; eauto.
Qed.

Lemma public_sub : forall g sh a b,
  my_half g sh a * public_half g b |-- !! (range_incl (fst a) (fst b) = true /\ match a.2 with Some x => b.2 = Some x | _ => True end).
Proof.
  intros.
  iIntros "(my1 & my2 & pub)"; iPoseProof (own_valid_2(RA := ref_PCM _) with "[$my1 $pub]") as "%"; iPureIntro.
  destruct H as ((?, ?) & [J H] & ?); simpl in *.
  inv H; destruct g0 as [(?, ?)|]; try contradiction.
  inv J; destruct H0 as (_ & ? & H); hnf in H.
  destruct x as [(?, ?)|].
  destruct H as (? & ? & ? & ?); eapply node_info_incl; eauto.
  { inv H; rewrite range_incl_refl; split; auto.
    destruct a.2; auto. }
Qed.

Lemma in_tree_left_range:
  ∀ (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (x x0: Z) (g g_root : gname)
    (inv_names : invG) (v: val) (g_in ga gb: gname) (gsh: share) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> x < x0 ->
    atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
                 b Q * my_half g_in gsh r * in_tree g g_in * my_half ga gsh1 a
    |-- atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
    b Q * my_half g_in gsh r *
    (EX ba, !! (less_than_equal ba r.1.1 = true /\
                range_incl a.1 (ba, Finite_Integer x0) = true) &&
            (in_tree g g_in * my_half ga gsh1 (ba, Finite_Integer x0, a.2))).
Proof.
  intros. rewrite sepcon_assoc. apply sync_rollback. intros t.
  unfold tree_rep at 1. Intros tg.
  sep_apply node_exist_in_tree; Intros.
  sep_apply (ghost_tree_rep_public_half_ramif2 _ _ (Neg_Infinity, Pos_Infinity) _ H6).
  rewrite distrib_orp_sepcon. apply orp_left.
  - Intros r0. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (@None ghost_info)). unfold public_half'; cancel. apply imp_andp_adjoint. Intros.
    apply node_info_incl' in H7 as [? Heq].
    rewrite H0 in Heq; inv Heq.
  - Intros r0 x1 v0 ga0 gb0 i1 i2.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (Some (x1, v0, ga0, gb0))). unfold public_half'; cancel. apply imp_andp_adjoint.
    Intros. apply node_info_incl' in H7 as [? Heq].
    destruct r; simpl fst in *; simpl snd in *; subst.
    inv Heq.
    rewrite <- wand_sepcon_adjoint.
    sep_apply (public_part_update ga gsh1 a (r0.1, Finite_Integer x0, Some i1)
                                  (r0.1, Finite_Integer x0, a.2)
                                  (r0.1, Finite_Integer x0, Some i1)).
    + intros. destruct H0. split; auto; simpl.
      hnf in H0; hnf.
      symmetry; rewrite merge_comm; eapply merge_again.
      symmetry; rewrite merge_comm; eauto.
    + Intros. rewrite -> if_false in H0 by auto.
      eapply derives_trans; [apply ghost_seplog.bupd_frame_r|].
      apply ghost_seplog.bupd_mono.
      Exists r0.1. entailer!.
      * destruct H0 as [? H0]; apply range_incl_join in H0 as []; split; auto.
        simpl in H7. destruct g0, r0; apply andb_prop in H7 as []; auto.
      * unfold tree_rep. Exists tg. entailer!.
        iIntros "[[[[[[? ?] ?] ?] ?] H] ?]".
        iApply "H"; iFrame.
Qed.

Lemma in_tree_right_range:
  ∀ (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (x x0: Z) (g g_root : gname)
    (inv_names : invG) (v: val) (g_in ga gb: gname) (gsh: share) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> x0 < x ->
    atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
                 b Q * my_half g_in gsh r * in_tree g g_in * my_half gb gsh1 a
    |-- atomic_shift (λ M, tree_rep g g_root M) ∅ ⊤
    b Q * my_half g_in gsh r *
    (EX ta, !! (less_than_equal r.1.2 ta = true /\
                range_incl a.1 (Finite_Integer x0, ta) = true) &&
            (in_tree g g_in * my_half gb gsh1 (Finite_Integer x0, ta, a.2))).
Proof.
  intros. rewrite sepcon_assoc. apply sync_rollback. intros t.
  unfold tree_rep at 1. Intros tg.
  sep_apply node_exist_in_tree; Intros.
  sep_apply (ghost_tree_rep_public_half_ramif2 _ _ (Neg_Infinity, Pos_Infinity) _ H6).
  rewrite distrib_orp_sepcon. apply orp_left.
  - Intros r0. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (@None ghost_info)). unfold public_half'; cancel. apply imp_andp_adjoint. Intros.
    apply node_info_incl' in H7 as [? Heq].
    rewrite H0 in Heq; inv Heq.
  - Intros r0 x1 v0 ga0 gb0 i1 i2.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (Some (x1, v0, ga0, gb0))). unfold public_half'; cancel. apply imp_andp_adjoint.
    Intros. apply node_info_incl' in H7 as [? Heq].
    destruct r; simpl fst in *; simpl snd in *; subst.
    inv Heq.
    rewrite <- wand_sepcon_adjoint.
    sep_apply (public_part_update gb gsh1 a (Finite_Integer x0, r0.2, Some i2)
                                  (Finite_Integer x0, r0.2, a.2)
                                  (Finite_Integer x0, r0.2, Some i2)).
    + intros. destruct H0. split; auto; simpl.
      hnf in H0; hnf.
      symmetry; rewrite merge_comm; eapply merge_again.
      symmetry; rewrite merge_comm; eauto.
    + Intros. rewrite -> if_false in H0 by auto.
      eapply derives_trans; [apply ghost_seplog.bupd_frame_r|].
      apply ghost_seplog.bupd_mono.
      Exists r0.2. entailer!.
      * destruct H0 as [? H0]; apply range_incl_join in H0 as []; auto.
        simpl in H7. destruct g0, r0; apply andb_prop in H7 as []; auto.
      * unfold tree_rep. Exists tg. entailer!.
        iIntros "[[[[[[? ?] ?] ?] ?] H] ?]".
        iApply "H"; iFrame.
Qed.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, node_lock_inv (fst (Share.split gsh1)) g np g_root lock). (* _acquire(_l); *)
  unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.
  Intros a. destruct a as (p, o). rewrite node_rep_def. Intros tp.
  forward. (* _p = (_tgt -> _t); *) simpl fst. simpl snd.
  set (AS := atomic_shift _ _ _ _ _).
  forward_while (lookup_inv b lock sh x gv inv_names Q g g_root AS).
  (* while (_p != (tptr tvoid) (0)) *)
  - (* current status implies lookup_inv *)
    unfold lookup_inv. Exists tp np (Neg_Infinity, Pos_Infinity, o) g_root lock (fst (Share.split gsh1)).
    sep_apply (my_half_range_inf g_root (Share.split gsh1).1 (Share.split gsh1).2 p (Neg_Infinity, Pos_Infinity)).
    entailer!.
    sep_apply (range_incl_tree_rep_R tp _ _ o g (range_incl_infty p)).
    unfold nodebox_rep. Exists np. cancel. unfold ltree, node_lock_inv. entailer!.
  - (* type check *) entailer!.
  - (* loop body *)
    unfold tree_rep_R. rewrite if_false; auto. Intros ga gb x0 v pa pb locka lockb.
    forward. (* _y = (_p -> _key); *)
    forward_if. (* if (_x < _y) { *)
    + forward. (* _tgt = (_p -> _left); *)
      forward. (* _l_old = _l; *) unfold ltree at 1. Intros.
      forward. (* _l = (_tgt -> _lock); *)
      forward_call (locka, lsh1, node_lock_inv gsh1 g pa ga locka). (* _acquire(_l); *)
      unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
      fold (node_lock_inv gsh1 g pa ga locka). unfold node_lock_inv_pred, sync_inv.
      Intros a. rewrite node_rep_def. Intros tpa.
      forward. (* _p = (_tgt -> _t); *)
      gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half ga _ _); unfold AS.
      set (post := fun M ret => fold_right_sepcon [_]).
      sep_apply (in_tree_left_range val post Q x x0 g g_root inv_names v g_in ga gb). Intros ba.
      forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in,
                    node_lock_inv gsh g np0 g_in lock_in). (* _release2(_l_old); *)
      * lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
        Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
        rewrite -> if_false by auto. Exists ga gb x0 v pa pb locka lockb; unfold ltree; entailer!.
        rewrite !later_sepcon; cancel.
      * destruct a as [rangea a]. simpl fst in *. simpl snd in *.
        Exists (((((tpa, pa), (ba, Finite_Integer x0, a)), ga), locka), gsh1).
        simpl fst. simpl snd. sep_apply (range_incl_tree_rep_R tpa _ _ a g H9).
        unfold AS, post; entailer!.
        simpl. rewrite andb_true_iff. clear -H1 H6 H8. split; [|lia].
        destruct r, g. simpl fst in *.
        eapply less_than_equal_less_than_trans; [eauto|].
        unfold key_in_range in *. apply andb_prop in H1 as []; auto.
    + forward_if. (* if (_y < _x) { *)
      * forward. (* _tgt = (_p -> _right); *)
        forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
        forward. (* _l = (_tgt -> _lock); *)
        forward_call (lockb, lsh1, node_lock_inv gsh1 g pb gb lockb). (* _acquire(_l); *)
        unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
        fold (node_lock_inv gsh1 g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
        Intros a. rewrite node_rep_def. Intros tpb.
        forward. (* _p = (_tgt -> _t); *)
        gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half gb _ _); unfold AS.
        set (post := fun M ret => fold_right_sepcon [_]).
        sep_apply (in_tree_right_range val post Q x x0 g g_root inv_names v g_in ga gb). Intros ta.
        forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in,
                      node_lock_inv gsh g np0 g_in lock_in). (* _release2(_l_old__1); *)
        -- lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
           Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
           rewrite -> if_false by auto. Exists ga gb x0 v pa pb locka lockb; unfold ltree; entailer!.
           rewrite !later_sepcon; cancel.
        -- destruct a as [rangea a]. simpl fst in *. simpl snd in *.
        Exists (((((tpb, pb), (Finite_Integer x0, ta, a)), gb), lockb), gsh1).
        simpl fst. simpl snd. sep_apply (range_incl_tree_rep_R tpb _ _ a g H10).
        unfold AS, post; entailer!.
        simpl. rewrite andb_true_iff. clear -H1 H7 H9. split; [lia|].
        destruct r, g. simpl fst in *.
        eapply less_than_less_than_equal_trans; [|eauto].
        unfold key_in_range in *. apply andb_prop in H1 as []; auto.
      * forward. (* _v = (_p -> _value); *)
        assert (x0 = x) by lia. subst x0. clear H6 H7.
        gather_SEP AS (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (EX y, Q y * (!!(y = v) && (in_tree g g_in * my_half g_in gsh r))). {
          go_lower. apply sync_commit_same. intro t. unfold tree_rep at 1. Intros tg.
          sep_apply node_exist_in_tree; Intros.
          sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H10). Intros r0.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. unfold public_half'; cancel.
          apply imp_andp_adjoint. Intros. apply node_info_incl' in H12 as [].
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists v; entailer!.
          simpl; entailer!.
          - destruct r as [range r2], r0 as [range0 r0]. simpl in *; subst.
            erewrite range_info_in_gmap; eauto.
          - iIntros "[[[? H] ?] ?]".
            unfold tree_rep. iExists tg. iFrame; iSplit; auto.
            iApply "H"; iFrame. } Intros y. subst y.
        forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in,
                      node_lock_inv gsh g np0 g_in lock_in). (* _release2(_l); *)
        -- lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
           fold (node_lock_inv gsh g np0 g_in lock_in). unfold node_lock_inv_pred.
           unfold sync_inv. Exists r. rewrite node_rep_def. Exists tp0. cancel.
           unfold tree_rep_R. rewrite -> if_false by auto.
           Exists ga gb x v pa pb locka lockb; entailer!.
        -- forward. Exists v. entailer!.
  - subst tp0. unfold tree_rep_R. simpl. Intros.
    gather_SEP AS (my_half g_in _ _) (in_tree g _).
    viewshift_SEP 0 (EX y, Q y * (!! (y = nullval) && (in_tree g g_in * my_half g_in gsh r))). {
      go_lower. apply sync_commit_same. intro t. unfold tree_rep at 1. Intros tg.
      sep_apply node_exist_in_tree; Intros.
      sep_apply (ghost_tree_rep_public_half_ramif _ _ (Neg_Infinity, Pos_Infinity) _ H7). Intros r0.
      eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. unfold public_half'; cancel.
      apply imp_andp_adjoint. Intros. apply node_info_incl' in H9 as [].
      eapply derives_trans; [|apply ghost_seplog.bupd_intro].
      rewrite <- wand_sepcon_adjoint.
      eapply derives_trans; [|apply ghost_seplog.bupd_intro].
      Exists nullval; simpl; entailer!.
      - destruct r as [range r2], r0 as [rg ?]. simpl in *; subst.
        erewrite range_info_not_in_gmap with (rn := rg)(r_root := (Neg_Infinity, Pos_Infinity)); eauto 1.
        eapply key_in_range_incl; eauto.
      - unfold tree_rep. Exists tg. entailer!. iIntros "[[? H] ?]"; iApply "H"; iFrame. } Intros y. subst y.
    forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in,
                  node_lock_inv gsh g np0 g_in lock_in). (* _release2(_l); *)
    + lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
      fold (node_lock_inv gsh g np0 g_in lock_in). unfold node_lock_inv_pred.
      unfold sync_inv. Exists r. rewrite node_rep_def. Exists nullval.
      unfold tree_rep_R. simpl. entailer!.
    + forward. Exists nullval. entailer!.
Qed.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv).
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv).
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (tarray (tptr tvoid) 2, gv).
  { vm_compute. split; intro; easy. }
  Intros l. (* lock_t *l *)
  ghost_alloc (both_halves (Neg_Infinity, Pos_Infinity, Some (@None ghost_info))).
  { apply @part_ref_valid. }
  Intros g_root'. rewrite <- general_locks.both_halves_join.
  ghost_alloc (ghost_part_ref (P := set_PCM) Tsh (Ensembles.Singleton g_root') (find_ghost_set E_ghost g_root')).
  { apply @part_ref_valid. }
  Intros g'.
  Local Typeclasses eauto := 1. (* Improve forward_call speed *)
  destruct (Share.split gsh1) as (sh1, sh2) eqn: Hsplit.
  pose proof (Share.split_nontrivial _ _ _ Hsplit) as Hcontra.
  Time forward_call (l, Ews, node_lock_inv sh1 g' newt g_root' l).
  Local Typeclasses eauto := 10. (* Restore *)
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
  forward_call (l, lsh2, node_lock_inv_pred sh1 g' newt g_root' l, node_lock_inv sh1 g' newt g_root' l).
  { lock_props.
    setoid_rewrite node_lock_inv_def at 3.
    Exists (Neg_Infinity, Pos_Infinity, Some (@None ghost_info)).
    unfold_data_at (data_at Ews t_struct_tree_t _ _).
    rewrite node_rep_def. Exists (vint 0).
    erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
    cancel. simpl.
    rewrite <- ghost_part_ref_join.
    unfold in_tree; Exists Tsh.
    assert (sepalg.join(Join := @Join_G node_ghost) (Neg_Infinity, Pos_Infinity, Some None) (Neg_Infinity, Pos_Infinity, None)
      (Neg_Infinity, Pos_Infinity, Some None)).
    { hnf. simpl. split.
      + hnf. now simpl.
      + constructor. }
    rewrite <- (my_half_join gsh1 gsh2 Tsh
                  ((Neg_Infinity, Pos_Infinity, Some None): node_info)
                  (Neg_Infinity, Pos_Infinity, @None (option ghost_info))); auto.
    rewrite <- (my_half_join sh1 sh2 gsh1
                  ((Neg_Infinity, Pos_Infinity, Some None): node_info)
                  (Neg_Infinity, Pos_Infinity, @None (option ghost_info))); auto.
    cancel. unfold tree_rep_R; simpl. entailer!.
    apply split_join; auto. }
  forward.
  unfold nodebox_rep. unfold ltree.
  Exists p l g' g_root'. Exists newt. entailer!.
  erewrite <- data_at_share_join by eauto; cancel.
  unfold tree_rep. unfold ghost_ref.
  Exists (E_ghost : @ghost_tree val).
  rewrite Hsplit; simpl; entailer!.
  { split; constructor. }
  unfold public_half; cancel.
Qed.

Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  unfold ltree; Intros.
  forward.
  forward_call (lock, lsh1, node_lock_inv sh g p g_root lock).
  Local Typeclasses eauto := 5. (* For some reason 5 is faster than 4 and 6 is slower than 5 *)
  Time setoid_rewrite node_lock_inv_def at 2. Intros a; destruct a as (range, g_info).
  rewrite node_rep_def; Intros tp; simpl.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _p tp; temp _l lock; gvars gv; temp _tgp p)
    SEP (lock_inv lsh1 lock (node_lock_inv sh g p g_root lock);
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        malloc_token Ews t_struct_tree_t p; in_tree g g_root;
        my_half g_root sh (range, g_info);
        field_at lsh2 t_struct_tree_t [StructField _lock] lock p;
        malloc_token Ews tlock lock;
        lock_inv lsh2 lock (node_lock_inv sh g p g_root lock);
        mem_mgr gv; field_at lsh1 t_struct_tree_t [StructField _lock] lock p)).
  unfold tree_rep_R; simpl.
  { rewrite -> if_false by auto.
    Intros ga gb x v pa pb locka lockb; clear H1.
    forward. (* p->left *)
    forward. (* p->right *)
    forward_call (t_struct_tree, tp, gv).
    { rewrite -> if_false by auto; cancel. }
    forward_call (locka, gsh1, pa, gv, g, ga). (* tree_free(pa) *)
    forward_call (lockb, gsh1, pb, gv, g, gb). (* tree_free(pb) *)
    entailer!. }
  { forward.
    entailer!.
    unfold tree_rep_R.
    rewrite -> if_true by auto; entailer!. }
  forward_call (lock, Ews, lsh2, node_lock_inv_pred sh g p g_root lock, node_lock_inv sh g p g_root lock).
  { lock_props.
    rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
    entailer!. }
  forward_call (tlock, lock, gv).
  { if_tac; entailer!. }
  gather_SEP (in_tree _ _) (my_half _ _ _).
  viewshift_SEP 0 (emp).
  { go_lower. unfold in_tree; Intros sh'; iIntros "[H1 H2]".
    iMod (own_dealloc with "H1"); iMod (own_dealloc with "H2"); eauto. }
  forward_call (t_struct_tree_t, p, gv).
  { if_tac; entailer!.
    unfold_data_at_ p.
    unfold_data_at (data_at Ews t_struct_tree_t _ p).
    rewrite <- (field_at_share_join lsh2 lsh1 Ews t_struct_tree_t [StructField _lock] _ p). cancel. apply sepalg.join_comm. eauto. }
    entailer!.
Qed.

Lemma ghost_tree_rep_dealloc : forall tg g_root n1 n2,
  ghost_tree_rep tg g_root (n1, n2) |-- (|==> emp)%I.
Proof.
  induction tg; simpl; intros.
  { iIntros "[H1 H2]"; iMod (own_dealloc with "H1"); iMod (own_dealloc with "H2"); eauto. }
  { iIntros "[[[H1 H2] HL] HR]".
    iMod (own_dealloc with "H1"); iMod (own_dealloc with "H2").
    iMod (IHtg1 with "HL") as "_"; iMod (IHtg2 with "HR") as "_"; eauto. }
Qed.

Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward.
  forward_call (lock, fst (Share.split gsh1), np, gv, g, g_root).
  gather_SEP (tree_rep _ _ _).
  viewshift_SEP 0 emp. {
    go_lower.
    unfold tree_rep. Intros tg.
    iIntros "[H1 H2]".
    iMod (ghost_tree_rep_dealloc with "H1"); iMod (own_dealloc with "H2"); auto.
  }
  gather_SEP (my_half _ _ _).
  viewshift_SEP 0 emp. {
    go_lower. iIntros "H". iMod (own_dealloc with "H"); auto. }
  forward_call (tptr t_struct_tree_t, b, gv).
  { destruct (eq_dec b nullval).
    { entailer!. }
    { erewrite <- (data_at__share_join _ _ Ews) by eauto; entailer!. } }
  entailer!.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  { entailer!. }
Qed.

Ltac logic_to_iris :=
  match goal with |-context[(|==> ?P)%logic] => change ((|==> P)%logic) with ((|==> P)%I) end.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree .
  Intros np.
  forward.
  forward.
  forward_call (lock, sh, (node_lock_inv (fst (Share.split gsh1)) g np g_root lock)).
  set (AS := atomic_shift _ _ _ _ _).
  forward_loop (insert_inv b lock sh x v g_root gv inv_names Q g AS).
  { (* Precondition *)
    unfold insert_inv.
    unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. unfold nodebox_rep, ltree. Intro r. destruct r as [p o].
    sep_apply (my_half_range_inf g_root (Share.split gsh1).1 (Share.split gsh1).2 p (Neg_Infinity, Pos_Infinity)).
    Exists (Neg_Infinity, Pos_Infinity, o) g_root lock np (fst (Share.split gsh1)). Exists np; entailer!.
    rewrite node_rep_def. Intros tp. unfold node_lock_inv. rewrite node_rep_def. Exists tp. entailer!. sep_apply ( range_incl_tree_rep_R tp p (Neg_Infinity, Pos_Infinity) o g).
    apply range_incl_infty. auto. }
  (* Loop body *)
  unfold insert_inv.
  Intros r g_in lock_in np0.
  rewrite node_rep_def.
  Intros gsh tp.
  forward. (*p=tgt->t*)
  forward_if.
  + (* then clause *)
    subst tp.
    unfold tree_rep_R. simpl. Intros.
    forward_call (t_struct_tree_t, gv).
    Intros p1'.
    forward_call (t_struct_tree_t, gv).
    Intros p2'.
    forward. (* p1->t=NULL *)
    assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer!.
    simpl.
    forward. (* p1->t=NULL *)
    assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer!.
    simpl.
    forward_call (tlock, gv).
    { simpl. rewrite Z.max_r. repeat (split; auto); rep_lia. rep_lia. }
    Intros l1.
    unfold tlock.
    destruct r as [p o].
    destruct p.
    simpl in H3; subst.
    gather_SEP AS (my_half g_in _  _)  (in_tree g  _).
    viewshift_SEP 0 (Q  * (EX g1 g2:gname, EX n1 n2:number, (!!(key_in_range x (n1,n2) = true) && my_half g_in gsh (n1, n2, Some (Some(x,v,g1,g2))) * in_tree g g_in *
      my_half g1 gsh1 (n1, Finite_Integer x, Some (@None ghost_info)) * my_half g2 gsh1 (Finite_Integer x, n2, Some (@None ghost_info)) * in_tree g g1 * in_tree g g2))).
    {  go_lower.
        eapply sync_commit_gen1.
        intros. iIntros "[H1 H2]".
        iModIntro. iPoseProof (tree_rep_insert with "[$H1 $H2]") as "Hadd". iDestruct "Hadd" as (r o0) "([Hmy H1] & H2)".
        iExists (r, Some o0). iFrame. iDestruct "H2" as "[[Hnew _] _]".  iIntros "H"; iDestruct "H" as %Hsub. iMod "Hnew". iDestruct "Hnew" as (g1 g2) "H". iModIntro. iExists (r, Some (Some(x,v,g1,g2))).
        iExists (r, Some (Some (x, v, g1, g2))).
        apply node_info_incl' in Hsub as [? Heq]; simpl snd in *; inv Heq.
        logic_to_iris. iSplit.
        { iPureIntro. intros ? Hincl.  destruct b0 as ((n3, n4), i).
           hnf. simpl. destruct (range_incl_join _ _ _ Hincl).
           simpl in *; subst. split. { symmetry; rewrite merge_comm; apply merge_range_incl'; auto. }
           destruct Hincl as [_ Hincl]; simpl in Hincl. inv Hincl; try constructor. inv H11. }
         iIntros "(H1 & H2)". instantiate (1 := x). instantiate (1:= v).  iSpecialize ("H" with "[$H2 $Hmy]"). iSplit; auto.
         { iPureIntro. split; auto.
           eapply key_in_range_incl; eassumption. }
         iDestruct "H" as "(((((? & ?) & ?) & ?) & ?) & ?)".
         iModIntro. rewrite exp_sepcon1; iExists tt.
         rewrite !exp_sepcon2; iExists g1.
         rewrite !exp_sepcon2; iExists g2.
         rewrite !exp_sepcon2; iExists r.1.
         rewrite !exp_sepcon2; iExists r.2; destruct r; iFrame.
         iPureIntro; split; auto.
         eapply key_in_range_incl; eassumption. }
    Intros g1 g2 n1 n2.
    Typeclasses eauto:= 2.
    forward_call (l1, Ews, node_lock_inv gsh1 g p1' g1 l1).
    Intros.
    forward. (*p1->lock = l1*)
    rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
    Typeclasses eauto:= 6.
    forward_call (l1, lsh2, node_lock_inv_pred gsh1 g p1' g1 l1, node_lock_inv gsh1 g p1' g1 l1).
    { lock_props.
      unfold node_lock_inv at 4. rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (n1, Finite_Integer x, Some (@None ghost_info)).
      rewrite node_rep_def . Exists nullval.
      unfold_data_at (data_at _ _ _ p1'). erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }
    forward_call (tlock, gv).
    { simpl.  rewrite Z.max_r. repeat (split; auto); rep_lia. rep_lia. }
    Intros l2.
    forward_call (l2, Ews, (node_lock_inv gsh1 g p2' g2 l2)).
    forward. (*p2->lock = l2*)
    rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
    forward_call (l2, lsh2, node_lock_inv_pred gsh1 g p2' g2 l2, node_lock_inv gsh1 g p2' g2 l2).
    { lock_props.
      unfold node_lock_inv at 5. rewrite selflock_eq .  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (Finite_Integer x,n2,Some (@None ghost_info)).
      rewrite node_rep_def . Exists nullval.
      unfold_data_at (data_at _ _ _ p2'). erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }
    forward_call (t_struct_tree, gv).
    Intros p'.
    forward. (* tgt->t=p; *)
    forward. (* p->key=x; *)
    forward. (* p->value=value; *)
    forward. (* p->left=NULL; *)
    forward. (* p->right=NULL; *)
    forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in, node_lock_inv gsh g np0 g_in lock_in).
    { lock_props.
      unfold node_lock_inv at 4.  rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists (n1, n2, Some (Some(x,v,g1,g2))).
      rewrite node_rep_def. unfold node_lock_inv. Exists p'; cancel. unfold tree_rep_R. assert_PROP (p' <> nullval) by entailer!. rewrite -> if_false by auto.
      Exists g1 g2 x v p1' p2' l1 l2. unfold node_lock_inv. unfold ltree. entailer!.
      rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later]. unfold node_lock_inv. entailer!.
    }
    forward. entailer!.   (* return; *)
  + (* else clause *)
    unfold tree_rep_R. rewrite -> if_false by auto.
    Intros ga gb x0 v0 pa pb locka lockb .
    forward. (* y=p->key; *)
    forward_if; [ | forward_if ].
    - (* Inner if clause: x<k *)
      forward.
      forward.
      unfold_data_at (data_at _ _ _ tp).
      unfold ltree at 1; Intros.
      forward.
      forward_call (locka, lsh1, node_lock_inv gsh1 g pa ga locka).
      Intros.
      unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Intros a.
      rewrite node_rep_def. Intros tp1. gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half ga _ _); unfold AS.
      sep_apply (in_tree_left_range () (λ M (_ : ()), tree_rep g g_root (<[x:=v]>M) * emp)
          (λ _ : (), Q) x x0 g g_root inv_names v0  g_in ga gb). Intros ba.
      forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in, node_lock_inv gsh g np0 g_in lock_in).
      { lock_props.
        unfold node_lock_inv at 3. fold (node_lock_inv gsh1 g pa ga locka). rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists r.
        rewrite node_rep_def. Exists tp; cancel. unfold tree_rep_R at 2. rewrite -> if_false by auto.
        Exists ga gb x0 v0 pa pb locka lockb. unfold ltree at 2; entailer!.
        repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp). entailer!.
      }
      Exists (ba, Finite_Integer x0, a.2) ga locka pa gsh1. unfold node_lock_inv. rewrite node_rep_def. Exists tp1.
      unfold AS; entailer!.
      { unfold key_in_range in *. apply andb_true_intro. split; [|simpl; lia]. destruct r as ((?, ?), ?). apply andb_prop in H2 as []. eapply less_than_equal_less_than_trans; eauto. }
      apply range_incl_tree_rep_R; auto.
      - (* Inner if, second branch:  k<x *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        unfold ltree at 2; Intros.
        forward.
        forward_call (lockb, lsh1, node_lock_inv gsh1 g pb gb lockb).
        Intros .
        unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Intros a.
        rewrite node_rep_def. Intros tp1. gather_SEP AS (my_half g_in _ _) (in_tree g g_in) (my_half gb gsh1 a); unfold AS.
        sep_apply (in_tree_right_range () (λ M (_ : ()), tree_rep g g_root (<[x:=v]>M) * emp)
          (λ _ : (), Q)  x x0 g g_root inv_names v0 g_in ga gb). Intros ba.
        forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in, node_lock_inv gsh g np0 g_in lock_in).
        { lock_props.
          unfold node_lock_inv at 3. fold (node_lock_inv gsh1 g pb gb lockb). rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists r.
          rewrite node_rep_def. Exists tp; cancel. unfold tree_rep_R at 2. rewrite -> if_false by auto.
          Exists ga gb x0 v0 pa pb locka lockb. unfold ltree at 3; entailer!.
          repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp); entailer!.
         }
         Exists (Finite_Integer x0, ba, a.2) gb lockb pb gsh1. unfold node_lock_inv. rewrite node_rep_def. Exists tp1.
         unfold AS; entailer!.
         { unfold key_in_range in *. apply andb_true_intro. split; [simpl; lia|]. destruct r as ((?, ?), ?). apply andb_prop in H2 as []. eapply less_than_less_than_equal_trans; eauto. }
         apply range_incl_tree_rep_R; auto.
      - (* x = k *)
        forward.
        destruct r as ((?, ?), ?); simpl in H4; subst.
        assert (x = x0) by lia; subst x0.
        gather_SEP AS (my_half g_in _ _) (in_tree g  _).
        viewshift_SEP 0 (Q * (EX n1 n2:number, !!(key_in_range x (n1,n2) = true) && my_half g_in gsh (n1,n2,Some (Some(x,v,ga,gb))) * in_tree g g_in)).
        { go_lower. eapply sync_commit_gen1.
          intros. iIntros "H". iDestruct "H" as "[H1 H2]".
          iModIntro. iPoseProof (tree_rep_insert with "[$H1 $H2]") as "Hadd". iDestruct "Hadd" as ((n1, n2) o0) "([Hmy H1] & H2)".
          iExists (n1,n2,Some o0). iFrame. iPoseProof (bi.and_elim_l with "H2") as "H3". iPoseProof (bi.and_elim_r with "H3") as "Hnew".  iIntros "H"; iDestruct "H" as %Hsub.
          iMod "Hnew". iSpecialize ("Hnew" $! ga gb). iModIntro. iExists (n1,n2, Some (Some(x,v,ga,gb))).
          apply node_info_incl' in Hsub as [? Heq]; simpl in Heq; inv Heq.
          iExists (n1,n2, Some (Some (x,v,ga,gb))). logic_to_iris. instantiate (1 := v). instantiate (1:= x).
          iSplit.
          { iPureIntro. intros ? Hincl.
             hnf. simpl. destruct (range_incl_join _ _ _ Hincl).
           simpl in *; subst. split. { symmetry; rewrite merge_comm; apply merge_range_incl'; auto. }
           destruct b0, Hincl as [_ Hincl]; simpl in Hincl. inv Hincl; try constructor. inv H15. }
          iIntros "(H1 & H2)". iSpecialize ("Hnew" with "[$H2 $Hmy]"). iSplit; auto.
          { iPureIntro. split; [reflexivity|].
           eapply key_in_range_incl; eassumption. }
          iModIntro. iDestruct "Hnew" as "($ & H3)". iSplit; [iExists tt; auto|]. iExists n1, n2; iFrame.
          iSplit; last done; iPureIntro.
          eapply key_in_range_incl; eassumption. }
        Intros n1 n2.
        forward_call (lock_in, lsh2, node_lock_inv_pred gsh g np0 g_in lock_in, node_lock_inv gsh g np0 g_in lock_in).
        { lock_props.
           unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists (n1, n2, Some(Some (x, v, ga, gb))).
          rewrite node_rep_def. Exists tp; cancel. unfold tree_rep_R. rewrite -> if_false by auto.
          Exists ga gb x v pa pb locka lockb. unfold node_lock_inv; entailer!.  }
        forward. entailer!.
Qed.

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (t, gv).
  Intros p.
  forward_if (p <> nullval).
  * if_tac; entailer!.
  * forward_call 1.
    contradiction.
  * forward.
    rewrite -> if_false by auto; entailer!.
  * forward. rewrite -> if_false by auto. Exists p; entailer!.
Qed.
