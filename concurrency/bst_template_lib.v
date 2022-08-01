Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks. 
Require Export VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.ghostsI.
Require Import VST.concurrency.semax_conc.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.bst_template.
Import FashNotation.


Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

 (* trees labeled with ghost names *)

Inductive ghost_tree: Type :=
 | E_ghost : ghost_tree
 | T_ghost : ghost_tree -> gname -> key -> V  -> ghost_tree -> gname -> ghost_tree.

Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 r g2 x v :
       (k = x) -> In_ghost k (T_ghost l g1 x v r g2 )
  | InLeft_ghost l g1 r g2 x v' :
      In_ghost k l -> In_ghost k (T_ghost l g1 x v' r g2)
  | InRight_ghost l g1 r g2 x v' :
      In_ghost k r -> In_ghost k (T_ghost l g1 x v' r g2).

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> Z.lt k x .
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> Z.lt x k .

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
| Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
| Sorted_Ghost_Tree x v l g1 r g2 (Hsortedl : sorted_ghost_tree l) (Hsortedr : sorted_ghost_tree r)
  (Hgtl : gt_ghost l x) (Hltr : lt_ghost r x) : sorted_ghost_tree (T_ghost l g1 x v r g2 ).

Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree) (g1:gname) (g2:gname) : ghost_tree :=
match s with
| E_ghost => T_ghost E_ghost g1 x v E_ghost g2
| T_ghost a ga y v' b gb => if (Z.ltb x y) then T_ghost (insert_ghost x v a g1 g2) ga y v' b gb
                            else if (Z.ltb y x) then T_ghost a ga y v' (insert_ghost x v b g1 g2) gb else T_ghost a ga x v b gb
end.

End TREES.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.
Definition t_struct_pn := Tstruct _pn noattr.

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

#[export] Program Instance range_ghost : Ghost :=
  { G := range; valid g := true; Join_G a b c := c = merge_range a b }.
Next Obligation.
  exists (fun _ => (Pos_Infinity,Neg_Infinity)).
  + intros; hnf.
      destruct t; auto.
  + intros; eexists (_, _); hnf; simpl; reflexivity.
  + reflexivity.
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

#[export] Instance bst_ghost : Ghost := ref_PCM range_ghost.

Definition ghost_ref g r1 := ghost_reference(P := invariants.set_PCM) r1 g.

Definition in_tree g r1 := EX sh: share, ghost_part(P := invariants.set_PCM) sh (Ensembles.Singleton r1) g.

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


Lemma in_tree_add : forall g s g1 g', ~Ensembles.In s g' -> in_tree g g1 * ghost_ref g s 
  |-- (|==> !! (g1 <> g') && (ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
Proof.
  intros.
  unfold in_tree at 1. Intros sh. iIntros "H".
  iPoseProof (ref_sub with "H") as "%".
  rewrite ghost_part_ref_join.
  assert (Ensembles.In s g1).
  { destruct (eq_dec sh Tsh); subst.
    - constructor.
    - destruct H0 as (? & ? & ?); subst.
      repeat constructor. }
  iMod (ref_add(P := invariants.set_PCM) _ _ _ _ (Singleton g') (Add (Singleton g1) g') (Add s g') with "H") as "H".
  { repeat constructor.
    inversion 1; subst.
    inv H3; inv H4; contradiction. }
  { split; auto.
    constructor; intros ? X; inv X.
    inv H3; contradiction. }
  fold (ghost_part_ref(P := invariants.set_PCM) sh (Add (Singleton g1) g') (Add s g') g).
  rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>".
  iDestruct "H" as "[in $]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := invariants.set_PCM) sh1 sh2 sh (Singleton g1) (Singleton g')); auto.
  iDestruct "in" as "[in1 in2]". iSplit.
  * iPureIntro; intros Hcontra; subst; congruence.
  * iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  * split; auto; constructor; intros ? X; inv X.
    inv H5; inv H6; contradiction.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
Qed.


Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM range_ghost (exclusive_PCM (option ghost_info)).

Notation node_info := (@G node_ghost).

Lemma ghost_node_alloc : forall g s g1 (a : node_info),
  finite s -> in_tree g g1 * ghost_ref g s |-- 
    (|==> EX g', !! (¬ Ensembles.In s g' /\ g1 <> g') && (both_halves a g' * ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
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
  sync_inv gp sh (curry (curry R p))  *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p (* *
  malloc_token Ews t_lock lock*).

Definition node_lock_inv_r (R : (val * (own.gname * node_info) → mpred)) sh p gp lock:=
      selflock (node_lock_inv_r' R sh p gp (ptr_of lock)) lsh2 lock.

Definition ltree_r R (g_root:gname) sh gsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] (ptr_of lock) p *
   lock_inv sh lock (node_lock_inv_r R gsh p g_root lock)).

(* Does the range ghost help at all, given that we could calculate it precisely from the nodes we've seen?
  Yes, since the nodes we've seen may change after we pass them. *)


Definition node_rep_r (g:gname) R arg : mpred := 
  let '(np, (g_current,(r,g_info))) := arg in
EX tp:val,
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) *
 malloc_token Ews t_struct_tree_t np * in_tree g g_current *
if eq_dec tp nullval 
then !!(g_info = Some None) && emp  
else
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX (locka lockb : lock_handle),
     !! (g_info = Some (Some(x,v,ga,gb)) /\ 
     and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\ 
     is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true) && 
     data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * 
     malloc_token Ews t_struct_tree tp  *
    |> ltree_r R ga lsh1 gsh1 pa locka * |> ltree_r R gb lsh1 gsh1 pb lockb.

Definition node_rep_closed g := HORec (node_rep_r g).

Definition node_rep np g g_current r := node_rep_closed g (np, (g_current, r)).

Definition node_lock_inv_pred sh g p gp lock :=
  sync_inv gp sh (node_rep p g) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p
 (* * 
  malloc_token Ews t_lock lock
 * malloc_token Ews t_struct_tree_t p  *).
(* No malloc token for t_struct_tree_t because node_rep_r contains one *)

Definition node_lock_inv sh g p gp lock :=
  selflock (node_lock_inv_pred sh g p gp (ptr_of lock)) lsh2 lock.

Definition public_half' (g : gname) (d : range * option (option ghost_info)) := 
  my_half g gsh2 (fst d, None) * public_half g d.

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
  split. split; auto; simpl.
  hnf in J1 |- *.
  symmetry in J1; rewrite merge_comm in J1; apply merge_range_incl in J1.
  symmetry; rewrite merge_comm; apply merge_range_incl'.
  eapply range_incl_trans; eauto.
  inversion 1; reflexivity.
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
  - unfold Add; simpl.
    now rewrite invariants.Union_Empty.
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


Definition ltree (g : gname) (g_root : gname) sh gsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] (ptr_of lock) p  *
     lock_inv sh lock (node_lock_inv gsh g p g_root lock)).


(* nodebox_rep knows that the range of the root is -infinity to +infinity, but doesn't know the data. *)
(* reduce share to something related to the sh argument *)
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock : lock_handle) (nb : val) :=
  EX np: val, data_at sh (tptr (t_struct_tree_t)) np nb *
                ltree g g_root sh (fst (Share.split gsh1)) np lock *
                my_half g_root (snd (Share.split gsh1)) (Neg_Infinity, Pos_Infinity, None).

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
  if eq_dec tp nullval
  then !!(g_info = Some None) && emp
  else
  EX ga : gname, EX gb : gname, EX x : Z, EX v : val, EX pa : val, EX pb : val, EX (locka lockb : lock_handle),
     !!(g_info = Some (Some(x,v,ga,gb)) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
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
    |> (selflock (P x) sh p <=> selflock (Q x) sh p)).
Proof.
  intros. apply allp_left with x. apply later_derives.
  apply nonexpansive_entail with (F := fun P => selflock P sh p).
  apply sepcon_nonexpansive, identity_nonexpansive; apply const_nonexpansive.
Qed.

Lemma lock_inv_node_lock_inv_r_nonexpansive:
  ∀ (P Q : val * (own.gname * node_info) → mpred)
    (sh gsh: share) (gp : own.gname) (p : val) (lock : lock_handle),
    ALL x : val * (own.gname * node_info),
    |> (P x <=> Q x)
       |-- |> lock_inv sh lock (node_lock_inv_r P gsh p gp lock) >=>
           |> lock_inv sh lock (node_lock_inv_r Q gsh p gp lock).
Proof.
  intros. eapply derives_trans, eqp_subp. eapply derives_trans, lock_inv_nonexpansive2.
  apply allp_right. intros v. unfold node_lock_inv_r.
  eapply derives_trans, selflock_nonexpansive2.
  apply allp_right. intros ?.
  unfold node_lock_inv_r'. unfold sync_inv, curry, Datatypes.curry.
  rewrite <- later_allp; apply later_derives.
  eapply eqp_sepcon, eqp_refl.
  apply eqp_exp. intros (?, ?). apply allp_left with (p, (gp, (g, g0))).
  apply eqp_sepcon; [apply derives_refl | apply eqp_refl].
Qed.

Lemma ltree_r_nonexpansive:
  ∀ (P Q : val * (own.gname * node_info) → mpred)
    (sh gsh: share) (gp : own.gname) (p : val) (lock : lock_handle),
    ALL x : val * (own.gname * node_info),
    |> (P x <=> Q x) |-- |> ltree_r P gp sh gsh p lock >=> |> ltree_r Q gp sh gsh p lock.
Proof.
  intros. unfold ltree_r. rewrite !later_andp. apply subp_andp; [apply subp_refl|].
  rewrite !later_sepcon. apply subp_sepcon; [apply subp_refl|].
  apply lock_inv_node_lock_inv_r_nonexpansive.
Qed.

Lemma node_rep_def : forall np r g g_current,
    node_rep np g g_current r =
    EX tp:val, (field_at Ews (t_struct_tree_t) [StructField _t] tp np) *
               malloc_token Ews t_struct_tree_t np *  in_tree g g_current *
               tree_rep_R tp (fst r) (snd r) g.
Proof.
  intros. assert (HOcontractive (node_rep_r g)). {
    apply prove_HOcontractive'. intros ?? (?, (?, (?, ?))). unfold node_rep_r.
    apply subp_exp; intros. apply subp_sepcon; [apply subp_refl|].
    destruct (eq_dec x nullval). 1: apply subp_refl. repeat (apply subp_exp; intro).
    rewrite !sepcon_assoc; apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; apply ltree_r_nonexpansive. }
  unfold node_rep, node_rep_closed.
  etransitivity; [eapply equal_f, HORec_fold_unfold|]; auto.
  unfold node_rep_r at 1.
  destruct r; reflexivity.
Qed.

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
    destruct (Z.ltb x  k) eqn: H1; [|destruct (Z.ltb k  x) eqn: H2]; simpl.
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
  iDestruct "H" as "[Ha Hb]".
  iPoseProof (ghost_node_alloc with "[$Ha $Hb]") as ">H". auto.
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
  + unfold Add. rewrite invariants.Union_Empty. reflexivity.
  + destruct (Z.ltb x k) eqn:E1; [|destruct (Z.ltb k x) eqn:E2]; simpl.
    - repeat rewrite -> find_ghost_set_equiv with (g := g).
      rewrite IHtg1. unfold Add.
      remember (find_ghost_set' tg1) as a1. remember (find_ghost_set tg2 g0) as a2.
      remember (Singleton g1) as b. remember (Singleton g2) as c.
      remember (Singleton g) as d.
      rewrite -> (invariants.Union_assoc a1 b c). rewrite -> (invariants.Union_assoc a1 _ d).
      rewrite -> (invariants.Union_comm _ d). rewrite <- (invariants.Union_assoc a1 d _).
      rewrite -> (invariants.Union_assoc _ _ a2). rewrite -> (invariants.Union_comm _ a2).
      rewrite <- (invariants.Union_assoc _ a2 _). rewrite <- invariants.Union_assoc; reflexivity.
      intro Hcontra. apply H. apply InLeft_ghost; auto.
    - repeat rewrite -> find_ghost_set_equiv with (g := g0).
      rewrite IHtg2. unfold Add.
      remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set' tg2) as a2.
      remember (Singleton g1) as b. remember (Singleton g2) as c.
      remember (Singleton g0) as d.
      rewrite -> (invariants.Union_assoc _ c d).
      rewrite -> (invariants.Union_assoc a2 b _). rewrite (invariants.Union_comm b _).
      rewrite (invariants.Union_assoc c d b). rewrite <- (invariants.Union_comm _ c).
      rewrite <- (invariants.Union_assoc a2 _ c). rewrite <- (invariants.Union_assoc a2 d b).
      rewrite <- (invariants.Union_assoc a1 _ c). rewrite <- (invariants.Union_assoc a1 _ b).
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
  rewrite !invariants.Union_assoc (invariants.Union_comm (Singleton _)) invariants.Union_assoc (invariants.Union_comm (Singleton _)) invariants.Union_assoc; reflexivity.
Qed.

Lemma ghost_set_insert_same: forall x v tg g1 g2, In_ghost x tg -> sorted_ghost_tree tg -> find_ghost_set' (insert_ghost x v tg g1 g2) = find_ghost_set' tg.
  induction tg; intros; simpl.
 + inv H.
 + inv H0; inv H; simpl.
    - rewrite Z.ltb_irrefl; reflexivity.
    - specialize (Hgtl _ H1). destruct (Z.ltb x k) eqn:?; try lia; simpl.
      rewrite !find_ghost_set_equiv IHtg1; auto.
    - specialize (Hltr _ H1). destruct (Z.ltb x k) eqn:?; [|destruct (Z.ltb k x) eqn:?]; try lia; simpl.
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
        assert (Z.ltb x k = true) as ->.
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
        assert (Z.ltb k x = true) as Hgt.
        { destruct r; eapply (less_than_equal_less_than_trans (Finite_Integer _) _ (Finite_Integer _)).
          unfold range_incl in H2; apply andb_prop in H2; apply H2.
          unfold key_in_range in H4; apply andb_prop in H4; apply H4. }
        assert (Z.ltb x  k = false) as -> by lia; rewrite Hgt.
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
        destruct (Z.ltb x x) eqn: E1; try lia.
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
    apply invariants.Intersection_Empty.
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
    simpl. inv H3. destruct (Z.ltb x k) eqn:E; [|destruct (Z.ltb k x) eqn:E2].
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
    + specialize (Hgtl _ H1); destruct (Z.ltb x k) eqn:E; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
    + specialize (Hltr _ H1); destruct (Z.ltb x k) eqn:E; try lia.
      destruct (Z.ltb k x) eqn:E2; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
Qed.

Lemma In_ghost_insert : forall x (v : val) k tg g1 g2, 
      In_ghost k (insert_ghost x v tg g1 g2) -> x = k \/ In_ghost k tg.
Proof.
  induction tg; simpl; intros.
  - inv H; auto.
  - destruct (Z.ltb x k0) eqn: ?; [|destruct (Z.ltb k0 x) eqn: ?].
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
  - inv H. destruct (Z.ltb x k) eqn:E; [|destruct (Z.ltb k x) eqn:E2].
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
  - erewrite update_ghost_ref. iIntros "(>H1 & [H2 _])". iDestruct "H1" as (g1 g2) "((((([HH H1] & H3) & H4) & H5) & H6) & H7)". iDestruct "HH" as %(? & ? & ?).
    rewrite <- !both_halves_join. iDestruct "H1" as "(H1 & H1')". iDestruct "H3" as "(H3 & H3')". iModIntro. iExists g1. iExists g2. iIntros "(HH & H')". iDestruct "HH" as %(? & ?); subst. iSpecialize ("H2" with "[%]"); first done.
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
  - iIntros "((H1 & H2) & [H3 _]) !>". iIntros (g1 g2 v0) "[HH H]"; iDestruct "HH" as %(? & ?); subst.
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
  my_half g sh a * public_half g b |-- 
    !! (range_incl (fst a) (fst b) = true /\ 
          match a.2 with 
          | Some x => b.2 = Some x 
          | _ => True end).
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
     (v: val) (g_in ga gb: gname) (gsh: share) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> Z.lt x x0 ->
    atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
                 b Q * my_half g_in gsh r * in_tree g g_in * my_half ga gsh1 a
    |-- |={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
    b Q * my_half g_in gsh r *
    (EX ba, !! (less_than_equal ba r.1.1 = true /\
                range_incl a.1 (ba, Finite_Integer x0) = true) &&
            (in_tree g g_in * my_half ga gsh1 (ba, Finite_Integer x0, a.2))).

Proof.
  intros. rewrite sepcon_assoc. 
  apply sync_rollback. intros t.
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
    + intros. destruct H0. split. split; auto; simpl.
      hnf in H0; hnf.
      symmetry; rewrite merge_comm; eapply merge_again.
      symmetry; rewrite merge_comm; eauto.
      intros; subst; reflexivity.
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
    (v: val) (g_in ga gb: gname) (gsh: share) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> Z.lt x0 x ->
    atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
                 b Q * my_half g_in gsh r * in_tree g g_in * my_half gb gsh1 a
    |-- |={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
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
    + intros. destruct H0. split. split; auto; simpl.
      hnf in H0; hnf.
      symmetry; rewrite merge_comm; eapply merge_again.
      symmetry; rewrite merge_comm; eauto.
      intros; subst; reflexivity.
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

#[export] Instance ghost_tree_rep_dealloc tg g_root r : Affine (ghost_tree_rep tg g_root r).
Proof.
  unfold Affine; revert g_root r; induction tg; simpl; intros.
  - iIntros "[_ _]"; auto.
  - destruct r; iIntros "[[[_ _] HL] HR]".
    iPoseProof (IHtg1 with "HL") as "_"; iPoseProof (IHtg2 with "HR") as "_"; auto.
Qed.

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
