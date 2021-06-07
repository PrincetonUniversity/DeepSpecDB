Require Import VST.progs.conclib.
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
    | Sorted_Ghost_Tree x v l g1 r g2 : sorted_ghost_tree l -> sorted_ghost_tree r -> gt_ghost l x -> lt_ghost r x -> sorted_ghost_tree (T_ghost l g1 x v r g2 ).

 Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree) (g1:gname) (g2:gname) : ghost_tree :=
 match s with
 | E_ghost => T_ghost E_ghost g1 x v E_ghost g2
 | T_ghost a ga y v' b gb => if  x <? y then T_ghost (insert_ghost x v a g1 g2) ga y v' b gb
                        else if (y <? x) then T_ghost a ga y v' (insert_ghost x v b g1 g2) gb else T_ghost a ga x v b gb

 end.

End TREES.

Program Instance range_ghost : Ghost :=
  { G := (number*number); valid g := True; Join_G a b c := c =  merge_range a b }.
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

Local Hint Resolve readable_lsh1 readable_lsh2 lsh1_lsh2_join : core.

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

Local Hint Resolve readable_sh1 readable_sh2 sh1_sh2_join : core.

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

Lemma finite_empty : finite (Empty_set).
Proof.
  exists O; intros; inv H.
Qed.

Lemma finite_singleton : forall x, finite (Singleton x).
Proof.
  intros; exists x; intros; inv H; auto.
Qed.

Lemma in_tree_add : forall g s g1 g', ~Ensembles.In s g' -> in_tree g g1 * ghost_ref g s |-- (|==> ghost_ref g (Add s g') * in_tree g g1 * in_tree g g')%I.
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
  change (own g _ _) with (ghost_part_ref(P := set_PCM) sh (Add (Singleton g1) g') (Add s g') g).
  rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>".
  iDestruct "H" as "[in $]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := set_PCM) sh1 sh2 sh (Singleton g1) (Singleton g')); auto.
  iDestruct "in" as "[in1 in2]"; iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  { split; auto; constructor; intros ? X; inv X.
    inv H5; inv H6; contradiction. }
  { intro; contradiction H2; eapply Share.split_nontrivial; eauto. }
  { intro; contradiction H2; eapply Share.split_nontrivial; eauto. }
Qed.

Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. Is this the right way to do it? *)
Instance node_ghost : Ghost := prod_PCM range_ghost (exclusive_PCM (option ghost_info)).

Notation node_info := (@G node_ghost).

Lemma ghost_node_alloc : forall g s g1 (a : node_info),
  finite s -> in_tree g g1 * ghost_ref g s |-- (|==> EX g', both_halves a g' * ghost_ref g (Add s g') * in_tree g g1 * in_tree g g')%I.
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
  iExists g'.
  iMod (in_tree_add _ _ _ g' with "r") as "(($ & $) & $)"; auto.
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
Local Hint Resolve gsh1_not_Tsh gsh2_not_Tsh : share.

Lemma range_incl_join: forall  (r1 r2 r3 : node_info), sepalg.join r1 r2 r3 -> range_incl r1.1 r3.1 = true /\ range_incl r2.1 r3.1 = true.
Proof.
  intros. destruct r1 as [range1 r1]. destruct r2 as [range2 r2]. destruct r3 as [range3 r3].
  hnf in H. simpl in *. destruct H. inv H; auto. split; [|rewrite merge_comm]; eapply merge_range_incl; eauto.
Qed.

(* Each lock will hold gsh1 of my_half, with gsh2 held by the invariant, allowing the lock's range to become outdated. *)
(* helper for node_lock_inv_r *)
Definition node_lock_inv_r' (R : (val * (own.gname * node_info) → mpred)) p gp lock :=
  sync_inv gp gsh1 (uncurry (uncurry R p)) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
  malloc_token Ews tlock lock.

(* selflock *)
Definition node_lock_inv_r (R : (val * (own.gname * node_info) → mpred)) p gp lock :=
      selflock (node_lock_inv_r' R p gp lock) lsh2 lock.

Definition ltree_r R (g_root:gname) sh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] lock p *
   lock_inv sh lock (node_lock_inv_r R p g_root lock)).

(* !! Once we've done delete, consider: does the range ghost help at all, given that we could calculate it
  precisely from the nodes we've seen? It should, since the nodes we've seen may change after we pass them. *)
 Definition node_rep_r (g:gname)  R arg : mpred := let '(np, (g_current,(r,g_info))) := arg in
EX tp:val,
(* (field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * in_tree g lsh1 g_current * *)
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * in_tree g g_current *
if eq_dec tp nullval then !!( g_info = Some None) && emp  else
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !! (g_info = Some (Some(x,v,ga,gb)) /\ Int.min_signed <= x <= Int.max_signed /\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp  *
    |> ltree_r R ga lsh1 pa locka * |> ltree_r R gb lsh1 pb lockb.

Definition node_rep_closed g  := HORec (node_rep_r g ).

Definition node_rep np g g_current r := node_rep_closed g (np, (g_current, r)) .

Definition node_lock_inv_pred g p gp lock :=
  sync_inv gp gsh1 (node_rep p g) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
  malloc_token Ews tlock lock (* * malloc_token Ews t_struct_tree_t p *).
(* No malloc token for t_struct_tree_t because node_rep_r contains one *)

Definition node_lock_inv g p gp lock :=
  selflock (node_lock_inv_pred g p gp lock) lsh2 lock.

Definition public_half' (g : gname) (d : range * option (option ghost_info)) := my_half g gsh2 (fst d, None) * public_half g d.

 Fixpoint ghost_tree_rep (t: @ ghost_tree val) (g:gname) range : mpred :=
 match t, range with
 | E_ghost , _ => public_half' g (range, Some (@None ghost_info))
 | (T_ghost a ga x v b gb ), (l, r) => public_half' g (range, Some (@Some ghost_info (x,v,ga,gb))) *  ghost_tree_rep a ga (l, Finite_Integer x) * ghost_tree_rep b gb (Finite_Integer x, r)
 end.

Lemma public_half_range_incl : forall g r r' o, range_incl r r' = true -> (public_half' g (r, o) |-- |==> public_half' g (r', o))%I.
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

Fixpoint find_pure_tree (t : @ghost_tree val) : @tree val :=
  match t with
  | E_ghost => E
  | (T_ghost a ga x v  b gb) => T (find_pure_tree a) x v (find_pure_tree b)
end.

Fixpoint find_ghost_set (t : @ghost_tree val) (g:gname) : Ensemble gname :=
  match t with
  | E_ghost => (Ensembles.Singleton g)
  | (T_ghost a ga x v  b gb) => (Add  (Union (find_ghost_set a ga) (find_ghost_set b gb)) g)
end.

Lemma find_ghost_set_finite : forall t g, finite (find_ghost_set t g).
Proof.
  induction t; intros; simpl.
  - apply finite_singleton.
  - apply finite_add, finite_union; auto.
Qed.

Definition tree_rep (g : gname) (g_root : gname)  (t : @tree val) : mpred := EX (tg : ghost_tree), !!(find_pure_tree tg = t) && ghost_tree_rep tg g_root (Neg_Infinity, Pos_Infinity) * ghost_ref g (find_ghost_set tg g_root).

Definition ltree (g : gname) (g_root : gname) sh p lock := !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] lock p  * lock_inv sh lock (node_lock_inv g p g_root lock)).

(* nodebox_rep knows that the range of the root is -infinity to +infinity, but doesn't know the data. *)
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock : val) (nb : val) :=
 EX np: val, data_at sh (tptr (t_struct_tree_t)) np nb * ltree g g_root sh np lock * my_half g_root gsh2 (Neg_Infinity, Pos_Infinity, None).

Lemma my_half_range_inf : forall g r1 r2 o,
    my_half g gsh1 (r1, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None) =
    my_half g gsh1 (r2, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None).
Proof.
  intros.
  unfold my_half; erewrite 2 ghost_part_join with
                      (a := (Neg_Infinity, Pos_Infinity, o));
  eauto with share; repeat constructor; simpl; hnf; rewrite merge_infinity; auto.
Qed.

(* Fixpoint prospect_key_range (t : @tree val) k (p_range : range) : range :=
 match t, p_range with
 | E, _ => p_range
 | T a x v b, (l,r) => if (k <? x) then prospect_key_range a k (l,Finite_Integer x) else
                             if (x <? k) then prospect_key_range b k (Finite_Integer x,r) else p_range end.*)

(*Lemma prospect_key_in_leaf: forall r t x r_root, key_in_range x r = true ->  EmptyRange r t r_root -> keys_in_range t r_root -> sorted_tree t -> ~ In x t ->
                                                           prospect_key_range t x r_root = r.
Proof.
intros.
revert dependent r_root.
induction t; intros.
- simpl. inversion H0. auto.
- apply keys_in_range_subtrees in H1 as (? & ? & ?); [|auto].
  inv H2. destruct r_root; simpl.
  destruct (x <? k) eqn:E1; [|destruct (k <? x) eqn:E2].
 * apply IHt1; auto.
    { intro a. contradiction H3. apply InLeft; auto. }
    { inv H0; auto. apply range_inside_range in H6; auto.
      eapply key_in_range_incl in H; eauto.
      unfold key_in_range in H; simpl in H; lia. }
 * apply IHt2; auto.
    { intro a. contradiction H3. apply InRight; auto. }
    { inv H0; auto. apply range_inside_range in H6; auto.
      eapply key_in_range_incl in H; eauto.
      unfold key_in_range in H; simpl in H; lia. }
 * contradiction H3. apply InRoot. lia.
Qed.*)

(* Lemma public_half_insert: forall x v g1 g2 t r g_root (n n0 : number), prospect_key_range t x r = (n,n0) -> ~ In x t ->
                                        public_half g1 (n, Finite_Integer x) * public_half g2 (Finite_Integer x,n0) * tree_rep g_root t r  |-- tree_rep g_root ( insert x v t) r.
Proof.
intros.
revert dependent g_root .
revert dependent r.
induction t.
 - simpl.  intros. cancel. subst r.  Exists g1 g2.  cancel.
 - simpl.  intros. destruct r.  Intros ga gb. destruct (x <? k) eqn: IHe.
    *  simpl.  Exists ga gb. cancel. apply IHt1. intros a. contradiction H0. apply InLeft. apply a. apply H.
    *  destruct (k <? x) eqn: IHe'. simpl. Exists ga gb.  cancel. apply IHt2. intros a. contradiction H0. apply InRight. apply a. apply H.
    contradiction H0. apply Z.ltb_nlt in IHe. apply Z.ltb_nlt in IHe'. assert (k = x). { lia. } apply InRoot. lia.
Qed.

 Lemma empty_tree_rep: forall g r,  tree_rep g E r = public_half g r.
 Proof.
 intros. simpl. auto.
 Qed.
 *)

Definition tree_rep_R (tp:val) (r:(range)) (g_info: option (option ghost_info)) g : mpred :=
if eq_dec tp nullval then !!( g_info = Some None) && emp  else
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !! (g_info = Some (Some(x,v,ga,gb)) /\ Int.min_signed <= x <= Int.max_signed/\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp *
     |> ltree g ga lsh1 pa locka * |> ltree g gb lsh1 pb lockb.

Lemma eqp_subp : forall P Q, P <=> Q |-- P >=> Q.
Proof.
  intros; constructor.
  apply subtypes.eqp_subp, predicates_hered.derives_refl.
Qed.

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
    (sh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * node_info),
    |> P x <=> |> Q x
       |-- |> lock_inv sh lock (node_lock_inv_r P p gp lock) >=>
           |> lock_inv sh lock (node_lock_inv_r Q p gp lock).
Proof.
  intros. eapply derives_trans, eqp_subp. eapply derives_trans, lock_inv_nonexpansive2.
  apply allp_right. intros v. unfold node_lock_inv_r.
  remember (fun (M: val * (own.gname *
                           node_info) -> mpred)
                (x: gname * val) =>
              (node_lock_inv_r' M (snd x) (fst x) v)) as func.
  pose proof (selflock_nonexpansive2 (func P) (func Q) lsh2 v (gp, p)).
  replace (func P (gp, p)) with (node_lock_inv_r' P p gp v) in H by
    now rewrite Heqfunc.
  replace (func Q (gp, p)) with (node_lock_inv_r' Q p gp v) in H by
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
    (sh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * node_info),
    |> P x <=> |> Q x |-- |> ltree_r P gp sh p lock >=> |> ltree_r Q gp sh p lock.
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

Theorem node_lock_inv_def : forall p lock g g_current,
  node_lock_inv g p g_current lock =
  (EX a : node_info,
    node_rep p g g_current a * my_half g_current gsh1 a) *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
    malloc_token Ews tlock lock *
    |> lock_inv lsh2 lock (node_lock_inv g p g_current lock).
Proof.
  intros p lock g g_current.
  unfold node_lock_inv at 1.
  setoid_rewrite (selflock_eq) at 1.
  unfold node_lock_inv_pred at 1.
  unfold sync_inv at 1.
  unfold node_lock_inv at 1.
  reflexivity.
Qed.

Lemma node_lock_exclusive : forall p lock g g_current,
  exclusive_mpred (node_lock_inv g p g_current lock).
Proof.
  intros. rewrite node_lock_inv_def.
  eapply derives_exclusive, exclusive_sepcon1 with
  (P := field_at lsh2 t_struct_tree_t [StructField _lock] lock p)
  (Q := (EX a : node_info, node_rep p g g_current a * my_half(P := node_ghost) g_current gsh1 a) *
         malloc_token Ews tlock lock * _).
  - Intros a. Exists a. cancel. apply derives_refl.
  - apply field_at_exclusive; auto.
    simpl. lia.
Qed.
Local Hint Resolve node_lock_exclusive : core.

Lemma node_lock_inv_rec: forall g p gp lock,
    rec_inv lsh2 lock (node_lock_inv_pred g p gp lock) (node_lock_inv g p gp lock).
Proof. intros. apply node_lock_inv_def. Qed.
Local Hint Resolve node_lock_inv_rec : core.

(* insert proof related lemmas *)

Lemma node_exist_in_tree: forall g s g_in,  in_tree g g_in * ghost_ref g s |-- !! (Ensembles.In s g_in).
Proof.
intros. unfold ghost_ref, in_tree; Intros sh. rewrite ref_sub.  destruct  (eq_dec sh Tsh).
- Intros. apply log_normalize.prop_derives. intros. subst s.  apply In_singleton.
- apply log_normalize.prop_derives. intros [m H].  unfold sepalg.join in H. hnf in H. destruct H. rewrite H0. apply Union_introl. apply In_singleton.
Qed.

Lemma insert_preserved_in_ghost_tree: forall t tg x v g1 g2, find_pure_tree tg = t -> find_pure_tree (insert_ghost x v tg g1 g2) = (insert x v t).
Proof.
intros.
revert dependent t.
induction tg.
  - intros. simpl.  simpl in H. symmetry in H. subst t. simpl. reflexivity.
 - intros. simpl. destruct (x <? k) eqn:E1.
    *  simpl. rewrite (IHtg1  (find_pure_tree tg1)).  simpl in H. rewrite <- H. simpl. rewrite E1. auto. auto.
    * destruct (k <? x) eqn:E2. simpl. rewrite ( IHtg2  (find_pure_tree tg2)). simpl in H. rewrite <- H. simpl. rewrite E1. rewrite E2. auto. auto.
       simpl. simpl in H. rewrite <- H. simpl. rewrite E1. rewrite E2. auto.
Qed.

Lemma update_ghost_ref: forall g s g_in (a b : node_info), finite s -> in_tree g g_in * ghost_ref g s |-- (|==> EX g1 g2:gname, both_halves a g1 * both_halves b g2 * ghost_ref g (Add (Add s g1) g2) *
    in_tree g g1 * in_tree g g2 * in_tree g g_in)%I .
 Proof.
 intros.
 iIntros "H".
iDestruct "H" as "[Ha Hb]". iPoseProof ( ghost_node_alloc with "[$Ha $Hb]") as ">H"; auto.
iDestruct "H" as ((* sh3 sh4  *)g1) "[[[Ha Hb] Hc] Hd]". instantiate(1:= a). iPoseProof( ghost_node_alloc with "[$Hb $Hc]") as ">Hnew". apply finite_add; auto.
 iDestruct "Hnew" as ((* sh5 sh6 *) g2) "[[[Hc Hb ] He] Hf]". instantiate(1:= b). iModIntro. iExists (* sh4, sh6, *) g1, g2. iFrame.
Qed.

Lemma update_ghost_tree_with_insert: forall x v tg g1 g2 g_root, ~In_ghost x tg ->  (find_ghost_set (insert_ghost x v tg g1 g2) g_root) =  (Add (Add (find_ghost_set tg g_root) g1) g2).
Proof.
intros.
revert dependent g_root.
induction tg.
 + intros. simpl. unfold Add. rewrite Union_comm. rewrite <- Union_assoc. reflexivity.
 + simpl. destruct (x <? k) eqn:E1.
    -  intros. simpl. rewrite IHtg1. unfold Add. remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set tg2 g0) as a2. remember (Singleton g1) as b.
        remember (Singleton g2) as c. remember (Singleton g_root) as d. rewrite (Union_comm _ a2). rewrite <- Union_assoc.
        rewrite <- Union_assoc. rewrite (Union_comm a2 a1). rewrite Union_comm. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite ( Union_comm d _). reflexivity.
        unfold not. intros. apply (InLeft_ghost x tg1 g tg2 g0 k v0) in H0. unfold not in H. apply H in H0. auto.
    - destruct (k <? x) eqn:E2.
        * intros;simpl. rewrite IHtg2. unfold Add. remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set tg2 g0) as a2. remember (Singleton g1) as b.
        remember (Singleton g2) as c. remember (Singleton g_root) as d. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite Union_comm. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite (Union_comm d _). reflexivity.
        unfold not. intros. apply (InRight_ghost x tg1 g tg2 g0 k v0) in H0. unfold not in H. apply H in H0. auto.
        * intros. assert (x = k). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. lia. } apply (InRoot_ghost x tg1 g tg2 g0 k v0) in H0. contradiction H.
Qed.

Lemma update_ghost_tree_with_insert2: forall x v tg g1 g2 g_root, ((In_ghost x tg) /\ (sorted_ghost_tree tg)) -> (find_ghost_set (insert_ghost x v tg g1 g2) g_root) =  (find_ghost_set tg g_root).
Proof.
intros. destruct H. revert dependent g_root. induction tg.
 + intros. inversion H.
 + intros. inversion H.
    -  simpl. destruct (x <? k) eqn:E2. { apply Z.ltb_lt in E2. lia. } { destruct (k <? x) eqn:E3. {apply Z.ltb_lt in E3. lia. } { simpl. reflexivity. } }
    - simpl. destruct (x <? k) eqn:E2.
      * simpl. rewrite IHtg1. reflexivity. apply H2. inversion H0. apply H12.
      * destruct (k <? x) eqn:E3. { inversion H0. unfold gt_ghost in H16. apply H16 in H2. apply Z.ltb_lt in E3. lia. } { simpl. reflexivity. }
    - simpl. destruct (x <? k) eqn:E2.
      * inversion H0. unfold lt_ghost in H17. apply H17 in H2. apply Z.ltb_lt in E2. lia.
      * destruct (k <? x) eqn:E3. { simpl. rewrite IHtg2. reflexivity. apply H2. inversion H0. apply H15. } { simpl. reflexivity. }
Qed.

Inductive IsEmptyGhostNode (rn : range * option ghost_info) :  (@ghost_tree val) -> range -> Prop :=
 | InEmptyGhostTree rn1 : (rn = (rn1,@None ghost_info)) -> IsEmptyGhostNode rn E_ghost rn1
 | InLeftGhostSubTree l g1 x v r g2  n1 n2 :  IsEmptyGhostNode rn l (n1, Finite_Integer x) -> IsEmptyGhostNode rn (T_ghost l g1 x v r g2) (n1,n2)
 | InRightGhostSubTree l g1 x v r g2 n1 n2 :  IsEmptyGhostNode rn r (Finite_Integer x, n2) -> IsEmptyGhostNode rn (T_ghost l g1 x v r g2) (n1,n2).
Local Hint Constructors IsEmptyGhostNode : core.

Definition keys_in_range_ghost (t : @ghost_tree val) r := forall k, In_ghost k t -> key_in_range k r = true.

Lemma keys_in_range_ghost_subtrees : forall t1 t2 g1 g2 k v r, keys_in_range_ghost (T_ghost t1 g1 k v t2 g2) r -> sorted_ghost_tree (T_ghost t1 g1 k v t2 g2) ->
  key_in_range k r = true /\ keys_in_range_ghost t1 (r.1, Finite_Integer k) /\ keys_in_range_ghost t2 (Finite_Integer k, r.2).
Proof.
  intros. inv H0. split3.
  - apply H; constructor; auto.
  - intros ??.
    specialize (H k0); spec H.
    { apply InLeft_ghost; auto. }
    apply H9 in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [->]; lia.
  - intros ??.
    specialize (H k0); spec H.
    { apply InRight_ghost; auto. }
    apply H10 in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [? H1].
    simpl in *; rewrite H1; lia.
Qed.

Lemma ghost_range_inside_ghost_range : forall r r_root tg, IsEmptyGhostNode r tg r_root -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg -> range_incl r.1 r_root = true.
Proof.
  intros; revert dependent r_root.
  induction tg; intros; inv H.
  - apply range_incl_refl.
  - eapply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); [|auto].
    inv H1.
    eapply range_incl_trans; [apply IHtg1; eauto 1|].
    unfold key_in_range in H.
    unfold range_incl.
    rewrite less_than_equal_refl.
    apply less_than_to_less_than_equal.
    apply andb_prop in H as [_ ->]; auto.
  - eapply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); [|auto].
    inv H1.
    eapply range_incl_trans; [apply IHtg2; eauto 1|].
    unfold key_in_range in H.
    unfold range_incl.
    rewrite less_than_equal_refl andb_true_r.
    apply less_than_to_less_than_equal.
    apply andb_prop in H as [-> _]; auto.
Qed.

Notation public_half := (public_half').

Lemma ghost_tree_insert: forall tg g_root g_in x v r_root
  (Hin : Ensembles.In (find_ghost_set tg g_root) g_in)
  (Hrange : keys_in_range_ghost tg r_root) (Hsorted : sorted_ghost_tree tg),
  ghost_tree_rep tg g_root r_root  |-- EX r : range, EX o : option ghost_info, !!(range_incl r r_root = true) && public_half g_in (r, Some o) *
  (* insert *)
  ((!! (key_in_range x r = true) --> ALL g1 g2 : gname, match o with
  | None => public_half g_in (r, Some (Some(x,v,g1,g2))) * public_half g1 (fst r, Finite_Integer x, Some (@None ghost_info)) * public_half g2 (Finite_Integer x, snd r, Some (@None ghost_info)) -*
    (!! IsEmptyGhostNode (r,o) tg r_root && ghost_tree_rep (insert_ghost x v tg g1 g2) g_root r_root)
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
    { apply range_incl_refl. }
    apply andp_right.
    * rewrite <- imp_andp_adjoint; Intros.
      apply allp_right; intro g1. apply allp_right; intro g2. rewrite <- wand_sepcon_adjoint. destruct r_root; entailer!; auto.
    * apply wand_refl_cancel_right.
  - apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
    inv Hsorted; inv Hin. destruct r_root; inv H2.
    * sep_apply IHtg1; clear IHtg1 IHtg2.
      Intros r o; Exists r o; entailer!.
      { destruct r; unfold range_incl in *.
        apply andb_prop in H2 as [->]; simpl in *.
        eapply less_than_to_less_than_equal, less_than_equal_less_than_trans; [eauto|].
        apply andb_prop in H as []; auto. }
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
           split; auto; apply InLeftGhostSubTree.
      + iDestruct "IH" as "[_ IH]".
        iIntros "H"; iSpecialize ("IH" with "H"); iFrame.
    * sep_apply IHtg2; clear IHtg1 IHtg2.
      Intros r o; Exists r o; entailer!.
      { destruct r; unfold range_incl in *.
        apply andb_prop in H2 as [? ->]; simpl in *.
        rewrite andb_true_iff; split; auto.
        eapply less_than_to_less_than_equal, less_than_less_than_equal_trans with (b := Finite_Integer _); [|eauto].
        apply andb_prop in H as []; auto. }
      iIntros "[[IH root] tree1]"; iSplit.
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
           split; auto; apply InRightGhostSubTree.
      + iDestruct "IH" as "[_ IH]".
        iIntros "H"; iSpecialize ("IH" with "H"); iFrame.
    * inv H2. Exists r_root (Some (k, v0, g, g0)).
      destruct r_root; entailer!.
      { apply range_incl_refl. }
      apply andp_right.
      + rewrite <- imp_andp_adjoint; Intros.
        apply allp_right; intro g1. apply allp_right; intro g2.
        rewrite <- wand_sepcon_adjoint; Intros; entailer!.
        { apply InRoot_ghost; auto. }
        destruct (x <? x) eqn: E1; try lia.
        simpl; entailer!.
      + rewrite <- wand_sepcon_adjoint; cancel.
Qed.

Lemma key_not_exist_in_tree: forall tg r_root d x (Hempty : IsEmptyGhostNode d tg r_root)
  (Hrange : keys_in_range_ghost tg r_root) (Hsorted : sorted_ghost_tree tg),
  key_in_range x d.1 = true -> ~ In_ghost x tg.
Proof.
  intros. revert dependent r_root. induction tg; intros.
  { intros X; inv X. }
  apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
  intros X. inv Hsorted. inv Hempty.
  - exploit IHtg1; eauto.
    apply ghost_range_inside_ghost_range in H14; auto.
    eapply key_in_range_incl in H; eauto.
    unfold key_in_range in H.
    inv X; auto.
    * simpl in H; lia.
    * specialize (H12 _ H4); simpl in H; lia.
  - exploit IHtg2; eauto.
    apply ghost_range_inside_ghost_range in H14; auto.
    eapply key_in_range_incl in H; eauto.
    unfold key_in_range in H.
    inv X; auto.
    * simpl in H; lia.
    * specialize (H11 _ H4); simpl in H; lia.
Qed.

Lemma In_pure : forall tg x, In x (find_pure_tree tg) <-> In_ghost x tg.
Proof.
  intros; induction tg; simpl.
  - split; inversion 1.
  - split; intros X; inv X.
    * constructor; auto.
    * apply InLeft_ghost, IHtg1; auto.
    * apply InRight_ghost, IHtg2; auto.
    * constructor; auto.
    * apply InLeft, IHtg1; auto.
    * apply InRight, IHtg2; auto.
Qed.

Lemma sorted_pure_sorted_ghost: forall t tg, find_pure_tree tg = t -> sorted_tree t -> sorted_ghost_tree tg.
Proof.
  intros.
  revert dependent t.
  induction tg.
  - intros. simpl in H0. apply Sorted_Empty_Ghost.
  - intros. simpl in H; subst. inv H0. apply Sorted_Ghost_Tree; eauto.
    * unfold gt, gt_ghost in *; intros ??%In_pure; auto.
    * unfold lt, lt_ghost in *; intros ??%In_pure; auto.
Qed.

Lemma both_halves_join : forall g a, my_half g gsh1 a * public_half g a = both_halves a g.
Proof.
  intros; rewrite <- both_halves_join.
  unfold public_half'; erewrite <- sepcon_assoc, my_half_join; eauto with share.
  repeat constructor; hnf; simpl.
  symmetry; apply merge_id.
Qed.

Lemma tree_rep_insert: forall t g g_root g_in x v ,
  sorted_tree t -> tree_rep g g_root t * in_tree g g_in |-- EX r, EX o, public_half g_in (r, Some o) *
  ((|==> (EX g1 g2:gname, (!!(o = None /\ key_in_range x r = true) && public_half g_in (r, Some (Some(x,v,g1,g2)))) -* tree_rep g g_root (insert x v t) * my_half g1 gsh1 (r.1, Finite_Integer x, Some (@None ghost_info)) * my_half g2 gsh1 (Finite_Integer x, r.2, Some (@None ghost_info)) *  in_tree g g_in * in_tree g g1 * in_tree g g2))%I
    && (|==> (ALL g1 g2:gname, ALL (v0:val), (!!(o = Some(x,v0,g1,g2) /\ (key_in_range x r = true)) &&  public_half g_in (r, Some (Some(x,v, g1,g2)))) -*  tree_rep g g_root (insert x v t) *  in_tree g g_in))%I
   && (public_half g_in (r, Some o) -* (tree_rep g g_root t * in_tree g g_in))).
Proof.
  intros.
  unfold tree_rep at 1. Intros tg.
  sep_apply node_exist_in_tree; Intros.
  assert (keys_in_range_ghost tg (Neg_Infinity, Pos_Infinity)).
  { intros ??; auto. }
  assert (sorted_ghost_tree tg).
  { eapply sorted_pure_sorted_ghost; eauto. }
  rewrite -> (ghost_tree_insert tg g_root g_in x v) by auto.
  Intros r o. Exists r o. cancel.
  apply andp_right; [apply andp_right|].
  - erewrite update_ghost_ref. iIntros "(>H1 & [H2 _])". iDestruct "H1" as (g1 g2) "(((((H1 & H3) & H4) & H5) & H6) & H7)". (*instantiate( 2 :=  (n1, Finite_Integer x, Some (@None ghost_info))). instantiate(1 :=  (Finite_Integer x, n2, Some (@None ghost_info))).*)
      rewrite <- !both_halves_join. iDestruct "H1" as "(H1 & H1')". iDestruct "H3" as "(H3 & H3')". iModIntro. iExists g1. iExists g2. iIntros "([% %] & H')"; subst. iSpecialize ("H2" with "[%]"); first done. iSpecialize ("H2" $! g1 g2 with "[$H' $H1' $H3']").
      unfold tree_rep. rewrite !exp_sepcon1. iExists (insert_ghost x v tg g1 g2). iDestruct "H2" as "[% H2]". rewrite update_ghost_tree_with_insert. iFrame. iSplit;auto.
      * iPureIntro; apply insert_preserved_in_ghost_tree; auto.
      * eapply key_not_exist_in_tree; eauto.
      * apply find_ghost_set_finite.
  - iIntros "((H1 & H2) & [H3 _]) !>". iIntros (g1 g2 v0) "[[% %] H]"; subst.
    iSpecialize ("H3" with "[%]"); first done. iSpecialize ("H3" $! g1 g2 with "[$H]"); first done.
    unfold tree_rep. rewrite !exp_sepcon1. iExists (insert_ghost x v tg g1 g2). iDestruct "H3" as "[% H3]". rewrite -> update_ghost_tree_with_insert2 by auto. iFrame.
    iSplit; auto; iPureIntro; apply insert_preserved_in_ghost_tree; auto.
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
         tree_rep g g_root E).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH lock: val, b: val, gv: globals, g: gname, g_root: gname, BST: tree
  PRE  [ tptr (tptr t_struct_tree_t) ]
       PROP()
       PARAMS (b) GLOBALS (gv)
       SEP (mem_mgr gv; nodebox_rep g g_root lsh1 lock b;
              (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) b;
              malloc_token Ews (tptr t_struct_tree_t) b;
              tree_rep g g_root BST)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH lock: val, p: val, gv : globals, g: gname, g_root: gname
  PRE  [ tptr t_struct_tree_t ]
       PROP()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv;
            ltree g g_root lsh1 p lock)
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
  ATOMIC TYPE (rmaps.ConstType ( val *  share * val * Z * val * globals*gname* gname)) OBJ BST INVS base.empty base.top
  WITH  b, sh, lock, x, v, gv, g, g_root
  PRE [ tptr (tptr t_struct_tree_t), tint, tptr tvoid ]
          PROP ( readable_share sh; Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v; is_pointer_or_null lock )
          PARAMS (b; Vint (Int.repr x); v) GLOBALS ( gv )
          SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) | (!!(sorted_tree BST)&&tree_rep g g_root  BST )
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (!!(sorted_tree (insert x v BST))&&tree_rep g g_root  (insert x v BST) ).

Program Definition delete_spec :=
 DECLARE _delete
 ATOMIC TYPE (rmaps.ConstType (_ * _ * _ * _ * _ * _ * _))
         OBJ BST INVS base.empty base.top
 WITH b, x, lock, gv, sh, g, g_root
 PRE  [ tptr (tptr t_struct_tree_t), tint]
    PROP (Int.min_signed <= x <= Int.max_signed; readable_share sh)
    PARAMS ( b;  Vint (Int.repr x)) GLOBALS ( gv )
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!!(sorted_tree BST) && tree_rep g g_root BST)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!!(sorted_tree (delete x BST)) && tree_rep g g_root (delete x BST)).

Time Program Definition pushdown_left_spec :=
 DECLARE _pushdown_left
 ATOMIC TYPE (rmaps.ConstType (val * val * val * Z * val * val * val * val * val * gname * gname * globals * (range) * gname * gname)) OBJ BST INVS base.empty base.top
 WITH p, tp, lockp,
       x, vx, locka, lockb, ta, tb,
       g, g_root, gv, range, ga, gb
  PRE [ tptr t_struct_tree_t ]
    PROP (Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) vx)
    PARAMS ( p ) GLOBALS ( gv )
    SEP (mem_mgr gv;
         in_tree g g_root;
         my_half g_root gsh1 (range, Some (Some (x, vx, ga, gb)));
         field_at Ews t_struct_tree_t [StructField _t] tp p;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (ta, tb))) tp;
         ltree g g_root lsh2 p lockp;
         ltree g ga lsh1 ta locka;
         ltree g gb lsh1 tb lockb;
         malloc_token Ews t_struct_tree tp;
         malloc_token Ews tlock lockp;
         malloc_token Ews t_struct_tree_t p) | (!!(sorted_tree BST) && tree_rep g g_root BST)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv) | (!!(sorted_tree (delete x BST)) && tree_rep g g_root (delete x BST)).

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * globals * gname * gname))
         OBJ BST INVS base.empty base.top
  WITH b, sh, lock, x, gv, g, g_root
  PRE [tptr (tptr t_struct_tree_t), tint]
    PROP (readable_share sh;
          Int.min_signed <= x <= Int.max_signed; is_pointer_or_null lock)
    PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
    SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) |
  (!! sorted_tree BST && tree_rep g g_root BST)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!! (sorted_tree BST /\ ret = lookup nullval x BST) && tree_rep g g_root BST).

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
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
    surely_malloc_spec;
    treebox_new_spec; tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec ;
    (* spawn_spec; thread_func_spec; *) main_spec
  ]).

Lemma node_rep_saturate_local:
   forall r p g g_current, node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof.
  intros. rewrite node_rep_def. Intros tp. entailer!.
Qed.
Local Hint Resolve node_rep_saturate_local: saturate_local.


Lemma node_rep_valid_pointer:
  forall t g g_current p, node_rep p g g_current t |-- valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp. sep_apply field_at_valid_ptr0; auto. entailer!.
Qed.
Local Hint Resolve node_rep_valid_pointer : valid_pointer.

Lemma tree_rep_R_saturate_local:
   forall t p g_children g, tree_rep_R p t g_children g |-- !! is_pointer_or_null p.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec p nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Local Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec tp nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!.
Qed.
Local Hint Resolve tree_rep_R_valid_pointer : valid_pointer.


Lemma ltree_saturate_local:
  forall g g_root lsh p lock, ltree g g_root lsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Local Hint Resolve ltree_saturate_local: saturate_local.


Definition insert_inv (b: val)  (lock: val)  (sh: share) (x: Z) (v: val) (g_root: gname) gv (inv_names : invG) (Q : mpred) (g: gname) : environ -> mpred :=
(EX r : node_info, EX g_in : gname, EX lock_in : val, EX np : val,
PROP (key_in_range x (fst r) = true)
LOCAL (temp _l lock_in; temp _tgt np; temp _t b; temp _x (vint x); temp _value v; gvars gv)
SEP (nodebox_rep g g_root sh lock b;
  field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
  malloc_token Ews tlock lock_in;
  node_rep np g g_in r; my_half g_in gsh1 r;
 |> lock_inv lsh2 lock_in  (node_lock_inv g np g_in lock_in);
atomic_shift (λ BST : @tree val, !! sorted_tree BST && tree_rep g g_root BST ) ∅ ⊤
  (λ (BST : @tree val) (_ : ()),
     fold_right_sepcon [!! sorted_tree  (insert x v BST) && tree_rep g g_root (insert x v BST) ])
  (λ _ : (), Q); mem_mgr gv ))%assert.

 Definition lookup_inv (b: val) (lock:val) (sh: share) (x: Z) gv (inv_names : invG)
           (Q : val -> mpred) (g g_root:gname) : environ -> mpred :=
  (EX tp: val, EX np: val, EX r : node_info,
   EX g_in :gname, EX lock_in: val,
   PROP (key_in_range x r.1 = true)
   LOCAL (temp _p tp; temp _l lock_in; temp _tgt np; temp _t b;
          temp _x (vint x); gvars gv)
   SEP (nodebox_rep g g_root sh lock b;
       field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np;
       |> lock_inv lsh2 lock_in (node_lock_inv g np g_in lock_in);
       field_at Ews t_struct_tree_t [StructField _t] tp np;
       malloc_token Ews t_struct_tree_t np; in_tree g g_in;
       tree_rep_R tp r.1 r.2 g; my_half g_in gsh1 r; malloc_token Ews tlock lock_in;
       atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep g g_root BST) ∅ ⊤
                    (λ (BST : tree) (ret : val),
                     fold_right_sepcon
                       [!! (sorted_tree BST /\ ret = lookup nullval x BST) &&
                        tree_rep g g_root BST]) Q;
       mem_mgr gv))%assert.

Lemma tree_rep_R_nullval: forall t g_info g,
  tree_rep_R nullval t (g_info: option (option ghost_info)) g |-- !! (g_info = Some (@None ghost_info)).
Proof.
  intros.
  unfold tree_rep_R. simpl. entailer!.
Qed.
Local Hint Resolve tree_rep_R_nullval: saturate_local.

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

Lemma range_info_in_tree_EmptyRange: forall ri range tg,
    range_info_in_tree (ri, Some None) range tg -> EmptyRange ri (find_pure_tree tg) range.
Proof.
  intros. destruct range as [l r]. revert tg l r H.
  induction tg; intros; inv H; simpl in *.
  - inv H0. now apply InEmptyTree.
  - inv H1.
  - specialize (IHtg1 _ _ H1). now apply InLeftSubTree.
  - specialize (IHtg2 _ _ H1). now apply InRightSubTree.
Qed.

Lemma ghost_tree_rep_public_half_ramif: forall tg g_root r_root g_in,
    Ensembles.In (find_ghost_set tg g_root) g_in ->
    ghost_tree_rep tg g_root r_root |--
                   EX r: node_info,
  !! (range_info_in_tree r r_root tg) &&
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

Lemma range_info_in_tree_In: forall tg x v ga gb range r_root,
    range_info_in_tree (range, Some (Some (x, v, ga, gb))) r_root tg ->
    In x (find_pure_tree tg).
Proof.
  intros. revert tg range r_root H. induction tg; intros. 1: inversion H; inversion H0.
  simpl. inv H.
  - inv H1. now apply InRoot.
  - apply InLeft. eapply IHtg1; eauto.
  - apply InRight. eapply IHtg2; eauto.
Qed.

Lemma sorted_tree_look_up_in: forall x v ga gb tg range r_root,
    sorted_tree (find_pure_tree tg) ->
    range_info_in_tree (range, Some (Some (x, v, ga, gb))) r_root tg ->
    lookup nullval x (find_pure_tree tg) = v.
Proof.
  intros. revert tg range r_root H H0. induction tg; intros.
  1: inversion H0; inversion H1. inv H. simpl. inv H0.
  - inv H1. now rewrite Z.ltb_irrefl.
  - specialize (IHtg1 _ _ H5 H1). red in H7. apply range_info_in_tree_In in H1.
    specialize (H7 _ H1). cut (x <? k = true).
    + intros. now rewrite H.
    + rewrite Z.ltb_lt. lia.
  - specialize (IHtg2 _ _ H6 H1). red in H8. apply range_info_in_tree_In in H1.
    specialize (H8 _ H1). assert (k <? x = true) by now rewrite Z.ltb_lt. rewrite H.
    intros. assert (x <? k = false) by (rewrite Z.ltb_ge; lia). now rewrite H0.
Qed.

Lemma range_info_in_tree_not_In: forall tg x range r_root,
    sorted_tree (find_pure_tree tg) -> key_in_range x range = true ->
    keys_in_range (find_pure_tree tg) r_root ->
    range_info_in_tree (range, Some None) r_root tg -> ~ In x (find_pure_tree tg).
Proof.
  intros. revert tg r_root H H1 H2. induction tg; intros; simpl in *.
  { intro; inv H3. }
  inv H. inv H2. { inv H3. }
  - assert (forall y : key, In y (find_pure_tree tg1) ->
                            key_in_range y (r_root.1, Finite_Integer k) = true). {
      intros. rewrite andb_true_iff. split.
      - assert (key_in_range y r_root = true) by now apply H1, InLeft.
        destruct r_root as [r1 r2]. simpl. apply andb_true_iff in H2.
        now destruct H2.
      - red in H9. simpl. specialize (H9 _ H). rewrite Z.ltb_lt. lia. }
    assert (range_incl range (r_root.1, Finite_Integer k) = true). {
        eapply range_inside_range with (t := find_pure_tree tg1); auto.
        now apply range_info_in_tree_EmptyRange. } destruct range as [r1 r2].
    simpl in H2. apply andb_true_iff in H2. destruct H2.
    apply andb_true_iff in H0. destruct H0. specialize (IHtg1 _ H7 H H3).
    intro. inv H6; auto.
    + assert (less_than (Finite_Integer k) (Finite_Integer k) = true) by
          (eapply less_than_less_than_equal_trans; eauto).
      rewrite less_than_irrefl in H6. inv H6.
    + assert (less_than (Finite_Integer x) (Finite_Integer k) = true) by
          (eapply less_than_less_than_equal_trans; eauto). simpl in H6.
      apply Z.ltb_lt in H6. specialize (H10 _ H12). lia.
  - assert (forall y : key, In y (find_pure_tree tg2) ->
                            key_in_range y (Finite_Integer k, r_root.2) = true). {
      intros. rewrite andb_true_iff. split.
      - red in H10. simpl. specialize (H10 _ H). now rewrite Z.ltb_lt.
      - assert (key_in_range y r_root = true) by now apply H1, InRight.
        destruct r_root as [r1 r2]. simpl. apply andb_true_iff in H2.
        now destruct H2. }
    assert (range_incl range (Finite_Integer k, r_root.2) = true). {
        eapply range_inside_range with (t := find_pure_tree tg2); auto.
        now apply range_info_in_tree_EmptyRange. } destruct range as [r1 r2].
    apply andb_true_iff in H2. destruct H2. apply andb_true_iff in H0. destruct H0.
    specialize (IHtg2 _ H8 H H3). intro. inv H6; auto.
    + assert (less_than (Finite_Integer k) (Finite_Integer k) = true) by
          (eapply less_than_equal_less_than_trans; eauto).
      rewrite less_than_irrefl in H6. inv H6.
    + assert (less_than (Finite_Integer k) (Finite_Integer x) = true) by
          (eapply less_than_equal_less_than_trans; eauto).
      simpl in H6. apply Z.ltb_lt in H6. specialize (H9 _ H12). lia.
Qed.

Lemma range_incl_tree_rep_R: forall tp r1 r2 g_info g,
    range_incl r1 r2 = true ->
    tree_rep_R tp r1 g_info g |-- tree_rep_R tp r2 g_info g.
Proof.
  intros. unfold tree_rep_R. if_tac. 1: cancel. Intros ga gb x v pa pb locka lockb.
  Exists ga gb x v pa pb locka lockb. entailer!.
  destruct (key_in_range x r1) eqn: ?. 2: easy.
  erewrite range_incl_key_in_range; eauto.
Qed.

Lemma in_tree_left_range:
  ∀ (B: Type) (b: tree -> B -> mpred) (Q : B → mpred) (x x0: Z) (g g_root : gname)
    (inv_names : invG) (v: val) (g_in ga gb: gname) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> x < x0 ->
    atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep g g_root BST) ∅ ⊤
                 b Q * my_half g_in gsh1 r * in_tree g g_in * my_half ga gsh1 a
    |-- atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep g g_root BST) ∅ ⊤
    b Q * my_half g_in gsh1 r *
    (EX ba, !! (less_than_equal ba r.1.1 = true /\
                range_incl a.1 (ba, Finite_Integer x0) = true) &&
            (in_tree g g_in * my_half ga gsh1 (ba, Finite_Integer x0, a.2))).
Proof.
   intros. rewrite sepcon_assoc. apply sync_rollback. intros t.
  unfold tree_rep at 1. Intros tg.
  assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in). {
    sep_apply node_exist_in_tree. entailer!. }
  sep_apply (ghost_tree_rep_public_half_ramif2 _ _ (Neg_Infinity, Pos_Infinity) _ H4).
  rewrite distrib_orp_sepcon. apply orp_left.
  - Intros r0. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (@None ghost_info)). unfold public_half'; cancel. apply imp_andp_adjoint. Intros.
    destruct r as [? rS]. simpl in H0. subst rS. if_tac in H5; try discriminate.
    destruct H5; inv H5. inv H7. inv H9.
  - Intros r0 x1 v0 ga0 gb0 i1 i2.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (Some (x1, v0, ga0, gb0))). unfold public_half'; cancel. apply imp_andp_adjoint.
    Intros. rewrite if_false in H5; auto with share. destruct H5. inv H5.
    simpl fst in *. simpl snd in *. rewrite H0 in H7.
    inv H7. 2: inv H9. clear H8. rewrite <- wand_sepcon_adjoint.
    sep_apply (public_part_update ga0 gsh1 a (r0.1, Finite_Integer x1, Some i1)
                                  (r0.1, Finite_Integer x1, a.2)
                                  (r0.1, Finite_Integer x1, Some i1)).
    + intros. hnf in H3. hnf. simpl in *. destruct H3. split; auto. hnf.
      hnf in H3. symmetry in H3. symmetry. rewrite merge_comm in H3.
      rewrite merge_comm. eapply merge_again; eauto.
    + Intros. rewrite if_false in H3; auto with share.
      eapply derives_trans; [apply ghost_seplog.bupd_frame_r |].
      apply ghost_seplog.bupd_mono. apply andp_right; [now apply prop_right|].
      Exists r0.1. entailer!.
      * destruct H3 as [c ?]. hnf in H3. destruct H3 as [? _]. hnf in H3.
        symmetry in H3. apply merge_range_incl in H3. simpl in H3. split; auto.
        clear -H6. hnf in H6. symmetry in H6. apply merge_range_incl in H6.
        destruct r. simpl in *. destruct g, r0. simpl in H6.
        apply andb_true_iff in H6. simpl. now destruct H6.
      * unfold tree_rep. Exists tg. entailer!.
        iIntros "[[[[[[? ?] ?] ?] ?] H] ?]".
        iApply "H"; iFrame.
Qed.

Lemma in_tree_right_range:
  ∀ (B: Type) (b: tree -> B -> mpred) (Q : B → mpred) (x x0: Z) (g g_root : gname)
    (inv_names : invG) (v: val) (g_in ga gb: gname) (r a: node_info),
    key_in_range x r.1 = true -> r.2 = Some (Some (x0, v, ga, gb)) -> x0 < x ->
    atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep g g_root BST) ∅ ⊤
                 b Q * my_half g_in gsh1 r * in_tree g g_in * my_half gb gsh1 a
    |-- atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep g g_root BST) ∅ ⊤
    b Q * my_half g_in gsh1 r *
    (EX ta, !! (less_than_equal r.1.2 ta = true /\
                range_incl a.1 (Finite_Integer x0, ta) = true) &&
            (in_tree g g_in * my_half gb gsh1 (Finite_Integer x0, ta, a.2))).
Proof.
 intros. rewrite sepcon_assoc. apply sync_rollback. intros t.
  unfold tree_rep at 1. Intros tg.
  assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in). {
    sep_apply node_exist_in_tree. entailer!. }
  sep_apply (ghost_tree_rep_public_half_ramif2 _ _ (Neg_Infinity, Pos_Infinity) _ H4).
  rewrite distrib_orp_sepcon. apply orp_left.
  - Intros r0. eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (@None ghost_info)). unfold public_half'; cancel. apply imp_andp_adjoint. Intros.
    destruct r as [? rS]. simpl in H0. subst rS. if_tac in H5; try discriminate.
    destruct H5; inv H5. inv H7. inv H9.
  - Intros r0 x1 v0 ga0 gb0 i1 i2.
    eapply derives_trans; [|apply ghost_seplog.bupd_intro].
    Exists (r0, Some (Some (x1, v0, ga0, gb0))). unfold public_half'; cancel. apply imp_andp_adjoint.
    Intros. rewrite if_false in H5; auto with share. destruct H5. inv H5.
    simpl fst in *. simpl snd in *. rewrite H0 in H7.
    inv H7. 2: inv H9. clear H8. rewrite <- wand_sepcon_adjoint.
    sep_apply (public_part_update gb0 gsh1 a (Finite_Integer x1, r0.2, Some i2)
                                  (Finite_Integer x1, r0.2, a.2)
                                  (Finite_Integer x1, r0.2, Some i2)).
    + intros. hnf in H3. hnf. simpl in *. destruct H3. split; auto. hnf.
      hnf in H3. symmetry in H3. symmetry. rewrite merge_comm in H3.
      rewrite merge_comm. eapply merge_again; eauto.
    + Intros. rewrite if_false in H3; auto with share.
      eapply derives_trans; [apply ghost_seplog.bupd_frame_r |].
      apply ghost_seplog.bupd_mono. apply andp_right; [now apply prop_right|].
      Exists r0.2. entailer!.
      * destruct H3 as [c ?]. hnf in H3. destruct H3 as [? _]. hnf in H3.
        symmetry in H3. apply merge_range_incl in H3. simpl in H3. split; auto.
        clear -H6. hnf in H6. symmetry in H6. apply merge_range_incl in H6.
        destruct r. simpl in *. destruct g, r0. simpl in H6.
        apply andb_true_iff in H6. simpl. now destruct H6.
      * unfold tree_rep. Exists tg. entailer!.
        iIntros "[[[[[[? ?] ?] ?] ?] H] ?]".
        iApply "H"; iFrame.
Qed.

Lemma node_info_join_Some:
  forall (r0 r1: node_info) (range: @G range_ghost) (g_info: option ghost_info),
    @sepalg.join node_info (@Join_G node_ghost) (range, Some g_info) r1 r0 ->
    r0.2 = Some g_info.
Proof.
  intros. destruct r1 as [range1 r1]. destruct r0 as [range0 r0].
  hnf in H. simpl in *. destruct H. inv H0; auto. inv H2.
Qed.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g np g_root lock)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.
  Intros a. destruct a as (p, o). rewrite node_rep_def. Intros tp.
  forward. (* _p = (_tgt -> _t); *) simpl fst. simpl snd.
  forward_while (lookup_inv b lock sh x gv inv_names Q g g_root).
  (* while (_p != (tptr tvoid) (0)) *)
  - (* current status implies lookup_inv *)
    unfold lookup_inv. Exists tp np (Neg_Infinity, Pos_Infinity, o) g_root lock.
    gather_SEP (my_half g_root gsh1 _) (my_half g_root gsh2 _).
    rewrite (my_half_range_inf _ _ (Neg_Infinity, Pos_Infinity)). entailer. cancel.
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
      forward_call (locka, lsh1, (node_lock_inv g pa ga locka)). (* _acquire(_l); *)
      unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
      fold (node_lock_inv g pa ga locka). unfold node_lock_inv_pred, sync_inv.
      Intros a. rewrite node_rep_def. Intros tpa.
      forward. (* _p = (_tgt -> _t); *)
      gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _)
                 (in_tree g g_in) (my_half ga _ _).
      sep_apply (in_tree_left_range
                   val
                   (λ (BST : tree) (ret : val),
                    !! (sorted_tree BST ∧ ret = lookup nullval x BST) &&
                    tree_rep g g_root BST * emp)
                   Q x x0 g g_root inv_names v g_in ga gb r a). Intros ba.
      forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                    node_lock_inv g np0 g_in lock_in). (* _release2(_l_old); *)
      * lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
        Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
        rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
        unfold ltree. entailer!. rewrite sepcon_comm. rewrite !later_sepcon. cancel.
      * destruct a as [rangea a]. simpl fst in *. simpl snd in *.
        Exists ((((tpa, pa), (ba, Finite_Integer x0, a)), ga), locka).
        simpl fst. simpl snd. sep_apply (range_incl_tree_rep_R tpa _ _ a g H10).
        entailer!. simpl. rewrite andb_true_iff. clear -H2 H7 H9. split.
        2: now rewrite Z.ltb_lt. destruct r. destruct g. simpl fst in *.
        unfold key_in_range in H2. apply andb_true_iff in H2. destruct H2.
        eapply less_than_equal_less_than_trans; eauto.
    + forward_if. (* if (_y < _x) { *)
      * forward. (* _tgt = (_p -> _right); *)
        forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
        forward. (* _l = (_tgt -> _lock); *)
        forward_call (lockb, lsh1, (node_lock_inv g pb gb lockb)). (* _acquire(_l); *)
        unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
        fold (node_lock_inv g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
        Intros a. rewrite node_rep_def. Intros tpb.
        forward. (* _p = (_tgt -> _t); *)
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _)
                 (in_tree g g_in) (my_half gb _ _).
        sep_apply (in_tree_right_range
                   val
                   (λ (BST : tree) (ret : val),
                    !! (sorted_tree BST ∧ ret = lookup nullval x BST) &&
                    tree_rep g g_root BST * emp)
                   Q x x0 g g_root inv_names v g_in ga gb r a). Intros ta.
        forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                      node_lock_inv g np0 g_in lock_in). (* _release2(_l_old__1); *)
        -- lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
           Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
           rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
           unfold ltree. entailer!. rewrite !later_sepcon. cancel.
        -- destruct a as [rangea a]. simpl fst in *. simpl snd in *.
        Exists ((((tpb, pb), (Finite_Integer x0, ta, a)), gb), lockb).
        simpl fst. simpl snd. sep_apply (range_incl_tree_rep_R tpb _ _ a g H11).
        entailer!. unfold key_in_range. rewrite andb_true_iff. clear -H2 H8 H10.
        split. 1: simpl; now rewrite Z.ltb_lt. destruct r, g. simpl fst in *.
        simpl in H10. unfold key_in_range in H2. apply andb_true_iff in H2.
        destruct H2. eapply less_than_less_than_equal_trans; eauto.
      * forward. (* _v = (_p -> _value); *)
        assert (x0 = x) by lia. subst x0. clear H6 H7.
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g _).
        viewshift_SEP 0 (EX y, Q y *
                               (!!(y = v) && (in_tree g g_in *
                                              my_half g_in gsh1 r))). {
          go_lower. apply sync_commit_same. intro t. unfold tree_rep at 1. Intros tg.
          assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in). {
            sep_apply node_exist_in_tree. entailer!. }
          sep_apply (ghost_tree_rep_public_half_ramif
                       _ _ (Neg_Infinity, Pos_Infinity) _ H9). Intros r0.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. unfold public_half'; cancel.
          apply imp_andp_adjoint. Intros. rewrite if_false in H11; auto with share.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          destruct H11 as [r1 ?]. rewrite <- wand_sepcon_adjoint.
          eapply derives_trans; [|apply ghost_seplog.bupd_intro].
          Exists (lookup nullval x t). entailer. apply andp_right.
          - apply prop_right. destruct r as [range r2]. simpl in H3.
            rewrite H3 in H11. apply node_info_join_Some in H11.
            destruct r0 as [range0 r0]. simpl in H11. subst r0.
            eapply sorted_tree_look_up_in; eauto.
          - cancel. iIntros "[[[? H] ?] ?]".
            unfold tree_rep. iExists tg. iFrame; iSplit; auto.
            iApply "H"; iFrame. } Intros y. subst y.
        forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                      node_lock_inv g np0 g_in lock_in). (* _release2(_l); *)
        -- lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
           fold (node_lock_inv g np0 g_in lock_in). unfold node_lock_inv_pred.
           unfold sync_inv. Exists r. rewrite node_rep_def. Exists tp0. cancel.
           unfold tree_rep_R. rewrite if_false; auto.
           Exists ga gb x v pa pb locka lockb. entailer!.
        -- forward. Exists v. entailer!.
  - subst tp0. unfold tree_rep_R. simpl. Intros.
    gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g _).
    viewshift_SEP 0 (EX y, Q y *
                           (!! (y = nullval) && (in_tree g g_in *
                                                 my_half g_in gsh1 r))). {
      go_lower. apply sync_commit_same. intro t. unfold tree_rep at 1. Intros tg.
      assert_PROP (Ensembles.In (find_ghost_set tg g_root) g_in). {
        sep_apply node_exist_in_tree. entailer!. }
      sep_apply (ghost_tree_rep_public_half_ramif
                   _ _ (Neg_Infinity, Pos_Infinity) _ H6). Intros r0.
      eapply derives_trans; [|apply ghost_seplog.bupd_intro]. Exists r0. unfold public_half'; cancel.
      apply imp_andp_adjoint. Intros. rewrite if_false in H8; auto with share.
      eapply derives_trans; [|apply ghost_seplog.bupd_intro].
      destruct H8 as [r1 ?]. rewrite <- wand_sepcon_adjoint.
      eapply derives_trans; [|apply ghost_seplog.bupd_intro].
      Exists (lookup nullval x t). entailer!.
      - destruct r as [range r2]. simpl in H3. rewrite H3 in H8.
        apply lookup_not_in. pose proof H8. apply node_info_join_Some in H8.
        destruct r0 as [rg ?]. simpl in H8. subst g0.
        apply (range_info_in_tree_not_In _ _ rg (Neg_Infinity, Pos_Infinity)); auto.
        hnf in H5. destruct H5 as [? _]. simpl in H5. hnf in H5. symmetry in H5.
        apply merge_range_incl in H5. eapply range_incl_key_in_range; eauto.
        { apply in_range_infty. }
      - unfold tree_rep. Exists tg. entailer!. iIntros "[[? H] ?]"; iApply "H"; iFrame. } Intros y. subst y.
    forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                  node_lock_inv g np0 g_in lock_in). (* _release2(_l); *)
    + lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
      fold (node_lock_inv g np0 g_in lock_in). unfold node_lock_inv_pred.
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
  Time forward_call (l, Ews, node_lock_inv g' newt g_root' l).
  Local Typeclasses eauto := 10. (* Restore *)
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
  forward_call (l, lsh2, node_lock_inv_pred g' newt g_root' l, node_lock_inv g' newt g_root' l).
  { lock_props.
    setoid_rewrite node_lock_inv_def at 3.
    Exists (Neg_Infinity, Pos_Infinity, Some (@None ghost_info)).
    unfold_data_at (data_at Ews t_struct_tree_t _ _).
    rewrite node_rep_def. Exists (vint 0).
    erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
    cancel. simpl.
    rewrite <- ghost_part_ref_join.
    unfold in_tree; Exists (Tsh).
    rewrite <- (my_half_join
                  gsh1 gsh2 Tsh
                  ((Neg_Infinity, Pos_Infinity, Some (@None ghost_info)): node_info)
                  (Neg_Infinity, Pos_Infinity, @None (option ghost_info))).
    - cancel. unfold tree_rep_R; simpl. entailer!.
    - apply gsh1_gsh2_join.
    - hnf. simpl. split.
      + hnf. now simpl.
      + constructor.
    - apply gsh1_not_bot.
    - apply gsh2_not_bot. }
  forward.
  unfold nodebox_rep. unfold ltree.
  Exists p l g' g_root'. Exists newt. entailer!.
  erewrite <- data_at_share_join by eauto; cancel.
  unfold tree_rep. unfold ghost_ref.
  Exists (E_ghost : @ghost_tree val).
  simpl. entailer!. (* actually we probably want to change all the shares to quantified shares, or just
  change my_half and public_half to be forgetful in the first place -- but that will prevent delete! *)
Admitted.

Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  unfold ltree; Intros.
  forward.
  forward_call (lock, lsh1, node_lock_inv g p g_root lock).
  Local Typeclasses eauto := 5. (* For some reason 5 is faster than 4 and 6 is slower than 5 *)
  Time setoid_rewrite node_lock_inv_def at 2. Intros a; destruct a as (range, g_info).
  rewrite node_rep_def; Intros tp; simpl.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _p tp; temp _l lock; gvars gv; temp _tgp p)
    SEP (lock_inv lsh1 lock (node_lock_inv g p g_root lock);
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        malloc_token Ews t_struct_tree_t p; in_tree g g_root;
        my_half g_root gsh1 (range, g_info);
        field_at lsh2 t_struct_tree_t [StructField _lock] lock p;
        malloc_token Ews tlock lock;
        lock_inv lsh2 lock (node_lock_inv g p g_root lock);
        mem_mgr gv; field_at lsh1 t_struct_tree_t [StructField _lock] lock p)).
  unfold tree_rep_R; simpl.
  { if_tac.
    { Intros. contradiction. }
    { Intros ga gb x v pa pb locka lockb; clear H1.
      forward. (* p->left *)
      forward. (* p->right *)
      forward_call (t_struct_tree, tp, gv).
      { if_tac.
        - contradiction.
        - entailer!. }
      forward_call (locka, pa, gv, g, ga). (* tree_free(pa) *)
      forward_call (lockb, pb, gv, g, gb). (* tree_free(pb) *)
      entailer!. }}
  { forward.
    entailer!.
    unfold tree_rep_R.
    if_tac; Intros.
    - cancel.
    - contradiction. }
  forward_call (lock, Ews, lsh2, node_lock_inv_pred g p g_root lock, node_lock_inv g p g_root lock).
  { lock_props.
    rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
    entailer!. }
  forward_call (tlock, lock, gv).
  { if_tac; entailer!. }
  gather_SEP (in_tree _ _) (my_half _ _ _).
  viewshift_SEP 0 (emp).
  { go_lower. unfold in_tree; Intros sh; iIntros "[H1 H2]".
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
  forward_call (lock, np, gv, g, g_root).
  gather_SEP (tree_rep _ _ _).
  viewshift_SEP 0 (emp). {
    go_lower.
    unfold tree_rep. Intros tg.
    iIntros "[H1 H2]".
    iMod (ghost_tree_rep_dealloc with "H1"); iMod (own_dealloc with "H2"); auto.
  }
  gather_SEP (my_half _ _ _).
  viewshift_SEP 0 (emp). {
    go_lower. iIntros "H". iMod (own_dealloc with "H"); auto. }
  forward_call (tptr t_struct_tree_t, b, gv).
  { destruct (eq_dec b nullval).
    { entailer!. }
    { erewrite <- (data_at__share_join _ _ Ews) by eauto; entailer!. }}
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

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree .
  Intros np.
  forward.
  forward.
  forward_call (lock, sh, (node_lock_inv g np g_root lock)).
   eapply semax_pre; [
    | apply (semax_loop _ (insert_inv b  lock sh x v g_root gv inv_names Q g) (insert_inv b  lock sh  x v g_root gv  inv_names Q g) )].
  * (* Precondition *)
    unfold insert_inv.
    unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. unfold nodebox_rep, ltree. Intro r. destruct r as [p o].
    sep_apply (my_half_range_inf g_root p (Neg_Infinity, Pos_Infinity) o). Exists (Neg_Infinity, Pos_Infinity, o) g_root lock np. Exists np.
    rewrite node_rep_def. Intros tp. unfold node_lock_inv. rewrite node_rep_def. Exists tp. entailer!. sep_apply ( range_incl_tree_rep_R tp p (Neg_Infinity, Pos_Infinity) o g).
    apply range_incl_infty. auto.
  * (* Loop body *)
    unfold insert_inv.
    Intros  r g_in lock_in np0.
    forward. (* Sskip *)
    rewrite node_rep_def.
    Intros tp.
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
      simpl in H4. Intros.
     gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _  _)  (in_tree g  _).
         viewshift_SEP 0 (Q  * (EX g1 g2:gname, EX n1 n2:number, (!!(key_in_range x (n1,n2) = true) && my_half g_in gsh1 (n1, n2, Some (Some(x,v,g1,g2))) *  in_tree g  g_in * my_half g1 gsh1 (n1, Finite_Integer x, Some(@None ghost_info)) * my_half g2 gsh1 ( Finite_Integer x, n2, Some(@None ghost_info)) *  in_tree g  g1 * in_tree g  g2))).
         {  go_lower.
            eapply sync_commit_gen1.
            intros. iIntros "H". iDestruct "H" as "[H1 H2]". iDestruct "H2" as "[% H2]".
             iModIntro.  iPoseProof (tree_rep_insert with "[H1 H2]") as "Hadd".  instantiate(1:= x0 ). auto. iFrame. iDestruct "Hadd" as (r o0) "([Hmy H1] & H2)".
             iExists (r, Some o0). iFrame. iDestruct "H2" as "[[Hnew _] _]".  iIntros "%". iMod "Hnew". iDestruct "Hnew" as (g1 g2) "H". iModIntro. iExists (r, Some (Some(x,v,g1,g2))).
              iExists (r, Some (Some (x, v, g1, g2))).
              match goal with |-context[(|==> ?P)%logic] => change ((|==> P)%logic) with ((|==> P)%I) end. iSplit.
              { iPureIntro. intros.  destruct b0 as ((n3, n4), i).
                hnf. simpl. split. apply range_incl_join in H9.
                rewrite -> if_false in H8 by (apply gsh1_not_Tsh).
                destruct H8 as (? & J).
                simpl in *. hnf in *. unfold merge_range.
                subst; destruct H9 as [H4 H8].
                destruct r; apply andb_prop in H4 as []. apply andb_prop in H8 as []. f_equal.
                apply leq_entail_min_number; auto. apply leq_entail_max_number; auto.
                hnf in H9. simpl in H9. inv H9.
                rewrite if_false in H8. destruct H8 as [x1 Hr].
                apply node_info_join_Some in Hr. simpl in Hr. inv Hr.
                inv H11. apply sepalg.join_unit2. apply psepalg.None_unit. auto.
                inv H12. apply gsh1_not_Tsh.  }
                iIntros "(H1 & H2)". instantiate (1 := x). instantiate (1:= v).  iSpecialize ("H" with "[$H2 $Hmy]"). iSplit;auto.
              { iPureIntro. split. rewrite if_false in H8.
                destruct H8 as [x1 Hr]. subst o. apply node_info_join_Some in Hr.
                simpl in Hr. inv Hr; auto. apply gsh1_not_Tsh.
                rewrite if_false in H8. destruct H8 as [x1 Hr]. subst o.
                apply range_incl_join in Hr. destruct Hr. simpl in H4.
                destruct r; apply andb_prop in H4. unfold key_in_range in *.
                apply andb_prop in H3. destruct H3. apply andb_true_intro.
                destruct H4.  split.
                apply less_than_equal_less_than_trans with (b := n); auto.
                apply less_than_less_than_equal_trans with (b := n0); auto.
                apply gsh1_not_Tsh. }
               iDestruct "H" as "(((((H2 & H3) & H4) & H5) & H6) & H7)".
               iModIntro. rewrite !exp_sepcon1; iExists tt.
               rewrite !exp_sepcon2; iExists g1.
               rewrite !exp_sepcon2; iExists g2.
               apply (insert_sorted x v) in H7.
               rewrite !exp_sepcon2; iExists r.1.
               rewrite !exp_sepcon2; iExists r.2; destruct r; iFrame.
               iSplitL "H2". { iFrame; auto. }
               iFrame.
               rewrite -> if_false in H8 by apply gsh1_not_Tsh. destruct H8 as [x1 Hr].
               iSplit; auto; iPureIntro.
               apply range_incl_join in Hr as [].
               eapply key_in_range_incl; eauto. }
      Intros g1 g2 n1 n2.
      Typeclasses eauto:= 2.
      forward_call (l1, Ews, (node_lock_inv g p1' g1 l1)).
      Intros.
      forward. (*p1->lock = l1*)
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      Typeclasses eauto:= 6.
      forward_call (l1, lsh2,(node_lock_inv_pred g p1' g1 l1) , (node_lock_inv g p1' g1 l1)).
     { lock_props.
       unfold node_lock_inv at 4. rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (n1, Finite_Integer x,Some (@None ghost_info)).
       rewrite node_rep_def . Exists nullval.
       unfold_data_at 2%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }
     forward_call (tlock, gv).
      { simpl.  rewrite Z.max_r. repeat (split; auto); rep_lia. rep_lia. }
      Intros l2.
      forward_call (l2, Ews, (node_lock_inv g p2' g2 l2)).
      forward. (*p2->lock = l2*)
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      forward_call (l2, lsh2,(node_lock_inv_pred g p2' g2 l2), (node_lock_inv g p2' g2 l2)).
     { lock_props.
       unfold node_lock_inv at 5. rewrite selflock_eq .  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (Finite_Integer x,n2,Some (@None ghost_info)).
       rewrite node_rep_def . Exists nullval.
       unfold_data_at 1%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }
      forward_call (t_struct_tree, gv).
      Intros p'.
      forward. (* tgt->t=p; *)
      forward. (* p->key=x; *)
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      forward_call(lock_in, lsh2,(node_lock_inv_pred g np0 g_in lock_in),  (node_lock_inv g np0 g_in lock_in)).
      { lock_props.
        unfold node_lock_inv at 4.  rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists (n1, n2, Some (Some(x,v,g1,g2))).
       rewrite node_rep_def. Exists p'. unfold node_lock_inv.  cancel. unfold tree_rep_R. assert_PROP (p' <> nullval). { entailer!. }  destruct (eq_dec p' nullval).  entailer!.
       Exists g1 g2 x v p1' p2' l1 l2. unfold node_lock_inv.  unfold ltree. entailer!.   rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later]. unfold node_lock_inv. entailer!.

       }
      forward. entailer!.   (* return; *)
    + (* else clause *)
      unfold tree_rep_R. rewrite if_false.
      Intros ga gb x0 v0 pa pb locka lockb .
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        unfold ltree at 1; Intros.
        forward.
        forward_call (locka, lsh1,(node_lock_inv g pa ga locka)).
        Intros .
        unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1.  unfold sync_inv at 1.  Intros a.
         rewrite node_rep_def. Intros tp1.  gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g g_in) (my_half ga _ _).
         sep_apply (in_tree_left_range () (λ (BST : tree) (_ : ()),
             !! sorted_tree (insert x v BST) &&
             tree_rep g g_root (insert x v BST) * emp)
          (λ _ : (), Q) x x0 g g_root inv_names v0  g_in ga gb r a).  Intros ba.
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
          unfold node_lock_inv at 3. change (selflock (node_lock_inv_pred g pa ga locka) lsh2 locka) with (node_lock_inv g pa ga locka). rewrite selflock_eq . unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Exists r.
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R at 2. rewrite if_false.  assert_PROP (tp <> nullval). { entailer!. }
          Exists ga gb x0 v0 pa pb locka lockb.  unfold ltree at 2. entailer!.   repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp). entailer!. auto.
        }
         Exists (ba, Finite_Integer x0, a.2) ga locka pa. unfold node_lock_inv. rewrite node_rep_def. Exists tp1.
         entailer!.  unfold key_in_range in *. apply andb_true_intro. split. destruct r as [p o]. destruct p as [p1 p2]. apply andb_prop in H3. destruct H3. simpl in H11. apply less_than_equal_less_than_trans with (b := p1).
         auto. auto. simpl;apply Zaux.Zlt_bool_true;auto. sep_apply ( range_incl_tree_rep_R tp1 a.1 (ba, Finite_Integer x0) a.2 g). auto.
      - (* Inner if, second branch:  k<x *)
        forward.
        forward.
        unfold_data_at (data_at _ _ _ tp).
        unfold ltree at 2; Intros.
        forward.
        forward_call (lockb, lsh1,(node_lock_inv g pb gb lockb)).
        Intros .
        unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1.  unfold sync_inv at 1.  Intros a.
        rewrite node_rep_def. Intros tp1. gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) (in_tree g g_in) (my_half gb gsh1 a).
        sep_apply (in_tree_right_range () (λ (BST : tree) (_ : ()),
             !! sorted_tree (insert x v BST) &&
             tree_rep g g_root (insert x v BST) * emp)
          (λ _ : (), Q)  x x0 g g_root inv_names v0 g_in ga gb r a). Intros ba.
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
          unfold node_lock_inv at 3. change (selflock (node_lock_inv_pred g pb gb lockb) lsh2 lockb) with (node_lock_inv g pb gb lockb).   rewrite selflock_eq . unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Exists r.
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R at 2. rewrite if_false.  assert_PROP (tp <> nullval). { entailer!. }
          Exists ga gb x0 v0 pa pb locka lockb.  unfold ltree at 3. entailer!.   repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp); entailer!. auto.
         }
         Exists (Finite_Integer x0, ba, a.2) gb lockb pb. unfold node_lock_inv. rewrite node_rep_def. Exists tp1.
         entailer!.  unfold key_in_range in *. apply andb_true_intro. split. simpl;apply Zaux.Zlt_bool_true;auto. destruct r as [p o]. destruct p as [p1 p2]. apply andb_prop in H3. destruct H3. simpl in H12. apply less_than_less_than_equal_trans with (b := p2).
         auto. auto. sep_apply ( range_incl_tree_rep_R tp1 a.1 (Finite_Integer x0, ba) a.2 g). auto.
      - (* x = k *)
        forward.
        destruct r as [p o]. destruct p.  simpl in H5.
        assert ( x = x0). {  lia.  }
        assert_PROP (tp <> nullval). { entailer!. }
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _ _) ( in_tree g  _).
        viewshift_SEP 0 (Q  * ( EX n1 n2:number, !!(key_in_range x (n1,n2) = true) && my_half g_in gsh1 (n1,n2,Some (Some(x,v,ga,gb)) ) * in_tree g g_in)).
        {
          go_lower.   eapply sync_commit_gen1.
          intros. iIntros "H". iDestruct "H" as "[H1 H2]". iDestruct "H2" as "[% H2]".
          iModIntro.  iPoseProof (tree_rep_insert with "[H1 H2]") as "Hadd". instantiate (1:= x1). auto. iFrame. iDestruct "Hadd" as ((n1, n2) o0) "([Hmy H1] & H2)".
          iExists (n1,n2,Some o0). iFrame. iPoseProof ( bi.and_elim_l with "H2") as "H3".  iPoseProof ( bi.and_elim_r with "H3") as "Hnew".  iIntros "%".  iMod "Hnew". iSpecialize ("Hnew" $! ga gb). iModIntro. iExists (n1,n2, Some (Some(x,v,ga,gb))).
          iExists (n1,n2, Some (Some(x,v,ga,gb))). match goal with |-context[(|==> ?P)%logic] => change ((|==> P)%logic) with ((|==> P)%I) end. instantiate (1 := v). instantiate (1:= x). iSplit.
          { iPureIntro. intros. destruct b0 as [r i]. destruct r as [n3 n4]. hnf.
            simpl. split. apply range_incl_join in H15. simpl in *. hnf in *.
            unfold merge_range. inv H15. apply andb_prop in H16.
            apply andb_prop in H17. destruct H16, H17. f_equal.
            apply leq_entail_min_number; auto. apply leq_entail_max_number; auto.
            hnf in H15. simpl in H15. inv H15. rewrite if_false in H14.
            destruct H14 as [x Hr]. apply node_info_join_Some in Hr. simpl in Hr.
            rewrite Hr in H17. inv H17. apply sepalg.join_unit2.
            apply psepalg.None_unit. auto. inv H15. apply gsh1_not_Tsh.  }
          iIntros "(H1 & H2)". iSpecialize ("Hnew" with "[$H2 $Hmy]"). iSplit; auto.
          instantiate ( 1:= v0).
          { iPureIntro. split. rewrite if_false in H14. destruct H14 as [a1 Hr].
            subst o. apply node_info_join_Some in Hr. simpl in Hr. inv Hr; auto.
            apply gsh1_not_Tsh. rewrite if_false in H14. destruct H14 as [a1 Hr].
            subst o. apply range_incl_join in Hr. destruct Hr. simpl in H5.
            apply andb_prop in H5. unfold key_in_range in *.
            apply andb_prop in H3. destruct H3. apply andb_true_intro.
            destruct H5. split.
            apply less_than_equal_less_than_trans with (b := n); auto.
            apply less_than_less_than_equal_trans with (b := n0); auto.
            apply gsh1_not_Tsh. }
          iModIntro. normalize. iDestruct "Hnew" as "(H2 & H3)". apply (insert_sorted x0 v) in H13. iExists n1. normalize. iExists n2. iFrame.  iSplit. rewrite H11.  auto.  iSplit. iPureIntro.
          { rewrite if_false in H14. destruct H14 as [a1 Hr].
            apply range_incl_join in Hr. destruct Hr. simpl in H15.
            apply andb_prop in H14. unfold key_in_range in *. subst x.
            apply andb_prop in H3. destruct H3. apply andb_true_intro.
            destruct H14.  split.
            apply less_than_equal_less_than_trans with (b := n); auto.
            apply less_than_less_than_equal_trans with (b := n0); auto.
            apply gsh1_not_Tsh. }
          auto.  done. }
        Intros n1 n2.
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
           unfold node_lock_inv at 2.  rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists (n1, n2, Some(Some (x, v, ga, gb))).
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R. rewrite if_false.
          Exists ga gb x v pa pb locka lockb. unfold node_lock_inv. entailer!. auto.  }
        forward. entailer!.
       - auto.
  *  (* After the loop *)
    forward. normalize.
Qed.


(* Program Definition lookup_spec :=
 DECLARE _lookup
   ATOMIC TYPE (rmaps.ConstType ( val * val *  Z * share * val  * gname)) OBJ BST INVS empty top
  WITH  b: _, np : _,  x: _, sh:_, lock : _, g: _
  PRE  [ _t OF (tptr (tptr t_struct_tree_t(*t_struct_tree*))), _x OF tint  ]
    PROP(readable_share sh; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEPS (nodebox_rep sh lock np b) | ( ltree  BST g  lock np)
  POST [ tptr Tvoid ]
   EX ret : val,
    PROP ()
    LOCAL(temp ret_temp ret)
    SEP (!! (ret =  lookup(Vint (Int.repr x))  x  BST) && nodebox_rep sh lock np b;  ltree  BST g  lock np  ).

Definition thread_lock_R sh lock np gv:=
   (mem_mgr gv*
   data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb)*
   data_at Ers (tarray tschar 16)
   (map (Vint oo cast_int_int I8 Signed)
   [Int.repr 79; Int.repr 78; Int.repr 69;
   Int.repr 95; Int.repr 70; Int.repr 82;
   Int.repr 79; Int.repr 77; Int.repr 95;
   Int.repr 84; Int.repr 72; Int.repr 82;
   Int.repr 69; Int.repr 65; Int.repr 68;
   Int.repr 0]) (gv ___stringlit_1)*
   nodebox_rep sh lock np).

Definition thread_lock_inv sh1 lsh2 np gv lockb lockt :=
  selflock (thread_lock_R sh1 lockb np gv) lsh2 lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * val * val * globals
    PRE [ _args OF (tptr tvoid) ]
         let '(sh, lock, np, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   ( mem_mgr gv;
                 data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb);
                 data_at Ers (tarray tschar 16)
                 (map (Vint oo cast_int_int I8 Signed)
                 [Int.repr 79; Int.repr 78; Int.repr 69;
                 Int.repr 95; Int.repr 70; Int.repr 82;
                 Int.repr 79; Int.repr 77; Int.repr 95;
                 Int.repr 84; Int.repr 72; Int.repr 82;
                 Int.repr 69; Int.repr 65; Int.repr 68;
                 Int.repr 0]) (gv ___stringlit_1);
                 nodebox_rep sh1 lock np;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh1 sh np gv lock (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (). *)



Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, (P |-- Q) -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.
(*
Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; lia)
                          | rewrite if_falseb by (apply Z.ltb_ge; lia)].

Lemma t_lock_exclusive : forall p l,
  exclusive_mpred (t_lock_pred p l).
Proof.
  intros. rewrite t_lock_pred_def.
  eapply derives_exclusive, exclusive_sepcon1 with
  (P := EX tp : _, field_at Ews t_struct_tree_t [StructField _t] tp p)
  (Q:= EX t0 : tree val, EX tp : val, _ * node_rep t0 tp * malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock l * _).
  - unfold t_lock_pred_base. Intros t0 tp. Exists tp. cancel. Exists t0 tp. apply derives_refl.
  - apply ex_field_at_exclusive; auto.
    simpl. lia.
Qed.
Hint Resolve t_lock_exclusive.

Lemma t_lock_rec : forall p l,
  rec_inv lsh2 l (t_lock_pred_base p l) (t_lock_pred p l).
Proof.
  intros; apply t_lock_pred_def.
Qed.
Hint Resolve t_lock_rec.


Lemma thread_inv_exclusive : forall sh1 lsh2 nb gv lockb lockt,
  exclusive_mpred (thread_lock_inv sh1 lsh2 nb gv lockb lockt).
Proof.
  intros; apply selflock_exclusive. unfold thread_lock_R. apply exclusive_sepcon1. apply exclusive_sepcon1.
  apply exclusive_sepcon2. apply data_at_exclusive. auto. simpl. lia.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
start_function.
forward.
unfold nodebox_rep.
Intros np0.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_1)). { entailer!. }
forward_call(sh1,lock,np,1,gv ___stringlit_1,gv).
 * unfold nodebox_rep. Exists np0. entailer!.
 * split. auto. split. rep_lia. auto.
 * forward_call (gv _thread_lock, sh, thread_lock_R sh1 lock np gv, thread_lock_inv sh1 sh np gv lock (gv _thread_lock)).
    { lock_props. unfold thread_lock_inv, thread_lock_R. rewrite selflock_eq at 2. entailer!. }
    forward.
Qed.

Lemma ltree_share_join : forall (sh1 sh2 sh : share) (p : val) (lock : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
  ltree sh1 p lock * ltree sh2 p lock = ltree sh p lock.
Proof.
  intros; unfold ltree.
  rewrite sepcon_andp_prop, sepcon_andp_prop', <- andp_assoc, andp_dup; f_equal.
  rewrite <- sepcon_assoc, (sepcon_assoc (field_at _ _ _ _ _)), (sepcon_comm (lock_inv _ _ _)), <- sepcon_assoc.
  erewrite field_at_share_join by eauto.
  rewrite sepcon_assoc.
  erewrite lock_inv_share_join by eauto; reflexivity.
Qed.

(* for conclib *)
Lemma field_at_value_cohere : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p, readable_share sh1 ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |--
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v1 p.
Proof.
  intros; unfold field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.

Lemma field_at_value_eq : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject (nested_field_type t gfs) v1 <> Vundef -> repinject (nested_field_type t gfs) v2 <> Vundef ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold field_at, at_offset; Intros.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  sep_apply mapsto_value_eq; Intros; apply prop_right.
  set (t' := nested_field_type t gfs) in *.
  pose proof (f_equal (valinject t') H6) as Heq.
  rewrite !valinject_repinject in Heq; auto.
Qed.

Lemma data_at_value_eq : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject t v1 <> Vundef -> repinject t v2 <> Vundef ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold data_at; apply field_at_value_eq; auto.
Qed.

Lemma nodebox_rep_share_join : forall (sh1 sh2 sh : share) (lock : val) (nb : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
       nodebox_rep sh1 lock nb * nodebox_rep sh2 lock nb = nodebox_rep sh lock nb.
Proof.
  intros; unfold nodebox_rep.
  apply pred_ext.
  - Intros np1 np2.
    assert_PROP (np1 <> Vundef) by entailer!.
    assert_PROP (np2 <> Vundef) by entailer!.
    sep_apply data_at_value_eq; Intros; subst.
    erewrite data_at_share_join, ltree_share_join by eauto.
    Exists np2; auto.
  - Intros np; Exists np np.
    erewrite <- data_at_share_join, <- (ltree_share_join sh3 sh4); eauto; cancel.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
forward_call(gv).
Intros vret.
forward.
forward.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_2)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),3,gv ___stringlit_2,gv).
 { split3. auto. rep_lia. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_3)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),1,gv ___stringlit_3,gv).
 { split3. auto. rep_lia. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_4)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),4,gv ___stringlit_4,gv).
 { split3. auto. rep_lia. auto. }
forward_call ((gv _thread_lock), Ews, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
forward_spawn _thread_func nullval (lsh2,(snd vret),(fst vret), gv).
 { erewrite <- lock_inv_share_join; try apply lsh1_lsh2_join; auto.
   erewrite <- nodebox_rep_share_join; try apply sh1_sh2_join; auto.
   erewrite <- data_at_share_join; try apply lsh1_lsh2_join; auto.
    entailer!. }
assert_PROP ( is_pointer_or_null (gv ___stringlit_5)). { entailer!. }
forward.
sep_apply (create_mem_mgr gv).
forward_call(sh2,(snd vret), (fst vret),1,gv ___stringlit_5,gv).
 { split3. auto. rep_lia. auto. }
forward_call ((gv _thread_lock), lsh1, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
unfold thread_lock_inv at 2. rewrite selflock_eq. Intros.

forward_call ((gv _thread_lock), Ews, lsh2, thread_lock_R sh1 (snd vret) (fst vret) gv, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
{ lock_props. unfold thread_lock_inv. erewrite <- (lock_inv_share_join _ _ Ews); try apply lsh1_lsh2_join; auto. entailer!. }
forward.
forward_call((snd vret), (fst vret), gv).
 { unfold thread_lock_R. erewrite <- (nodebox_rep_share_join _ _ lsh1) ; try apply sh1_sh2_join; auto.
entailer!. }
forward.
Qed.

Lemma node_rep_D {TR p} (P: p<>nullval) :
  node_rep TR p |-- (EX l k v r, !!(TR = T l k v r) && node_rep TR p).
Proof.
destruct TR as [ | l k v r]; simpl; Intros. contradiction.
Exists l k v r. entailer!.
Qed.

(*Variant of t_lock_pred but without the |> lock_inv lsh2 lock (t_lock_pred p lock) term*)
Definition tlp TR (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt *
  node_rep TR p * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

(*Version of tlp that existentially quantifies over the semantic tree*)
Definition tlp' (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt *
  (EX TR, node_rep TR p) * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

Definition lookup_inv (*TR*) b lsh0 lock0 (x:Z): environ -> mpred :=
  EX p: val, EX tgt:val, EX lock:val,
  PROP()
  LOCAL(temp _p p; temp _l lock; temp _x (Vint (Int.repr x)))
  SEP (|>lock_inv lsh2 lock (t_lock_pred tgt lock);
       tlp' (* TR*) p tgt lock;  nodebox_rep lsh0 lock0 b).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function. rename H into Hx.
  unfold nodebox_rep; Intros tgt.
  forward. deadvars.
  unfold ltree; Intros. rename H into FC_tgt. rewrite lock_inv_isptr; Intros.
  forward.

  (*aquire(l)*)
  forward_call (lock, sh, t_lock_pred tgt lock).
  rewrite t_lock_pred_def at 2. Intros TREE1 p.
  forward. (*p=tgt->t*)
  deadvars.

  forward_while (lookup_inv (*TREE1*) b sh lock x).
  + Exists p tgt lock. entailer.
    unfold tlp' at 1. cancel. Exists TREE1; cancel.
    unfold nodebox_rep. Exists tgt; cancel.
    unfold ltree. entailer!.

  + unfold tlp'; try Intros TR. entailer!.
  + clear TREE1. unfold tlp'; Intros TR.
    clear FC_tgt tgt p. rename p0 into p. rename tgt0 into tgt.
    sep_apply (@node_rep_D TR p HRE); Intros l k v r; subst. simpl; Intros pa pb locka lockb.
    rename H into K.
    forward.
    forward_if.
    - rename H into HK.
      forward. forward.
      unfold ltree at 1; Intros. rename H into FC_pa.
      forward. deadvars.

      (*aquire(l)*)
      forward_call (locka, lsh1, t_lock_pred pa locka).
      rewrite t_lock_pred_def at 2. Intros pa_T pa_t.

      forward. (*p=tgt->t*)

      (*release*)
      forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
      { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] locka pa;
                  node_rep pa_T pa_t; malloc_token Ews t_struct_tree_t pa;
                  malloc_token Ews tlock locka; lock_inv lsh2 locka (t_lock_pred pa locka);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pa_t pa]);
          subst Frame; [ reflexivity | clear H].
        lock_props.
        setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
        (*Parameter TR1: tree val.
          Parameter TR2: tree val.*)
        Exists (T (*TR1*)l k v (*TR2*)r) p.
        cancel. unfold node_rep.
        Exists pa pb locka lockb; entailer!.
        unfold ltree; entailer!.
        rewrite later_sepcon. eapply derives_trans.
        2: apply sepcon_derives, derives_refl; try apply now_later.
        cancel. }
      Exists ((pa_t, pa), locka); entailer!.
      unfold tlp'; cancel. Exists pa_T; cancel.

    - rename H into XK.
      forward_if.
      * rename H into KX. forward. forward.
        unfold ltree at 2; Intros. rename H into FC_pb.
        forward. deadvars.

        (*aquire(l)*)
        forward_call (lockb, lsh1, t_lock_pred pb lockb).
        rewrite t_lock_pred_def at 2. Intros pb_T pb_t.

        forward. (*p=tgt->t*)

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] lockb pb;
                  node_rep pb_T pb_t; malloc_token Ews t_struct_tree_t pb;
                  malloc_token Ews tlock lockb; lock_inv lsh2 lockb (t_lock_pred pb lockb);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pb_t pb]);
            subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
          (*Parameter TR4: tree val.
            Parameter TR5: tree val.*)
          Exists (T (*TR4*)l k v (*TR5*)r) p.
          cancel. unfold node_rep.
          Exists pa pb locka lockb. entailer!.
          unfold ltree; entailer.
          rewrite later_sepcon. eapply derives_trans.
          2: apply sepcon_derives, derives_refl; try apply now_later.
          cancel. }
        Exists ((pb_t, pb), lockb). entailer!.
        unfold tlp'. cancel. Exists pb_T; cancel.
      * rename H into KX.
        forward.

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
          (*Parameter TR6: tree val.
            Parameter TR7: tree val.*)
          Exists (T (*TR6*)l k v (*TR7*)r) p.
          cancel. unfold node_rep.
          Exists pa pb locka lockb. entailer!. }
        forward. Exists v; entailer!.
  + subst. unfold tlp'; simpl; Intros. Intros TR.

    (*release*)
    forward_call(lock0, lsh2, t_lock_pred_base tgt0 lock0, t_lock_pred tgt0 lock0).
    { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
      lock_props.
      setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
      Exists (@E val) nullval; simpl. entailer!. simpl; entailer!. }
    forward. Exists (vint 0); entailer!.
Qed.
*)
Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
  * if_tac.
    subst p. entailer!.
    entailer!.
  * forward_call 1.
    contradiction.
  * if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
  * forward. Exists p; entailer!.
Qed.
