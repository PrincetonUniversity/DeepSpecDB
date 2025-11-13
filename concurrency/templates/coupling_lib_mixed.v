Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks. 
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.semax_conc.
Require Import bst.puretree.
From refinedc.project.rc.bst_template_coupling Require Import generated_code generated_spec.
From iris.algebra Require Import auth gset excl.

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

Canonical Structure rangeO := leibnizO range.

Local Instance range_pcore : PCore range := λ r, Some r.
Local Instance range_op : Op range := merge_range.
Local Instance range_valid : Valid range := λ _, True%type.

Lemma range_ra_mixin : RAMixin range.
Proof.
  apply ra_total_mixin; try done.
  - by intros ??? ->.
  - by intros ?? ->.
  - intros ???. symmetry; apply puretree.merge_assoc.
  - intros ??. apply puretree.merge_comm.
  - intros ?. apply puretree.merge_id.
Qed.
Canonical Structure rangeR := discreteR range range_ra_mixin.

Local Instance range_unit : Unit range := (Pos_Infinity, Neg_Infinity).

Lemma range_ucmra_mixin : UcmraMixin range.
Proof.
  split; try done.
  by intros (?, ?).
Qed.
Canonical Structure rangeUR := Ucmra range range_ucmra_mixin.

Definition ghost_ref `{!inG Σ (ext_order.inclR (authR (gsetUR gname)))} g r1 := own(inG0 := inG0) g (● r1).

Definition in_tree `{!inG Σ (ext_order.inclR (authR (gsetUR gname)))} g r1 := own(inG0 := inG0) g (◯ {[r1]}).

(*Lemma in_tree_add : forall g s g1 g', ~Ensembles.In s g' -> in_tree g g1 * ghost_ref g s 
  ⊢ (|==> !! (g1 <> g') && (ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
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
  iMod (ref_add(P := invariants.set_PCM) _ _ _ _ (Singleton g') (Add (Singleton g1) g') (Add s g')
         with "H") as "H".
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
  * iPureIntro; intros Hcontra. subst; congruence.
  * iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  * split; auto; constructor; intros ? X; inv X.
    inv H5; inv H6; contradiction.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
  * intro; contradiction H2; eapply Share.split_nontrivial; eauto.
Qed.*)

Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
Definition nodeR := prodR rangeR (optionR (exclR (option ghost_info))).

Notation node_info := (cmra_car nodeR).

(*Lemma ghost_node_alloc : forall g s g1 (a : node_info),
  finite s -> in_tree g g1 * ghost_ref g s ⊢ 
    (|==> ∃ g', !! (¬ Ensembles.In s g' /\ g1 <> g') &&
                   (both_halves a g' * ghost_ref g (Add s g') * in_tree g g1 * in_tree g g'))%I.
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
      pose proof (Nat.le_max_l (fold_right max O l) n); lia.
    - intros X; specialize (H _ X).
      pose proof (Nat.le_max_r (fold_right max O l) n); lia. }
  { apply @part_ref_valid. }
  iExists g'. iFrame.
  iMod (in_tree_add _ _ _ g' with "r") as "(% & ($ & $))"; auto.
Qed.*)

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

(*Lemma range_incl_join: forall  (r1 r2 r3 : node_info), sepalg.join r1 r2 r3 -> range_incl r1.1 r3.1 = true /\ range_incl r2.1 r3.1 = true.
Proof.
  intros. destruct r1 as [range1 r1]. destruct r2 as [range2 r2]. destruct r3 as [range3 r3].
  hnf in H. simpl in *. destruct H. inv H; auto. split; [|rewrite merge_comm]; eapply merge_range_incl; eauto.
Qed.*)

Section inv.
Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct threads._atom_int noattr)}
  `{!inG Σ (ext_order.inclR (authR (gsetUR gname)))} `{!inG Σ (frac_auth.frac_authR nodeR)} `{!cinvG Σ}.

(* Each lock will hold gsh1 of my_half, with gsh2 held by the invariant, allowing the lock's range to become outdated.
  The exception is the root node, which will hold some smaller fraction of gsh1, allowing clients to know that the root's range is total. *)

(* base definition for node_lock_inv_r *)

Definition node_lock_inv_r' (R : (val * (gname * node_info) -d> mpred)) : Qp -d> val -d> gname -d> val -d> mpred :=
  λ sh p gp lock,
  sync_inv gp sh (curry (curry R p)) ∗
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p (* *
  malloc_token Ews t_lock lock*).

Local Instance node_lock_inv_r'_ne : NonExpansive node_lock_inv_r'.
Proof. repeat intro. rewrite /node_lock_inv_r' /sync_inv. do 6 f_equiv.
  intros ?? ->%discrete; last apply _. done. Qed.

Definition node_lock_inv_r (R : (val * (gname * node_info) -d> mpred)) : Qp -d> val -d> gname -d> lock_handle -d> mpred :=
  λ sh p gp lock, selflock (node_lock_inv_r' R sh p gp (ptr_of lock)) (1/2) lock.

Local Instance node_lock_inv_r_ne : NonExpansive node_lock_inv_r.
Proof. repeat intro. rewrite /node_lock_inv_r /selflock. f_equiv. by apply node_lock_inv_r'_ne. Qed.

(* fix share
   sh - for field_at
   ish - for lock_inv
   gsh - for node_lock_inv
 *)
Definition ltree_r R : gname -d> share -d> Qp -d> Qp -d> val -d> lock_handle -d> mpred :=
λ g_root sh ish gsh p lock,
  ⌜field_compatible t_struct_tree_t nil p⌝ ∧
  (field_at sh t_struct_tree_t [StructField _lock] (ptr_of lock) p ∗
   lock_inv ish lock (node_lock_inv_r R gsh p g_root lock)).

Local Instance ltree_r_ne : NonExpansive ltree_r.
Proof. repeat intro. rewrite /ltree_r. do 3 f_equiv. by apply node_lock_inv_r_ne. Qed.

(* Does the range ghost help at all, given that we could calculate it precisely from the nodes we've seen?
  Yes, since the nodes we've seen may change after we pass them. *)


Definition node_rep_r (g:gname) (R : val * (gname * node_info) -d> mpred) : (val * (gname * node_info)) -d> mpred := λ arg,
  let '(np, (g_current,(r,g_info))) := arg in
∃ tp:val,
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) ∗
 malloc_token Ews t_struct_tree_t np ∗ in_tree g g_current ∗
if eq_dec tp nullval 
then ⌜g_info = Excl' None⌝ ∧ emp  
else
∃ ga:gname, ∃ gb: gname, ∃ x: Z, ∃ v: val, ∃ pa : val, ∃ pb : val, ∃ (locka lockb : lock_handle),
     ⌜g_info = Excl' (Some(x,v,ga,gb)) /\ 
     and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\ 
     is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true⌝ ∧
     data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp ∗
     malloc_token Ews t_struct_tree tp ∗
    ▷ ltree_r R ga lsh1 (1/2)%Qp (1/2)%Qp pa locka ∗ ▷ ltree_r R gb lsh1 (1/2)%Qp (1/2)%Qp pb lockb.

Local Instance node_rep_r_contractive g : Contractive (node_rep_r g).
Proof.
  rewrite /node_rep_r => n ???.
  intros (?, (?, (?, ?))).
  do 26 f_equiv; f_contractive; by apply ltree_r_ne.
Qed.

Definition node_rep_closed g := fixpoint (node_rep_r g).

Definition node_rep np g g_current r := node_rep_closed g (np, (g_current, r)).

Definition node_lock_inv_pred sh g p gp lock :=
  sync_inv gp sh (node_rep p g) ∗
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p
 (* * 
  malloc_token Ews t_lock lock
 * malloc_token Ews t_struct_tree_t p  *).
(* No malloc token for t_struct_tree_t because node_rep_r contains one *)

Definition node_lock_inv sh g p gp lock :=
  selflock (node_lock_inv_pred sh g p gp (ptr_of lock)) (1/2) lock.

Definition ltree (g : gname) (g_root : gname) sh ish gsh p lock :=
  ⌜field_compatible t_struct_tree_t nil p⌝ ∧
  (field_at sh t_struct_tree_t [StructField _lock] (ptr_of lock) p ∗
     lock_inv ish lock (node_lock_inv gsh g p g_root lock)).

Definition public_half' (g : gname) (d : range * excl' (option ghost_info)) := 
  my_half g (1/2) (fst d, None) ∗ public_half g d.

 Fixpoint ghost_tree_rep (t: @ ghost_tree val) (g:gname) range : mpred :=
 match t, range with
 | E_ghost , _ => public_half' g (range, Excl' (@None ghost_info))
 | T_ghost a ga x v b gb, (l, r) => public_half' g (range, Excl' (Some (x,v,ga,gb))) ∗ ghost_tree_rep a ga (l, Finite_Integer x) ∗ ghost_tree_rep b gb (Finite_Integer x, r)
 end.

(*Lemma public_half_range_incl : forall g r r' o, range_incl r r' = true -> public_half' g (r, o) ⊢ (|==> public_half' g (r', o))%I.
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
Qed.*)

Fixpoint find_ghost_set (t : @ghost_tree val) (g:gname) : gset gname :=
  match t with
  | E_ghost => {[g]}
  | T_ghost a ga x v  b gb => {[g]} ∪ find_ghost_set a ga ∪ find_ghost_set b gb
end.

Definition find_ghost_set' (t : @ghost_tree val) :=
  match t with
  | E_ghost => ∅
  | T_ghost a ga x v  b gb => find_ghost_set a ga ∪ find_ghost_set b gb
end.

Lemma find_ghost_set_equiv : forall t g,
  find_ghost_set t g = {[g]} ∪ find_ghost_set' t.
Proof.
  intros. destruct t; simpl; set_solver.
Qed.

Inductive unique_gname : ghost_tree -> Prop :=
  | Unique_Empty : unique_gname E_ghost
  | Unique_Tree : forall (x : key) (v : val) (l : ghost_tree) (g1 : gname) (r : ghost_tree) (g2 : gname),
                  unique_gname l -> unique_gname r ->
                  g1 <> g2 ->
                  find_ghost_set' l ∩ find_ghost_set' r = ∅ ->
                  ~g1 ∈ (find_ghost_set' l) ->
                  ~g1 ∈ (find_ghost_set' r) ->
                  ~g2 ∈ (find_ghost_set' r) ->
                  ~g2 ∈ (find_ghost_set' l) ->
                  unique_gname (T_ghost l g1 x v r g2).

(* turn a tree into a gmap *)
Fixpoint tree_to_gmap (t : @ghost_tree val) : gmap key val :=
  match t with
  | E_ghost => empty
  | T_ghost a ga x v b gb => base.insert x v (union (tree_to_gmap a) (tree_to_gmap b))
  end.

Definition tree_rep (g : gname) (g_root : gname)  (m: gmap key val) : mpred := ∃ tg : ghost_tree,
  ⌜~ g_root ∈ (find_ghost_set' tg) /\ unique_gname tg /\ sorted_ghost_tree tg /\ tree_to_gmap tg = m⌝ ∧
  ghost_tree_rep tg g_root (Neg_Infinity, Pos_Infinity) ∗ ghost_ref g (find_ghost_set tg g_root).

(* fix share
   sh - for field_at
   ish - for lock_inv
   gsh - for node_lock_inv
 *)

(* nodebox_rep knows that the range of the root is -infinity to +infinity, but doesn't know the data. *)
(* reduce share to something related to the sh argument *)
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) sh' (lock : lock_handle) (nb : val) :=
  ∃ np: val, data_at sh (tptr (t_struct_tree_t)) np nb ∗
                ltree g g_root sh sh' (1/4) np lock ∗
                my_half g_root (1/4) (Neg_Infinity, Pos_Infinity, None).

Lemma my_half_range_inf : forall g sh1 sh2 r1 r2 o,
    my_half g sh1 (r1, o) ∗ my_half g sh2 (Neg_Infinity, Pos_Infinity, None) ⊢
    my_half g sh1 (r2, o) ∗ my_half g sh2 (Neg_Infinity, Pos_Infinity, None).
Proof.
  intros.
  iIntros "H"; rewrite !my_half_join -!pair_op.
  rewrite {2 5}/op /cmra_op /= /range_op !merge_infinity //.
Qed.

Definition tree_rep_R (tp:val) (r:(range)) (g_info: excl' (option ghost_info)) g : mpred :=
  if eq_dec tp nullval
  then ⌜g_info = Excl' None⌝ ∧ emp
  else
  ∃ ga : gname, ∃ gb : gname, ∃ x : Z, ∃ v : val,
            ∃ pa : val, ∃ pb : val, ∃ (locka lockb : lock_handle),
     ⌜g_info = Excl' (Some(x,v,ga,gb)) /\
          and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
          is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v
     /\ key_in_range x r = true⌝ ∧
       data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp ∗
       malloc_token Ews t_struct_tree tp ∗
     ▷ ltree g ga lsh1 (1/2) (1/2) pa locka ∗ ▷ ltree g gb lsh1 (1/2) (1/2) pb lockb.

Lemma node_rep_def : forall np r g g_current,
    node_rep np g g_current r ≡
    ∃ tp:val, (field_at Ews (t_struct_tree_t) [StructField _t] tp np) ∗
               malloc_token Ews t_struct_tree_t np ∗ in_tree g g_current ∗
               tree_rep_R tp (fst r) (snd r) g.
Proof.
  intros; rewrite /node_rep /node_rep_closed.
  etrans; first apply (fixpoint_unfold (node_rep_r g)).
  rewrite {1}/node_rep_r /tree_rep_R.
  destruct r; repeat f_equiv; done.
Qed.

Lemma node_lock_inv_pred_exclusive : forall sh p lock g g_current,
  exclusive_mpred (node_lock_inv_pred sh g p g_current lock).
Proof.
  intros.
  unfold node_lock_inv_pred, sync_inv.
  eapply derives_exclusive, exclusive_sepcon1  with
  (P := field_at lsh2 t_struct_tree_t [StructField _lock] lock p)
  (Q := (∃ a : node_info, node_rep p g g_current a ∗ my_half g_current sh a)).
  - Intros a.
    Exists a. cancel.
  - apply field_at_exclusive; auto.
    simpl. lia.
Qed.

Lemma node_exist_in_tree: forall g s g_in, in_tree g g_in ∗ ghost_ref g s ⊢
                                      ⌜g_in ∈ s⌝.
Proof.
  intros.
  unfold ghost_ref, in_tree.
  rewrite -own_op own_valid ouPred.discrete_valid; f_equiv.
  rewrite /impl comm auth_both_valid_discrete gset_included.
  set_solver.
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

Inductive range_info_in_tree (ri: node_info)
          (range: range): ghost_tree -> Prop :=
| riit_none: ri = (range, Excl' None) -> range_info_in_tree ri range E_ghost
| riit_root: forall (l r: ghost_tree) (g1 g2: gname) k v,
    ri = (range, Excl' (Some (k, v, g1, g2))) ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2)
| riit_left: forall (l r: ghost_tree) (g1 g2: gname) k v,
    range_info_in_tree ri (range.1, Finite_Integer k) l ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2)
| riit_right: forall (l r: ghost_tree) (g1 g2: gname) k v,
    range_info_in_tree ri (Finite_Integer k, range.2) r ->
    range_info_in_tree ri range (T_ghost l g1 k v r g2).

Definition empty_range rn tg r_root := range_info_in_tree (rn, Excl' None) r_root tg.

Lemma empty_range_E : forall r, empty_range r E_ghost r.
Proof. constructor; auto. Qed.

Definition keys_in_range_ghost (t : @ghost_tree val) r := forall k,
    In_ghost k t -> key_in_range k r = true.

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

Lemma ghost_range_inside_ghost_range : forall r r_root tg, empty_range r tg r_root -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg -> range_incl r r_root = true.
Proof.
  intros; generalize dependent r_root.
  induction tg; intros; inv H.
  - apply range_incl_refl.
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

Lemma key_not_exist_in_tree: forall tg r_root d x (Hempty : empty_range d tg r_root)
  (Hrange : keys_in_range_ghost tg r_root) (Hsorted : sorted_ghost_tree tg),
  key_in_range x d = true -> ~In_ghost x tg.
Proof.
  induction tg; intros.
  { intros X; inv X. }
  apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
  intros X. inv Hsorted. inv Hempty.
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

Global Instance range_core (a : rangeR): CoreId a.
Proof. rewrite /CoreId //. Qed.

Lemma both_halves_join : forall g a, my_half g (1/2) a ∗ public_half g a ⊣⊢ both_halves a g.
Proof.
  intros; rewrite <- both_halves_join.
  unfold public_half'. rewrite sep_assoc my_half_join.
  destruct a; rewrite -pair_op right_id.
  rewrite /my_half -core_id_dup frac_op Qp.half_half //.
Qed.

Lemma ghost_tree_rep_public_half_ramif2: forall tg g_root r_root g_in,
    g_in ∈ (find_ghost_set tg g_root) ->
    ghost_tree_rep tg g_root r_root
    ⊢
    (∃ r: range ,
           (public_half g_in (r, Excl' (@None ghost_info)) ∗
            (public_half g_in (r, Excl' (@None ghost_info)) -∗
                         ghost_tree_rep tg g_root r_root))) ∨
    (∃ r: range, ∃ x: key, ∃ v: val, ∃ ga gb: gname,
     ∃ i1 i2: option ghost_info,
        ((public_half g_in (r, Excl' (Some (x, v, ga, gb))) ∗
          public_half ga ((r.1, Finite_Integer x), Excl' i1) ∗
          public_half gb ((Finite_Integer x, r.2), Excl' i2)) ∗
        ((public_half g_in (r, Excl' (Some (x, v, ga, gb))) ∗
          public_half ga ((r.1, Finite_Integer x), Excl' i1) ∗
          public_half gb ((Finite_Integer x, r.2), Excl' i2))
           -∗ ghost_tree_rep tg g_root r_root))).
Proof.
  induction tg; intros; simpl in *.
  - rewrite -bi.or_intro_l. apply elem_of_singleton in H as ->. Exists r_root. cancel. apply wand_refl_cancel_right.
  - destruct r_root as [lroot rroot]. rewrite !elem_of_union in H; destruct H as [[H | H] | H].
    + apply elem_of_singleton in H as ->.
      rewrite -bi.or_intro_r. Exists (lroot, rroot) k v g g0. clear.
      destruct tg1, tg2; simpl.
      * Exists (@None ghost_info) (@None ghost_info). cancel.
        apply wand_refl_cancel_right.
      * Exists (@None ghost_info) (Some (k0, v0, g1, g2)). cancel.
        apply bi.wand_intro_r. cancel.
      * Exists (Some (k0, v0, g1, g2)) (@None ghost_info). cancel.
        apply bi.wand_intro_r. cancel.
      * Exists (Some (k0, v0, g1, g2)) (Some (k1, v1, g3, g4)). cancel.
        apply bi.wand_intro_r. cancel.
    + specialize (IHtg1 _ (lroot, Finite_Integer k) _ H). sep_apply IHtg1. clear.
      rewrite bi.sep_or_r; f_equiv.
      * Intros r. Exists r. cancel. apply bi.wand_intro_r.
        cancel. apply wand_frame_elim''.
      * Intros r x v0 ga gb i1 i2. Exists r x v0 ga gb i1 i2. cancel.
        apply bi.wand_intro_r. cancel.
        rewrite -!sep_assoc. apply wand_frame_elim''.
    + specialize (IHtg2 _ (Finite_Integer k, rroot) _ H). sep_apply IHtg2. clear.
      rewrite bi.sep_or_r; f_equiv.
      * Intros r. Exists r. cancel. apply bi.wand_intro_r.
        cancel. apply wand_frame_elim''.
      * Intros r x v0 ga gb i1 i2. Exists r x v0 ga gb i1 i2. cancel.
        apply bi.wand_intro_r. cancel.
        rewrite -!sep_assoc. apply wand_frame_elim''.
Qed.

Lemma range_info_in_tree_In: forall tg x v ga gb rn r_root,
    range_info_in_tree (rn, Excl' (Some (x, v, ga, gb))) r_root tg ->
    In_ghost x tg.
Proof.
  induction tg; intros.
  { inv H. }
  inv H.
  - now constructor 1.
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
    range_info_in_tree (rn, Excl' (Some (x, v, ga, gb))) r_root tg ->
    tree_to_gmap tg !! x = Some v.
Proof.
  induction tg; intros; simpl.
  { inv H0. }
  inv H. inv H0.
  - apply lookup_insert.
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
    range_info_in_tree (rn, Excl' None) r_root tg -> tree_to_gmap tg !! x = None.
Proof.
  induction tg; intros; simpl.
  { apply lookup_empty. }
  apply keys_in_range_ghost_subtrees in H1 as (? & ? & ?); auto.
  inv H; inv H2.
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
    tree_rep_R tp r1 g_info g ⊢ tree_rep_R tp r2 g_info g.
Proof.
  intros. unfold tree_rep_R. if_tac. 1: cancel. do 16 f_equiv. entailer!.
  destruct (key_in_range a1 r1) eqn: ?. 2: easy.
  eapply key_in_range_incl; eauto.
Qed.

(*Lemma node_info_incl: forall a b c,
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
  my_half g sh a * public_half g b ⊢ 
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
    ⊢ |={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
    b Q * my_half g_in gsh r *
    (∃ ba, !! (less_than_equal ba r.1.1 = true /\
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
    ⊢ |={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅
    b Q * my_half g_in gsh r *
    (∃ ta, !! (less_than_equal r.1.2 ta = true /\
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
Qed.*)

Lemma ghost_tree_rep_public_half_ramif: forall tg g_root r_root g_in,
    g_in ∈ (find_ghost_set tg g_root) ->
    ghost_tree_rep tg g_root r_root ⊢
    ∃ r: node_info, ⌜range_info_in_tree r r_root tg⌝ ∧
      (public_half g_in r ∗ (public_half g_in r -∗ ghost_tree_rep tg g_root r_root)).
Proof.
  induction tg; intros; simpl in *.
  - apply elem_of_singleton in H as ->. Exists (r_root, Excl' (@None ghost_info)). apply bi.and_intro.
    + apply bi.pure_intro. now constructor.
    + iIntros "$ $".
  - destruct r_root as [l r]. rewrite !elem_of_union in H; destruct H as [[H | H] | H].
    + apply elem_of_singleton in H as ->.
      Exists (l, r, Excl' (Some (k, v, g, g0))). apply bi.and_intro.
      * apply bi.pure_intro. now apply riit_root.
      * cancel. iIntros "($ & $) $".
    + specialize (IHtg1 _ (l, Finite_Integer k) _ H). sep_apply IHtg1.
      Intros r0. Exists r0. apply bi.and_intro.
      * apply bi.pure_intro. now apply riit_left.
      * cancel. apply bi.wand_intro_r. cancel. apply wand_frame_elim''.
    + specialize (IHtg2 _ (Finite_Integer k, r) _ H). sep_apply IHtg2.
      Intros r0. Exists r0. apply bi.and_intro.
      * apply bi.pure_intro. now apply riit_right.
      * cancel. apply bi.wand_intro_r. cancel. apply wand_frame_elim''.
Qed.

(*Lemma public_update : forall g (a b a' : G), my_half g gsh1 a * public_half g b ⊢ 
  (|==> my_half g gsh1 a' * public_half g a')%I.
Proof.
  intros; unfold public_half'.
  assert_PROP (sepalg.joins a (b.1, None)).
  { iIntros "(my1 & my2 & ?)".
    iPoseProof (own_valid_2(RA := ref_PCM _) with "[$my1 $my2]") as "%"; iPureIntro.
    destruct H as ((?, ?) & [J ?] & ?); simpl in *.
    destruct g0 as [(?, ?)|]; try contradiction.
    eexists; apply J. }
  destruct H.
  erewrite <- sepcon_assoc, my_half_join by eauto.
  sep_apply (public_update g x b a'); Intros; subst x.
  erewrite <- my_half_join with (a1 := a')(a2 := (fst a', None)); eauto.
  rewrite sepcon_assoc; apply derives_refl.
  { split; hnf; simpl.
    * symmetry; apply merge_id.
    * constructor.
  }
Qed. *)

End inv.

Global Hint Resolve node_lock_inv_pred_exclusive : core.
Global Hint Resolve empty_range_E : core.
Global Hint Resolve keys_in_range_infinity : core.
