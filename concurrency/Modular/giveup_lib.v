Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Export VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.ghostsI.
Require Import VST.concurrency.semax_conc.
Require Import Coq.Sets.Ensembles.
Require Import VST.veric.rmaps.
Require Import bst.puretree.

Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

 (* trees labeled with ghost names *)
(* ghost_tree -> gname -> val -> lock_handle -> key -> V -> ghost_tree -> gname -> val -> lock_handle ->ghost_tree. *)
Inductive ghost_tree: Type :=
 | E_ghost : ghost_tree
 | T_ghost : ghost_tree -> gname -> val -> val -> key -> V -> ghost_tree -> gname -> val -> val -> ghost_tree.

Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 lp llk r g2 rp rlk x v :
       (k = x) -> In_ghost k (T_ghost l g1 lp llk x v r g2 rp rlk)
  | InLeft_ghost l g1 lp r llk g2 rp rlk x v':
      In_ghost k l -> In_ghost k (T_ghost l g1 lp llk x v' r g2 rp rlk)
  | InRight_ghost l g1 lp r llk g2 rp rlk x v':
      In_ghost k r -> In_ghost k (T_ghost l g1 lp llk x v' r g2 rp rlk).

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> Z.lt k x .
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> Z.lt x k .

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
| Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
| Sorted_Ghost_Tree x v l g1 lp llk r g2 rp rlk (Hsortedl: sorted_ghost_tree l) (Hsortedr: sorted_ghost_tree r) (Hgtl: gt_ghost l x) (Hltr: lt_ghost r x):
  sorted_ghost_tree (T_ghost l g1 lp llk x v r g2 rp rlk).

Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree)
  (g1:gname) (lp: val) (llk: val) (g2:gname) (rp: val) (rlk: val): ghost_tree :=
match s with
| E_ghost => T_ghost E_ghost g1 lp llk x v E_ghost g2 rp rlk
| T_ghost a ga la llka y v' b gb rb rlkb =>
    if (Z.ltb x y) then T_ghost (insert_ghost x v a g1 lp llk  g2 rp rlk) ga la llka y v' b gb rb rlkb
    else if (Z.ltb y x) then T_ghost a ga la llka y v' (insert_ghost x v b g1 lp llk g2 rp rlk) gb rb rlkb
         else T_ghost a ga la llka x v b gb rb rlkb
end.

End TREES.
(*
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
*)

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

Definition number2Z (x : number) : Z :=
  match x with
    | Finite_Integer y => y
    | Neg_Infinity => Int.min_signed
    | Pos_Infinity => Int.max_signed
  end.

#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val * gname * gname)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition ghost_ref (g : own.gname) r1 :=
  ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) r1 g.

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.

Lemma ghost_snapshot_intree g (s : gmap gname (val * val))(pn : val)(lock: val)(g_in: gname):
    ghost_ref g s * (!! (s !! g_in = Some(pn, lock)) && seplog.emp)
                      |-- ( in_tree g g_in pn lock * ghost_ref g s).
Proof.
  unfold ghost_ref, ghost_master1, in_tree.
  iIntros "(H & (%Hx & _))".
  rewrite snap_master_join; auto.
  iFrame "H".
  iPureIntro.
  by eapply map_singleton_subseteq_l in Hx.
Qed.

Lemma node_exist_in_tree: forall g (s : gmap gname (val * val)) (pn : val) (lock: val) (g_in:gname),
    in_tree g g_in pn lock * ghost_ref g s |-- !! ( s !! g_in = Some(pn, lock)).
Proof.
 intros.
 unfold ghost_ref, in_tree.
 rewrite -> snap_master_join1.
 iIntros "(% & H)".
 iPureIntro.
 by apply map_singleton_subseteq_l.
Qed.

Lemma in_tree_add : forall (g : gname) (s : gmap gname (val * val)) g1 g' pn pn' lock lock',
    s !! g' = None -> in_tree g g1 pn lock * ghost_ref g s |--
    (|==> !! (g1 <> g') && (ghost_ref g (<[g':=(pn', lock')]> s) *
                   in_tree g g1 pn lock * in_tree g g' pn' lock'))%I.
Proof.
  intros.
  iIntros "(Hin & H)".
  iPoseProof (node_exist_in_tree g _ pn lock with "[$Hin $H]") as "%Hx".
  iPoseProof(in_tree_duplicate with "[$Hin]") as "(Hin & Hin1)".
  iPoseProof(snap_master_update1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val)))
               {[g1 := (pn, lock)]} s g (<[g':=(pn', lock')]> s) with "[$Hin $H]") as "H"; auto.
  { by apply (insert_subseteq s g' (pn', lock')) in H. }
  iFrame "Hin1".
  iMod "H" as "(H1 & H2)".
  iPoseProof(ghost_snap_forget (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val)))
                 {[g' := (pn', lock')]} (<[g':=(pn', lock')]> s) g with "[$H1]") as "H1".
  {
    pose proof H as Hy.
    apply (insert_union_singleton_r s g' (pn', lock')) in H.
    rewrite H.
    eapply map_union_subseteq_r.
    apply map_disjoint_spec.
    intros.
    apply lookup_singleton_Some in H1.
    destruct H1 as (H1x & _); subst.
    rewrite Hy in H0. easy.
  }
  iMod "H1".
  iModIntro.
  iFrame.
  iPureIntro; (split; auto).
  intros Hcontra; subst. congruence.
Qed.

Lemma foldr_max_ge_a1 ls a: fold_right Init.Nat.max a ls >= a.
Proof. intros. induction ls; simpl; lia. Qed.

Lemma max_foldr_l l1 l2: foldr Init.Nat.max O l2 <= foldr Init.Nat.max (foldr Init.Nat.max O l1) l2.
Proof.
  induction l2 as [|x xs IH]; simpl; lia.
Qed.

Lemma max_list_geq_x (ls : list nat) (x a : nat): x ∈ ls -> x <= fold_right max a ls.
Proof.
  intros.
  induction ls as [| y ys IH]; simpl.
  - pose proof (not_elem_of_nil x); contradiction.
  - apply elem_of_cons in H.
    destruct H as [H1 | H2]; subst; try lia.
    specialize (IH H2); lia.
Qed.

Lemma ghost_node_alloc : forall g s g1 pn lock p' lock' a,
  in_tree g g1 pn lock * ghost_ref g s |--
    (|==> EX g' , !! (s !! g' = None /\ g1 <> g') &&
                   (both_halves a g' * ghost_ref g (<[g':=(p', lock')]> s) *
                      in_tree g g1 pn lock *
                      in_tree g g' p' lock'))%I.
Proof.
  intros.
  iIntros "r".
  unfold ghost_ref, ghost_reference.
  iMod (own_alloc_strong(RA := ref_PCM node_ghost) (fun x => s !! x = None)
    (Some (Tsh, a), Some a) with "[$]") as (g') "[% ?]".
  {
    intros l.
    exists (S (fold_right max O (map fst(map_to_list s) ++ l))).
    split.
    - assert (foldr Init.Nat.max O (map fst (map_to_list s) ++ l) >= foldr Init.Nat.max O l).
      { rewrite foldr_app. apply foldr_max_ge_a1. }
      intros X%own.list_max; try lia.
    - apply eq_None_ne_Some_2.
      intros x H1.
      rewrite - elem_of_map_to_list in H1.
      assert (S (foldr Init.Nat.max 0%nat (map fst (map_to_list s) ++ l))
                <= fold_right Init.Nat.max O (map fst (map_to_list s))).
      {
        apply max_list_geq_x, elem_of_list_In.
        apply (in_map_iff fst (map_to_list s) _).
        eexists (S (foldr Init.Nat.max 0%nat (map fst (map_to_list s) ++ l)), x); split; eauto.
        apply elem_of_list_In; auto.
      }
      assert (foldr Init.Nat.max O (map fst (map_to_list s) ++ l) >=
                foldr Init.Nat.max O (map fst (map_to_list s))).
      {
        rewrite foldr_app.
        apply Z.ge_le_iff, max_foldr_l.
      }
      lia.
  }
  apply @part_ref_valid.
  iExists g'.
  iFrame.
  iMod (in_tree_add _ _ _ g' with "r") as "(% & H)"; auto.
Qed.

Lemma lock_join lsh1 lsh2 pn lock_in :
  (!!(readable_share lsh1) && @field_at CompSpecs lsh1 t_struct_tree_t (DOT _lock) lock_in pn) *
  (!!(readable_share lsh2) && @field_at CompSpecs lsh2 t_struct_tree_t (DOT _lock) lock_in pn) |--
  EX (lsh : share), !!(readable_share lsh) &&
    @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lock_in pn.
Proof.
  intros.
  normalize.
  sep_apply field_at_share_joins.
  normalize.
  destruct H1 as (lsh & H1).
  rewrite (field_at_share_join lsh1 lsh2 lsh); auto.
  Exists lsh.
  entailer !.
  apply (@join_readable1 lsh1 lsh2 lsh); auto.
Qed.

Lemma update_ghost_ref: forall g s g_in pn lock p1 p2 lock1 lock2 (a b: node_info),
    in_tree g g_in pn lock * ghost_ref g s |--
    (|==> EX g1 g2:gname,
          !!(s !! g1 = None /\ s !! g2 = None /\ (g1 <> g2)) &&
    both_halves a g1 * both_halves b g2 * ghost_ref g (<[g2:=(p2, lock2)]> (<[g1:=(p1, lock1)]> s)) *
    in_tree g g1 p1 lock1 * in_tree g g2 p2 lock2 * in_tree g g_in pn lock).
 Proof.
   intros.
   iIntros "(Hin & H)".
   iPoseProof (ghost_node_alloc g s g_in pn lock _ _ a with "[$Hin $H]") as ">H".
   iDestruct "H" as (g1) "(% & (((Ha & Hb) & Hc) & Hd))".
   iPoseProof(ghost_node_alloc with "[Hb Hd]") as ">Hnew".
   iFrame "Hd". iFrame "Hb".
   iDestruct "Hnew" as (g2) "(% & (((Ha' & Hb') & Hb) & He))".
   iModIntro.
   iExists g1, g2.
   instantiate (1:= lock2).
   instantiate (1:= p2).
   instantiate (1:= lock1).
   instantiate (1:= p1).
   instantiate (1:= b).
   iFrame.
   iPureIntro.
   rewrite and_True.
   destruct H as (Hx & Hy).
   destruct H0 as (Hz & Ht).
   split; auto.
   destruct (decide (g1 = g2)).
   - subst.
     apply (lookup_insert_None s g2 g2 (p1, lock1)) in Hz.
     destruct Hz. easy.
   - split; auto.
     apply (lookup_insert_None s g1 g2 (p1, lock1)) in Hz.
     by destruct Hz.
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

Definition tree_rep_R (tp:val) (r:(range)) (g_info: option (option ghost_info)) g : mpred :=
  if eq_dec tp nullval
  then !!(g_info = Some None) && seplog.emp
  else
  EX (ga gb : gname), EX (x : Z), EX (v pa pb : val), EX (locka lockb : val),
     !!(g_info = Some (Some (x, v, ga, gb)) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree (Vint (Int.repr x), (v, (pa, pb))) tp *
       malloc_token Ews t_struct_tree tp *
       in_tree g ga pa locka * in_tree g gb pb lockb.

(* r contains node_info (((pointer, lock), range), ghost_info (key * value * gname * gname)), and range (number * number) *)
(*
  r.1.1.1 : pn (pointer); r.1.1.2 : lock;
  r.1.2 : range; r.2 : ghost_info
*)
Definition node_rep pn g g_current (r : node_info) :=
  !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2) /\
    is_pointer_or_null r.1.1.2) &&
  field_at Ews (t_struct_tree_t) [StructField _t] r.1.1.1 pn *
  field_at Ews (t_struct_tree_t) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
  field_at Ews (t_struct_tree_t) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
   malloc_token Ews t_struct_tree_t pn * in_tree g g_current pn r.1.1.2 *
   tree_rep_R r.1.1.1 r.1.2 r.2 g.

Definition node_lock_inv_pred g p gp a := my_half gp Tsh a * node_rep p g gp a.

Definition ltree (g g_in : gname) p (lock : val) R:=
  EX lsh, !!(field_compatible t_struct_tree_t nil p /\ readable_share lsh) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p * inv_for_lock lock R).

Fixpoint ghost_tree_rep (t: @ghost_tree val) (p: val) (g_in: gname)
  (lock: val) (g: gname) (range: range) : mpred :=
 match t, range with
 | E_ghost , _ => public_half g_in ((nullval, lock, range), Some (@None ghost_info)) *
  ltree g g_in p lock (node_lock_inv_pred g p g_in ((nullval, lock, range), (Some (@None ghost_info))))
 | T_ghost a ga la lka x v b gb rb lkb, (l, r) => EX pt,
  public_half g_in ((pt, lock, range), Some (Some (x, v, ga, gb))) *
  ltree g g_in p lock (node_lock_inv_pred g p g_in ((pt, lock, range), (Some (Some (x, v, ga, gb))))) *
  ghost_tree_rep a la ga lka g (l, Finite_Integer x) *
  ghost_tree_rep b rb gb lkb g (Finite_Integer x, r)
 end.

Fixpoint find_ghost_set (t: @ghost_tree val) (g: gname) (pn: val) (lock: val) :
  (gmap gname (val * val)) :=
  match t with
  | E_ghost => {[g:= (pn, lock)]}
  | T_ghost a ga la lka x v b gb rb lkb =>
     <[g:=(pn, lock)]> ((find_ghost_set a ga la lka) ∪ (find_ghost_set b gb rb lkb))
end.

Definition find_ghost_set' (t: @ghost_tree val) : (gmap gname (val * val)) :=
  match t with
  | E_ghost => ∅
  | T_ghost a ga la lka x v b gb rb lkb => (find_ghost_set a ga la lka) ∪ (find_ghost_set b gb rb lkb)
end.

Lemma find_ghost_set_equiv t g pn lock:
  find_ghost_set t g pn lock = <[g:= (pn, lock)]> (find_ghost_set' t).
Proof. intros; destruct t; simpl; auto. Qed.

Lemma find_ghost_None tg g_root g p lk : find_ghost_set tg g_root p lk !! g = None -> g_root <> g.
Proof.
  induction tg; intros; simpl.
  - by rewrite lookup_singleton_None in H.
  - inv H; rewrite lookup_insert_None in H1; by destruct H1.
Qed.

Inductive unique_gname : ghost_tree -> Prop :=
  | Unique_Empty : unique_gname E_ghost
  | Unique_Tree : forall (x : key) (v : val) (l : ghost_tree) (g1 : gname) (la: val) (lka: val)
                    (r : ghost_tree) (g2 : gname) (rb: val) (lkb: val),
                  unique_gname l -> unique_gname r ->
                  g1 <> g2 ->
                  intersection (find_ghost_set' l) (find_ghost_set' r) = ∅ ->
                  ((find_ghost_set' l) !! g1 = None ) ->
                  ((find_ghost_set' r) !! g1 = None ) ->
                  ((find_ghost_set' l) !! g2 = None ) ->
                  ((find_ghost_set' r) !! g2 = None ) ->
                  unique_gname (T_ghost l g1 la lka x v r g2 rb lkb).

Lemma empty_intersection_l: forall {A} {K} `{Countable K} (m1 m2:  gmap K A),
    intersection m1 m2 = ∅ <-> (forall i, m1 !! i <> None -> m2 !! i = None).
Proof.
  split; intros.
  - eapply map_empty with (i := i) in H0.
    apply lookup_intersection_None in H0. destruct H0; easy.
  - apply map_empty.
    intros i.
    specialize (H0 i).
    destruct (decide (m1 !! i = None)).
    + eapply lookup_intersection_None; eauto.
    + assert (m2 !! i = None) as H1; auto.
      eapply lookup_intersection_None; eauto.
Qed.

Lemma empty_intersection_r: forall {A} {K} `{Countable K} (m1 m2:  gmap K A),
    intersection m1 m2 = ∅ <-> (forall i, m2 !! i <> None -> m1 !! i = None).
Proof.
  split; intros.
  - eapply map_empty with (i := i) in H0.
    apply lookup_intersection_None in H0; destruct H0; easy.
  - apply map_empty.
    intros i.
    specialize (H0 i).
    destruct (decide (m2 !! i = None)).
    + eapply lookup_intersection_None; eauto.
    + assert (m1 !! i = None) as H1; auto.
      eapply lookup_intersection_None; eauto.
Qed.

Lemma find_ghost_contra tg1 tg2 g1 g2 g p1 p2 lk1 lk2 x v:
  find_ghost_set' (T_ghost tg1 g1 p1 lk1 x v tg2 g2 p2 lk2) !! g = None -> g <> g1 /\ g <> g2.
Proof.
  intros.
  unfold find_ghost_set' in H.
  apply lookup_union_None_1 in H.
  destruct H as (Hx & Hy).
  erewrite find_ghost_set_equiv in Hx, Hy.
  apply lookup_insert_None in Hx, Hy.
  destruct Hx as (_ & Hx);
  destruct Hy as (_ & Hy); auto.
Qed.

Lemma ghost_set_insert x v tg g1 g2 p1 p2 lock1 lock2:
     unique_gname (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) -> g1 <> g2 ->
     ~In_ghost x tg -> find_ghost_set' (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) =
                 <[g2:=(p2, lock2)]> (<[g1:=(p1, lock1)]> (find_ghost_set' tg)).
Proof.
  intros.
  induction tg; intros; simpl.
  - rewrite insert_union_singleton_r.
    rewrite insert_empty. reflexivity.
    rewrite insert_empty. rewrite lookup_singleton_None; auto.
  - destruct (Z.ltb x k) eqn:E1; [|destruct (Z.ltb k x) eqn:E2]; simpl.
    + rewrite -> ! find_ghost_set_equiv with (g := g).
      assert (¬ In_ghost x tg1) as NIn_ghost.
      { intros Hcon. apply H1. by apply InLeft_ghost. }
      assert (unique_gname (insert_ghost x v tg1 g1 p1 lock1 g2 p2 lock2)) as HUni.
      { inv H; [rewrite E1 in H3 | rewrite E1 in H2]; [easy | by inv H2]. }
      rewrite IHtg1; auto.
      inv H. rewrite E1 in H3; easy.
      rewrite E1 in H2. inv H2; auto.
      rewrite IHtg1 in H7; auto.
      rewrite ! lookup_insert_None in H7.
      destruct H7 as ( (HG & Hx) & Hy).
      remember (find_ghost_set' tg1) as a1.
      remember (find_ghost_set tg2 g0 v3 v4) as a2.
      rewrite -> 2insert_union_l; auto.
      setoid_rewrite -> insert_commute at 1.
      setoid_rewrite -> insert_commute at 2; auto.
      done.
    + rewrite -> !find_ghost_set_equiv with (g := g0).
      assert (¬ In_ghost x tg2) as NIn_ghost.
      { intros Hcon. apply H1. by apply InRight_ghost. }
      assert (unique_gname (insert_ghost x v tg2 g1 p1 lock1 g2 p2 lock2)) as HUni.
      { inv H; [rewrite E1 E2 in H3 | rewrite E1 E2 in H2]; [easy | by inv H2]. }
      rewrite IHtg2; auto.
      inv H; [rewrite E1 E2 in H3 | rewrite E1 E2 in H2]; [easy|inv H2; auto].
      rewrite IHtg2 in H8; auto.
      rewrite IHtg2 in H10; auto.
      rewrite ! lookup_insert_None in H8, H10.
      destruct H8 as ( (HG & Hx) & Hy).
      destruct H10 as ( (HG' & Hx') & Hy').
      remember (find_ghost_set' tg1) as a1.
      remember (find_ghost_set tg2 g0 v3 v4) as a2.
      remember (find_ghost_set' tg1) as a3.
      remember (find_ghost_set' tg2) as a4.
      rewrite -> 2insert_union_r.
      setoid_rewrite -> insert_commute at 1.
      setoid_rewrite -> insert_commute at 2; auto. done.
      subst.
      eapply empty_intersection_r with (i := g2) in H6.
      { by rewrite find_ghost_set_equiv lookup_insert_None. }
      { specialize (IHtg2 HUni NIn_ghost).
        rewrite IHtg2.
        assert (<[g2:=(p2, lock2)]> (<[g1:=(p1, lock1)]> (find_ghost_set' tg2)) !! g2 = None -> False); auto.
        { intros. rewrite ! lookup_insert_None in H2. destruct H2 as (_ & H2). easy. }
      }
      subst.
      eapply empty_intersection_r with (i := g1) in H6.
      { by rewrite find_ghost_set_equiv lookup_insert_None. }
      { specialize (IHtg2 HUni NIn_ghost).
        rewrite IHtg2.
        assert (<[g2:=(p2, lock2)]> (<[g1:=(p1, lock1)]> (find_ghost_set' tg2)) !! g1 = None -> False); auto.
        { intros. rewrite ! lookup_insert_None in H2. destruct H2 as ((_ & H2) & _). easy. }
      }
    + assert (x = k) by lia.
      pose proof (InRoot_ghost x tg1 g v0 v1 tg2 g0 v3 v4 k v2).
      specialize (H3 H2). easy.
Qed.

Lemma ghost_set_insert2 x v tg g_root g1 g2 p lk p1 p2 lock1 lock2:
     unique_gname (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) ->
     g_root <> g1 -> g_root <> g2 -> g1 ≠ g2 ->
     ~In_ghost x tg ->
     find_ghost_set (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) g_root p lk =
      <[g2:=(p2, lock2)]> (<[g1:=(p1, lock1)]> (find_ghost_set tg g_root p lk)).
Proof.
  intros;
  rewrite !find_ghost_set_equiv ghost_set_insert; auto.
  setoid_rewrite -> insert_commute at 1; auto.
  setoid_rewrite -> insert_commute at 2; auto.
Qed.

Lemma insert_ghost_unique x (v : val) tg g1 g2 p1 p2 lock1 lock2:
  g1 <> g2 -> ~In_ghost x tg ->
  (find_ghost_set' tg) !! g1 = None ->
  (find_ghost_set' tg) !! g2 = None ->
  unique_gname tg ->
  unique_gname (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2).
Proof.
  intros.
  induction tg; simpl; intros.
  - simpl. apply Unique_Tree; try (intros Hcontra; inv Hcontra; fail); auto.
    simpl. apply map_interaction_empty.
  - assert (¬ In_ghost x tg1 /\ ¬ In_ghost x tg2) as (Hntg1 & Hntg2).
    {
      split; intros Hcontra; apply H0; [apply InLeft_ghost | apply InRight_ghost]; auto.
    }
    assert (find_ghost_set' tg1 !! g1 = None /\ find_ghost_set' tg1 !! g2 = None
           /\ find_ghost_set' tg2 !! g1 = None /\ find_ghost_set' tg2 !! g2 = None)
      as (Hnghosttg1g1 & Hnghosttg1g2 & Hnghosttg2g1 & Hnghosttg2g2).
    {
      split; apply lookup_union_None_1 in H1, H2;
      destruct H1 as (H1x & H1y); destruct H2 as (H2x & H2y);
      erewrite find_ghost_set_equiv in H1x, H2x, H1y, H2y;
      apply lookup_insert_None in H1x, H1y, H2x, H2y;
      destruct H1x as (H1x & _); destruct H2x as (H2x & _);
      destruct H1y as (H1y & _); destruct H2y as (H2y & _);
        eauto.
    }
    inv H3. destruct (Z.ltb x k) eqn:E; [|destruct (Z.ltb k x) eqn:E2].
    + constructor; auto.
      * rewrite ghost_set_insert; auto.
        (*Unset Printing Notations.
        Set Printing Implicit. *)
        eapply empty_intersection_l.
        rewrite empty_intersection_l in H17.
        intros ? Hin.
        apply not_eq_None_Some in Hin.
        unfold is_Some in Hin.
        destruct Hin as (y & Hin).
        apply lookup_insert_Some in Hin.
        destruct Hin as [(Hin1 & Hin2) | (Hin3 & Hin4)]. { by subst. }
        { apply lookup_insert_Some in Hin4.
          destruct Hin4 as [(HI1 & HI2) | (HI3 & HI4)]. { subst; auto. }
          { apply H17. rewrite HI4. apply Some_ne_None. }
        }
      * rewrite ghost_set_insert; auto.
        pose proof (find_ghost_contra tg1 tg2 g g0 g1 v0 v3 v1 v4 k v2) as Hcon.
        specialize (Hcon H1).
        destruct Hcon as (Hx & _).
        pose proof (find_ghost_contra tg1 tg2 g g0 g2 v0 v3 v1 v4 k v2) as Hcon.
        specialize (Hcon H2).
        destruct Hcon as (Hy & _).
        rewrite ! lookup_insert_None.
        repeat (split; auto).
      * rewrite ghost_set_insert; auto.
        pose proof (find_ghost_contra tg1 tg2 g g0 g1 v0 v3 v1 v4 k v2) as Hcon.
        specialize (Hcon H1).
        destruct Hcon as (_ & Hx).
        pose proof (find_ghost_contra tg1 tg2 g g0 g2 v0 v3 v1 v4 k v2) as Hcon.
        specialize (Hcon H2).
        destruct Hcon as (_ & Hy).
        rewrite ! lookup_insert_None.
        repeat (split; auto).
    + constructor; auto.
      * rewrite ghost_set_insert; auto.
        eapply empty_intersection_l.
        rewrite empty_intersection_l in H17.
        intros ? Hin.
        rewrite ! lookup_insert_None.
        split; try (split; auto); (intros Hcontra; subst; easy).
     * rewrite ghost_set_insert; auto.
       pose proof (find_ghost_contra tg1 tg2 g g0 g1 v0 v3 v1 v4 k v2) as Hcon.
       specialize (Hcon H1).
       destruct Hcon as (Hx & _).
       pose proof (find_ghost_contra tg1 tg2 g g0 g2 v0 v3 v1 v4 k v2) as Hcon.
       specialize (Hcon H2).
       destruct Hcon as (Hy & _).
       rewrite ! lookup_insert_None.
       repeat (split; auto).
     * rewrite ghost_set_insert; auto.
       pose proof (find_ghost_contra tg1 tg2 g g0 g1 v0 v3 v1 v4 k v2) as Hcon.
       specialize (Hcon H1).
       destruct Hcon as (_ & Hx).
       pose proof (find_ghost_contra tg1 tg2 g g0 g2 v0 v3 v1 v4 k v2) as Hcon.
       specialize (Hcon H2).
       destruct Hcon as (_ & Hy).
       rewrite ! lookup_insert_None.
       repeat (split; auto).
   + constructor; auto.
Qed.

Inductive range_info_in_tree (ri: node_info)
          (range: range): ghost_tree -> Prop :=
| riit_none: ri = ((ri.1.1.1, ri.1.1.2, range), Some None) -> range_info_in_tree ri range E_ghost
| riit_root: forall (l r: ghost_tree) (g1 g2: gname) (p1 p2: val) (lk1 lk2: val) k v,
    ri = ((ri.1.1.1, ri.1.1.2, range), Some (Some (k, v, g1, g2))) ->
    range_info_in_tree ri range (T_ghost l g1 p1 lk1 k v r g2 p2 lk2)
| riit_left: forall (l r: ghost_tree) (g1 g2: gname) (p1 p2 : val) (lk1 lk2 : val) k v,
    range_info_in_tree ri (range.1, Finite_Integer k) l ->
    range_info_in_tree ri range (T_ghost l g1 p1 lk1 k v r g2 p2 lk2)
| riit_right: forall (l r: ghost_tree) (g1 g2: gname) (p1 p2: val) (lk1 lk2: val) k v,
    range_info_in_tree ri (Finite_Integer k, range.2) r ->
    range_info_in_tree ri range (T_ghost l g1 p1 lk1 k v r g2 p2 lk2).

Definition empty_range rn tg (r_root : range) :=
  range_info_in_tree (rn, Some None) r_root tg.

Lemma empty_range_E : forall p lk r, empty_range (p, lk, r) E_ghost r.
Proof. constructor; auto. Qed.
Global Hint Resolve empty_range_E : core.

Definition keys_in_range_ghost (t : @ghost_tree val) (r : range) := forall k,
    In_ghost k t -> key_in_range k r = true.

Lemma keys_in_range_ghost_subtrees : forall t1 t2 g1 g2 p1 p2 lk1 lk2 k v (r: range),
    keys_in_range_ghost (T_ghost t1 g1 p1 lk1 k v t2 g2 p2 lk2) r ->
    sorted_ghost_tree (T_ghost t1 g1 p1 lk1 k v t2 g2 p2 lk2) ->
    key_in_range k r = true /\
    keys_in_range_ghost t1 (r.1, Finite_Integer k) /\
    keys_in_range_ghost t2 (Finite_Integer k, r.2).
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

Lemma keys_in_range_infinity : forall tg,
    keys_in_range_ghost tg (Neg_Infinity, Pos_Infinity).
Proof.
  intros ???; auto.
Qed.
Global Hint Resolve keys_in_range_infinity : core.

Lemma ghost_range_inside_ghost_range : forall (p lk : val) (r: range) (r_root : range) tg,
    empty_range (p, lk, r) tg r_root -> keys_in_range_ghost tg r_root ->
    sorted_ghost_tree tg -> range_incl r r_root = true.
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

Lemma key_not_exist_in_tree: forall tg r_root p lk d x (Hempty : empty_range (p, lk, d) tg r_root)
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

(* turn a tree into a gmap *)
Fixpoint tree_to_gmap (t: @ghost_tree val) : gmap key val :=
  match t with
  | E_ghost => empty
  | T_ghost a ga la lka x v b gb rb lkb => base.insert x v (union (tree_to_gmap a) (tree_to_gmap b))
  end.

Definition tree_rep (g g_root: gname) (m: gmap key val) : mpred :=
  EX (tg : ghost_tree) (p: val) (lock: val),
  !! ((find_ghost_set' tg) !! g_root = None /\ unique_gname tg /\ sorted_ghost_tree tg /\ tree_to_gmap tg = m) &&
    ghost_tree_rep tg p g_root lock g (Neg_Infinity, Pos_Infinity) *
    ghost_ref g (find_ghost_set tg g_root p lock).

Lemma ghost_tree_insert: forall tg g_root g g_in p lk pn lock_in x v pnt l1 r2 lk1 rk2 (r_root : range)
  (Hin : (find_ghost_set tg g_root p lk ) !! g_in = Some (pn, lock_in))
  (Hrange : keys_in_range_ghost tg r_root)
  (Hsorted : sorted_ghost_tree tg),
   ghost_tree_rep tg p g_root lk g r_root   |--
    EX r : (val * val * range), EX o : option ghost_info,
  !!(range_incl r.2 r_root = true) && public_half g_in (r, Some o) *
     ltree g g_in pn lock_in (node_lock_inv_pred g pn g_in (r, Some o)) *
  (* insert *)
   ((!! (key_in_range x r.2 = true) --> ALL g1 g2 : gname,
       match o with
         | None => public_half g_in ((pnt, r.1.2, r.2), Some (Some(x, v, g1, g2))) *
                  ltree g g_in pn lock_in (node_lock_inv_pred g pn g_in ((pnt, r.1.2, r.2), Some (Some(x, v, g1, g2)))) *
                  public_half g1 ((nullval, lk1, (r.2.1, Finite_Integer x)), Some (@None ghost_info)) *
                  ltree g g1 l1 lk1 (node_lock_inv_pred g l1 g1 ((nullval, lk1, (r.2.1, Finite_Integer x)), (Some (@None ghost_info)))) *
                  public_half g2 ( (nullval, rk2, (Finite_Integer x, r.2.2)), Some (@None ghost_info)) *
                  ltree g g2 r2 rk2 (node_lock_inv_pred g r2 g2 ((nullval, rk2, (Finite_Integer x, r.2.2)), (Some (@None ghost_info)))) -*
       (!! empty_range (r.1.1, r.1.2, r.2) tg r_root &&
          ghost_tree_rep (insert_ghost x v tg g1 l1 lk1 g2 r2 rk2) p g_root lk g r_root)
        | Some (x0, v0, ga, gb) => !! (x0 = x) && public_half g_in (r, Some (Some(x, v, ga, gb))) * ltree g g_in pn lock_in (node_lock_inv_pred g pn g_in (r, Some (Some(x, v, ga, gb)))) -*
        (!! In_ghost x tg && ghost_tree_rep (insert_ghost x v tg g1 l1 lk1 g2 r2 rk2) p g_root lk g r_root)
   end) &&
(*no changes *)
 (public_half g_in (r, Some o) *
     ltree g g_in pn lock_in (node_lock_inv_pred g pn g_in (r, Some o)) -*
                                ghost_tree_rep tg p g_root lk g r_root)
).
Proof.
  intros.
  generalize dependent g_root.
  generalize dependent lk.
  generalize dependent p.
  generalize dependent r_root.
  induction tg; intros. simpl in *; intros.
  - destruct (decide(g_root = g_in)).
    + subst.
      rewrite lookup_singleton in Hin.
      subst.
      Exists (nullval, lk, r_root).
      Exists (@None ghost_info).
      inversion Hin. subst.
      iIntros "(H1 & H2)".
      iSplitL "H1 H2". { iFrame. done. }
      iSplit; last first. { by iIntros "?". }
      iIntros "%".
      iIntros (ga gb) "(((((H1 & H2) & H3) & H4) & H5) & H6)".
      destruct r_root.
      iSplit; auto.
      iExists pnt. iFrame "H1 H2 H3 H4 H5 H6".
    + eapply lookup_singleton_None with (x:= (p, lk)) in n.
       rewrite Hin in n. easy.
 - apply keys_in_range_ghost_subtrees in Hrange as (? & ? & ?); [|auto].
    inv Hsorted. inversion Hin.
    simpl in *.
    destruct r_root.
    Intros pt.
    destruct (decide(g_root = g_in)).
    + subst.
      apply lookup_insert_rev in Hin.
      inversion Hin.
      subst.
      Exists (pt, lock_in, (n, n0)) (Some (k, v2, g0, g1)).
      assert (range_incl (n, n0) (n, n0) = true); auto.
      iIntros "(((H1 & H2) & H3) & H4)".
      iSplitL "H1 H2". by iFrame.
      iSplit; last first.
      { iIntros "(H1 & H2)". iExists _. iFrame "H1 H2 H3 H4". }
      iIntros "%".
      iIntros (ga gb) "((%Hx & H1) & H2)".
      assert ((Z.ltb x k = false) /\ (Z.ltb k x = false)) as (-> & ->); try lia.
      subst.
      iSplit. iPureIntro. by constructor.
      iExists _. iFrame "H1 H2 H3 H4".
    + apply lookup_insert_Some in H3.
      destruct H3.
      * destruct H2. contradiction.
      * destruct H2.
        rewrite lookup_union_Some_raw in H3.
        destruct H3.
         ** destruct tg1. destruct tg2. simpl in *.
            *** rewrite lookup_singleton_Some in H3.
                destruct H3. inversion H4. subst.
                Exists (nullval, lock_in, (n, Finite_Integer k)) (@None ghost_info).
                assert((range_incl (n, Finite_Integer k) (n, n0) = true)).
                {
                  unfold range_incl.
                  apply andb_prop in H.
                  destruct H.
                  apply andb_true_intro.
                  split. apply less_than_equal_refl. by apply less_than_to_less_than_equal.
                }
                iIntros "(((H1 & H2) & (H3 & H4)) & (H5 & H6))".
                iSplitL "H3 H4".  { by iFrame "H3 H4". }
                iSplit; last first.
                {
                  iIntros "(H3 & H4)". iExists _. iFrame "H1 H2 H3 H4 H5 H6".
                }
                iIntros "%".
                iIntros (ga gb) "(((((K1 & K2) & K3) & K4) & K5) & K6)".
                apply andb_prop in H5. destruct H5.
                simpl in *.
                rewrite H6.
                iSplit. iPureIntro. apply riit_left; by constructor.
                iExists pt. iFrame "H1 H2".
                iSplitR "H5 H6".
                iExists _. iFrame "K1 K2 K3 K4 K5 K6".
                iFrame "H5 H6".
            *** simpl in *.
                rewrite lookup_singleton_Some in H3.
                destruct H3. inversion H4. subst.
                Intros pt1.
                Exists (nullval, lock_in, (n, Finite_Integer k)) (@None ghost_info).
                assert (range_incl (n, Finite_Integer k) (n, n0) = true).
                {
                  unfold range_incl.
                  apply andb_prop in H.
                  destruct H.
                  apply andb_true_intro.
                  split. apply less_than_equal_refl.
                  by apply less_than_to_less_than_equal.
               }
               iIntros "(((H1 & H2) & (H3 & H4)) & (((H5 & H6) & H7) & H8))".
               iSplitL "H3 H4". { by iFrame "H3 H4". }
               iSplit; last first.
               {
                 iIntros "(H3 & H4)". iExists _. iFrame "H1 H2 H3 H4".
                 iExists _. iFrame "H5 H6 H7 H8".
               }
               iIntros "%".
               iIntros (ga gb) "(((((K1 & K2) & K3) & K4) & K5) & K6)".
               simpl in *. apply andb_prop in H5. destruct H5.
               rewrite H6.
               iSplit. iPureIntro. apply riit_left; by constructor.
               iExists pt. iFrame "H1 H2".
               iSplitL "K1 K2 K3 K4 K5 K6". { iExists _. iFrame "K1 K2 K3 K4 K5 K6". }
               iExists _. iFrame "H5 H6 H7 H8".
           *** sep_apply IHtg1.
               clear IHtg1 IHtg2.
               Intros r o. Exists r o.
               entailer!.
               { eapply range_incl_trans; [eassumption|].
                 apply key_in_range_l with (r := (_, _)); auto.
               }
               iIntros "[[IH root] tree2]".
               iSplit; last first.
               {
                 iIntros "(H1 & H2)".
                 iDestruct "IH" as "([_ IH] & IH1)".
                 iExists _. iFrame "root tree2 IH1".
                 by iSpecialize ("IH" with "[$H1 $H2]").
               }
               iIntros "%".
               iDestruct "IH" as "[[IH _] IH1]".
               iSpecialize ("IH" with "[%]"); auto.
               iIntros (ga gb).
               iSpecialize ("IH" $! ga gb).
               assert (Z.ltb x k = true) as ->.
               {
                 simpl in *.
                 destruct r.2.
                 eapply (less_than_less_than_equal_trans (Finite_Integer _) _ (Finite_Integer _)).
                 unfold key_in_range in H5; apply andb_prop in H5; apply H5.
                 unfold range_incl in H4; apply andb_prop in H4. apply H4.
               }
               destruct o as [(((?, ?), ?), ?)|].
               -- iIntros "H". iDestruct ("IH" with "H") as "(% & H)".
                  iSplit. iPureIntro. by apply InLeft_ghost.
                  iExists _; iFrame "IH1 root tree2 H".
               -- iIntros "H". iDestruct ("IH" with "H") as "(% & H)".
                  iSplit.
                  iPureIntro. by apply riit_left.
                  iExists _; iFrame "IH1 root tree2 H".
       ** sep_apply IHtg2. clear IHtg1 IHtg2. apply H3.
          Intros r o; Exists r o. entailer !.
          { eapply range_incl_trans; [eassumption|].
            apply key_in_range_r with (r := (_, _)); auto.
          }
          iIntros "[[IH root] tree2]".
          iSplit; last first.
          {
            iIntros "(H1 & H2)".
            iDestruct "IH" as "([_ IH] & IH1)".
            iExists _. iFrame "root tree2 IH1".
            by iSpecialize ("IH" with "[$H1 $H2]").
          }
          iIntros "%".
          iDestruct "IH" as "[[IH _] IH1]".
          iSpecialize ("IH" with "[%]"); auto.
          iIntros (ga gb).
          iSpecialize ("IH" $! ga gb).
          assert (Z.ltb k x = true) as Hgt.
          { destruct r.2.
            eapply (less_than_equal_less_than_trans (Finite_Integer _) _ (Finite_Integer _)).
            unfold range_incl in H4; apply andb_prop in H4; apply H4.
            unfold key_in_range in H5. apply andb_prop in H5. apply H5.
          }
          assert (Z.ltb x k = false) as -> by lia; rewrite Hgt.
          simpl in *.
          destruct o as [(((?, ?), ?), ?)|].
          -- iIntros "H". iDestruct ("IH" with "H") as "(% & H)".
             iSplit. iPureIntro; by apply InRight_ghost.
             iExists _; iFrame "IH1 root tree2 H".
          -- iIntros "H". iDestruct ("IH" with "H") as "(% & H)".
             iSplit. iPureIntro; by apply riit_right.
             iExists _. iFrame "IH1 root tree2 H".
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
        { apply IHt1 in H1; destruct (tree_to_gmap t1 !! x); auto;
            destruct (tree_to_gmap t2 !! x); auto. }
        { apply IHt2 in H1; destruct (tree_to_gmap t1 !! x); auto;
            destruct (tree_to_gmap t2 !! x); auto. }
      * destruct (tree_to_gmap t1 !! x) eqn: H1.
        { intros; constructor 2; apply IHt1; auto. }
        { destruct (tree_to_gmap t2 !! x); last contradiction.
          intros; constructor 3; apply IHt2; auto. }
Qed.

Lemma insert_tree_to_gmap : forall t x v g1 lp lka g2 rp lkb, sorted_ghost_tree t ->
  tree_to_gmap (insert_ghost x v t g1 lp lka g2 rp lkb) = <[x := v]>(tree_to_gmap t).
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

Lemma In_ghost_insert : forall x (v : val) k tg g1 g2 p1 p2 lock1 lock2,
      In_ghost k (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) ->
      x = k \/ In_ghost k tg.
Proof.
  induction tg; simpl; intros.
  - inv H; auto.
  - destruct (Z.ltb x k0) eqn: ?; [|destruct (Z.ltb k0 x) eqn: ?].
    * inv H.
      + right; apply InRoot_ghost; auto.
      + destruct (IHtg1 _ _ _ _ _ _ H1); auto.
        right. apply InLeft_ghost. auto.
      + right. apply InRight_ghost. auto.
    * inv H.
      + right. apply InRoot_ghost. auto.
      + right. apply InLeft_ghost. auto.
      + destruct (IHtg2 _ _ _ _ _ _ H1); auto.
        right. apply InRight_ghost. auto.
    * assert (k0 = x) by lia; subst.
      right; inv H.
      + apply InRoot_ghost. auto.
      + apply InLeft_ghost. auto.
      + apply InRight_ghost. auto.
Qed.

Lemma insert_ghost_sorted: forall x (v : val) tg g1 g2 p1 p2 lock1 lock2,
  sorted_ghost_tree tg ->
  sorted_ghost_tree (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2).
Proof.
  induction tg; intros; simpl.
  - apply Sorted_Ghost_Tree; auto.
    unfold gt_ghost; inversion 1.
    unfold lt_ghost; inversion 1.
  - inv H. destruct (Z.ltb x k) eqn:E; [|destruct (Z.ltb k x) eqn:E2].
    + apply Sorted_Ghost_Tree; auto.
      unfold gt_ghost; intros.
      apply In_ghost_insert in H as [?|?]; auto; lia.
    + apply Sorted_Ghost_Tree; auto.
      unfold lt_ghost; intros. apply In_ghost_insert in H as [?|?]; auto; lia.
    + assert (k = x) by lia; subst.
      apply Sorted_Ghost_Tree; auto.
Qed.

Lemma ghost_set_insert_same x (v : val) tg g1 g2 p1 p2 lock1 lock2:
      In_ghost x tg -> sorted_ghost_tree tg ->
      find_ghost_set' (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) = find_ghost_set' tg.
Proof.
  induction tg; intros; simpl.
  - inv H.
  - inv H0; inv H; simpl.
    + rewrite Z.ltb_irrefl; reflexivity.
    + specialize (Hgtl _ H1).
      destruct (Z.ltb x k) eqn:?; try lia; simpl.
      rewrite !find_ghost_set_equiv IHtg1; auto.
    + specialize (Hltr _ H1). destruct (Z.ltb x k) eqn:?;
                                [|destruct (Z.ltb k x) eqn:?]; try lia; simpl.
      rewrite !find_ghost_set_equiv IHtg2; auto.
Qed.

Lemma ghost_set_insert_same2 x (v : val) tg p lk g1 g2 g_root p1 p2 lock1 lock2:
      In_ghost x tg -> sorted_ghost_tree tg ->
      find_ghost_set (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2) g_root p lk =
        find_ghost_set tg g_root p lk.
Proof.
  intros.
  rewrite !find_ghost_set_equiv ghost_set_insert_same; auto.
Qed.

Lemma insert_ghost_same_unique x (v : val) tg g1 g2 p1 p2 lock1 lock2:
  In_ghost x tg -> sorted_ghost_tree tg ->
  unique_gname tg ->
  unique_gname (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2).
Proof.
  induction tg; intros; simpl.
  - inv H.
  - inv H0; inv H1; inv H.
    + rewrite Z.ltb_irrefl. constructor; auto.
    + specialize (Hgtl _ H1); destruct (Z.ltb x k) eqn:E; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
    + specialize (Hltr _ H1); destruct (Z.ltb x k) eqn:E; try lia.
      destruct (Z.ltb k x) eqn:E2; try lia.
      constructor; auto; rewrite ghost_set_insert_same; auto.
Qed.

Lemma tree_rep_insert: forall (t: gmap key val) g g_root g_in pn lock (x: Z) (v: val)
                      pnt p1 p2 lock1 lock2,
  tree_rep g g_root t * in_tree g g_in pn lock
  |-- EX (r : (val * val * range)) (o : option (ghost_info)),
  public_half g_in (r, Some o) * ltree g g_in pn lock (node_lock_inv_pred g pn g_in (r, Some o)) *
  (((@bupd _ (@bi_bupd_bupd _ mpred_bi_bupd))
      (EX (g1 g2: gname),
                        (my_half g1 Tsh (nullval, lock1, (r.2.1, Finite_Integer x), Some None) *
                         my_half g2 Tsh (nullval, lock2, (Finite_Integer x, r.2.2), Some None) *
                         in_tree g g1 p1 lock1 * in_tree g g2 p2 lock2) *
                         (!!(o = None /\ key_in_range x r.2 = true) &&
                         (public_half g_in ((pnt, r.1.2, r.2), Some (Some(x, v, g1, g2))) *
                         ltree g g_in pn lock (node_lock_inv_pred g pn g_in ((pnt, r.1.2, r.2), Some (Some(x, v, g1, g2)))) *
                         ltree g g1 p1 lock1 (node_lock_inv_pred g p1 g1 (nullval, lock1, (r.2.1, Finite_Integer x), (Some (@None ghost_info)))) *
                         ltree g g2 p2 lock2 (node_lock_inv_pred g p2 g2 (nullval, lock2, (Finite_Integer x, r.2.2), (Some (@None ghost_info))))) -*
                          tree_rep g g_root (<[x:=v]>t) *
                          in_tree g g_in pn lock * in_tree g g1 p1 lock1 * in_tree g g2 p2 lock2)))%I
   && (|==> (ALL g1 g2: gname, ALL (v0: val), (!!(o = Some(x, v0, g1, g2) /\
      (key_in_range x r.2 = true)) && public_half g_in (r, Some (Some(x, v, g1, g2))) *
       ltree g g_in pn lock (node_lock_inv_pred g pn g_in (r, Some (Some(x, v, g1, g2))))
         -* tree_rep g g_root (<[x:=v]>t) * in_tree g g_in pn lock)))%I &&
     (* no changes *)
     (public_half g_in (r, Some o) * ltree g g_in pn lock (node_lock_inv_pred g pn g_in (r, Some o))
     -* (tree_rep g g_root t * in_tree g g_in pn lock))).
Proof.
  intros.
  unfold tree_rep at 1.
  Intros tg p lk.
  sep_apply node_exist_in_tree.
  Intros.
  rewrite -> (ghost_tree_insert tg g_root g g_in p lk pn lock); auto.
  Intros r o.
  Exists r o.
  cancel.
  apply andp_right; [apply andp_right|].
  - erewrite (update_ghost_ref g (find_ghost_set tg g_root p lk)  g_in pn lock p1 p2 lock1 lock2
           (nullval, lock1, (r.2.1, Finite_Integer x), Some None)
           (nullval, lock2, (Finite_Integer x, r.2.2), Some None)).
   iIntros "(>H1 & [H2 _])".
   iDestruct "H1" as (g1 g2) "((((([HH H1] & H3) & H4) & #H5) & #H6) & H7)".
   iDestruct "HH" as %(? & ? & ?).
   iModIntro.
   iExists g1, g2.
   rewrite <- (both_halves_join g1).
   rewrite <- (both_halves_join g2).
   iDestruct "H1" as "(H1x & H1y)".
   iDestruct "H3" as "(H3x & H3y)".
   iSplitL "H1x H3x". iFrame. iFrame "H5 H6".
   iIntros "(HH & (((H11 & H12) & H13) & H14))".
   iDestruct "HH" as %(? & ?); subst.
   iSpecialize ("H2" with "[%]"). done.
   iSpecialize ("H2" $! g1 g2 with "[H1y H3y H11 H12 H13 H14]").
   iSplitR "H14"; last first. iFrame "H14".
   iFrame.
   iFrame "H5 H6 H7".
   iDestruct "H2" as "(% & H2)".
   unfold tree_rep.
   iExists (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2).
   iExists p, lk.
   iFrame.
   assert (~In_ghost x tg) as Hout. { by eapply key_not_exist_in_tree. }
   rewrite -> find_ghost_set_equiv in *.
   rewrite ! lookup_insert_None in H5, H6.
   destruct H5 as (Hx & Hy).
   destruct H6 as (Hz & Ht).
   assert(unique_gname (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2)) as HUn; auto.
   { apply insert_ghost_unique; auto. }
   rewrite -> ghost_set_insert, ghost_set_insert2; auto.
   iSplitR "H4". iPureIntro.
   {
     repeat (split; auto).
     {
       rewrite ! lookup_insert_None; auto.
     }
     { apply insert_ghost_sorted; auto. }
     { apply insert_tree_to_gmap; auto. }
   }
   by rewrite -> find_ghost_set_equiv.
 - iIntros "((H1 & H2) & [H3 _]) !>".
   iIntros (g1 g2 v0) "((HH & H4) & H5)". iDestruct "HH" as %(? & ?); subst.
   iSpecialize ("H3" with "[%]"); auto.
   iSpecialize ("H3" $! g1 g2 with "[$H4 $H5]"); first done.
   unfold tree_rep.
   rewrite !exp_sepcon1.
   iExists (insert_ghost x v tg g1 p1 lock1 g2 p2 lock2).
   iFrame.
   iExists p, lk.
   iDestruct "H3" as "(% & H3)". iFrame.
   rewrite -> ghost_set_insert_same, ghost_set_insert_same2 ; auto.
   iSplitR "H2"; last first; auto.
   {
     iPureIntro.
     repeat (split; auto).
     + apply insert_ghost_same_unique; auto.
     + apply insert_ghost_sorted; auto.
     + apply insert_tree_to_gmap; auto.
   }
 - iIntros "((H1 & H2) & [_ H3]) H4".
   iSpecialize ("H3" with "H4").
   iFrame "H1". unfold tree_rep.
   iExists tg, p, lk. by iFrame.
Qed.

Lemma share_divided lsh pn (lock_in : val):
  !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lock_in pn |--
  (EX lsh, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lock_in pn) *
  (EX lsh, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lock_in pn).
Proof.
  iIntros "(% & H1)".
  assert(sepalg.join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) lsh).
  apply slice.cleave_join.
  iPoseProof(field_at_share_join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) with "[H1]")
    as "(H11 & H12)"; auto; auto.
  pose proof H as H'.
  apply cleave_readable1 in H.
  apply cleave_readable2 in H'.
  iSplitL "H11";
  iExists _; by iFrame.
Qed.

Lemma in_tree_equiv g g_in p1 p2 lk1 lk2:
  in_tree g g_in p1 lk1 * in_tree g g_in p2 lk2 |-- !!((p1 = p2) /\ (lk1 = lk2)) .
Proof.
  iIntros "H".
  iPoseProof(ghost_snap_join' with "H") as (v') "(%H & _)".
  iPureIntro.
  specialize (H g_in).
  rewrite ! lookup_insert in H.
  inversion H; subst; inversion H3; inversion H0; auto.
Qed.

Lemma in_tree_inv1 (tg : ghost_tree) pn p g g_in g_root (lock_in : val) (lk : val) range:
      in_tree g g_in pn lock_in * (ghost_tree_rep tg p g_root lk g range *
         ghost_ref g (find_ghost_set tg g_root p lk)) |--
      (EX a, (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)) *
            (inv_for_lock lock_in (node_lock_inv_pred g pn g_in  a)
               -* (ghost_tree_rep tg p g_root lk g range *
                     ghost_ref g (find_ghost_set tg g_root p lk)))) &&
     (EX R, (ltree g g_in pn lock_in R) *
                           (ltree g g_in pn lock_in R
                              -* (ghost_tree_rep tg p g_root lk g range *
                                    ghost_ref g (find_ghost_set tg g_root p lk)))).
Proof.
  iIntros "(H1 & (H2 & H3))".
  iPoseProof (node_exist_in_tree with "[$H1 $H3]") as "%".
  iFrame "H3".
  iVST.
  generalize dependent g_root.
  generalize dependent lk.
  generalize dependent p.
  generalize dependent range.
  induction tg; intros range p lk g_root; simpl in *; intros; unfold ltree.
  - destruct (decide(g_root = g_in)).
    + subst.
      rewrite lookup_singleton in H.
      inversion H.
      subst.
      iIntros "(H & (H1 & H2))".
      iDestruct "H2" as (lsh) "(%H2 & (H3 & H4))".
      iSplit.
      * iExists _. iFrame "H4". iIntros "H4". iFrame "H1".
        iExists lsh. by iFrame.
      * iExists _.
        iSplitL "H3 H4". iExists _. by iFrame.
        iIntros "H2".
        iDestruct "H2" as (lsh1) "(%H21 & (H22 & H23))".
        iFrame "H1". iExists _. by iFrame.
    + eapply lookup_singleton_None with (x:= (p, lk)) in n.
      rewrite H in n. inversion n.
  - destruct range.
    destruct (decide(g_root = g_in)).
    + subst.
      apply lookup_insert_rev in H.
      inversion H.
      subst.
      iIntros "(H & H1)". iDestruct "H1" as (pt) "(((H1 & H2) & H3) & H4)".
      iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
      iSplit.
      * iExists _; iFrame. iIntros "H2". iExists _; iFrame. iExists _; by iFrame.
      * iExists _; iFrame. iSplitL "H21". iExists _. by iFrame.
        iIntros "H2". iExists _. iFrame.
    + apply lookup_insert_Some in H.
      destruct H.
      * destruct H; rewrite H in n1; contradiction.
      * destruct H.
        rewrite lookup_union_Some_raw in H0.
        destruct H0.
        ** destruct tg1. destruct tg2.
           simpl in *; unfold ltree.
           *** rewrite lookup_singleton_Some in H0.
               iIntros "(H & H1)". iDestruct "H1" as (pt) "(((H1 & H2) & (H3 & H4)) & H5)".
               iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
               iSplit.
               ++ iExists _.
                  destruct H0.
                  simpl. inversion e0. subst.
                  iDestruct "H4" as (lsh1) "(%H4 & (H41 & H42))".
                  iFrame .
                  iIntros "H2".
                  iExists _. iFrame.
                  iSplitL "H21". iExists lsh. iFrame. done.
                  iExists _. iFrame. done.
               ++ iExists _.
                  destruct H0 as (H1 & H1'). inversion H1'; subst.
                  iDestruct "H4" as (lsh1) "(%H4 & (H41 & H42))".
                  iSplitL "H41 H42". iExists lsh1. by iFrame.
                  iIntros "H11".
                  iExists _. iFrame. iExists _. by iFrame.
           *** simpl in *; unfold ltree.
               rewrite lookup_singleton_Some in H0.
               destruct H0. inversion H1. subst.
               iIntros "(H & H1)". iDestruct "H1" as (pt) "(((H1 & H2) & (H3 & H4)) & H5)".
               iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
               iDestruct "H4" as (lsh1) "(%H4 & (H41 & H42))".
               iSplit.
               ++ iExists _. iFrame.
                  iIntros "H2". iExists _. iFrame.
                  iSplitL "H21". iExists _. iFrame. done.
                  iExists _. iFrame. done.
               ++ iExists _. iFrame.
                  iSplitL "H41". iExists _. by iFrame.
                  iIntros "H2".
                  iFrame. iExists _. iFrame. iExists _. by iFrame.
           *** simpl in *; unfold ltree.
               specialize (IHtg1 (n, Finite_Integer k) v v0 g0).
               specialize (IHtg1 H0).
               simpl in IHtg1.
               iIntros "(H & H1)".
               iDestruct "H1" as (pt) "(((H1 & H2) & H3) & H4)".
               iPoseProof (IHtg1 with "[$H3 $H]") as "IH".
               iSplit.
               ++ iDestruct "IH" as "(IH & _)".
                  iDestruct "IH" as (r) "(IH & IH1)".
                  iExists r.
                  iFrame.
                  iIntros "H3".
                  iSpecialize ("IH1" with "H3").
                  iFrame.
                  iExists _. iFrame.
               ++ iDestruct "IH" as "(_ & IH)".
                  iDestruct "IH" as (r) "(IH & IH1)".
                  iExists _. iFrame "IH".
                  iIntros "H3".
                  iExists _. iFrame.
                  iSpecialize ("IH1" with "H3").
                  iFrame.
        ** destruct H0.
           specialize (IHtg2 (Finite_Integer k, n0) v2 v3 g1).
           specialize (IHtg2 H1).
           iIntros "(H & H1)".
           iDestruct "H1" as (pt) "(((H1 & H2) & H3) & H4)".
           iPoseProof (IHtg2 with "[$H $H4]") as "IH".
           iSplit.
           ++ iDestruct "IH" as "(IH & _)".
              iDestruct "IH" as (r) "(IH & IH1)".
              iExists r.
              iFrame.
              iIntros "H3".
              iExists _. iFrame.
              by iSpecialize ("IH1" with "H3").
           ++ iDestruct "IH" as "(_ & IH)".
              iDestruct "IH" as (r) "(IH & IH1)".
              iExists r.
              iFrame.
              iIntros "H".
              iSpecialize ("IH1" with "H").
              iExists _. iFrame.
Qed.

Lemma in_tree_inv g g_in g_root (pn : val) (lock_in : val) (M: gmap key val):
    in_tree g g_in pn lock_in * tree_rep g g_root M |--
      (EX a, (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)
         -* tree_rep g g_root M))) &&
      (EX R, (ltree g g_in pn lock_in R) * (ltree g g_in pn lock_in R -* tree_rep g g_root M)).
Proof.
  unfold tree_rep.
  iIntros "[H1 H2]".
  iDestruct "H2" as (tg p lk) "[[% H2] H3]".
  iPoseProof (in_tree_inv1 with "[H1 H2 H3]") as "H".
  iFrame "H1"; iFrame "H2"; iFrame "H3".
  iSplit.
  - iDestruct "H" as "(H & _)".
    iDestruct "H" as (r) "(H1 & H2)".
    iExists r. iFrame.
    iIntros "H".
    iSpecialize ("H2" with "H").
    iExists tg, p, lk.
    iDestruct "H2" as "(H1 & H2)"; iFrame; done.
  - iDestruct "H" as "(_ & H)".
    iDestruct "H" as (r) "(H1 & H2)".
    iExists r. iFrame.
    iIntros "H".
    iSpecialize ("H2" with "H").
    iExists tg, p, lk.
    iDestruct "H2" as "(H1 & H2)"; iFrame; done.
Qed.

Lemma node_conflict_local pn g g_in a b: node_rep pn g g_in a * node_rep pn g g_in b  |-- FF.
Proof.
  unfold node_rep.
  iIntros "(((((((_ & H) & _) & _) & _) & _) & _) & ((((((_ & H') & _) & _) & _) & _) & _))".
  iPoseProof (field_at_conflict Ews t_struct_tree_t (DOT _t) pn  with "[$H $H']") as "HF";
      simpl; eauto. lia.
Qed.
Global Hint Resolve node_conflict_local: saturate_local.

Lemma inv_lock g pn g_in (lock_in : val) a b c:
  node_lock_inv_pred g pn g_in a *
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in b) |--
  node_lock_inv_pred g pn g_in a *
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in c).
Proof.
  iIntros "(H1 & H2)".
  unfold inv_for_lock.
  iDestruct "H2" as (b0) "(H2 & H3)".
  destruct b0.
  - iFrame. iExists _. iFrame.
  - iExFalso.
    unfold node_lock_inv_pred.
    iDestruct "H1" as "(_ & Hn1)".
    iDestruct "H3" as "(_ & Hn2)".
    iPoseProof (node_conflict_local pn g g_in a b  with "[$Hn1 $Hn2]") as "HF"; auto.
Qed.

Lemma in_tree_inv1' (tg : ghost_tree) pn p g g_in g_root (lock_in lk : val) range a:
      in_tree g g_in pn lock_in * node_lock_inv_pred g pn g_in a *
        (ghost_tree_rep tg p g_root lk g range *
         ghost_ref g (find_ghost_set tg g_root p lk)) |--
         node_lock_inv_pred g pn g_in a *
       (inv_for_lock lock_in (node_lock_inv_pred g pn g_in  a)) *
             (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)
               -*  ( ghost_tree_rep tg p g_root lk g range *
                     ghost_ref g (find_ghost_set tg g_root p lk))).
Proof.
  iIntros "((H1 & H2) & (H3 & H4))".
  iPoseProof (node_exist_in_tree with "[$H1 $H4]") as "%".
  iFrame "H4".
  iVST.
  generalize dependent g_root.
  generalize dependent lk.
  generalize dependent p.
  generalize dependent range.
  induction tg; intros range p lk g_root; simpl in *; intros; unfold ltree.
  - destruct (decide(g_root = g_in)).
    + subst.
      rewrite lookup_singleton in H.
      inversion H.
      subst.
      iIntros "(H & ((H1 & H1') & (H2 & H3)))".
      iDestruct "H3" as (lsh) "(%H3 & (H31 & H32))".
      iPoseProof (public_agree with "[$H1 $H2]") as "%H1".
      iPoseProof (inv_lock with "[H1 H1' H32]") as "(H1 & H32)".
      iFrame "H1". iFrame "H32". iFrame.
      iFrame "H1". iFrame "H32".
      iIntros "H1". iFrame.
      iExists _. rewrite H1. iFrame. done.
    + eapply lookup_singleton_None with (x:= (p, lk)) in n.
      rewrite H in n. inversion n.
  - destruct range.
    destruct (decide(g_root = g_in)).
    + subst.
      apply lookup_insert_rev in H.
      inversion H.
      subst.
      iIntros "(H & ((H1 & H2') & H1'))".
      iDestruct "H1'" as (pt) "(((H1' & H2) & H3) & H4)".
      iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
      iPoseProof (public_agree with "[$H1 $H1']") as "%H1".
      iPoseProof (inv_lock with "[H1 H2' H22]") as "(H1 & H32)". iFrame.
      subst.
      iFrame.
      iIntros "H1". iExists _. iFrame. iExists _. by iFrame.
    + apply lookup_insert_Some in H.
      destruct H.
      * destruct H; rewrite H in n1; contradiction.
      * destruct H.
        rewrite lookup_union_Some_raw in H0.
        destruct H0.
        ** destruct tg1. destruct tg2.
           simpl in *; unfold ltree.
           *** rewrite lookup_singleton_Some in H0.
               iIntros "(H & ((H1 & H2') & H1'))".
               iDestruct "H1'" as (pt) "(((H1' & H2) & (H3 & H4)) & (H5 & H6))".
               iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
               iDestruct "H4" as (lsh1) "(%H4 & (H41 & H42))".
               destruct H0. inversion H1. subst.
               iPoseProof (public_agree with "[$H1 $H3]") as "%H11".
               iPoseProof (inv_lock with "[H1 H2' H42]") as "(H1 & H42)". iFrame.
               iFrame.
               iIntros "?".
               iExists _. iFrame.
               iSplitL "H21". iExists _. by iFrame. subst.
               iExists _. by iFrame.
           *** simpl in *; unfold ltree.
               rewrite lookup_singleton_Some in H0.
               destruct H0. inversion H1. subst.
               iIntros "(H & ((H1 & H2') & H1'))".
               iDestruct "H1'" as (pt) "(((H1' & H2) & (H3 & H4)) & H5)".
               iDestruct "H2" as (lsh) "(%H2 & (H21 & H22))".
               iDestruct "H4" as (lsh1) "(%H4 & (H41 & H42))".
               iPoseProof (public_agree with "[H1 H3]") as "%H11". iFrame.
               subst.
               iPoseProof (inv_lock with "[H1 H2' H42]") as "(H1 & H42)". iFrame.
               iFrame.
               iIntros "?". iExists _. iFrame.
               iSplitL "H21". iExists _. by iFrame.
               iExists _. by iFrame.
           *** simpl in *; unfold ltree.
               specialize (IHtg1 (n, Finite_Integer k) v v0 g0).
               specialize (IHtg1 H0).
               simpl in IHtg1.
               iIntros "(H & ((H1 & H2') & H1'))".
               iDestruct "H1'" as (pt) "(((H1' & H2) & H3) & H4)".
               iPoseProof (IHtg1 with "[$H $H1 $H2' $H3]") as  "(IH & IH1)".
               iFrame.
               iIntros "H1".
               iSpecialize ("IH1" with "H1").
               iExists _. iFrame.
        ** destruct H0.
           specialize (IHtg2 (Finite_Integer k, n0) v2 v3 g1).
           specialize (IHtg2 H1).
           iIntros "(H & ((H1 & H2') & H1'))".
           iDestruct "H1'" as (pt) "(((H1' & H2) & H3) & H4)".
           iPoseProof (IHtg2 with "[$H $H1 $H2' $H4]") as "(IH & IH1)".
           iFrame. iIntros "H1". iSpecialize ("IH1" with "H1").
           iExists _. iFrame.
Qed.

Lemma in_tree_inv' g g_in g_root (pn : val) (lock_in : val) (M: gmap key val) a:
    in_tree g g_in pn lock_in * node_lock_inv_pred g pn g_in a *
      tree_rep g g_root M |-- (node_lock_inv_pred g pn g_in a *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a))) *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)
         -* (tree_rep g g_root M)).
Proof.
  unfold tree_rep.
  iIntros "[[H1 H2] H3]".
  iDestruct "H3" as (tg p lk) "[[% H3] H4]".
  iPoseProof (in_tree_inv1' with "[$H1 $H2 $H3 $H4]") as "((H & H') & H1)".
  iFrame "H H'".
  iIntros "H".
  iSpecialize ("H1" with "H").
  iExists _, _, _.
  iDestruct "H1" as "(H1 & H1')".
  by iFrame "H1 H1'".
Qed.


Lemma node_lock_inv_pred_exclusive : forall p g g_current a1,
  exclusive_mpred (node_lock_inv_pred g p g_current a1 ).
Proof.
  intros.
  unfold exclusive_mpred, node_lock_inv_pred.
  iIntros "((_ & H) & (_ & H'))".
   iPoseProof (node_conflict_local p g g_current  a1 a1  with "[$H $H']") as "?"; done.
Qed.
Global Hint Resolve node_lock_inv_pred_exclusive : core.

(*supporting lemmas for traverse, insert *)
(*****************************************)
Lemma inv_lock_1 g pn g_in (lock_in : val) pt b c:
  field_at Ews t_struct_tree_t (DOT _t) pt pn *
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in b) |--
  field_at Ews t_struct_tree_t (DOT _t) pt pn *
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in c).
Proof.
  iIntros "(H1 & H2)".
  unfold inv_for_lock.
  iDestruct "H2" as (b0) "(H2 & H3)".
  destruct b0.
  - iFrame. iExists _. iFrame.
  - iExFalso.
    unfold node_lock_inv_pred.
    iDestruct "H3" as "(_ & Hn2)".
    unfold node_rep.
    iDestruct "Hn2" as "((((((_ & H) & _) & _) & _) & _) & _)".
    iPoseProof (field_at_conflict Ews t_struct_tree_t (DOT _t) pn with "[$H1 $H]") as "HF";
      simpl; eauto. lia.
Qed.

Lemma ltree_update g g_in p pt lk a b:
  field_at Ews t_struct_tree_t (DOT _t) pt p *
  ltree g g_in p lk (node_lock_inv_pred g p g_in a) |--
  field_at Ews t_struct_tree_t (DOT _t) pt p *
  ltree g g_in p lk (node_lock_inv_pred g p g_in b).
Proof.
  unfold ltree.
  iIntros "(H1 & H2)".
  iDestruct "H2" as (lsh) "(% & (H2 & H3))".
  iPoseProof (inv_lock_1 with "[$H1 $H3]") as "(H1 & H3)".
  iFrame "H1".
  iExists _. iFrame. iPureIntro. done.
Qed.

Lemma lock_alloc (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (g g_root g_in: gname) p lk:
  atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk |--
  (|={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk *
         (EX lsh0: share, !! readable_share lsh0 && field_at lsh0 t_struct_tree_t (DOT _lock) lk p)).
Proof.
  iIntros "(AU & #H)".
  iMod "AU" as (m) "[Hm HClose]".
  iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
  iDestruct "InvLock" as "(_ & InvLock)".
  iDestruct "InvLock" as (R) "[H1 H2]".
  unfold ltree.
  iDestruct "H1" as (lsh) "(%H12 & (H12 & H13))".
  destruct H12.
  iPoseProof (share_divided with "[$H12]") as "H1"; auto.
  iDestruct "H1" as "(H1 & H1')".
  iDestruct "H1" as (lsh1) "(% & H1)".
  iDestruct "H1'" as (lsh2) "(% & H1')".
  iAssert (EX lsh: Share.t, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lk p) with "[H1]" as "H3". iExists _; by iFrame.
  iAssert (EX lsh: Share.t, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lk p) with "[H1']" as "H3'". iExists _; by iFrame.
  iFrame. iFrame "H".
  iAssert (EX lsh : share,
          !! (field_compatible t_struct_tree_t [] p ∧ readable_share lsh) &&
          (@field_at CompSpecs lsh t_struct_tree_t (DOT _lock) lk p *
           inv_for_lock lk R))  with "[H3 H13]" as "H1".
      { iDestruct "H3" as (lsh') "(% & H3)". iExists _; iFrame. done. }
      iSpecialize ("H2" with "H1").
      by iSpecialize ("HClose" with "H2").
Qed.

Lemma push_lock_back (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (g g_root g_in: gname) p lk lsh
  (Hrs: readable_share lsh):
  atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk *
  field_at lsh t_struct_tree_t (DOT _lock) lk p |--
  (|={⊤}=> atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk ).
Proof.
  iIntros "((AU & #H) & Hf)".
  iMod "AU" as (m) "[Hm HClose]".
  iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
  iDestruct "InvLock" as "(_ & InvLock)".
  iDestruct "InvLock" as (R) "[H1 H2]".
  iDestruct "H1" as (lsh1) "(% & (Hf' & HInv))".
  destruct H as (Hf & Hrs1).
  iAssert(EX lsh0 : share, !! (field_compatible t_struct_tree_t [] p ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_tree_t (DOT _lock) lk p * inv_for_lock lk R))
              with "[Hf Hf' HInv ]" as "H1".
  {
    iPoseProof (lock_join with "[$Hf $Hf']") as "H1"; try iSplit; auto.
    iDestruct "H1" as (Lsh) "(% & Hf)".
    iExists _. by iFrame.
  }
  unfold ltree.
  iSpecialize ("H2" with "H1").
  iDestruct "HClose" as "(HClose & _)".
  iSpecialize ("HClose" with "H2").
  iMod "HClose". by iFrame "H".
Qed.

Lemma non_null_ltree g g_in p lock lsh pt p1 p2 lock1 lock2 g1 g2 range x (v : val)
  (Hrg: Int.min_signed ≤ x ≤ Int.max_signed)
  (Hp1: is_pointer_or_null p1) (Hp2: is_pointer_or_null p2)
  (Hl1: is_pointer_or_null lock1) (Hl2: is_pointer_or_null lock2)
  (Hpt: pt ≠ nullval) (Hrs: readable_share lsh)
  (Hrbl: repable_signed (number2Z range.1) ∧ repable_signed (number2Z range.2))
  (Htc: tc_val (tptr Tvoid) v) (Hkrg: key_in_range x range = true) :
  in_tree g g_in p lock * in_tree g g1 p1 lock1 * in_tree g g2 p2 lock2 *
  atomic_int_at Ews (vint 0) lock * field_at Ews t_struct_tree_t (DOT _t) pt p *
  malloc_token Ews t_struct_tree_t p * field_at lsh t_struct_tree_t (DOT _lock) lock p *
  malloc_token Ews t_struct_tree pt * my_half g_in Tsh (pt, lock, range, Some (Some (x, v, g1, g2))) *
  field_at Ews t_struct_tree_t (DOT _min) (vint (number2Z range.1)) p *
  field_at Ews t_struct_tree_t (DOT _max) (vint (number2Z range.2)) p *
  data_at Ews t_struct_tree (vint x, (v, (p1, p2))) pt |--
  ltree g g_in p lock (node_lock_inv_pred g p g_in (pt, lock, range, Some (Some (x, v, g1, g2)))).
Proof.
  unfold ltree, inv_for_lock, node_lock_inv_pred, node_rep, tree_rep_R.
  Exists lsh false.
  rewrite -> if_false; auto. simpl.
  Exists g1 g2 x v p1 p2 lock1 lock2.
  entailer !. apply derives_refl.
Qed.

Lemma null_ltree g g_in p lock (range : range)
  (Hrbl: repable_signed (number2Z range.1) ∧ repable_signed (number2Z range.2)):
  in_tree g g_in p lock * malloc_token Ews t_struct_tree_t p *
  my_half g_in Tsh (nullval, lock, range, Some None) * atomic_int_at Ews (vint 0) lock *
  data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock, (vint (number2Z range.1), vint (number2Z range.2)))) p |--
  ltree g g_in p lock (node_lock_inv_pred g p g_in (nullval, lock, range, Some None)).
Proof.
  unfold ltree, inv_for_lock, node_lock_inv_pred, node_rep, tree_rep_R.
  unfold_data_at (data_at Ews t_struct_tree_t _ p).
  Exists Ews false.
  rewrite -> if_true; auto.
  entailer !.
Qed.

Lemma key_range x a b (Hrg: Int.min_signed ≤ x ≤ Int.max_signed) (Hrgx: number2Z a < x < number2Z b):
  key_in_range x (a, b) = true.
Proof.
  unfold key_in_range; apply andb_true_iff;
    (split; unfold number2Z in Hrgx; destruct a; destruct b; simpl; rep_lia).
Qed.
Global Hint Resolve key_range : core.

Lemma release_root (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) g g_root g_in pn lock_in
  (pa pb : val) locka lockb ga gb r x0 (v1 : val)
  (Hrbl: repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2) ∧ is_pointer_or_null r.1.1.2)
  (Hnull: r.1.1.1 ≠ nullval) (Hlk: lock_in = r.1.1.2)
  (HH: r.2 = Some (Some (x0, v1, ga, gb)) ∧ Int.min_signed ≤ x0 ≤ Int.max_signed ∧ is_pointer_or_null pa ∧ is_pointer_or_null locka ∧ is_pointer_or_null pb ∧ is_pointer_or_null lockb ∧ tc_val (tptr Tvoid) v1 ∧ key_in_range x0 r.1.2 = true):
  atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q * in_tree g g_in pn lock_in * my_half g_in Tsh r *
  field_at Ews t_struct_tree_t (DOT _min) (vint (number2Z r.1.2.1)) pn *
  field_at Ews t_struct_tree_t (DOT _max) (vint (number2Z r.1.2.2)) pn *
  malloc_token Ews t_struct_tree_t pn * field_at Ews t_struct_tree_t (DOT _t) r.1.1.1 pn *
  data_at Ews t_struct_tree (vint x0, (v1, (pa, pb))) r.1.1.1 * malloc_token Ews t_struct_tree r.1.1.1 *
  in_tree g ga pa locka * in_tree g gb pb lockb
  |-- atomic_shift
        (λ _ : (),
           node_lock_inv_pred g pn g_in r * inv_for_lock lock_in (node_lock_inv_pred g pn g_in r))
        (⊤ ∖ ∅) ∅
        (λ _ _ : (), fold_right_sepcon [inv_for_lock lock_in (node_lock_inv_pred g pn g_in r)])
        (λ _ : (), atomic_shift (λ M, tree_rep g g_root M) ⊤ ∅ b Q).
Proof.
  subst.
  unfold atomic_shift; iIntros "((((((((((AU & #HITlkin) & Hmhr) & Hftmin) & Hftmax) & Hmlpn) & Hdtpn) & Hdtpapb) & Hmlpn') & #HITlka) & #HITlkb)"; iAuIntro; unfold atomic_acc; simpl.
  iMod "AU" as (m) "[Hm HClose]".
  iModIntro.
  iExists tt.
  iAssert (node_lock_inv_pred g pn g_in r)
    with "[$Hmhr $Hftmin $Hftmax $Hmlpn $Hdtpn Hdtpapb Hmlpn' HITlka HITlkb $HITlkin]" as "Hnode_Iinv".
  { iSplitR; try done.
    unfold tree_rep_R; rewrite if_false; auto.
    iExists ga, gb, x0, v1, pa, pb, locka, lockb.
    iFrame "HITlkb HITlka"; by iFrame.
  }
  iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
        with "[HITlkin $Hnode_Iinv $Hm]") as "(HI1 & HI2)".
  iFrame "HITlkin". iFrame "HI1".
  iSplit.
  {
    iIntros "(Hnode_Iinv & InvLock)".
    iSpecialize ("HI2" with "InvLock").
    iDestruct "HClose" as "[HClose _]".
    iDestruct "Hnode_Iinv" as "(Hmhr & (((Hfatpn & Hmlpn) & HITlkin2) & HTRep))".
    unfold tree_rep_R; rewrite if_false; auto.
    iDestruct "HTRep" as (ga0 gb0 x1 v0 pa0 pb0 locka0 lockb0)
                                     "((((%H122 & H123) & H124) & #H125) & #H126)".
    destruct H122 as (? & ? & ? & ? & ? & ?).
    destruct HH as (HH & Hx).
    rewrite H in HH. inversion HH. subst x1 v0 ga0 gb0.
    iAssert (!! (pa = pa0 /\ pb = pb0))%I as "Hpab".
    {
      iPoseProof (in_tree_equiv g ga pa pa0 locka locka0
                   with "[$HITlka $H125]") as "(%Hpa & _)".
      by iPoseProof (in_tree_equiv g gb pb pb0 lockb lockb0
                   with "[$HITlkb $H126]") as "(%Hpb & _)".
    }
    iDestruct "Hpab" as "(% & %)". subst pa0. subst pb0.
    iDestruct "Hfatpn" as "(((% & ?) & ?) & ?)".
    iSpecialize ("HClose" with "HI2").
    iFrame.
  }
  iIntros (_) "(H & _)".
  iSpecialize ("HI2" with "H").
  iDestruct "HClose" as "[HClose _]".
  by iSpecialize ("HClose" with "HI2").
Qed.

(*supporting lemmas for  lookup *)
(*****************************************)
Lemma range_info_incl: forall tg o ri rn r_root,
  range_info_in_tree ((ri, rn), o) r_root tg -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg ->
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

Lemma range_info_not_in_gmap: forall tg x ri rn r_root,
    sorted_ghost_tree tg -> key_in_range x rn = true ->
    keys_in_range_ghost tg r_root ->
    range_info_in_tree ((ri, rn), Some None) r_root tg -> tree_to_gmap tg !! x = None.
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

Lemma ghost_tree_rep_public_half_ramif: forall tg g_root p lk pn lockn r_root g g_in,
    find_ghost_set tg g_root p lk !! g_in = Some (pn, lockn) ->
    ghost_tree_rep tg p g_root lk g r_root |--
    EX r o, !! (range_info_in_tree (r, Some o) r_root tg) &&
              public_half g_in (r, Some o)
           * (public_half g_in (r, Some o) -* (ghost_tree_rep tg p g_root lk g r_root)).
Proof.
  intros.
  generalize dependent g_root.
  generalize dependent lk.
  generalize dependent p.
  generalize dependent r_root.
  induction tg; intros r_root p lk g_root; simpl in *; intros; unfold ltree.
  - destruct (decide(g_root = g_in)).
    + subst.
      rewrite lookup_singleton in H.
      subst.
      Exists (nullval, lk, r_root).
      Exists (@None ghost_info).
      inversion H; subst.
      iIntros "(H1 & H2)".
      iSplitL "H1".
      { iFrame. iPureIntro. try repeat (split; auto); by constructor. }
      iIntros "H1". iFrame.
    + eapply lookup_singleton_None with (x:= (p, lk)) in n.
      rewrite H in n. inversion n.
  - destruct r_root.
    Intros pt.
    destruct (decide(g_root = g_in)).
    + subst.
      apply lookup_insert_rev in H.
      inversion H; subst.
      Exists (pt, lockn, (n, n0)) (Some (k, v1, g0, g1)).
      iIntros "(((H1 & H2) & H3) & H4)".
      iSplitL "H1".
      { iFrame "H1". iPureIntro.  (split; auto); by econstructor. }
      iIntros "H".
      iExists _. iFrame.
    + apply lookup_insert_Some in H.
      destruct H.
      * destruct H; rewrite H in n1; contradiction.
      * destruct H.
        rewrite lookup_union_Some_raw in H0.
        destruct H0.
        ** destruct tg1. destruct tg2. simpl in *.
           *** rewrite lookup_singleton_Some in H0.
               destruct H0. inv H1.
               Exists (nullval, lockn, (n, Finite_Integer k)) (@None ghost_info).
               iIntros "(((H1 & H2) & (H3 & H4)) & (H5 & H6))".
               iSplitL "H3".
               { iFrame.
                 iPureIntro. (split; auto); apply riit_left; by constructor.
               }
               iIntros "H".
               iExists _. iFrame "H H1 H2 H4 H5 H6".
           *** simpl in *; unfold ltree.
               rewrite lookup_singleton_Some in H0.
               destruct H0. inversion H1. subst.
               iIntros "(((H & H1) & (H2 & H3)) & H4)".
               iExists _, _.
               iSplitL "H2".
               { iFrame. iPureIntro. (split; auto); apply riit_left; by constructor. }
               iIntros "HH".
               iExists _. iFrame "H H1 H3 H4 HH".
           *** simpl in *.
               specialize (IHtg1 (n, Finite_Integer k) v v0 g0).
               specialize (IHtg1 H0).
               simpl in IHtg1.
               iIntros "((H & H1) & H2)".
               iPoseProof (IHtg1 with "[$H1]") as "IH".
               iDestruct "IH" as (r o) "((%IH & IH1) & IH2)".
               iExists _, _. iSplitL "IH1".
               { iFrame. iPureIntro. (split; auto); apply riit_left. auto. }
               iIntros "H1".
               iExists _. iFrame.
               iSpecialize ("IH2" with "H1").
               iFrame.
       ** destruct H0.
          specialize (IHtg2 (Finite_Integer k, n0) v2 v3 g1).
          specialize (IHtg2 H1).
          iIntros "((H & H1) & H2)".
          iPoseProof (IHtg2 with "[$H2]") as "IH".
          iDestruct "IH" as (r o) "((%IH & IH1) & IH2)".
          iExists _, _. iSplitL "IH1".
          { iFrame. iPureIntro. (split; auto); apply riit_right. auto. }
          iIntros "H2".
          iExists _. iFrame.
          iSpecialize ("IH2" with "H2").
          auto.
Qed.
