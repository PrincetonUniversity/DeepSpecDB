Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks. 
Require Import VST.concurrency.conclib.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.

(* ghost state for nonblocking BST proofs -- file name?? *)

Section TREES.
 (* ghost tree properties and function *)
 Context { V : Type } .
 Variable default: V.

 Definition key := Z.

 Inductive ghost_tree: Type :=
 | E_ghost :  ghost_tree
 | T_ghost: ghost_tree ->gname ->val -> key -> V -> val -> ghost_tree -> gname ->val -> ghost_tree.


 Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 lp r g2 rp x v vp :
       (k = x) -> In_ghost k (T_ghost l g1 lp x v vp r g2 rp)
  | InLeft_ghost l g1 lp r g2 rp x v' vp :
      In_ghost k l -> In_ghost k (T_ghost l g1 lp x v' vp r g2 rp)
  | InRight_ghost l g1 lp r g2 rp x v' vp :
      In_ghost k r -> In_ghost k (T_ghost l g1 lp x v' vp r g2 rp).


Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k < x . 
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k > x . 

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
    | Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
    | Sorted_Ghost_Tree x v vp l g1 lp r g2 rp : sorted_ghost_tree l -> sorted_ghost_tree r -> gt_ghost l x -> lt_ghost r x -> sorted_ghost_tree (T_ghost l g1 lp x v vp r g2 rp ).
        
 
 Fixpoint insert_ghost (x: key) (v: V) (vp:val) (s: ghost_tree) (g1:gname) (lp:val) (g2:gname) (rp:val): ghost_tree :=
 match s with
 | E_ghost => T_ghost E_ghost g1 lp x v vp E_ghost g2 rp
 | T_ghost a ga la y v' vp' b gb rb => if  x <? y then T_ghost (insert_ghost x v vp a g1 lp g2 rp) ga la y v' vp' b gb rb
                        else if (y <? x) then T_ghost a ga la y v' vp' (insert_ghost x v vp b g1 lp g2 rp) gb rb else T_ghost a ga la x v vp' b gb rb
                        
 end.

Fixpoint find_pure_tree t : @tree V :=
  match t with 
  | E_ghost => E
  | (T_ghost a ga lp x v vp b gb rp) => T (find_pure_tree a) x v (find_pure_tree b)
end.

Lemma In_pure_In_ghost : forall tg x, In _ x (find_pure_tree tg) <-> In_ghost x tg.
Proof.
  induction tg; intros.
  - split; inversion 1.
  - simpl; split; inversion 1; subst.
    + apply InRoot_ghost; auto.
    + apply InLeft_ghost, IHtg1; auto.
    + apply InRight_ghost, IHtg2; auto.
    + apply InRoot; auto.
    + apply InLeft, IHtg1; auto.
    + apply InRight, IHtg2; auto.
Qed.

Lemma sorted_pure_sorted_ghost : forall tg, sorted_tree (find_pure_tree tg) -> sorted_ghost_tree tg.
Proof.
  intros; induction tg.
  - constructor.
  - inv H; constructor; auto.
    + unfold gt_ghost; unfold gt in *; intros ??%In_pure_In_ghost; auto.
    + unfold lt_ghost; unfold lt in *; intros ??%In_pure_In_ghost; auto.
Qed. 

Lemma insert_ghost_tree: forall tg x v vp g1 g2 lp rp, find_pure_tree (insert_ghost x v vp tg g1 lp g2 rp) = insert x v (find_pure_tree tg).
Proof.
  induction tg; intros; simpl; auto.
  destruct (x <? k); [|destruct (k <? x)]; auto; simpl; congruence.
Qed.

Definition keys_in_range_ghost t r := forall k, In_ghost k t -> key_in_range k r = true.

Lemma keys_in_range_ghost_subtrees : forall t1 t2 g1 g2 p p1 p2 k v r, keys_in_range_ghost (T_ghost t1 g1 p1 k v p t2 g2 p2) r -> sorted_ghost_tree (T_ghost t1 g1 p1 k v p t2 g2 p2) ->
  key_in_range k r = true /\ keys_in_range_ghost t1 (r.1, Finite_Integer k) /\ keys_in_range_ghost t2 (Finite_Integer k, r.2).
Proof.
  intros. inv H0. split3.
  - apply H; constructor; auto.
  - intros ??.
    specialize (H k0); spec H.
    { apply InLeft_ghost; auto. }
    apply H12 in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [->]; lia.
  - intros ??.
    specialize (H k0); spec H.
    { apply InRight_ghost; auto. }
    apply H13 in H0.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [? H1].
    simpl in *; rewrite H1; lia.
Qed.

Lemma in_range_infty:
  forall t, keys_in_range_ghost t (Neg_Infinity, Pos_Infinity).
Proof. repeat intro; auto. Qed.

End TREES.

Program Instance range_ghost : Ghost :=
  { G := (range); valid g := True; Join_G a b c := c =  merge_range a b }.
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
 
Instance range_info : Ghost := prod_PCM range_ghost (discrete_PCM ( val)).

Definition ghost_ref g r1 := ghost_reference(P := map_PCM (A :=gname) (P := range_info)) r1 g.

Definition in_tree (g1:gname) (range :range) (v:val)g := EX sh: share, ghost_part(P := map_PCM (A:=gname)) sh (ghosts.singleton g1 (range,v) ) g.


Lemma node_exist_in_tree: forall g  (r: range) v s (g_in:gname),  in_tree g_in r v g * ghost_ref g s |-- !! (exists r' : range, s g_in = Some (r', v) /\ range_incl r r' = true).
Proof.
 intros. unfold ghost_ref, in_tree; Intros sh. rewrite ref_sub. apply prop_left; intro; apply prop_right. destruct (eq_dec sh Tsh); subst.
  - exists r; split; [|apply range_incl_refl].
    unfold ghosts.singleton; apply eq_dec_refl.
  - destruct H as [r' J]. specialize (J g_in).
    unfold ghosts.singleton in J; rewrite eq_dec_refl in J.
    inv J.
    + exists r; split; auto; apply range_incl_refl.
    + destruct a3; inv H2; simpl in *.
      inv H; inv H3.
      eexists; split; [auto|].
      eapply merge_range_incl; eauto.
Qed.
 
Lemma in_tree_add : forall g s (r:range) v (r':range) v' (g1:gname) (g':gname),  s g' = None -> in_tree g1 r v g  * ghost_ref g s |-- (|==> ghost_ref g (map_upd s g' (r',v') ) * in_tree g1 r v g * in_tree g' r' v' g)%I.
Proof.
  intros.
  unfold in_tree at 1; Intros sh; iIntros "H".
  iPoseProof (ref_sub with "H") as "%".
  destruct (eq_dec g1 g').
  { subst; if_tac in H0; subst.
    + unfold ghosts.singleton in H; rewrite eq_dec_refl in H; discriminate.
    + destruct H0 as [? J]; specialize (J g').
      unfold ghosts.singleton in J; rewrite eq_dec_refl in J; inv J; congruence. }
  rewrite ghost_part_ref_join.
  iMod (ref_add(P :=  @ map_PCM gname range_info ) _ _ _ _ (ghosts.singleton g' (r', v')) (map_upd (ghosts.singleton g1 (r, v)) g' (r', v'))
    (map_upd s g' (r', v')) with "H") as "H".
  { apply (map_upd_single (P := range_info )).
    unfold ghosts.singleton; if_tac; auto; subst; contradiction. }
  { apply (map_upd_single (P := range_info )); auto. } 
  setoid_rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>".
  iDestruct "H" as "[in $]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := @ map_PCM gname range_info) sh1 sh2 sh (ghosts.singleton g1 (r, v)) (ghosts.singleton g' (r', v'))); auto.
  iDestruct "in" as "[in1 in2]"; iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  { apply  (map_upd_single (P := range_info )).
    unfold ghosts.singleton; if_tac; auto; subst; contradiction. }
  { intro; contradiction H1; eapply Share.split_nontrivial; eauto. }
  { intro; contradiction H1; eapply Share.split_nontrivial; eauto. }
Qed.


Definition ghost_info : Type := (key * val * gname * gname)%type.

Instance node_ghost : Ghost := prod_PCM range_ghost (option_PCM (P := discrete_PCM ghost_info) ).

Notation node_info := (@G node_ghost). 

Instance range_order : PCM_order (fun a b => range_incl a.1 b.1 = true /\ match snd a with None => True | Some _ => snd a = snd b end ).
Proof.
 constructor; simpl; intros.
  - constructor.
    + intro;split. apply range_incl_refl. destruct x.2;auto.
    + intro. intros. destruct H, H0. split. apply range_incl_trans with (b := y.1);auto. 
       destruct x.2; destruct y.2;destruct z.2;auto.
       inv H1;auto. discriminate. discriminate.
  - exists ( (merge_range a.1 b.1, if eq_dec a.2 None then b.2 else a.2)). destruct H, H0. 
    destruct a as [[al ar] ao]; destruct b as [[bl br] bo]; destruct c as [[cl cr] co]. unfold sepalg.join; simpl in *;split.
     + unfold sepalg_generators.Join_prod;simpl;split.
        * unfold sepalg.join;auto.
        * unfold sepalg.join. hnf. if_tac. subst ao.  apply psepalg.lower_None1. destruct ao;destruct bo;destruct co;auto;inv H1; inv H2;
        try ( (now  apply psepalg.lower_Some) || (now apply psepalg.lower_None1 ) || (now apply psepalg.lower_None2 ) || discriminate || contradiction).
    +  apply andb_prop in H;destruct H. apply andb_prop in H0;destruct H0. split.
        * rewrite andb_true_iff;split. destruct cl;destruct al; destruct bl; simpl in *; try( repeat auto).  apply Zaux.Zle_bool_true. apply Z.leb_le in H. apply Z.leb_le in H0. apply Z.min_glb;auto.
          destruct cr;destruct ar; destruct br; simpl in *; try( repeat auto).  apply Zaux.Zle_bool_true. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.max_lub;auto.
        * if_tac. auto. auto.
 - destruct H. unfold sepalg.join in H. repeat split. apply merge_range_incl with (b := b.1);auto. inv H0;auto. destruct a.2;auto. inv H4;auto.
    rewrite merge_comm in H. apply merge_range_incl with (b := a.1);auto. inv H0;auto. destruct b.2;auto. inv H4;auto.  
- destruct a as [[al ar] ao]; destruct b as [[bl br] bo];simpl in *. unfold sepalg.join. unfold sepalg_generators.Join_prod. destruct H. unfold sepalg.join. simpl. split. apply andb_prop in H;destruct H.
   f_equal. apply leq_entail_min_number;auto. apply leq_entail_max_number;auto. destruct ao;destruct bo;inv H0;try ( (now  apply psepalg.lower_Some) || (now apply psepalg.lower_None1 ) || (now apply psepalg.lower_None2 )).
Defined.

Definition finite (m : gname -> option (range * val)) := exists n, forall g x, m g = Some x -> (g <= n)%nat.

Lemma finite_new : forall m, finite m -> exists g, m g = None.
Proof.
  intros ? [n ?].
  exists (S n).
  destruct (m (S n)) eqn: Hn; auto.
  apply H in Hn; lia.
Qed.

Lemma finite_upd : forall m g x, finite m -> finite (map_upd m g x).
Proof.
  intros ??? [n ?].
  exists (max n g); intros.
  rewrite Nat.max_le_iff.
  unfold map_upd in H0; if_tac in H0; subst; eauto.
Qed.

Lemma finite_add : forall m1 m2, finite m1 -> finite m2 -> finite (map_add m1 m2).
Proof.
  intros ?? [n1 H1] [n2 H2].
  exists (max n1 n2); intros.
  unfold map_add in H.
  rewrite Nat.max_le_iff.
  destruct (m1 g) eqn: Hm1; eauto.
Qed.

Lemma finite_empty : finite (empty_map ).
Proof.
  exists O.
  unfold empty_map; discriminate.
Qed.

Lemma finite_singleton : forall g x, finite (ghosts.singleton g x).
Proof.
  intros; exists g.
  unfold ghosts.singleton; intros.
  if_tac in H; inv H; auto.
Qed.

Lemma ghost_node_alloc : forall g s (g1 : gname) (r : range) (r' : range) v v' (o : option ghost_info),
 finite s -> in_tree g1 r v g * ghost_ref g s |-- (|==> EX g', !!(s g' = None) && ghost_master1(ORD := range_order) (r', o) g' * ghost_ref g (map_upd s g' (r',v')) * in_tree g1 r v g * in_tree g' r' v' g)%I.
Proof.
  intros.
  iIntros "r".
  iMod (own_alloc_strong (RA := snap_PCM(ORD := range_order)) (fun x => s x = None) (Tsh,(r',o)) with "[$]") as (g') "[% ?]".
  { intros l.
    destruct H as [n H].
    exists (S (max (fold_right max O l) n)).
    split.
    - intros X%own.list_max.
      pose proof (Max.le_max_l (fold_right max O l) n); lia.
    - destruct (s _) eqn: Hs; auto.
      apply H in Hs.
      pose proof (Max.le_max_r (fold_right max O l) n). simpl in *. lia. }
  { simpl; auto. }
  iExists g'.
  rewrite -> prop_true_andp by auto.
  iMod (in_tree_add with "r") as "(($ & $) & $)"; auto.
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
Global Hint Resolve gsh1_not_Tsh gsh2_not_Tsh : share.

Lemma range_incl_join: forall  (r1 r2 r3 : node_info), sepalg.join r1 r2 r3 -> range_incl r1.1 r3.1 = true /\ range_incl r2.1 r3.1 = true.
Proof.
  intros.
  destruct H.
  hnf in H.
  symmetry in H; split.
  - eapply merge_range_incl; eauto.
  - rewrite merge_comm in H; eapply merge_range_incl; eauto.
Qed.

Lemma my_half_range_inf : forall g r1 r2 o,
    my_half g gsh1 (r1, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None) =
    my_half g gsh1 (r2, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None).
Proof.
  intros.
  unfold my_half; erewrite 2 ghost_part_join with
                      (a := (Neg_Infinity, Pos_Infinity, o));
  eauto with share; repeat constructor; simpl; hnf; rewrite merge_infinity; auto.
Qed.

Inductive IsEmptyGhostNode (rn : range * option ghost_info) :  (@ghost_tree val) -> range -> Prop :=
 | InEmptyGhostTree rn1 : (rn = (rn1,@None ghost_info)) -> IsEmptyGhostNode rn E_ghost rn1
 | InLeftGhostSubTree l g1 lp x v vp r g2 rp  n1 n2 :  IsEmptyGhostNode rn l (n1, Finite_Integer x) -> IsEmptyGhostNode rn (T_ghost l g1 lp x v vp r g2 rp) (n1,n2) 
 | InRightGhostSubTree l g1 lp x v vp r g2 rp n1 n2 :  IsEmptyGhostNode rn r (Finite_Integer x, n2) -> IsEmptyGhostNode rn (T_ghost l g1 lp x v vp r g2 rp) (n1,n2).

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

Fixpoint find_ghost_set {V} (t : @ghost_tree V) (g : gname) (r : range) nb : gname -> option (@G range_info) :=
  match t with 
  | E_ghost => (ghosts.singleton g (r,nb))
  | T_ghost a ga lp x v vp b gb rp =>  (map_upd (map_add (find_ghost_set a ga (fst r, Finite_Integer x) lp) (find_ghost_set b gb ( Finite_Integer x, snd r) rp)) g (r,nb))
end. 

Lemma find_ghost_set_finite : forall {V} (t : @ghost_tree V) g r0 p, finite (find_ghost_set t g r0 p).
Proof.
  induction t; intros; simpl.
  - apply finite_singleton.
  - apply finite_upd, finite_add; auto.
Qed.

(* lemmas for insert proof *)
Lemma find_ghost_set_root : forall {V} (t : @ghost_tree V) g r o, find_ghost_set t g r o g <> None.
Proof.
  destruct t; intros; simpl.
  - unfold ghosts.singleton.
    rewrite eq_dec_refl; discriminate.
  - unfold map_upd, map_add.
    rewrite eq_dec_refl; discriminate.
Qed.

Corollary find_ghost_set_out : forall {V} (t : @ghost_tree V) g r o g1, find_ghost_set t g r o g1 = None -> g1 <> g.
Proof.
  intros; intros X; subst.
  apply find_ghost_set_root in H; auto.
Qed.

Lemma map_upd_out : forall {A B} {A_eq : EqDec A} (m : A -> option B) k1 k2 v, map_upd m k1 v k2 = None -> m k2 = None /\ k2 <> k1.
Proof.
  unfold map_upd; intros.
  if_tac in H; auto; discriminate.
Qed.

Lemma upd_ghost_set_out : forall {V} (t : @ghost_tree V) g g1 g2 r o o1, map_upd (find_ghost_set t g r o) g1 o1 g2 = None ->
  g2 <> g /\ g2 <> g1.
Proof.
  intros.
  apply map_upd_out in H as [?%find_ghost_set_out ?]; auto.
Qed.

Lemma map_add_upd2 : forall {A B} {A_eq : EqDec A} (m1 m2 : A -> option B) k v, m1 k = None ->
  map_upd (map_add m1 m2) k v = map_add m1 (map_upd m2 k v).
Proof.
  intros; unfold map_upd, map_add.
  extensionality x.
  if_tac; destruct (m1 x) eqn: ?; auto; congruence.
Qed.

Lemma update_ghost_tree_with_insert: forall x v vp tg g1 g2 g_root r_root (lp rp b:val) (n1 n2:number) (o1: option ghost_info) ,
  IsEmptyGhostNode (n1,n2,o1) tg r_root  -> (find_ghost_set tg g_root r_root b) g1 = None -> (map_upd (find_ghost_set tg g_root r_root b) g1 (n1, Finite_Integer x, lp)) g2 = None -> ~ In_ghost x tg ->
  sorted_ghost_tree tg  -> keys_in_range_ghost tg r_root -> key_in_range x (n1,n2) = true ->
  find_ghost_set (insert_ghost x v vp tg g1 lp g2 rp) g_root r_root b =
  (map_upd (map_upd (find_ghost_set tg g_root r_root b) g1 (n1, Finite_Integer x, lp)) g2 (Finite_Integer x, n2, rp)).
Proof.
  intros until 1.
  revert g_root b.
  induction H as [| ???????????? IHtg1 | ???????????? IHtg2]; intros; simpl.
  + inv H.
    rewrite <- !map_add_single. rewrite map_add_comm. rewrite <- map_add_assoc. rewrite (map_add_comm (ghosts.singleton g2 (Finite_Integer x, n2, rp)) _ ). reflexivity.
    { apply upd_ghost_set_out in H1 as []. apply disjoint_compatible. hnf; intros. unfold ghosts.singleton in *. destruct (eq_dec k g2); destruct (eq_dec k g1); subst; auto; congruence. }
    { apply upd_ghost_set_out in H1 as []. unfold ghosts.singleton in *. apply disjoint_compatible. hnf; intros. unfold map_add. destruct (eq_dec k g1); destruct (eq_dec k g2); subst; simpl; auto; try congruence.
      apply find_ghost_set_out in H0; rewrite -> if_false in H6 by auto; discriminate.
      rewrite -> if_false in H6 by auto; discriminate. }
  + apply keys_in_range_ghost_subtrees in H4 as (? & ? & ?); auto. inv H3.
    apply ghost_range_inside_ghost_range in H; auto.
    eapply key_in_range_incl in H; eauto.
    unfold key_in_range in H; simpl in H.
    apply andb_prop in H as [_ ->]; simpl.
    rewrite IHtg1; auto.
    rewrite !map_add_upd; f_equal.
    rewrite (map_upd_comm _ g2). f_equal.
    apply map_upd_comm.
    { apply find_ghost_set_out in H0; auto. }
    { apply upd_ghost_set_out in H1 as []; auto. }
    { simpl in H0. unfold map_upd, map_add in H0.
      if_tac in H0; first done.
      destruct (find_ghost_set l _ _ _ _); auto. }
    { simpl in H1. unfold map_upd, map_add in *.
      if_tac; first done.
      if_tac in H1; first done.
      destruct (find_ghost_set l _ _ _ _); auto. }
    { intros X; contradiction H2; apply InLeft_ghost; auto. }
  + apply keys_in_range_ghost_subtrees in H4 as (? & ? & ?); auto. inv H3.
    apply ghost_range_inside_ghost_range in H; auto.
    eapply key_in_range_incl in H; eauto.
    unfold key_in_range in H; simpl in H.
    apply andb_prop in H as [H _]; rewrite H.
    destruct (x <? x0) eqn: ?; first lia; simpl.
    rewrite IHtg2; auto.
    rewrite -> 2map_add_upd, !map_add_upd2; auto.
    { destruct (upd_ghost_set_out _ _ _ _ _ _ _ H1).
      simpl in H1. unfold map_upd, map_add in *.
      if_tac; first done.
      if_tac in H1; first done.
      destruct (find_ghost_set l _ _ _ _); auto. }
    { simpl in H0. unfold map_upd, map_add in *.
      if_tac in H0; first done.
      destruct (find_ghost_set l _ _ _ _); auto. }
    { simpl in H0. unfold map_upd, map_add in *.
      if_tac in H0; first done.
      destruct (find_ghost_set l _ _ _ _); auto; discriminate. }
    { destruct (upd_ghost_set_out _ _ _ _ _ _ _ H1).
      simpl in H1. unfold map_upd, map_add in *.
      if_tac; first done.
      if_tac in H1; first done.
      destruct (find_ghost_set l _ _ _ _); auto; discriminate. }
    { intros X; contradiction H2; apply InRight_ghost; auto. }
 Qed.

Lemma update_ghost_tree_with_insert2: forall {V} x (v : V) vp tg g1 g2 g_root r_root lp rp b, ((In_ghost x tg) /\ (sorted_ghost_tree tg)) ->   (find_ghost_set (insert_ghost x v vp tg g1 lp g2 rp) g_root r_root b) =   
find_ghost_set tg g_root r_root b.
Proof.
intros. destruct H. revert r_root. revert dependent g_root. revert b. induction tg.
 + intros. inversion H.
 + intros. inversion H.
    -  simpl. destruct (x <? k) eqn:E2. { apply Z.ltb_lt in E2. lia. } { destruct (k <? x) eqn:E3. {apply Z.ltb_lt in E3. lia. } { simpl. assert (k = x). { lia. } rewrite H11.  reflexivity. } }
    - simpl. destruct (x <? k) eqn:E2.
      * simpl. rewrite IHtg1. reflexivity. apply H2. inversion H0. apply H15.
      * destruct (k <? x) eqn:E3. { inversion H0. unfold gt_ghost in H22. apply H22 in H2. apply Z.ltb_lt in E3. lia. } { simpl. assert (k = x). { apply Z.ltb_ge in E3. apply Z.ltb_ge in E2. lia.  } rewrite H11.  reflexivity. }
    - simpl. destruct (x <? k) eqn:E2.
      * inversion H0. unfold lt_ghost in H23. apply H23 in H2. apply Z.ltb_lt in E2. lia.
      * destruct (k <? x) eqn:E3. { simpl. rewrite IHtg2. reflexivity. apply H2. inversion H0. apply H21. } { simpl. assert (k = x). { apply Z.ltb_ge in E3. apply Z.ltb_ge in E2. lia.  } rewrite H11.  reflexivity. }
Qed.

Lemma keys_in_range_ghost_incl : forall {V} (t : @ghost_tree V) r r', keys_in_range_ghost t r -> range_incl r r' = true -> keys_in_range_ghost t r'.
Proof.
  repeat intro.
  eapply key_in_range_incl, H0; apply H; auto.
Qed.

Notation public_half := (public_half(P := node_ghost)).

Lemma key_not_exist_in_tree: forall (tg : @ghost_tree val) r_root range x, IsEmptyGhostNode range tg r_root -> keys_in_range_ghost tg r_root -> sorted_ghost_tree tg -> key_in_range x range.1 = true -> ~ In_ghost x tg.
 Proof.
  induction 1 as [| ???????????? IHtg1 | ???????????? IHtg2]; intros; subst; intros X.
  - inv X.
  - apply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); auto. inv H1.
    eapply ghost_range_inside_ghost_range in H; eauto.
    eapply key_in_range_incl in H; eauto.
    inv X.
    * unfold key_in_range in H; simpl in H; lia.
    * eapply IHtg1; eauto.
    * apply H17 in H5.
      simpl in H; lia.
  - apply keys_in_range_ghost_subtrees in H0 as (? & ? & ?); auto. inv H1.
    eapply ghost_range_inside_ghost_range in H; eauto.
    eapply key_in_range_incl in H; eauto.
    inv X.
    * unfold key_in_range in H; simpl in H; lia.
    * apply H16 in H5.
      simpl in H; lia.
    * eapply IHtg2; eauto.
Qed.
