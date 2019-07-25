Require Import VST.floyd.functional_base.
Require Import VST.veric.val_lemmas.
Require Import VST.progs.conclib.
Require Import VST.floyd.sublist.
Require Import Program.Basics. (* for compose *)
Require Import Program.Combinators. (* for compose notation "∘" *)

Require Import Sorting.Sorted.
Require Import FMapList.
Require Import Structures.OrderedTypeEx.
Module int_otable := FMapList.Make Z_as_OT.

Definition param: Z := 8.
Definition max_depth: Z := 20.

Lemma param_eq: param = 8. Proof. reflexivity. Qed.
Lemma max_depth_eq: max_depth = 20. Proof. reflexivity. Qed.
Opaque param. Opaque max_depth.

Hint Rewrite param_eq: rep_omega. Hint Rewrite max_depth_eq: rep_omega.

Definition V: Type := {p: val | is_pointer_or_null p}.
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

Instance Inhabitant_V: Inhabitant V := nullV.

Instance EqDecV: EqDec V.
Proof.
  intros [x hx] [y hy]. destruct (eq_dec x y) as [heq | hneq].
  + left. now apply exist_ext.
  + right. intro hcontr. apply hneq. inversion hcontr. reflexivity.
Qed.

Unset Elimination Schemes.
Inductive node: Type :=
| leaf: forall (entries: list (Z * V)) (address: val), node
| internal: forall (ptr0: node) (entries: list (Z * node)) (address: val), node.

Lemma node_ind (P: node -> Prop)
      (hleaf: forall entries address, P (leaf entries address))
      (hinternal: forall ptr0 entries address, P ptr0 -> Forall P (map snd entries) ->
                                          P (internal ptr0 entries address)) : forall n, P n.
Proof.
  fix hrec 1.
  intros [].
  apply hleaf.
  apply hinternal. apply hrec.
  induction entries as [|[k n] entries]. constructor.
  constructor. cbn. apply hrec. assumption.
Qed.

Inductive direct_subnode: relation node :=
| subnode_ptr0: forall ptr0 entries address,
    direct_subnode ptr0 (internal ptr0 entries address)
| subnode_entry: forall n ptr0 entries address,
    In n (map snd entries) ->
    direct_subnode n (internal ptr0 entries address).

Lemma direct_subnode_wf: well_founded direct_subnode.
Proof.
  unfold well_founded.
  apply (node_ind (fun n => Acc direct_subnode n)).
  + constructor. intros n hn. inversion hn.
  + intros * hptr0 hentries. constructor.
    intros n hn. inversion hn. assumption.
    rewrite Forall_forall in hentries. apply hentries.
    assumption.
Qed.

Definition subnode: relation node := clos_refl_trans node direct_subnode.

Lemma node_ind2 (P: node -> Prop)
      (hleaf: forall entries address, P (leaf entries address))
      (hinternal: forall ptr0 entries address, (forall i, -1 <= i < Zlength entries -> P (@Znth _ ptr0 i (map snd entries))) ->
                                          P (internal ptr0 entries address)) : forall n, P n.
Proof.
  apply (Fix direct_subnode_wf). intros n hrec.
  destruct n.
  + apply hleaf.
  + apply hinternal. intros i hi.
    apply hrec. destruct (eq_dec i (-1)).
    - subst. apply subnode_ptr0.
    - apply subnode_entry. apply Znth_In. rewrite Zlength_map; rep_omega.
Qed.

Instance Inhabitant_node: Inhabitant node :=
  leaf [] nullval. (* The empty root *)

Inductive balanced: Z -> node -> Prop :=
| balanced_leaf: forall {entries address}, balanced 0 (leaf entries address)
| balanced_internal: forall {depth ptr0 entries address},
    balanced depth ptr0 -> Forall (balanced depth) (map snd entries) ->
    balanced (Z.succ depth) (internal ptr0 entries address). 

Lemma inv_balanced_leaf: forall depth entries address,
    balanced depth (leaf entries address) ->
    depth = 0.
Proof. intros * h. inversion h. reflexivity. Qed.

Lemma inv_balanced_internal: forall depth ptr0 entries address,
    balanced depth (internal ptr0 entries address) ->
    balanced (depth - 1) ptr0 /\ Forall (balanced (depth - 1)) (map snd entries).
Proof. intros * h. inversion h.
       replace (Z.succ depth0 - 1) with depth0 by omega.
       auto.
Qed.

Lemma depth_nonneg: forall n depth, balanced depth n -> depth >= 0.
Proof.
  apply (node_ind (fun n => forall depth, balanced depth n -> depth >= 0)).
  + intros * h. now inversion h.
  + intros * hptr0 hentries depth hbal%inv_balanced_internal.
    specialize (hptr0 _ (proj1 hbal)). omega.
Qed.

Import int_otable.Raw.PX.
Arguments ltk {elt}.

Inductive good_node: forall (min: Z) (max: Z) (n: node), Prop :=
| good_leaf: forall min max entries address,
    Sorted ltk entries ->
    param <= Zlength entries <= 2*param ->
    Forall (fun k => min <= k < max) (map fst entries) ->
    good_node min max (leaf entries address)
| good_internal: forall ptr0 min_ptr0 max_ptr0 max_entries entries address,
    param <= Zlength entries <= 2*param ->
    good_node min_ptr0 max_ptr0 ptr0 ->
    assert_entries max_ptr0 max_entries entries ->
    good_node min_ptr0 max_entries (internal ptr0 entries address)
with assert_entries: forall (min max: Z) (entries: list (Z * node)), Prop :=
| assert_nil: forall m m', m <= m' -> assert_entries m m' []
| assert_cons: forall k n max_n max tl,
    good_node k max_n n ->
    assert_entries max_n max tl ->
    assert_entries k max ((k, n) :: tl).

Scheme Induction for good_node Sort Prop
with Induction for assert_entries Sort Prop.

Fixpoint good_root (root: node): Prop :=
  match root with
  | leaf entries address => Sorted ltk entries /\ Zlength entries <= 2*param
  | internal ptr0 entries address =>
    exists min_ptr0 max_ptr0 max, 1 <= Zlength entries <= 2*param
                             /\ good_node min_ptr0 max_ptr0 ptr0
                             /\ assert_entries max_ptr0 max entries
  end.

Lemma good_node_root: forall n min max, good_node min max n -> good_root n.
Proof.
  intros * h.
  inversion h; simpl. split; [assumption | rep_omega].
  exists min. exists max_ptr0. exists max. split3.
  rep_omega.
  assumption.
  assumption.
Qed.

Definition is_leaf (n: node): Prop :=
  match n with
  | leaf _ _ => True
  | _ => False
  end.

Definition is_leaf_dec (n: node): {is_leaf n} + {not (is_leaf n)} :=
  match n as m return {is_leaf m} + {not(is_leaf m)} with
  | leaf _ _ => left I
  | internal _ _ _ => right (fun hcontr => hcontr)
  end.

Definition keys (n: node): list Z := 
  match n with
  | leaf entries _ | internal _ entries _ => map fst entries
  end.

Definition node_address (n: node): val := 
  match n with | leaf _ address | internal _ _ address => address end.

Arguments node_address n: simpl nomatch.

Definition num_keys (n: node): Z := Zlength (keys n).

Print int_otable.

Fixpoint flatten (n: node): int_otable.Raw.t V :=
  match n with
  | leaf entries _ => entries
  | internal ptr0 entries _ => flatten ptr0 ++ flat_map (flatten ∘ snd) entries
  end.

Fixpoint num_records (n: node): Z :=
  match n with
  | leaf entries _ => Zlength entries
  | internal ptr0 entries _ => num_records ptr0 + fold_right Z.add 0 (map (num_records ∘ snd) entries)
  end.

Lemma num_records_flatten_length n : Zlength (flatten n) = num_records n.
Proof.
  apply (node_ind (fun n => Zlength (flatten n) = num_records n)).
  + intros. reflexivity.
  + intros * hlength hforall.
    simpl. rewrite Zlength_app, hlength, flat_map_concat_map, Zlength_concat,
           map_map. do 2 f_equal.
    apply map_ext_in.
    intros [k n']. rewrite Forall_forall in hforall.
    intro hin. eapply in_map in hin.
    apply hforall. eassumption.
Qed.

Lemma good_node_extend: forall min max n,
    good_node min max n ->
    forall min' max', min' <= min -> max <= max' ->
    good_node min' max' n.
Proof.
  apply (good_node_ind_dep (fun min max n h => forall min' max', min' <= min -> max <= max' ->
    good_node min' max' n) (fun min max entries h => forall max', max <= max' -> assert_entries min max' entries)).
  + constructor; auto; eapply Forall_impl; try eassumption; cbn; intros; omega.
  + intros * hbounds hptr0 hrecptr0 hentries hrecentries * hmin' hmax'.
    econstructor; auto. apply hrecptr0. assumption. omega.
  + intros. apply assert_nil. rep_omega.
  + intros. econstructor. eassumption. auto.
Qed.

Lemma assert_entries_le: forall {min max entries},
    assert_entries min max entries ->
    min <= max.
Proof.
  apply (assert_entries_ind_dep (fun min max n h => min < max) (fun min max entries h => min <= max));
  intros;
  try match goal with
        | [ h: Forall _ _ |- _ ] => rewrite Forall_map in h; inversion h
      end; subst; cbn in *; rep_omega.
Qed.

Lemma good_node_lt: forall {min max n},
    good_node min max n ->
    min < max.
Proof.
  apply (good_node_ind_dep (fun min max n h => min < max) (fun min max entries h => min <= max));
  intros;
  try match goal with
        | [ h: Forall _ _ |- _ ] => rewrite Forall_map in h; inversion h
      end; subst; cbn in *; rep_omega.
Qed.

Lemma good_node_flatten_bounds: forall n min max,
  good_node min max n ->
  Forall (fun k => min <= k < max) (map fst (flatten n)).
Proof.
  apply (node_ind (fun n => forall min max, good_node min max n ->
                                    Forall (fun k => min <= k < max) (map fst (flatten n)))).
  + intros * h. inversion h. assumption.
  + intros * hptr0 hentries * h.
    cbn. rewrite map_app, Forall_app.
    split.
    - apply hptr0. inversion h. subst.
      eapply good_node_extend. eassumption. omega.
      eapply assert_entries_le. eassumption.
    - rewrite flat_map_concat_map, concat_map, map_map.
      rewrite Forall_forall in hentries |- *.
      intros k hkin%in_concat. destruct hkin as (l & hkl & hl).
      cbn in hl. apply list_in_map_inv in hl.
      destruct hl as ([k' n] & hl & hk'n).
      setoid_rewrite Forall_forall in hentries. eapply hentries.
      apply in_map. eassumption. inversion h. subst. cbn.
      { apply good_node_lt in H5. pose proof (assert_entries_le H6).
        clear -hk'n H5 H H6. revert dependent max_ptr0.
        induction entries.
        intros. contradiction. 
        intros max_ptr0 hmax_ptr0 hentries hmax.
        destruct hk'n. 
        * subst. inversion hentries. eapply good_node_extend. eassumption. omega.
          eapply assert_entries_le. eassumption.
        * inversion hentries. eapply IHentries with (max_ptr0 := max_n). assumption.
          etransitivity. eassumption. eapply good_node_lt. eassumption. assumption.
          eapply assert_entries_le. eassumption. }
      subst; assumption.
Qed.

Lemma good_root_flatten_sorted: forall n,
  good_root n ->
  Sorted ltk (flatten n).
Proof.
  apply (node_ind (fun n => good_root n -> Sorted ltk (flatten n))).
  + intros * h.
    simpl in h |- *. easy.
  + intros * hrecptr0 hrecentries h.
    simpl in h |- *. destruct h as (min_ptr0 & max_ptr0 & max & _ & hptr0 & hentries).
    specialize (hrecptr0 (good_node_root _ _ _ hptr0)).
    pose proof (good_node_lt hptr0) as hminptr0.
    apply good_node_flatten_bounds in hptr0.
    revert hptr0 hminptr0 hrecptr0 hentries.
    generalize (flatten ptr0) max_ptr0.
    induction entries as [|[k n] entries]; intros t maxt htbounds hminptr0 htsorted hentries; simpl.
    rewrite app_nil_r. auto.
    rewrite app_assoc. inversion hentries. subst.
    eapply IHentries with (max_ptr0 := max_n).
    now inversion hrecentries.
    rewrite map_app, Forall_app. split.
    eapply Forall_impl; try eassumption. apply good_node_lt in H3; intros ? h; cbn in h; omega.
    apply good_node_flatten_bounds. eapply good_node_extend. eassumption.
    omega. omega. etransitivity. eassumption. eapply good_node_lt. eassumption.
    { 
      assert (hsorted_flatten: Sorted ltk (flatten n)).
      { inversion hrecentries. apply H1.
        eapply good_node_root. eassumption. }
      pose proof (good_node_flatten_bounds _ _ _ H3) as hbounds_flatten.
      induction t.
      assumption.
      simpl. apply Sorted_inv in htsorted. constructor. apply IHt.
      now inversion htbounds.
      easy.
      destruct htsorted as [htsorted hhdrel].
      inversion hhdrel.
      * simpl.
        destruct (flatten n) as [|[k' n'] l]. constructor.
        constructor. inversion hbounds_flatten. inversion htbounds. 
        unfold ltk; cbn; omega.
      * simpl. constructor. subst. now inversion hhdrel.
    } 
    assumption.
Qed.

Import Sumbool. Arguments sumbool_and {A B C D}.

Fixpoint find_path (key: Z) (root: node) {struct root}: list (Z * node) :=
match root with
| leaf entries address =>
  let index := (fix get_index entries index :=
     match entries with
     | [] => index
     | (k, r) :: entries => if Z_ge_lt_dec k key then index else get_index entries (index + 1)
  end) entries 0 in [(index, root)]
| internal ptr0 (((first_k, first_n) :: _) as entries) address =>
  if Z_lt_ge_dec key first_k then (-1, root) :: find_path key ptr0 else
    (fix get_cursor_entry entries index :=
       match entries with
       | [] => [] (* impossible case *)
       | [(k, n)] => (index, root) :: find_path key n
       | (k, n) :: (((k', n') :: _) as entries) =>
         if (sumbool_and (Z_le_dec k key) (Z_lt_ge_dec key k')) then (index, root) :: find_path key n
         else get_cursor_entry entries (index + 1)
       end) entries 0
| internal ptr0 [] p => (-1, root) :: find_path key ptr0
end.

Theorem find_path_leaf: forall key entries address,
    exists i, find_path key (leaf entries address) = [(i, leaf entries address)] /\
         0 <= i <= Zlength entries /\
         Forall (Z.gt key) (sublist 0 i (map fst entries)) /\
         (i < Zlength entries -> fst (Znth i entries) >= key).
Proof.
  intros.
  pose (i entries z := (fix get_index (entries0 : list (Z * V)) (index : Z) {struct entries0} : Z :=
         match entries0 with
         | [] => index
         | (k, _) :: entries1 => if Z_ge_lt_dec k key then index else get_index entries1 (index + 1)
         end) entries z).
  
  assert (hadd: forall entries z, i entries z = i entries 0 + z).
  { intro l; induction l as [|[k n] l]; simpl; intro z.
    omega.
    destruct Z_ge_lt_dec. omega.
    rewrite (IHl (z + 1)), (IHl 1).
    omega. }
  
  assert (hbounds: forall entries, 0 <= i entries 0 <= Zlength entries).
  { intro l; induction l as [|[k' n'] l]; simpl.
    - easy.
    - rewrite Zlength_cons. destruct Z_ge_lt_dec. omega.
      rewrite hadd. omega. }

  assert (hforall: Forall (Z.gt key) (sublist 0 (i entries 0) (map fst entries))).
  { induction entries as [|[k n] entries].
    rewrite sublist_nil_gen. constructor.
    unfold i; omega. simpl.
    destruct Z_ge_lt_dec. rewrite sublist_nil_gen. constructor. omega.
    specialize (hbounds entries).
    rewrite sublist_0_cons' by (try rewrite hadd; rep_omega). constructor. omega.
    rewrite hadd, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. assumption. }

  exists (i entries 0); split3; auto; split; auto.
  { clear hforall; induction entries as [|[k n] entries].
    cbn. omega.
    simpl. destruct Z_ge_lt_dec. rewrite Znth_0_cons. simpl; omega.
    rewrite Zlength_cons, hadd, Znth_pos_cons,
      <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by (specialize (hbounds entries); rep_omega).
    intros. apply IHentries. omega. }
Qed.

Theorem find_path_internal: forall key ptr0 entries address,
    exists i, find_path key (internal ptr0 entries address) =
         (i, internal ptr0 entries address) :: find_path key (@Znth _ ptr0 i (map snd entries)) /\
         -1 <= i < Zlength entries /\
         Forall (Z.ge key) (sublist 0 (i + 1) (map fst entries)) /\
         (i + 1 < Zlength entries -> key < Znth (i + 1) (map fst entries)).
Proof.
  intros.
  destruct entries as [|[first_k first_n] entries]; simpl.
  + exists (-1). split3.
    - reflexivity.
    - rewrite Zlength_nil; omega.
    - now rewrite sublist_of_nil, Zlength_nil, Znth_nil.
  + destruct Z_lt_ge_dec as [hlt | hge]; simpl.
    - exists (-1). rewrite Zlength_cons, Znth_underflow, sublist_nil, Znth_0_cons by omega.
      split3; try easy; rep_omega.
    - generalize (internal ptr0 ((first_k, first_n) :: entries) address) as root.
      revert hge.
      generalize first_k as k, first_n as n. clear first_k first_n. intros.

      pose (i l z := (fix get_index (l : list (Z * node)) index :=
                     match l with
                     | [] => index
                     | [(k, n)] => index
                     | (k, _) :: ((k', _) :: _) as tl =>
                       if (sumbool_and (Z_le_dec k key) (Z_lt_ge_dec key k'))
                       then index
                       else get_index tl (index + 1)
                     end) l z).
      
      assert (hadd: forall l z, i l z = i l 0 + z).
      { induction l as [|[k' n'] l]; intros; simpl.
        omega.
        destruct l as [|[k'' n''] l]. omega.
        destruct sumbool_and. omega. rewrite (IHl (z + 1)), (IHl 1). omega. }
      
      assert (hbounds: forall l k n z, z <= i ((k, n) :: l) z < z + 1 + Zlength l).
      { induction l as [|[k' n'] l]; intros. simpl.
        rewrite Zlength_nil; simpl; omega.
        specialize (IHl k' n' (z + 1)). rewrite Zlength_cons; simpl in IHl |- *.
        destruct sumbool_and; rep_omega. }
      
      exists (i ((k, n) :: entries) 0).
      split3.
      ++ generalize k as k0, n as n0.
         change 1 with (0 + 1) at 2.
         generalize 0 at -5 as z.
         induction entries as [|[k0 n0] entries]; intros.
         reflexivity.
         simpl; destruct sumbool_and.
         reflexivity.
         simpl in hadd.
         rewrite IHentries.
         rewrite (Znth_pos_cons _ (n0 :: _)).
         simpl. 
         specialize (hadd ((k0, n0) :: entries) 1). simpl in hadd.
         rewrite hadd. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. reflexivity. 
         destruct entries as [|[k' n'] entries]. omega.
         destruct sumbool_and. omega. specialize (hbounds entries k' n' 2). omega.
      ++ pose proof (hbounds entries k n 0) as h.
         rewrite Zlength_cons; omega.
      ++ split.
      -- revert hge. generalize k as k0, n as n0. 
         induction entries as [|[k' n'] entries]; intros.
         cbn. constructor. omega. constructor.
         specialize (IHentries k' n').
         rewrite <- hadd in IHentries.
         pose proof (hbounds entries k n 1). pose proof (hbounds entries k' n' 1).
         simpl in *. rewrite sublist_0_cons in IHentries by rep_omega.
         destruct sumbool_and.
         cbn. constructor. omega. constructor.
         rewrite sublist_0_cons by rep_omega.
         constructor. apply Z.le_ge. omega.
         rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_0_cons by rep_omega.
         constructor. omega.
         specialize (IHentries ltac:(omega)).
         inversion IHentries. assumption.
      -- revert hge. generalize k. induction entries as [|[k' n'] entries]. 
         cbn; intros; omega.
         simpl; intros k_ hk_.
         specialize (IHentries k'). specialize (hbounds entries k' n' 1).
         destruct sumbool_and.
         * simpl. rewrite Znth_pos_cons, Znth_0_cons; omega.
         * rewrite <- hadd in IHentries. simpl in IHentries.
           rewrite Znth_pos_cons. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
           intro h. apply IHentries. omega.
           rewrite Zlength_cons, Zlength_cons in h.
           rewrite Zlength_cons. rep_omega.
           simpl in hbounds. rep_omega.
Qed.

Corollary find_path_hd: forall key root,
    exists tl, map snd (find_path key root) = root :: tl.
Proof.
  intros.
  destruct root as [|ptr0].
  + pose proof (find_path_leaf key entries address) as hleaf.
    destruct hleaf as [i (heq & _)].
    rewrite heq. exists nil. reflexivity.
  + pose proof (find_path_internal key ptr0 entries address) as hinternal.
    destruct hinternal as [i (heq & _)].
    rewrite heq. exists (map snd (find_path key (@Znth _ ptr0 i (map snd entries)))). reflexivity.
Qed.

Corollary find_path_Zlength: forall key root depth,
    balanced depth root ->
    Zlength (find_path key root) = depth + 1.
Proof.
  intro key. apply (node_ind (fun root => forall depth, balanced depth root -> Zlength (find_path key root) = depth + 1)).
  + intros * h. inversion h. reflexivity.
  + intros * hptr0 hentries depth h.
    inversion h. edestruct find_path_internal as [i (heq & hbounds & _)].
    rewrite heq. rewrite Zlength_cons.
    destruct (eq_dec i (-1)).
    - subst. replace (Znth _ _) with ptr0 by now compute.
      erewrite hptr0 by eassumption. reflexivity.
    - rewrite Forall_forall in hentries.
      erewrite hentries. reflexivity. apply Znth_In. rewrite Zlength_map; rep_omega.
      eapply computable_theorems.Forall_forall1. eassumption.
      apply Znth_In. rewrite Zlength_map; rep_omega.
Qed.

Theorem find_path_is_path: forall key root,
    Sorted (flip direct_subnode) (map snd (find_path key root)).
Proof.
  intro key.
  apply node_ind.
  + repeat constructor.
  + intros * hptr0 hentries.
    edestruct (find_path_internal key ptr0 entries address) as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq.
    case_eq (@Znth _ ptr0 i (map snd entries)).
  - intros entries' address' h.
    edestruct (find_path_leaf key entries' address') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. constructor. do 2 constructor.
    constructor. simpl. rewrite <- h.
    destruct (eq_dec i (-1)) as [hm1|hm1].
    rewrite hm1. compute. constructor.
    apply subnode_entry. apply Znth_In. rewrite Zlength_map; rep_omega.
  - intros ptr0' entries' address' h.
    edestruct (find_path_internal key ptr0' entries' address') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. simpl.
    destruct (eq_dec i (-1)) as [hm1 | hm1].
    * rewrite hm1 in *. compute in h. rewrite h.
      constructor. rewrite h, heq' in hptr0.
      assumption.
      constructor. constructor.
    * constructor. rewrite Forall_forall in hentries.
      specialize (hentries (internal ptr0' entries' address')).
      rewrite heq' in hentries. apply hentries.
      rewrite <- h. apply Znth_In. rewrite Zlength_map. omega.
      constructor. rewrite <- h. apply subnode_entry with (n := Znth i (map snd entries)).
      apply Znth_In. rewrite Zlength_map. omega.
Qed.

Corollary find_path_subnode: forall key root n,
    List.In n (map snd (find_path key root)) -> subnode n root.
Proof.
  intros key root. rewrite <- Forall_forall.
  change (fun x => subnode x root) with (flip subnode root).
  apply Sorted_extends.
  apply flip_Transitive. unfold subnode, Transitive. apply rt_trans.
  edestruct find_path_hd as [tl htl].
  rewrite htl.
  constructor. rewrite <- htl.
  apply Sorted_ind with (R := flip direct_subnode). constructor.
  intros * hl hldirect hhdrel. constructor. assumption.
  inversion hhdrel. constructor. constructor. apply rt_step. assumption.
  apply find_path_is_path.
  constructor. apply rt_refl.
Qed.

Fixpoint insert_aux (key: Z) (rec: V) (l: list (Z * node)):
  node * option (Z * node) :=
  match l with
  | (i, leaf entries address) :: _ =>
    if (sumbool_and (Z_lt_ge_dec i (Zlength entries)) (eq_dec (fst (Znth i entries)) key)) then
      (leaf (upd_Znth i entries (key, rec)) address, None)
    else
      let new_entries := sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_address := nullval in
        let new_node_left := leaf (sublist 0 param new_entries) address in
        let new_node_right := leaf (sublist param (2 * param + 1) new_entries) new_address in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (leaf new_entries address, None)
  | (i, internal ptr0 entries address) :: tl =>
    let (new_at_i, entry_to_add) := insert_aux key rec tl in
    let ptr0 := if eq_dec i (-1) then new_at_i else ptr0 in
    let entries := if Z_ge_lt_dec i 0 then upd_Znth i entries (fst (Znth i entries), new_at_i) else entries in
    match entry_to_add with
    | None => (internal ptr0 entries address, None)
    | Some (new_key, new_node) =>
      let new_entries := sublist 0 (i + 1) entries ++ (new_key, new_node) :: sublist (i + 1) (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_address := nullval in
        let new_node_left := internal ptr0 (sublist 0 param new_entries) new_address in
        let new_node_right := internal (snd (Znth param new_entries))
                                       (sublist (param + 1) (2 * param + 1) new_entries) address in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (internal ptr0 new_entries address, None)
    end 
  | [] => (default, None)
  end.

Definition insert (root: node) (key: Z) (value: V): node :=
  let path := find_path key root in
  let (root, new_entry) := insert_aux key value path in
  match new_entry with
    | None => root
    | Some new_entry => internal root [new_entry] nullval
  end.

Lemma Sorted_sublist: forall X R (l: list X) lo hi,
    Sorted R l -> Sorted R (sublist lo hi l).
Proof.
  induction l; intros * h.
  + now rewrite sublist_of_nil.
  + destruct (Z_lt_ge_dec lo hi).
    - destruct (Z_gt_le_dec lo 0).
      { rewrite sublist_S_cons by assumption. apply IHl.
        inversion h. assumption. }
      { rewrite sublist_0_cons' by omega.
        apply Sorted_inv in h. destruct h as [hsorted hR].
        constructor. apply IHl. easy.
        destruct l.
        rewrite sublist_of_nil. constructor.
        apply HdRel_inv in hR.
        destruct (Z_lt_ge_dec lo (hi - 1)).
        rewrite sublist_0_cons' by omega. constructor. assumption.
        rewrite sublist_nil_gen by omega. constructor. }
    - rewrite sublist_nil_gen. constructor. omega.
Qed.

Lemma Sorted_ltk_map: forall X (l: list (Z * X)),
    Sorted ltk l <-> Sorted Z.lt (map fst l).
Proof.
  intros.
  unfold ltk.
  induction l. split; constructor.
  cbn; split; intros h%Sorted_inv; destruct h as [hsorted hhdrel]; constructor.
  + rewrite <- IHl. assumption.
  + inversion hhdrel. constructor. constructor. assumption.
  + rewrite IHl. assumption.
  + inversion hhdrel. symmetry in H0. apply map_eq_nil in H0. subst. constructor. 
    destruct l. discriminate. inversion H. subst. constructor. assumption.
Qed.

Lemma Sorted_insert {X} {x: Inhabitant X}: forall (l: list (Z * X)) i key value,
    0 <= i <= Zlength l ->
    Sorted ltk l ->
    Forall (Z.gt key) (sublist 0 i (map fst l)) ->
    (i < Zlength l -> fst (Znth i l) > key) ->
    Sorted ltk (sublist 0 i l ++ (key, value) :: sublist i (Zlength l) l).
Proof.
  intros * hi hsorted hbefore hafter.
  destruct (eq_dec i (Zlength l)) as [heq|hneq].
  - rewrite sublist_same_gen, sublist_nil_gen by rep_omega.
    rewrite sublist_same_gen in hbefore by (try rewrite Zlength_map; rep_omega).
    clear -hsorted hbefore.
    rewrite Sorted_ltk_map, map_app. simpl. rewrite Sorted_ltk_map in hsorted.
    induction l. repeat constructor.
    simpl. constructor. apply IHl. now inversion hsorted. now inversion hbefore.
    destruct l; constructor. inversion hbefore; omega. inversion hsorted. now inversion H2.
  - rewrite Sorted_ltk_map, map_app, map_sublist, map_cons, map_sublist, (sublist_next i), Znth_map by
        (try rewrite Zlength_map; rep_omega).
    specialize (hafter ltac:(rep_omega)).
    erewrite <- sublist_same in hsorted by reflexivity.
    rewrite sublist_split with (mid := i), (sublist_next i), Sorted_ltk_map, map_app, map_cons, map_sublist, map_sublist in hsorted by (try rewrite Zlength_sublist; rep_omega).
    revert hafter hbefore hsorted. simpl. clear.
    generalize (sublist 0 i (map fst l)) (sublist (i + 1) (Zlength l) (map fst l)) (fst (Znth i l)).
    intros. induction l0.
    constructor. assumption. constructor. omega.
    simpl. constructor. apply IHl0. now inversion hbefore. now inversion hsorted.
    destruct l0. constructor. inversion hbefore; omega.
    constructor. inversion hsorted. inversion H2. assumption.    
Qed.

Lemma Sorted_bounds {X} {inh: Inhabitant X}: forall (l: list (Z * X)) i j,
    0 <= i < j -> j < Zlength l ->
    Sorted ltk l ->
    Forall (fun k => fst (Znth i l) <= k < fst (Znth j l)) (sublist i j (map fst l)).
Proof.
  setoid_rewrite Sorted_ltk_map.
  induction l; simpl.
  + intros. rewrite sublist_of_nil. constructor.
  + intros i j hij hj hsorted.
    unshelve epose proof (Sorted_extends _ hsorted) as hforall.
    do 3 intro; omega. rewrite Zlength_cons in hj. inversion hsorted.
    destruct (eq_dec i 0).
    ++ subst. rewrite sublist_0_cons, Znth_0_cons, Znth_pos_cons by omega.
       constructor.
       { split. omega.
         rewrite Forall_forall in hforall. eapply hforall.
         apply in_map. apply Znth_In. omega. }
       destruct (eq_dec j 1). subst. rewrite sublist_nil_gen by omega. constructor.
       eapply Forall_impl; [|apply IHl; try omega].
       simpl. destruct l. rewrite Zlength_nil in hj. intros; omega.
       intro. inversion hforall. cbn. omega.
       assumption.
    ++ rewrite sublist_S_cons, Znth_pos_cons, Znth_pos_cons by omega.
       apply IHl. omega. omega. assumption.
Qed.

Lemma Sorted_add: forall (l l': list Z) m M key,
    Add key l l' ->
    Forall (fun k => m <= k < M) l ->
    Forall (fun k => Z.min m key <= k < Z.max M (key + 1)) l'.
Proof.
  intros * hadd hl.
  pose proof (Z.le_min_l m key). pose proof (Z.le_max_l M (key + 1)).
  induction hadd.
  + constructor. split. apply Z.le_min_r. apply (Z.lt_le_trans _ (key + 1)).
    omega. apply Z.le_max_r.
    eapply Forall_impl; try eassumption. simpl.
    intros. omega.
  + inversion hl. constructor. omega.
    apply IHhadd. now inversion hl.
Qed.

Theorem insert_aux_good: forall key rec n,
    match insert_aux key rec (find_path key n) with
    | (le, None) => good_root n -> good_root le
    | (le, Some (rik, ri)) => forall m M, good_node m M n ->
                                    good_node (Z.min m key) rik le /\ good_node rik (Z.max M key) ri
    end.
Proof.
  intros key rec.
  apply (node_ind2 (fun n =>
                     match insert_aux key rec (find_path key n) with
                     | (le, None) => good_root n -> good_root le
                     | (le, Some (rik, ri)) =>
                       forall m M, good_node m M n ->
                              good_node (Z.min m key) rik le /\ good_node rik (Z.max M key) ri
                     end)).
  + intros *.
    edestruct find_path_leaf as (i & heq & hbounds & hbefore & hafter). rewrite heq.
    simpl.
    destruct sumbool_and as [[hilt hifst] | ].
    - intros [sorted_entries Zlength_entries]. split.
       ++ rewrite Sorted_ltk_map, <- upd_Znth_map, <- hifst, upd_Znth_triv, <- Sorted_ltk_map;
          try rewrite Zlength_map; try rewrite Znth_map; auto; rep_omega.
       ++ rewrite upd_Znth_Zlength; rep_omega.
    - assert (Zlength (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries) =
             Zlength entries + 1).
      { rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; rep_omega. }
      destruct Z_gt_le_dec.
       ++ intros * hgn.
          assert (hforall: Forall (fun k => Z.min m key <= k < Z.max M key) (sublist 0 i (map fst entries) ++ key :: sublist i (Zlength entries) (map fst entries))).
          { admit. }
          assert (hsorted: Sorted ltk (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries)).
          { inversion hgn.
            apply Sorted_insert; try assumption.
            destruct o; omega. }
          split.
          -- constructor.
             +++ apply Sorted_sublist; assumption. 
             +++ rewrite Zlength_sublist; rep_omega.
             +++ rewrite map_sublist.
                 eapply Forall_impl;
                 try apply Sorted_bounds; try assumption; try rep_omega.
                 simpl. intros k hk.
                 assert (Z.min m key <= fst (Znth 0 (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries))).
                 { rewrite Forall_forall in hforall. specialize (hforall (fst (Znth 0 (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries)))).
                   refine (proj1 (hforall _)).
                   rewrite <- Znth_map, map_app, map_sublist, map_cons, map_sublist by rep_omega.
                   apply Znth_In.
                   rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; try rewrite Zlength_map; rep_omega. }
                 omega.
          -- constructor.
             +++ apply Sorted_sublist; assumption.
             +++ rewrite Zlength_sublist; rep_omega.
             +++ rewrite map_sublist. admit.
       ++ intros [sorted_entries Zlength_entries]. split.
          -- admit.
          -- admit.
  + intros * hZnth *.
    edestruct find_path_internal as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq. specialize (hZnth i hbounds).
    simpl.
    case_eq (insert_aux key rec (find_path key (@Znth _ ptr0 i (map snd entries)))); intros le [[ri_k ri]|] hrem; rewrite hrem in hZnth.
    - destruct Z_gt_le_dec.
      -- intros * h.
         admit.
      -- intros (min_ptr0 & max_ptr0 & max & hZlength & hptr0 & hentries).
         simpl.
         admit.
   - admit.
Admitted.

Corollary insert_good: forall key rec root,
    good_root root -> good_root (insert root key rec).
Proof.
  intros * h.
  unfold insert.
  pose proof (insert_aux_good key rec root) as haux.
  case_eq (insert_aux key rec (find_path key root)); intros n [[k ri]|] heq; rewrite heq in haux.
  + assert (hnode: exists m M, good_node m M root). admit.
    destruct hnode as (m & M & hnode).
    destruct (haux _ _ hnode) as [gptr0 gri].
    simpl.
    exists (Z.min m key). exists k. exists (Z.max M key).
    split3. rewrite Zlength_cons, Zlength_nil. rep_omega.
    assumption. econstructor. eassumption. constructor. omega.
  + auto.
Admitted. 

Section Tests.

  Definition aux (l: list Z): list (Z * V) := map (fun k => (k, nullV)) l.
  
  Definition test_node: node :=
    internal (leaf (aux [1; 2; 3]) nullval)
             [(4, leaf (aux [4; 5; 6]) nullval);
              (7, leaf (aux [7; 8; 9]) nullval);
              (11, leaf (aux [11; 12; 13]) nullval)] nullval.

  Compute (find_path 10 test_node).
  Print insert.
  Compute (find_path 13 test_node).
  Print insert_aux.
  Definition x: V.
   refine (exist _ (Vptr 1%positive Ptrofs.zero) _). easy.
  Defined.
  
  Fixpoint insert_list (n: node) (l: list (Z * V)): node :=
    match l with
    | [] => n
    | (key, rec) :: tl => insert_list (insert n key rec) tl
    end.    

  Definition test := flatten (insert_list default (combine (upto 100) (Zrepeat 100 x))).

  Compute test.

End Tests.
