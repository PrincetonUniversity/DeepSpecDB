Require Import VST.floyd.functional_base.
Require Import VST.veric.val_lemmas.
Require Import VST.progs.conclib.
Require Import VST.floyd.sublist.
Require Import Program.Basics. (* for compose *)
Require Import Program.Combinators. (* for compose notation "∘" *)

Definition param: Z := 8.
Definition max_depth: Z := 20.

Lemma param_eq: param = 8. Proof. reflexivity. Qed.
Lemma max_depth_eq: max_depth = 20. Proof. reflexivity. Qed.
Opaque param. Opaque max_depth.

Hint Rewrite param_eq: rep_omega. Hint Rewrite max_depth_eq: rep_omega.

Definition K: Type := Z.

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
| leaf: forall (entries: list (K * V)) (address: val), node
| internal: forall (ptr0: node) (entries: list (K * node)) (address: val), node.

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

Definition subnode: relation node := clos_refl_trans node direct_subnode.

Instance Inhabitant_node: Inhabitant node :=
  leaf (combine (upto (Z.to_nat param)) (Zrepeat param nullV)) nullval.

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

Require Import Sorting.Sorted.

Inductive good_node: forall (min: Z) (max: Z) (n: node), Prop :=
| good_leaf: forall min max entries address,
    Sorted Z.lt (map fst entries) ->
    param <= Zlength entries <= 2*param ->
    min <= fst (Znth 0 entries) ->
    fst (Znth (Zlength entries - 1) entries) < max ->
    good_node min max (leaf entries address)
| good_internal: forall ptr0 min_ptr0 max_ptr0 max_entries entries address,
    param <= Zlength entries <= 2*param ->
    good_node min_ptr0 max_ptr0 ptr0 ->
    assert_entries max_ptr0 max_entries entries ->
    good_node min_ptr0 max_entries (internal ptr0 entries address)
with assert_entries: forall (min max: Z) (entries: list (Z * node)), Prop :=
| assert_nil: forall k, assert_entries k k []
| assert_cons: forall k n max_n max tl,
    k < max_n ->
    good_node k max_n n ->
    assert_entries max_n max tl ->
    assert_entries k max ((k, n) :: tl).

Fixpoint good_root (root: node): Prop :=
  match root with
  | leaf entries address => Sorted Z.lt (map fst entries) /\ Zlength entries <= 2*param
  | internal ptr0 entries address =>
    exists min_ptr0 max_ptr0 max, 1 <= Zlength entries <= 2*param
                             /\ good_node min_ptr0 max_ptr0 ptr0
                             /\ assert_entries max_ptr0 max entries
  end.

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

Definition keys (n: node): list K := 
  match n with
  | leaf entries _ | internal _ entries _ => map fst entries
  end.

Definition node_address (n: node): val := 
  match n with | leaf _ address | internal _ _ address => address end.

Arguments node_address n: simpl nomatch.

Definition num_keys (n: node): Z := Zlength (keys n).

(* Abstracting a node to an ordered list of (key, value) pairs *)
Fixpoint flatten (n: node): list (K * V) :=
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

Fixpoint find_path (key: K) (root: node) {struct root}: list (Z * node) :=
match root with
| leaf entries address =>
  let index := (fix get_index entries index :=
     match entries with
     | [] => index
     | (k, r) :: entries => if k >=? key then index else get_index entries (index + 1)
  end) entries 0 in [(index, root)]
| internal ptr0 (((first_k, first_n) :: _) as entries) address =>
  if key <? first_k then (-1, root) :: find_path key ptr0 else
    (fix get_cursor_entry entries index :=
       match entries with
       | [] => [] (* impossible case *)
       | [(k, n)] => (index, root) :: find_path key n
       | (k, n) :: (((k', n') :: _) as entries) =>
         if ((k <=? key) && (key <? k'))%bool then (index, root) :: find_path key n
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
         | (k, _) :: entries1 => if k >=? key then index else get_index entries1 (index + 1)
         end) entries z).
  
  assert (hadd: forall entries z, i entries z = i entries 0 + z).
  { intro l; induction l as [|[k n] l]; simpl; intro z.
    omega.
    destruct Z.geb. omega.
    rewrite (IHl (z + 1)), (IHl 1).
    omega. }
  
  assert (hbounds: forall entries, 0 <= i entries 0 <= Zlength entries).
  { intro l; induction l as [|[k' n'] l]; simpl.
    - easy.
    - rewrite Zlength_cons. destruct Z.geb. rep_omega.
      rewrite hadd.
      destruct (dec_Zgt (Zlength l) 0) as [hgt|hngt]; omega. }

  assert (hforall: Forall (Z.gt key) (sublist 0 (i entries 0) (map fst entries))).
  { induction entries as [|[k n] entries].
    rewrite sublist_nil_gen. constructor.
    unfold i; omega. simpl.
    case_eq (k >=? key); intro hbool. rewrite sublist_nil_gen. constructor. omega.
    specialize (hbounds entries).
    rewrite sublist_0_cons' by (try rewrite hadd; rep_omega). constructor. rewrite Z.geb_leb, Z.leb_gt in hbool. omega.
    rewrite hadd, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. assumption. }

  exists (i entries 0); split3; auto; split; auto.
  { clear hforall; induction entries as [|[k n] entries].
    cbn. omega.
    simpl. case_eq (k >=? key). intros hb%Z.geb_le _. rewrite Znth_0_cons. simpl; omega.
    intros hb. rewrite Zlength_cons, hadd, Znth_pos_cons,
      <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by (specialize (hbounds entries); rep_omega).
    intros. apply IHentries. rep_omega. }
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
  + case_eq (key <? first_k); simpl; intro hb.
    - exists (-1). rewrite Zlength_cons, Znth_underflow, sublist_nil, Znth_0_cons by omega.
      split3; try easy; try rep_omega.
      split. constructor. intros _. now rewrite Z.ltb_lt in hb.
    - generalize (internal ptr0 ((first_k, first_n) :: entries) address) as root.
      revert hb.
      generalize first_k as k, first_n as n. clear first_k first_n. intros.

      pose (i l z := (fix get_index (l : list (K * node)) index :=
                     match l with
                     | [] => index
                     | [(k, n)] => index
                     | (k, _) :: ((k', _) :: _) as tl =>
                       if ((k <=? key) && (key <? k'))%bool
                       then index
                       else get_index tl (index + 1)
                     end) l z).
      
      assert (hadd: forall l z, i l z = i l 0 + z).
      { induction l as [|[k' n'] l]; intros; simpl.
        omega.
        destruct l as [|[k'' n''] l]. omega.
        destruct andb. omega. rewrite (IHl (z + 1)), (IHl 1). omega. }
      
      assert (hbounds: forall l k n z, z <= i ((k, n) :: l) z < z + 1 + Zlength l).
      { induction l as [|[k' n'] l]; intros. simpl.
        rewrite Zlength_nil; simpl; omega.
        specialize (IHl k' n' (z + 1)). rewrite Zlength_cons; simpl in IHl |- *.
        destruct andb; rep_omega. }
      
      exists (i ((k, n) :: entries) 0).
      split3.
      ++ generalize k as k0, n as n0.
         change 1 with (0 + 1) at 2.
         generalize 0 at -5 as z.
         induction entries as [|[k0 n0] entries]; intros.
         reflexivity.
         simpl; case_eq ((k1 <=? key) && (key <? k0))%bool; intro hb'.
         reflexivity.
         simpl in hadd.
         rewrite IHentries.
         rewrite (Znth_pos_cons _ (n0 :: _)).
         simpl. 
         specialize (hadd ((k0, n0) :: entries) 1). simpl in hadd.
         rewrite hadd. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. reflexivity. 
         destruct entries as [|[k2 n2] entries]. omega.
         destruct ((k0 <=? key) && (key <? k2))%bool. omega. specialize (hbounds entries k2 n2 2). omega.
      ++ pose proof (hbounds entries k n 0) as h.
         rewrite Zlength_cons; omega.
      ++ split.
      -- revert hb. generalize k as k0, n as n0. 
         induction entries as [|[k' n'] entries]; intros.
         cbn. constructor. rewrite Z.ltb_ge in hb. omega. constructor.
         specialize (IHentries k' n').
         rewrite <- hadd in IHentries.
         pose proof (hbounds entries k n 1). pose proof (hbounds entries k' n' 1).
         simpl in *. rewrite sublist_0_cons in IHentries by rep_omega.
         case_eq ((k0 <=? key) && (key <? k'))%bool; intro hb'.
         cbn. constructor. rewrite andb_true_iff, Z.leb_le in hb'.  destruct hb'; omega. constructor.
         assert (hk': k' <= key).
         {  rewrite andb_false_iff in hb'.
            rewrite Z.ltb_ge in hb', hb. rewrite Z.leb_gt in hb'. destruct hb'. omega. assumption. }
         rewrite sublist_0_cons by rep_omega.
         constructor. apply Z.le_ge. rewrite <- Z.ltb_ge. assumption.
         rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_0_cons by rep_omega.
         constructor. omega.
         rewrite <- Z.ltb_ge in hk'. specialize (IHentries hk').
         inversion IHentries. assumption.
      -- revert hb. generalize k. induction entries as [|[k' n'] entries]. 
         cbn; intros; omega.
         simpl; intros k_ hk_.
         specialize (IHentries k'). specialize (hbounds entries k' n' 1).
         case_eq ((k_ <=? key) && (key <? k'))%bool; intros hb h.
         * simpl. rewrite Znth_pos_cons, Znth_0_cons by omega.
           rewrite andb_true_iff in hb. destruct hb. rewrite <- Z.ltb_lt. assumption.
         * rewrite <- hadd in IHentries. simpl in IHentries.
           rewrite Znth_pos_cons. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
           apply IHentries. rewrite andb_false_iff in hb. destruct hb.
           rewrite Z.ltb_ge in hk_. rewrite Z.leb_gt in H. omega.
           assumption. rewrite Zlength_cons, Zlength_cons in h.
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
    In n (map snd (find_path key root)) -> subnode n root.
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

Fixpoint insert_aux (left: node) (key: K) (value: V + node) (l: list (Z * node)): node :=
  match l, value with
  | (i, leaf entries address) :: tl, inl rec =>
    if ((i <? Zlength entries) && (fst (Znth i entries) =? key))%bool then
      leaf (upd_Znth i entries (key, rec)) address
    else
      let new_entries := sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries in
      if Zlength entries + 1 >? 2*param then
        let new_address := address in
        let new_node_left := leaf (sublist 0 param new_entries) address in
        let new_node_right := leaf (sublist param (2 * param + 1) new_entries) new_address in
        insert_aux new_node_left (fst (Znth param new_entries)) (inr new_node_right) tl
      else leaf new_entries address
  | (i, internal ptr0 entries address) :: tl, inr n =>
    let new_entries := sublist 0 i entries ++ (key, n) :: sublist i (Zlength entries) entries in
    if Zlength entries + 1 >? 2*param then
      let new_address := address in
      let new_node_left := internal ptr0 (sublist 0 param new_entries) new_address in
      let new_node_right := internal (snd (Znth param new_entries)) (sublist (param + 1) (2 * param + 1) new_entries) address in
      insert_aux new_node_left (fst (Znth param new_entries)) (inr new_node_right) tl
    else internal ptr0 new_entries address
  | [], inr n =>
    let new_address := nullval in
    internal left [(key, n)] new_address
  | _, _ => default
  end.

Definition insert (root: node) (key: K) (value: V): node :=
  let path := find_path key root in
  insert_aux default key (inl value) path.

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

Theorem insert_good: forall key value root,
    good_root root -> good_root (insert root key value).
Proof.
  intros key value.
  apply (node_ind (fun root => good_root root -> good_root (insert root key value))). admit. unfold insert.
  + intros * h.
    edestruct find_path_leaf as [i (heq & hbounds & hbefore & hafter)]. rewrite heq.
    simpl.
    case_eq ((i <? Zlength entries) && (fst (Znth i entries) =? key))%bool; intro hb.
    - rewrite andb_true_iff, <- Zlt_is_lt_bool, Z.eqb_eq in hb. destruct hb as [hlt heqkey].
      simpl in h |- *.
      split.
      ++ rewrite <- upd_Znth_map, upd_Znth_triv.
         easy.
         rewrite Zlength_map; omega. rewrite Znth_map by omega; easy.
      ++ rewrite upd_Znth_Zlength. easy. omega.
    - rewrite andb_false_iff, Z.ltb_ge, Z.eqb_neq in hb.
      case_eq (Zlength entries + 1 >? 2 * param); simpl; intros hb'.
      * rewrite <- Zgt_is_gt_bool in hb'.
        rewrite Zlength_cons, Zlength_nil.
        exists (if i =? 0 then key else Znth 0 (map fst entries)).
        exists (if i =? param - 1 then key + 1 else Znth (param - 1) (map fst entries) + 1).
        exists (if i =? Zlength entries + 1 then key else Znth (Zlength entries) (map fst entries)).
        split3.
        ** easy.
        ** inversion h. constructor.
           { rewrite map_sublist, map_app, map_cons, map_sublist.
             simpl.
             apply Sorted_sublist.
             destruct (eq_dec i (Zlength entries)) as [hi|hni].
             rewrite (sublist_nil_gen _ i) by omega.
             rewrite sublist_same by (try rewrite Zlength_map; rep_omega).
             simpl.
             admit.
             rewrite (sublist_next i), map_cons by rep_omega.
             admit. }
           { rewrite Zlength_sublist; try rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; rep_omega. }
           { destruct entries as [|[k n] entries].
             simpl in hb'. rep_omega.
             simpl. rewrite Znth_0_cons, Znth_sublist by rep_omega.
             destruct (eq_dec i 0) as [hi | hi].
             now subst. rewrite sublist_next by rep_omega.
             rewrite <- Z.eqb_neq in hi. rewrite hi.
             easy. }
           { rewrite Zlength_sublist, Znth_sublist by (try rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; rep_omega).
             destruct (eq_dec i (param - 1)). subst.
             rewrite Z.eqb_refl, app_Znth2; rewrite Zlength_sublist; try rep_omega. 
             replace (param - 0 - 1 + 0 - (param - 1 - 0)) with 0 by rep_omega.
             rewrite Znth_0_cons. cbn. omega.
             admit. }
        ** admit.
      * admit.
+ intros * hptr0 hentries h.
  edestruct find_path_internal as [i (heq & hbounds & hbefore & hafter)].
  rewrite heq.
  simpl.

Admitted.

Section Tests.

  Definition aux (l: list K): list (K * V) := map (fun k => (k, nullV)) l.
  
  Definition test_node: node :=
    internal (leaf (aux [1; 2; 3]) nullval)
             [(4, leaf (aux [4; 5; 6]) nullval);
              (7, leaf (aux [7; 8; 9]) nullval);
              (10, leaf (aux [10; 11; 12]) nullval)] nullval.

  Timeout 20 Compute (find_path 11 test_node).

End Tests.
