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
| subnode_ptr0: forall n ptr0 entries address,
    direct_subnode n (internal ptr0 entries address)
| subnode_entry: forall n ptr0 entries address m,
    In m (map snd entries) ->
    direct_subnode n (internal ptr0 entries address).

Definition subnode: relation node := clos_refl_trans node direct_subnode.

Instance Inhabitant_node: Inhabitant node :=
  leaf (combine (upto (Z.to_nat param)) (Zrepeat param nullV)) nullval.

Inductive balanced: Z -> node -> Prop :=
| balanced_leaf: forall {entries address}, balanced 0 (leaf entries address)
| balanced_internal: forall {depth ptr0 entries address},
    balanced depth ptr0 -> Forall (balanced depth ∘ snd) entries ->
    balanced (Z.succ depth) (internal ptr0 entries address). 

Lemma inv_balanced_leaf: forall depth entries address,
    balanced depth (leaf entries address) ->
    depth = 0.
Proof. intros * h. inversion h. reflexivity. Qed.

Lemma inv_balanced_internal: forall depth ptr0 entries address,
    balanced depth (internal ptr0 entries address) ->
    balanced (depth - 1) ptr0 /\ Forall (balanced (depth - 1) ∘ snd) entries.
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

Inductive good_node: node -> Prop :=
| good_leaf: forall entries address,
    param <= Zlength entries <= 2*param ->
    good_node (leaf entries address)
| good_internal: forall ptr0 entries address,
    param <= Zlength entries <= 2*param ->
    good_node ptr0 ->
    Forall (good_node ∘ snd) entries ->
    good_node (internal ptr0 entries address).

Fixpoint good_root (root: node): Prop :=
  match root with
  | leaf entries address => Zlength entries <= 2*param
  | internal ptr0 entries address =>
    1 <= Zlength entries <= 2*param /\ good_node ptr0 /\ Forall (good_node ∘ snd) entries
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

Lemma find_path_leaf: forall key entries address,
    exists i, find_path key (leaf entries address) = [(i, leaf entries address)] /\
         0 <= i <= Zlength entries /\
         Forall (fun '(k, _) => k < key) (sublist 0 i entries) /\
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

  assert (hforall: Forall (fun '(k, _) => k < key) (sublist 0 (i entries 0) entries)).
  { induction entries as [|[k n] entries].
    rewrite sublist_nil_gen. constructor.
    unfold i; omega.
    case_eq (k >=? key); intro hbool. rewrite sublist_nil_gen. constructor. unfold i. rewrite hbool. omega.
    rewrite sublist_0_cons'. constructor. rewrite <- Z.leb_gt, <- Z.geb_leb. assumption.
    replace (sublist 0 (i ((k, n) :: entries) 0 - 1) entries) with
        (sublist 0 (i ((k, n) :: entries) 0 - 1) (sublist 0 (i entries 0) entries)).
    apply Forall_sublist, IHentries.
    rewrite sublist_sublist00. reflexivity. simpl. rewrite hbool.
    rewrite hadd. specialize (hbounds entries). omega. omega.
    simpl. rewrite hbool. rewrite hadd. specialize (hbounds entries). omega. }

  exists (i entries 0); split3; auto; split; auto.
  { clear hforall; induction entries as [|[k n] entries].
    easy.
    simpl. case_eq (k >=? key). intros hb%Z.geb_le _. simpl. omega.
    intros hb h. rewrite hadd, Znth_pos_cons.
    replace (_ + 1 - 1) with (i entries 0) by omega.
    apply IHentries. rewrite Zlength_cons, hadd in h. omega.
    specialize (hbounds entries); omega. }
Qed.

Lemma find_path_internal: forall key ptr0 entries address,
    exists i, find_path key (internal ptr0 entries address) =
         (i, internal ptr0 entries address) :: find_path key (@Znth _ ptr0 i (map snd entries)) /\
         -1 <= i < Zlength entries /\
         Forall (fun '(k, _) => k <= key) (sublist 0 (i + 1) entries) /\
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
         cbn. constructor. rewrite <- Z.ltb_ge. assumption. constructor.
         specialize (IHentries k' n').
         rewrite <- hadd in IHentries.
         pose proof (hbounds entries k n 1). pose proof (hbounds entries k' n' 1).
         simpl in *. rewrite sublist_0_cons in IHentries by rep_omega.
         case_eq ((k0 <=? key) && (key <? k'))%bool; intro hb'.
         cbn. constructor. rewrite <- Z.ltb_ge. assumption. constructor.
         assert (hk': k' <= key).
         {  rewrite andb_false_iff in hb'.
            rewrite Z.ltb_ge in hb', hb. rewrite Z.leb_gt in hb'. destruct hb'. omega. assumption. }
         rewrite sublist_0_cons by rep_omega.
         constructor. rewrite <- Z.ltb_ge. assumption.
         rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_0_cons by rep_omega.
         constructor. assumption.
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

Require Import Sorting.Sorted.

Lemma find_path_is_path: forall key root depth,
    balanced depth root ->
    Sorted (flip direct_subnode) (map snd (find_path key root)).
Proof.
  intro key.
  apply (node_ind (fun root => forall depth, balanced depth root -> Sorted (flip direct_subnode) (map snd (find_path key root)))).
  + repeat constructor.
  + intros * hptr0 hentries depth hbalanced.
    pose proof (find_path_internal key ptr0 entries address) as hfp.
    destruct hfp as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq.
    Admitted.
    

Lemma find_path_subnode: forall key root n,
    In n (map snd (find_path key root)) -> subnode n root.
Proof.
  intro key. apply (node_ind (fun root => forall n, In n (map snd (find_path key root)) -> subnode n root)).
  + intros * hin. replace n with (leaf entries address). constructor.
    symmetry. replace (map snd (find_path key (leaf entries address))) with [leaf entries address] in hin.
    now inversion hin. clear hin.
    induction entries as [|[k r] entries].
    reflexivity.
    cbn.
    intros hin. destruct hin. subst. constructor. contradiction.
    cbn in hin.
    destruct (k >=? key). inversion hin. subst. reflexivity. contradiction.
    
  intros * hin.
  

Section Tests.

  Definition aux (l: list K): list (K * V) := map (fun k => (k, nullV)) l.
  
  Definition test_node: node :=
    internal (leaf (aux [1; 2; 3]) nullval)
             [(4, leaf (aux [4; 5; 6]) nullval);
              (7, leaf (aux [7; 8; 9]) nullval);
              (10, leaf (aux [10; 11; 12]) nullval)] nullval.

  Timeout 20 Compute (find_path 11 test_node).

End Tests.
