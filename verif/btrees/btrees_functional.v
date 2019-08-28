Require Orders OrdersTac.
Require GenericMinMax SetoidList.

Require Import Sorting.Sorted.

(* I don't know exactly what is in functional_base, but this file only requires
   Z, omega, the compose notation "oo" and the sublist library *)
Require Import VST.floyd.functional_base VST.progs.conclib VST.floyd.sublist.

(* Parameters of the B+Tree:
   `InfoTyp.t` stores any information in each B+Tree node (e.g. val for augmented types)
   `min_fanout` is the minimum number of entries in a non-root node:
   any node (internal or leaf) that is not the root can store between min_fanout and 2 * min_fanout entries *)

Module Type BPlusTreeParams.
  Module InfoTyp.
    Parameter t: Type.
  End InfoTyp.
  Parameter min_fanout: Z.
  Axiom min_fanout_pos: min_fanout > 0.
End BPlusTreeParams.

(* X is the usual (with Leibniz equality) ordered type of keys *)
Module Raw (X: Orders.UsualOrderedTypeFull') (Params: BPlusTreeParams).
  Import Params.
  Module Info := InfoTyp.
  Module XMinMax := GenericMinMax.GenericMinMax X.
  Module MinMaxProps := GenericMinMax.MinMaxProperties X XMinMax.
  
  Notation key := X.t.
  Notation key_max := (GenericMinMax.gmax X.compare).
  Notation key_min := (GenericMinMax.gmin X.compare).
  
  Notation key_le := X.le.
  Notation key_lt := X.lt.
  Definition key_compare k1 k2 := CompareSpec2Type (X.compare_spec k1 k2).

  Module OrderTac := OrdersTac.OTF_to_OrderTac X.
  Ltac order := OrderTac.order.
  Instance key_le_Transitive: Transitive key_le. do 3 intro; order. Qed.

  Definition entries (elt: Type): Type := list (key * elt).

  Section Elt.

    (* `elt` is the type of the values stored in the B+Tree *)

    Context {elt: Type}.
    
    Unset Elimination Schemes.
    
    (* The B+Tree node inductive type.
       We could have used it to encode the height and the balanced property
       but then I don't know how we would have defined the cursor type. *)

    Inductive node: Type :=
    | leaf: forall (records: entries elt) (info: Info.t), node
    | internal: forall (ptr0: node) (children: entries node) (info: Info.t), node.
    
    (* Coq fails at generating a proper induction principle, so we have to define one here. *)

    Lemma node_ind (P: node -> Prop)
          (hleaf: forall records info, P (leaf records info))
          (hinternal: forall ptr0 children info,
              P ptr0 ->
              Forall P (map snd children) ->
              P (internal ptr0 children info)) :
      forall n, P n.
    Proof.
      fix hrec 1.
      intros [].
      apply hleaf.
      apply hinternal. apply hrec.
      induction children as [|[k n] children]. constructor.
      constructor. apply hrec. assumption.
    Qed.
    
    Set Elimination Schemes.

    Inductive direct_subnode: relation node :=
    | subnode_ptr0: forall ptr0 records info,
        direct_subnode ptr0 (internal ptr0 records info)
    | subnode_entry: forall n ptr0 children info,
        In n (map snd children) ->
        direct_subnode n (internal ptr0 children info).
    
    Lemma direct_subnode_wf: well_founded direct_subnode.
    Proof.
      unfold well_founded.
      apply (node_ind (fun n => Acc direct_subnode n)).
      + constructor. intros n hn. inversion hn.
      + intros * hptr0 hchildren. constructor.
        intros n hn. inversion hn. assumption.
        eapply Forall_forall; eassumption.
    Qed.
    
    Definition subnode: relation node := Relation_Operators.clos_refl_trans node direct_subnode.

    (* `balanced d n` means: all paths from n to a leaf are the same length d
       We could have encoded the balanced property inside the node datatype.
       However, I don't know how we would have defined the cursor type. *)
    Inductive balanced: nat -> node -> Prop :=
    | balanced_leaf: forall {records info}, balanced 0 (leaf records info)
    | balanced_internal: forall {depth ptr0 children info},
        balanced depth ptr0 -> Forall (balanced depth oo snd) children ->
        balanced (S depth) (internal ptr0 children info). 

    (* `well_sorted m M n` means that n is a search (multiway) tree
       and that all the keys k of n are such that m <= k <= M
       
       I originally thought that the keys in a well_sorted node would verify m < k <= M.
       This is shorter and more natural, but it doesn't work with insertion and deletions:
       we want to prove
       `well_sorted m M n -> well_sorted (min k m) (max k M) (insert k e n)`
       which cannot be expressed with the first definition.
       
       Given an internal node `internal ptr0 [(k1, n1), (k2, n2), ... , (kp, np)]`
       that is `well_sorted m M`, then

       the keys k in ptr0 satisfy `m <= k <= k1`,
       the keys k in n1 satisfy `k1 < k <= k2`
       the keys k in n2 satisfy `k2 < k <= k3`
       ...
       the keys k in np satisfy `kp < k <= M`
     *)
    
    (* For Coq to check the termination of that function,
     it is necessary to express ws_children as a nested fixpoint. *)
    Fixpoint well_sorted (min max: key) (n: node): Prop :=
      match n with
      | leaf records info => Sorted key_lt (map fst records) /\
                            key_le min max /\ (* in case `records` is empty, we still want `min <= max` *)
                            Forall (fun k => key_le min k /\ key_le k max) (map fst records)
      | internal ptr0 children info => exists max_ptr0, well_sorted min max_ptr0 ptr0 /\
                                                  (fix ws_children l min: Prop :=
                                                     match l with
                                                     | nil => key_le min max
                                                     | (k, n) :: tl =>
                                                       key_le min k /\
                                                       exists min_n max_n,
                                                         key_lt k min_n /\
                                                         well_sorted min_n max_n n /\
                                                         ws_children tl max_n
                                                     end) children max_ptr0
      end.

    Definition well_sorted_children min max children :=
        (fix ws_children (l : list (X.t * node)) min: Prop :=
           match l with
           | nil => key_le min max
           | (k, n) :: tl =>
               key_le min k /\
               exists min_n max_n, key_lt k min_n /\
                              well_sorted min_n max_n n /\
                              ws_children tl max_n
           end) children min.

    Lemma well_sorted_equation: forall min max n,
        well_sorted min max n <->
        match n with
        | leaf records info => Sorted key_lt (map fst records) /\
                              key_le min max /\ (* in case records is empty *)
                              Forall (fun k => key_le min k /\ key_le k max) (map fst records)
        | internal ptr0 children info => exists max_ptr0, well_sorted min max_ptr0 ptr0 /\
                                                    well_sorted_children max_ptr0 max children
        end.
    Proof.
      intros. destruct n; reflexivity.
    Qed.

    Opaque well_sorted.

    Definition is_leaf (n: node): Prop :=
      match n with
      | leaf _ _ => True
      | _ => False
      end.
    
    Definition is_leaf_dec (n: node): { is_leaf n } + { ~ is_leaf n } :=
      match n as m return { is_leaf m } + { ~ is_leaf m } with
      | leaf _ _ => left I
      | internal _ _ _ => right (fun hcontr => hcontr)
      end.

    Definition node_info (n: node): Info.t := 
      match n with | leaf _ info | internal _ _ info => info end.
    
    Fixpoint flatten (n: node): entries elt :=
      match n with
      | leaf records _ => records
      | internal ptr0 children _ => flatten ptr0 ++ flat_map (flatten oo snd) children
      end.
    
    Fixpoint card (n: node): nat :=
      match n with
      | leaf children _ => Datatypes.length children
      | internal ptr0 children _ => card ptr0 + fold_right Nat.add 0%nat (List.map (card oo snd) children)
      end.

    Lemma card_flatten_length: forall n, Datatypes.length (flatten n) = card n.
    Proof.
      apply node_ind.
      + intros. reflexivity.
      + intros * hlength hchildren.
        simpl. rewrite app_length, hlength. f_equal.
        induction children as [|[k n] children].
        - reflexivity.
        - simpl. rewrite app_length.
          rewrite IHchildren by now inversion hchildren.
          apply Forall_inv in hchildren. cbn in hchildren. rewrite hchildren. reflexivity.
    Qed.

    Lemma well_sorted_extends: forall n min max min' max',
        well_sorted min max n ->
        key_le min' min -> key_le max max' ->
        well_sorted min' max' n.
    Proof.
      apply (node_ind (fun n => forall min max min' max',
                           well_sorted min max n ->
                           key_le min' min -> key_le max max' ->
                           well_sorted min' max' n)).
      + intros * (hsorted & hminmax & hrecords) hm hM. split; [|split].
      - assumption.
      - order.
      - eapply Forall_impl; try eassumption.
        intros e [hmin hmax]. split; order.
      + intros * hptr0 hchildren * hn hm hM.
        rewrite well_sorted_equation in hn |- *.
        destruct hn as (max_ptr0 & ptr0_ws & children_ws).
        exists max_ptr0. split.
        eapply hptr0. eassumption. order. order.
        clear - children_ws hm hM.
        revert children_ws. generalize max_ptr0.
        induction children as [|[k n] children].
        - simpl. intros. order.
        - intros max_ptr1 (hk & min_n & max_n & hmink & ws_n & rest).
          split. assumption. exists min_n. exists max_n. split. assumption. split.
          assumption. apply IHchildren.
          assumption.
    Qed.

    Lemma well_sorted_children_extends: forall children min max min' max',
        well_sorted_children min max children ->
        key_le min' min -> key_le max max' ->
        well_sorted_children min' max' children.
    Proof.
      induction children as [|[k child] children].
      + intros * h hmin hmax. cbn in h |- *. order.
      + intros * hwsc hmin hmax.
        destruct hwsc as (hk & max_n & min_n & hkmax_n & hchild & htl).
        simpl. split. order.
        exists max_n. exists min_n. split.
        assumption. split. easy.
        eapply IHchildren. eassumption.
        order. order.
    Qed.

    Lemma well_sorted_le: forall n min max,
        well_sorted min max n -> key_le min max.
    Proof.
      apply (node_ind (fun n => forall min max, well_sorted min max n -> key_le min max)).
      + intros * h%well_sorted_equation. easy.
      + intros * hptr0 hchildren * h%well_sorted_equation.
        eapply hptr0.
        destruct h as (max_ptr0 & ptr0_ws & children_ws).
        assert (key_le max_ptr0 max).
        { clear ptr0_ws.
          revert dependent max_ptr0. induction children as [|[k n] children].
          easy.
          intros max_ptr0 (hk & max_n & min_n & hmaxk_n & n_ws & rest).
          apply IHchildren in rest.
          apply Forall_inv in hchildren.
          eapply hchildren in n_ws. 
          order. now inversion hchildren. }
        eapply well_sorted_extends. eassumption. order. order.
    Qed.

    (* well_sorted doesn't include sortedness directly for the keys of the entries of an internal node
       But we can prove these keys are ordered. *)
    Lemma well_sorted_children_Sorted: forall children min max,
        well_sorted_children min max children -> Sorted key_lt (map fst children).
    Proof.
      induction children as [|[k n] children].
      + intros * h. constructor.
      + intros * h.
        simpl in h. destruct h as (hle & min_n & max_n & hlt & n_ws & children_wsc).
        constructor.
        eapply IHchildren. 
        eassumption. 
        destruct children as [|[k' n'] children]. constructor.
        destruct children_wsc as (hle' & min_n' & max_n' & hlt' & n_ws' & children_wsc).
        constructor. cbn. apply well_sorted_le in n_ws. order.
    Qed.

    Lemma well_sorted_children_facts: forall children min max,
        well_sorted_children min max children ->
        key_le min max /\
        forall k n, In (k, n) children -> key_le min k /\
                                    exists min_n max_n, well_sorted min_n max_n n /\
                                                   key_lt k min_n /\
                                                   key_le max_n max.
    Proof.
      induction children as [|[k n] children].
      easy. intros min max (hk & max_n & min_n & hk_max_n & n_ws & rest).
      specialize (IHchildren _ _ rest). pose proof (well_sorted_le _ _ _ n_ws).
      destruct IHchildren as [hle hin].
      split. order. intros k' n' hkn'%in_inv.
      destruct hkn' as [heq|hmapsto]. inversion heq. subst.
      split. order. exists max_n. exists min_n. split.          
      assumption.
      split. order. order.
      specialize (hin _ _ hmapsto).
      destruct hin as (hlek' & h).
      split. order. assumption.
    Qed.

    (* A simpler version of the lemma originally present in the SetoidList module *)
    Lemma Sorted_app {A: Type}: forall (R: relation A) l1 l2,
        Sorted R l1 -> Sorted R l2 ->
        (forall x y, In x l1 -> In y l2 -> R x y) ->
        Sorted R (l1 ++ l2).
    Proof.
      intros * h1 h2 hbi.
      eapply SetoidList.SortA_app. apply eq_equivalence.
      assumption. assumption.
      intros x y hinax hinay.
      rewrite SetoidList.InA_alt in hinax, hinay.
      destruct hinax as (x' & hx' & hinx').
      destruct hinay as (y' & hy' & hiny').
      subst. apply hbi; assumption.
    Qed.     

    (* The flatten function behaves how it should on a well_sorted node. *)

    (* It is required to prove at the same time the bounds and the sortedness,
       because the bounds of l1 and l2 are needed for the sortedness of `l1 ++ l2` *)
    Lemma well_sorted_flatten: forall n min max,
        well_sorted min max n ->
        Forall (fun k => key_le min k /\ key_le k max) (map fst (flatten n)) /\ Sorted key_lt (map fst (flatten n)).
    Proof.
      apply (node_ind (fun n => forall min max, well_sorted min max n ->
                                        Forall (fun k => key_le min k /\ key_le k max) (map fst (flatten n)) /\ Sorted key_lt (map fst (flatten n)))).
      + intros * h%well_sorted_equation. easy.
      + intros * hptr0 hchildren * h%well_sorted_equation. simpl.
        destruct h as (max_ptr0 & ptr0_ws & children_ws).
        rewrite map_app, Forall_app. rewrite and_assoc. split.
        - refine (proj1 (hptr0 _ _ _)).
          eapply well_sorted_extends in ptr0_ws. eassumption. order.
          specialize (well_sorted_children_facts _ _ _ children_ws). easy.
        - specialize (hptr0 _ _ ptr0_ws). destruct hptr0 as [ptr0_flatten_bounds ptr0_flatten_sorted].
          enough (henough: Forall (fun k => key_lt max_ptr0 k /\ key_le k max) (map fst (flat_map (flatten oo snd) children)) /\
                           Sorted key_lt (map fst (flat_map (flatten oo snd) children))).
          destruct henough as [hbounds hsorted].
          split.
          eapply Forall_impl; try eassumption. intros k [h1 h2].
          apply well_sorted_le in ptr0_ws. split; order.
          apply Sorted_app. assumption. assumption.
          intros k k' hk hk'.
          rewrite Forall_forall in hbounds. cbn.
          specialize (hbounds k' hk').
          rewrite Forall_forall in ptr0_flatten_bounds.
          specialize (ptr0_flatten_bounds k hk). simpl in ptr0_flatten_bounds, hbounds.
          destruct ptr0_flatten_bounds, hbounds. order.
          clear ptr0_ws ptr0_flatten_bounds ptr0_flatten_sorted ptr0.        
          generalize dependent max_ptr0.
          induction children as [|[k n] children].
          -- split. apply Forall_nil. constructor.
          -- intros min' (hk & max_n & min_n & h_k_max_n & n_ws & rest).
             specialize (IHchildren
                           ltac:(now inversion hchildren) _ rest).
             apply Forall_inv in hchildren. cbn in hchildren.
             pose proof (well_sorted_le _ _ _ n_ws).
             apply hchildren in n_ws.
             apply well_sorted_children_facts in rest. destruct rest.
             destruct IHchildren as [hforallrec hsortedrec]. split.
             simpl. rewrite map_app. apply Forall_app. split.
             unshelve eapply (Forall_impl _ _ (proj1 n_ws)).
             intros k' [h1 h2]. split; order.
             unshelve eapply (Forall_impl _ _ hforallrec).
             intros k' [h1 h2].
             split; order.
             simpl. rewrite map_app. apply Sorted_app. 
             easy. assumption.
             intros k1 k2 h1 h2.
             destruct n_ws as [n_ws _].
             rewrite Forall_forall in n_ws, hforallrec.
             pose proof (n_ws k1 h1) as h3.
             pose proof (hforallrec k2 h2) as h4.
             destruct h3, h4.
             order.
    Qed.

    Context {default_key: Inhabitant key} {default_elt: Inhabitant elt} {default_info: Inhabitant Info.t}.

    Instance Inhabitant_node: Inhabitant node := leaf [] default_info.

    Section FindIndex.
      
      (* find_index is used to define cursors.
         Contrary to the previous implementation, the same function is now used for both
         leaves and internal nodes.
         This is because I changed the "search tree" property for an equivalent one
         (the strict and non-strict bounds for the keys in a subtree can be changed).
       *)
      
      Context {X: Type}.
      Fixpoint find_index_aux k0 (l: entries X) i: Z :=
        match l with
        | nil => i
        | (k, rec) :: tl =>
          match key_compare k0 k with
          | CompGtT _ => find_index_aux k0 tl (i + 1)
          | _ => i
          end
        end.
      
      (* find_index k l finds the index i such that
         the (i+1)-th key in l is equal or greater than k.
       
       Examples:
       
       |  3  |  6  |  9  |      l == [3; 6; 9]   (has to be sorted!)
       0     1     2     3            


       |  3  |  6  |  9  |
       ^                     find_index 2 l = 0

       |  3  |  6  |  9  |
             ^               find_index 6 l = 1

       |  3  |  6  |  9  |
                         ^   find_index 10 l = 3   *)
      
      Definition find_index (k0: key) (l: entries X): Z :=
        find_index_aux k0 l 0.

      Lemma find_index_aux_add: forall k l i,
          find_index_aux k l i = find_index_aux k l 0 + i.
      Proof.
        induction l as [|[k' e'] l].
        + simpl; intros; omega.
        + simpl. intro i. destruct key_compare. omega.
          omega. rewrite (IHl (i + 1)), (IHl 1). omega.
      Qed. 

      Lemma find_index_bounds: forall k l,
          0 <= find_index k l <= Zlength l.
      Proof.
        unfold find_index.
        induction l as [|[k' e'] l].
        + cbn; omega.
        + simpl. rewrite Zlength_cons. destruct key_compare. omega.
          omega. rewrite find_index_aux_add.
          omega.
      Qed.

      Lemma find_index_HdRel: forall k l,
          find_index k l = 0 <-> HdRel key_le k (map fst l).
      Proof.
        intros.
        induction l as [|[k' n'] l].
        + cbn. easy.
        + split.
        - intros h. pose proof (find_index_bounds k l) as hb. unfold find_index in hb.
          constructor. cbn in h. cbn.
          rewrite find_index_aux_add in h.
          destruct key_compare; try order; omega.
        - intro hn. cbn. apply HdRel_inv in hn.
          cbn in hn. destruct key_compare; try reflexivity; order.
      Qed. 

      Lemma find_index_pos_before {_: Inhabitant (key * X)}: forall k0 l,
          let i := find_index k0 l in
          i > 0 ->
          key_lt (Znth (i - 1) (map fst l)) k0.
      Proof.
        intros k0 l i. unfold i. clear i.
        induction l as [|[k x] l].
        + cbn; omega.
        + intro hi.
          cbn in hi |- *.
          destruct key_compare; try omega.
          rewrite find_index_aux_add in *.
          rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
          destruct (Z.eq_dec (find_index_aux k0 l 0) 0) as [h0|hn0].
        - rewrite h0, Znth_0_cons.
          simpl. assumption.
        - rewrite Znth_pos_cons by omega.
          apply IHl. unfold find_index. omega.
      Qed.

      Lemma find_index_after {_: Inhabitant (key * X)}: forall k0 l,
          let i := find_index k0 l in
          i < Zlength l ->
          key_le k0 (Znth i (map fst l)).
      Proof.
        intros k0 l i. unfold i. clear i.
        induction l as [|[k x] l].
        + cbn; omega.
        + intro hi.
          rewrite Zlength_cons in hi. cbn in hi |- *.
          destruct key_compare.
        - rewrite Znth_0_cons; cbn; order.
        - rewrite Znth_0_cons; cbn; order.
        - rewrite find_index_aux_add in hi |- *.
          pose proof (find_index_bounds k0 l) as hb. unfold find_index in hb, IHl.
          rewrite Znth_pos_cons by omega.
          rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
          apply IHl. omega.
      Qed.

      Lemma find_index_before {_: Inhabitant (key * X)}: forall k0 l,
          let i := find_index k0 l in
          0 < i ->
          key_lt (Znth (i - 1) (map fst l)) k0.
      Proof.
        intros k0 l i. unfold i. clear i.
        induction l as [|[k x] l].
        + cbn; omega.
        + intro hi.
          cbn in hi |- *.
          destruct key_compare; try omega.
          rewrite find_index_aux_add in hi |- *.
          pose proof (find_index_bounds k0 l) as hb. unfold find_index in hb, IHl.
          rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
          destruct (Z.eq_dec (find_index_aux k0 l 0) 0) as [h0|h0].
        - rewrite h0. assumption.
        - rewrite Znth_pos_cons by omega.
          apply IHl. omega.
      Qed.

    End FindIndex.

    (* This functions allows fast well-founded recursive computations (from the Coq-Club) *)
    Fixpoint wf_guard {A} {R : A -> A -> Prop}
             (n : nat) (wfR : well_founded R) : well_founded R :=
      match n with
      | 0%nat => wfR
      | S n => fun x =>
                Acc_intro x (fun y _ => wf_guard n (wf_guard n wfR) y)
      end.
    Strategy 100 [wf_guard].

    (* `get_cursor k0 root` returns the list of nodes and indices
       that is the path from root to the entry in the leaf containing k0
       (or to the position of insertion if k0 is not present in root) *)

    Function get_cursor (k0: key) (root: node)
             {wf direct_subnode root}: list (Z * node) :=
      match root with
      | leaf records info => [(find_index k0 records, root)]
      | internal ptr0 children info =>
        let i := find_index k0 children in
        (i, root) :: get_cursor k0 (if Z.eq_dec i 0 then ptr0 else Znth (i - 1) (List.map snd children))
      end.
    Proof.
      + intros * heq.
        destruct Z.eq_dec as [hptr0|hentry].
      - apply subnode_ptr0. 
      - eapply subnode_entry.
        pose proof (find_index_bounds k0 children).
        apply Znth_In. rewrite Zlength_map. omega.
      + apply (wf_guard 32), direct_subnode_wf.
    Defined.

    Import Sumbool.
    Arguments sumbool_and {A} {B} {C} {D}.
    
    (* `insert_aux k e c`
       inserts the mapping `k |-> e` along the cursor c
       it returns a pair (left, oright) such that
       left is the updated node with k inserted
       oright is an option. If oright is Some (right_k, right_n), then
       a new entry (right_k, right_n) has to be inserted in the parent node.
       If oright is None, the parent just has to be updated with left.
     *)

    Fixpoint insert_aux (k0: key) (e: elt) (cursor: list (Z * node)):
      node * option (key * node) :=
      match cursor with
      | (i, leaf records info) :: _ =>
        if sumbool_and (Z_lt_ge_dec i (Zlength records)) (X.eq_dec k0 (Znth i (map fst records))) then
          (leaf (upd_Znth i records (k0, e)) info, None)
        else
          let new_records := sublist 0 i records ++ (k0, e) :: sublist i (Zlength records) records in
          if Z_gt_le_dec (Zlength new_records) (2 * min_fanout) then
            let new_info := info in
            let new_node_left := leaf (sublist 0 min_fanout new_records) info in
            let new_node_right := leaf (sublist min_fanout (Zlength new_records) new_records) new_info in
            (new_node_left, Some ((Znth (min_fanout - 1) (List.map fst new_records)), new_node_right))
          else (leaf new_records info, None)
      | (i, internal ptr0 children info) :: tl =>
        let (to_update, new_child) := insert_aux k0 e tl in
        match new_child with
        | Some (new_child_key, new_child_node) =>
          if Z.eq_dec i 0 then
            let new_children := (new_child_key, new_child_node) :: children in
            if Z_gt_le_dec (Zlength new_children) (2 * min_fanout) then
              let new_info := info in
              let new_node_left := internal to_update (sublist 0 min_fanout new_children) info in
              let (new_key, new_ptr0) := Znth min_fanout new_children in
              let new_node_right := internal new_ptr0 (sublist (min_fanout + 1) (Zlength new_children) new_children) new_info in
              (new_node_left, Some (new_key, new_node_right))
            else (internal to_update new_children info, None)
          else
            let new_children := sublist 0 (i - 1) children ++
                                       (Znth (i - 1) (map fst children), to_update) ::
                                       (new_child_key, new_child_node) ::
                                       sublist i (Zlength children) children in
            if Z_gt_le_dec (Zlength new_children) (2 * min_fanout) then
              let new_info := info in
              let new_node_left := internal ptr0 (sublist 0 min_fanout new_children) info in
              let (new_key, new_ptr0) := Znth min_fanout new_children in
              let new_node_right := internal new_ptr0 (sublist (min_fanout + 1) (Zlength new_children) new_children) new_info in
              (new_node_left, Some (new_key, new_node_right))
            else
              (internal ptr0 new_children info, None)
        | None =>
          if Z.eq_dec i 0 then (internal to_update children info, None)
          else (internal ptr0 (upd_Znth (i - 1) children (Znth (i - 1) (map fst children), to_update)) info, None)
        end
      | [] => (default, None)
      end.

    (* insert creates a new root if needed *)
    Definition insert (k0: key) (e: elt) (new_info: Info.t) (root: node): node :=
      let c := get_cursor k0 root in
      let (root, new_child) := insert_aux k0 e c in
      match new_child with
      | None => root
      | Some (new_child_key, new_child_node) => internal root [(new_child_key, new_child_node)] new_info
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
    
    (* The following functions and proofs (until "END") are an experiment I made,
       but they are not used in the final proof.
       I'm keeping it because it could still be interesting for e.g. movetofirst. *)

    Fixpoint leftmost (n: node): option key :=
      match n with
      | leaf records _ => hd_error (map fst records)
      | internal ptr0 _ _ => leftmost ptr0
      end.

    Definition last_error {A: Type} (l: list A): option A :=
      last (map Some l) None.

    Lemma last_error_Some {A: Type}: forall (l: list A) a,
        last_error l = Some a ->
        l <> nil.
    Proof.
      intros * h hcontr.
      subst. discriminate.
    Qed.

    Lemma last_error_app {A: Type}: forall (l1: list A) l2 a,
        last_error l2 = Some a ->
        last_error (l1 ++ l2) = Some a.
    Proof.
      intros * h.
      unfold last_error. rewrite map_app, last_app. assumption.
      intros hcontr%map_eq_nil. subst. discriminate.
    Qed.

    Lemma last_error_map {A B: Type}: forall (l: list A) (f: A -> B),
        last_error (map f l) = option_map f (last_error l).
    Proof.
      intros.
      induction l as [|hd tl].
      + reflexivity.
      + unfold last_error in IHtl |- *.
        cbn. rewrite IHtl.
        destruct tl; reflexivity.
    Qed.

    Lemma last_error_cons {A: Type}: forall (l: list A) a,
        l <> nil ->
        last_error (a :: l) = last_error l.
    Proof.
      intros * hnil.
      induction l as [|hd tl].
      + contradiction.
      + destruct tl; reflexivity.
    Qed.

    Lemma last_error_In {A: Type}: forall (l: list A) a,
        last_error l = Some a ->
        In a l.
    Proof.
      intros * h.
      induction l as [|hd tl].
      + discriminate.
      + destruct (nil_dec tl) as [hnil|hnil].
        - subst. left. cbn in h. now inversion h.
        - right.
          rewrite last_error_cons in h by assumption.
          auto.
    Qed.

    Lemma last_error_removelast {A: Type}: forall (l: list A) a,
        last_error l = Some a ->
        l = removelast l ++ [a].
    Proof.
      intros * h.
      induction l as [|hd tl].
      + discriminate.
      + destruct tl. cbn in h. inversion h. reflexivity.
        rewrite IHtl at 1 by assumption.
        reflexivity.
    Qed.      
    
    Function rightmost (n: node) {wf direct_subnode n}: option key :=
      match n with
      | leaf records _ => option_map fst (last_error records)
      | internal ptr0 children _ =>
        match last_error children with
        | Some (k, child) => rightmost child
        | None => None
        end
      end.
    Proof.
      + intros * hn * h1 h2.
        apply subnode_entry.
        unfold last_error in h2.
        destruct (nil_dec children) as [hnil | hnil].
      - subst. discriminate.
      - apply exists_last in hnil.
        destruct hnil as (children_prefix & [last_k last_child] & heq).
        subst. rewrite map_app in h2. simpl in h2. rewrite last_snoc in h2.
        inversion h2. rewrite map_app, in_app_iff.
        right. constructor. reflexivity.
      + apply (wf_guard 32), direct_subnode_wf.
    Qed.

    Lemma flatten_leftmost: forall n lm,
        leftmost n = Some lm ->
        map fst (flatten n) = lm :: tl (map fst (flatten n)).
    Proof.
      apply (node_ind (fun n => forall lm,
        leftmost n = Some lm ->
        map fst (flatten n) = lm :: tl (map fst (flatten n)))).
      + intros.
        now rewrite <- hd_error_tl_repr.
      + intros * hptr0 hchildren * hlm.
        cbn in hlm |- *.
        specialize (hptr0 _ hlm). rewrite map_app, hptr0.
        reflexivity.
    Qed.

    Lemma flatten_rightmost: forall n rm,
        rightmost n = Some rm ->
        last_error (map fst (flatten n)) = Some rm.
    Proof.
      apply (node_ind (fun n => forall rm,
        rightmost n = Some rm ->
        last_error (map fst (flatten n)) = Some rm)).
      + intros * h.
        rewrite rightmost_equation in h.
        rewrite last_error_map. assumption.
      + intros * hptr0 hchildren * hrm.
        rewrite rightmost_equation in hrm.
        simpl. rewrite flat_map_concat_map, map_app.
        erewrite last_error_app. reflexivity.
        case_eq (last_error children).
      - intros [k n] heq.
        rewrite heq in hrm.
        rewrite (last_error_removelast children _ heq).
        rewrite concat_map, map_app, map_app, concat_app.
        erewrite last_error_app. reflexivity. simpl. rewrite app_nil_r.
        rewrite Forall_forall in hchildren.
        apply hchildren.
        apply last_error_In. rewrite last_error_map. rewrite heq. reflexivity. assumption.
      - intro hnone. rewrite hnone in hrm. discriminate.
    Qed.

    Corollary well_sorted_leftmost: forall n m M lm,
        well_sorted m M n -> leftmost n = Some lm ->
        key_le m lm.
    Proof.
      intros * hws%well_sorted_flatten hlm%flatten_leftmost.
      destruct hws as [hbounds _]. rewrite Forall_forall in hbounds.
      assert (hin: In lm (map fst (flatten n))).
      { rewrite hlm. left. reflexivity. }
      specialize (hbounds lm hin).
      destruct hbounds. order.
    Qed.

    Corollary well_sorted_rightmost: forall n m M rm,
        well_sorted m M n -> rightmost n = Some rm ->
        key_le rm M.
    Proof.
      intros * hws%well_sorted_flatten hrm%flatten_rightmost%last_error_In.
      destruct hws as [hbounds _]. rewrite Forall_forall in hbounds.
      specialize (hbounds _ hrm). destruct hbounds.
      order.
    Qed.

    (* END of the unused functions and proofs *)

    Lemma well_sorted_children_cons: forall l min max k n min_n max_n,
        well_sorted min_n max_n n ->
        well_sorted_children min max l ->
        key_lt k min_n -> key_le max_n min ->
        well_sorted_children k max ((k, n) :: l).
    Proof.
      intros * n_ws l_wsc hlt.
      simpl. split. order.
      exists min_n. exists max_n. split.
      assumption.
      split. assumption.
      eapply well_sorted_children_extends. eassumption. order. order.
    Qed.

    Lemma well_sorted_children_app: forall l1 min1 max1 l2 min2 max2,
        well_sorted_children min1 max1 l1 ->
        well_sorted_children min2 max2 l2 ->
        key_le max1 min2 ->
        well_sorted_children min1 max2 (l1 ++ l2).
    Proof.
      induction l1 as [|[k1 child1] l1];
      intros * h1 h2 h12;
      simpl in h1 |- *.
      + eapply well_sorted_children_extends. eassumption.
        order. order.
      + destruct h1 as (hk1 & min_n & max_n & h_k_max_n & hchild1 & htl).
        split.
        order.
        exists min_n. exists max_n. split. assumption. split. assumption.
        eapply IHl1.
        eassumption. eassumption.
        order.
    Qed.

    Lemma well_sorted_children_split1: forall i,
        0 <= i ->
        forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children m (Znth i (map fst l)) (sublist 0 i l).
    Proof.
      intros i hi.
      refine (natlike_ind (fun i => forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children m (Znth i (map fst l)) (sublist 0 i l)) _ _ i hi).
      + intros * hlength h.
        destruct l as [|[k n] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl in h |- *.
          easy.
      + intros j hj hrec * hlength h.
        destruct l as [|[k child] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl. rewrite Znth_pos_cons, sublist_0_cons by omega.
          rewrite <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
          simpl.
          destruct h as (hle & min_child & max_child & hlt & child_ws & l_wsc).
          split. assumption.
          exists min_child. exists max_child.
          split3. assumption. assumption.
          eapply hrec.
          rewrite Zlength_cons in hlength. omega.
          eassumption.
    Qed.

    Lemma well_sorted_children_split2: forall i,
        0 <= i ->
        forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children (Znth i (map fst l)) M (sublist i (Zlength l) l).
    Proof.
      intros i hi.
      refine (natlike_ind (fun i => forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children (Znth i (map fst l)) M (sublist i (Zlength l) l)) _ _ i hi).
      + intros * hlength h.
        destruct l as [|[k n] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl in h |- *.
          rewrite sublist_same by reflexivity. simpl. split.
          rewrite Znth_0_cons. order. easy.
      + intros j hj hrec * hlength h.
        destruct l as [|[k child] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl. rewrite Znth_pos_cons, Zlength_cons, sublist_S_cons by omega.
          do 2 rewrite <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
          destruct h as (hle & min_child & max_child & hlt & child_ws & l_wsc).
          eapply hrec. rewrite Zlength_cons in hlength; omega.
          eassumption.
    Qed.

    Lemma HdRel_swap_le_lt: forall (x y: key) l,
        key_lt x y -> HdRel key_le y l -> HdRel key_lt x l.
    Proof.
      intros * hxy hy.
      destruct l; constructor.
      apply HdRel_inv in hy. order.
    Qed.

    Lemma HdRel_swap_le_le: forall (x y: key) l,
        key_le x y -> HdRel key_le y l -> HdRel key_le x l.
    Proof.
      intros * hxy hy.
      destruct l; constructor.
      apply HdRel_inv in hy. order.
    Qed.
    
    Lemma find_index_In_sublist1 {X: Type}: forall k k0 (l: entries X),
        In k (map fst (sublist 0 (find_index k0 l) l)) -> key_lt k k0.
    Proof.
      induction l as [|[k' x'] l].
      + rewrite sublist_of_nil. contradiction.
      + intro h. cbn in h.
        destruct key_compare.
      - rewrite sublist_nil_gen in h by omega. contradiction.
      - rewrite sublist_nil_gen in h by omega. contradiction.
      - rewrite find_index_aux_add in h.
        pose proof (find_index_bounds k0 l) as hb. unfold find_index in hb.
        rewrite sublist_0_cons in h by omega.
        simpl in h. destruct h as [h|h].
        ++ order.
        ++ apply IHl. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r in h. assumption.
    Qed.

    Lemma Forall_Sorted_bounds: forall (l: list key),
        Sorted key_lt l -> 0 <= Zlength l ->
        Forall (fun k => key_le (Znth 0 l) k /\ key_le k (Znth (Zlength l - 1) l)) l.
    Proof.
      induction l as [|k l].
      + constructor.
      + intros * hsorted hlength. rewrite Zlength_cons in hlength.
        destruct l as [|k' l].
      - repeat constructor; cbn; order.
      - rewrite Zlength_cons. rewrite Znth_0_cons in IHl |- *.
        rewrite Znth_pos_cons by (rewrite Zlength_cons; rep_omega).
        replace (Z.succ (Zlength (k' :: l)) - 1 - 1) with (Zlength (k' :: l) - 1) by omega.
        pose proof (Sorted_inv hsorted) as hsorted'. pose proof (HdRel_inv (proj2 hsorted')).
        constructor.
        split. order. 
        apply Sorted_StronglySorted, StronglySorted_inv in hsorted.
        destruct hsorted as [_ hforall]. rewrite Forall_forall in hforall.
        specialize (hforall (Znth (Zlength (k' :: l) - 1) (k' :: l))).
        lapply hforall. order. apply Znth_In. rewrite Zlength_cons. rep_omega.
        do 3 intro; order.
        lapply IHl. intro h. lapply h. apply Forall_impl.
        intros k1 [h1 h2]. split; order. rep_omega.
        easy.
    Qed.

    Lemma well_sorted_children_select: forall children min max,
        well_sorted_children min max children ->
        forall i, 0 <= i < Zlength children ->
        well_sorted_children min (Znth i (map fst children)) (sublist 0 i children) /\
        exists min_n max_n, well_sorted min_n max_n (Znth i (map snd children)) /\
                       key_le max_n max /\
                       key_lt (Znth i (map fst children)) min_n /\
                       (i + 1 < Zlength children -> key_le max_n (Znth (i + 1) (map fst children)) /\
                       well_sorted_children (Znth (i + 1) (map fst children)) max (sublist (i + 1) (Zlength children) children)).
    Proof.
      induction children as [|[k n] children].
      + intros * hminmax i hi. cbn in hi. omega.
      + intros * hchildren i hi.
        rewrite Zlength_cons in hi.
        destruct hchildren as (hle & min_n & max_n & hlt & n_ws & children_ws).
        specialize (IHchildren _ _ children_ws).
        destruct (Z.eq_dec i 0).
      - subst. simpl. rewrite (Znth_pos_cons 1) by omega.
        simpl. split. assumption.
        exists min_n. exists max_n. split3. assumption. apply well_sorted_children_facts in children_ws. easy.
        split. assumption. destruct children as [|[k' n'] children].
        cbn; omega.
        intros _. simpl. split.
        destruct children_ws. assumption.
        rewrite sublist_1_cons, Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_same by reflexivity.
        destruct children_ws. split.
        cbn. order. assumption.
      - simpl. rewrite Znth_pos_cons, sublist_0_cons, Znth_pos_cons by omega.
        specialize (IHchildren (i - 1) ltac:(omega)).
        replace (i - 1 + 1) with i in IHchildren by omega.
        replace (i + 1 - 1) with i by omega.
        destruct IHchildren as (pref & min_ith & max_ith & ith_ws & hmax_ith & hmin_ith & hafter).
        split.
        ++ simpl. split.
           order. exists min_n. exists max_n. split3; try order; assumption.
        ++ exists min_ith. exists max_ith. split3.
           easy. easy. split. assumption. intro h. rewrite Zlength_cons in h.
           rewrite sublist_S_cons, Znth_pos_cons, Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, <- Z.add_sub_assoc,
             Z.sub_diag, Z.add_0_r, Z.add_0_r by omega.
           apply hafter. omega.
    Qed.
    
    Lemma insert_aux_well_sorted: forall root k0 e m M,
        well_sorted m M root ->
        let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
        match oright with
        | None => well_sorted (key_min m k0) (key_max M k0) left
        | Some (right_k, right_n) => well_sorted (key_min m k0) right_k left /\
                                    exists min_right, key_lt right_k min_right /\
                                                 well_sorted min_right (key_max M k0) right_n
        end.
    Proof.
      pose proof min_fanout_pos as min_fanout_pos.
      apply (node_ind (fun root => forall k0 e m M,
                           well_sorted m M root ->
                           let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
                           match oright with
                           | None => well_sorted (key_min m k0) (key_max M k0) left
                           | Some (right_k, right_n) =>
                             well_sorted (key_min m k0) right_k left /\
                             exists min_right : key, key_lt right_k min_right /\
                                                well_sorted min_right (key_max M k0) right_n
                           end)).
      + intros * h.
        rewrite get_cursor_equation. simpl.
        set (i := find_index k0 records).
        pose proof (find_index_bounds k0 records) as hb.
        destruct h as (records_sorted & hmM & records_bounds).
        assert (himpl:  forall k : key, key_le m k /\ key_le k M -> key_le (key_min m k0) k /\ key_le k (key_max M k0)).
        { intros k [hk1 hk2]. split.
          etransitivity. apply MinMaxProps.le_min_l. order.
          etransitivity. apply hk2. apply MinMaxProps.le_max_l. }
          
        assert (hforall: forall i' j', Forall (fun k => key_le (key_min m k0) k /\ key_le k (key_max M k0)) (map fst (sublist i' j' records))).
        { intros. rewrite map_sublist. apply Forall_sublist. apply (Forall_impl _ himpl records_bounds). }
        assert (hk0: key_le (key_min m k0) k0 /\ key_le k0 (key_max M k0)).
        { split. apply MinMaxProps.le_min_r. apply MinMaxProps.le_max_r. }

        destruct sumbool_and as [h|h].
        ++ (* mere update of a record *)
          rewrite well_sorted_equation. split3.
      - rewrite upd_Znth_unfold.
        rewrite map_app, map_app, map_sublist, map_sublist, (proj2 h) by omega.
        simpl. erewrite <- upd_Znth_triv, upd_Znth_unfold, Zlength_map in records_sorted.
        apply records_sorted.
        rewrite Zlength_map; omega. reflexivity.
      - eapply OrderTac.le_trans.
        apply MinMaxProps.le_min_r. apply MinMaxProps.le_max_r.
      - rewrite <- upd_Znth_map. apply Forall_upd_Znth.
        apply (Forall_impl _ himpl records_bounds).
        assumption.
        ++
          assert (hsorted: Sorted key_lt (map fst (sublist 0 i records ++ (k0, e) :: sublist i (Zlength records) records))).
          { rewrite map_app. simpl.
            assert (hsorted1: Sorted key_lt (map fst (sublist 0 i records))).
            { rewrite map_sublist. apply Sorted_sublist. assumption. }
            assert (hsorted2: Sorted key_lt (k0 :: map fst (sublist i (Zlength records) records))).
            { constructor. rewrite map_sublist. apply Sorted_sublist. assumption.
              destruct (Z_lt_ge_dec i (Zlength records)).
              ++ rewrite sublist_next by omega. simpl. rewrite <- Znth_map by omega. constructor.
                 assert (k0 <> Znth i (map fst records)).
                 { destruct h. contradiction. assumption. }
                 pose proof (find_index_after k0 records) as hafter. simpl in hafter.
                 lapply hafter. fold i. order. omega.
              ++ rewrite sublist_nil_gen by omega. constructor. }
            apply Sorted_app. apply hsorted1. apply hsorted2.
            intros k1 k2 h1 h2.
            apply find_index_In_sublist1 in h1.
            enough (key_le k0 k2) by order.
            apply Sorted_StronglySorted, StronglySorted_inv in hsorted2.
            destruct h2 as [h2|h2]. order.
            destruct hsorted2 as [_ hsorted2]. rewrite Forall_forall in hsorted2.
            specialize (hsorted2 k2). lapply hsorted2. order. assumption.
            do 3 intro; order. }
          destruct Z_gt_le_dec as [hoverflow|]. 
      - (* new entry triggers split *)
        split.
        -- rewrite well_sorted_equation.
           match goal with [ |- _ /\ _ /\ ?a] => assert (hforall_new: a) end.
           { eapply Sorted_sublist in hsorted. rewrite sublist_map in hsorted.
             eapply Forall_Sorted_bounds in hsorted.
             refine (Forall_impl _ _ hsorted). intros k' [hk1 hk2]. clear hsorted.
             rewrite Zlength_map, Zlength_sublist, Z.sub_0_r, map_sublist,
             Znth_sublist, Z.add_0_r in hk2 by (rewrite ?map_sublist, ?Zlength_map; rep_omega).
             split. 
             { destruct (Z.eq_dec i 0) as [hi0|hi0]. 
               rewrite hi0 in hk1.
               rewrite (sublist_nil_gen _ 0 0), app_nil_l, sublist_0_cons,
               map_cons, Znth_0_cons in hk1 by omega. simpl in hk1.
               etransitivity. apply MinMaxProps.le_min_r. order.
               rewrite map_sublist, Znth_sublist, map_app, app_Znth1 in hk1
                 by (rewrite ?Zlength_map, ?Zlength_sublist; omega).
               rewrite map_sublist, Znth_sublist in hk1 by omega.
               simpl in hk1.
               rewrite Forall_forall in records_bounds.
               specialize (records_bounds (Znth 0 (map fst records))).
               lapply records_bounds. intros [h1 h2].
               etransitivity. apply MinMaxProps.le_min_l. order. 
               apply Znth_In. rewrite Zlength_map. omega. }
             assumption.
             rewrite Zlength_map, Zlength_sublist; omega. }

           split3.
           --- rewrite map_sublist. apply Sorted_sublist.
               apply hsorted.
           --- destruct (Z.eq_dec i 0) as [hi0|hi0].
               * rewrite hi0 in hforall_new |- *.
                 simpl in hforall_new |- *. rewrite sublist_0_cons in hforall_new by omega.
                 simpl in hforall_new. inversion hforall_new. destruct H1. order.
               * rewrite sublist_next in hforall_new |- * by omega. simpl in hforall_new |- *.
                 rewrite sublist_0_cons in hforall_new by omega. simpl in hforall_new. inversion hforall_new. 
                 destruct H1. order. 
           --- apply hforall_new.
        -- exists (Znth min_fanout (map fst (sublist 0 i records ++
                                                (k0, e) :: sublist i (Zlength records) records))).
           split.
           {
             rewrite <- (Zlength_map _ _ fst) in hoverflow.
             generalize dependent (map fst (sublist 0 i records ++
                                                    (k0, e) :: sublist i (Zlength records) records)).
             clear - min_fanout_pos. revert min_fanout_pos.
             apply (natlike_ind (fun min_fanout => min_fanout > 0 -> forall l : list key,
                                     Sorted key_lt l ->
                                     Zlength l > 2 * min_fanout ->
                                     key_lt (Znth (min_fanout - 1) l) (Znth min_fanout l))).
             intros; omega.
             intros min_fanout hmin_fanout hrec _ l hsorted hlength.             
             rewrite <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
             destruct l as [|k [|k' l]].
             rewrite Zlength_nil in hlength; omega.
             rewrite Zlength_cons, Zlength_nil in hlength; omega.
             destruct (Z.eq_dec min_fanout 0).
             + subst. cbn. apply Sorted_inv in hsorted. destruct hsorted as [_ hhdrel%HdRel_inv].
               order.
             + rewrite Znth_pos_cons by omega. rewrite (Znth_pos_cons (min_fanout + 1)) by omega.
               rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. apply hrec. omega.
               now inversion hsorted. rewrite Zlength_cons in hlength |- *.
               rewrite Zlength_cons in hlength. omega. 
             + pose proof min_fanout_pos. omega. }
           {
             rewrite well_sorted_equation.
             match goal with [ |- _ /\ _ /\ ?a ] => assert (hforall_new: a) end.
             { 
               eapply Sorted_sublist in hsorted. rewrite sublist_map in hsorted.
               eapply Forall_Sorted_bounds in hsorted.
               refine (Forall_impl _ _ hsorted). intros k' [hk1 hk2]. clear hsorted.
               rewrite Znth_map, Znth_sublist, <- (Znth_map _ fst), Z.add_0_l in hk1
                 by (rewrite ?Zlength_sublist; rep_omega).
               split. order. 
               { etransitivity. apply hk2. clear hk2.
                 rewrite Forall_forall in records_bounds.
                 specialize (records_bounds (Znth (Zlength records - 1) (map fst records))).
                 lapply records_bounds. intros [_ hM].
                 match goal with [ |- key_le ?a _ ] =>
                                 enough (henough: a = k0 \/
                                                  a = (Znth (Zlength records - 1) (map fst records)))
                 end. destruct henough as [henough|henough]; rewrite henough.
                 apply MinMaxProps.le_max_r.
                 etransitivity. apply hM. apply MinMaxProps.le_max_l.
                 { destruct (eq_dec i (Zlength records)).
                   + left.
                     rewrite (sublist_nil_gen _ i) in hoverflow |- * by omega.
                     rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_nil in hoverflow by omega.
                     autorewrite with sublist.
                     rewrite map_sublist, Znth_sublist by omega.
                     rewrite map_app, app_Znth2, Zlength_map, Zlength_sublist by
                         (rewrite ?Zlength_map, ?Zlength_sublist; omega).
                     match goal with [ |- Znth ?k _ = _ ] => replace k with 0 by omega; reflexivity end.
                   + right.
                     replace (Zlength records) with (Zlength records - 1 + 1) by omega.
                     rewrite sublist_last_1 by omega.
                     rewrite Zlength_app, Zlength_sublist, Zlength_cons,
                     Zlength_sublist in hoverflow by omega.
                     autorewrite with sublist.
                     rewrite map_sublist, Znth_sublist by omega.
                     rewrite map_app, app_Znth2, Zlength_map, Zlength_sublist by
                         (rewrite ?Zlength_map, ?Zlength_sublist; omega).
                     rewrite map_cons, map_app.
                     rewrite Znth_pos_cons, app_Znth2 by (rewrite ?Zlength_map, ?Zlength_sublist; omega).
                     simpl. rewrite Zlength_map, Zlength_sublist, Znth_map by omega.
                     match goal with [ |- Znth ?k _ = _ ] => replace k with 0 by omega; reflexivity end. }
                 apply Znth_In.
                 rewrite Zlength_app, Zlength_sublist, Zlength_cons,
                 Zlength_sublist in hoverflow by omega. rewrite Zlength_map. omega. }
             rewrite Zlength_map, Zlength_sublist; omega.
             }
             split3.
             --- rewrite map_sublist. apply Sorted_sublist.
                 apply hsorted.
             --- enough (hnil: (map fst
                     (sublist min_fanout
                        (Zlength (sublist 0 i records ++ (k0, e) :: sublist i (Zlength records) records))
                        (sublist 0 i records ++ (k0, e) :: sublist i (Zlength records) records))) <> nil).
                 match type of hnil with (?a <> nil) => destruct a end. contradiction. inversion hforall_new.
                 destruct H1. order.
                 intros hcontr%map_eq_nil. apply (f_equal (@Zlength _)) in hcontr.
                 rewrite Zlength_sublist, Zlength_nil in hcontr; omega.
             --- apply hforall_new. }
      - (* new entry doesn't trigger split *)
        rewrite well_sorted_equation. split3.
        -- apply hsorted.
        -- destruct hk0. order.
        -- rewrite map_app, Forall_app. simpl. split.
           +++ apply hforall.
           +++ constructor. assumption.
               apply hforall.
        + intros * hptr0 hchildren * h%well_sorted_equation.
          rewrite get_cursor_equation.
          destruct h as (max_ptr0 & ws_ptr0 & ws_children).
          simpl.
          set (i := find_index k0 children) in *.
          pose proof (find_index_bounds k0 children) as hb_index. fold i in hb_index.
          case_eq (insert_aux k0 e (get_cursor k0 (if Z.eq_dec i 0 then ptr0 else Znth (i - 1) (List.map snd children)))).
          destruct (Z.eq_dec i 0) as [hi0|].
          ++ unfold i in hi0. rewrite find_index_HdRel in hi0.
             specialize (hptr0 k0 e _ _ ws_ptr0).
             intros left o heqrec.
             rewrite heqrec in hptr0. clear hchildren heqrec.
             destruct o as [[new_child_key new_child_node]|].
      - destruct hptr0 as (left_ws & min_right & lt_min_right & right_ws).
        destruct Z_gt_le_dec as [hoverflow|].
        -- rewrite Zlength_cons in hoverflow.
           rewrite <- (combine_eq (_ :: _)), Znth_combine by (do 2 rewrite Zlength_map; reflexivity).
           rewrite well_sorted_equation. split.
           { exists new_child_key. split. assumption.
             simpl.
           rewrite sublist_0_cons by omega. simpl. split. order.
           exists min_right. exists (key_max max_ptr0 k0). split3.
           order. assumption.
           rewrite Znth_pos_cons by omega.
           rewrite combine_eq.
           unshelve eapply (well_sorted_children_split1 _ _ _ M). omega. omega.
           destruct children as [|[k n] children].
           rewrite Zlength_nil in hoverflow. omega.
           simpl in hi0, ws_children |- *.
           split. apply MinMaxProps.max_lub. easy. now inversion hi0. easy. }
           eapply well_sorted_children_select in ws_children.
           destruct ws_children as (wsc_before & min_mid & max_mid & ws_mid & le_max_mid &
                                    lt_min_mid & hafter).
           exists min_mid.
           simpl. rewrite sublist_S_cons, Znth_pos_cons, Znth_pos_cons, Zlength_cons, <- Z.add_1_r by omega.
           do 2 rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
           split. apply lt_min_mid. 
           rewrite <- Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r in hafter by omega.
           rewrite well_sorted_equation. exists max_mid. split.
           assumption.
           destruct (Z.eq_dec min_fanout (Zlength children)).
        * rewrite sublist_nil_gen by omega. simpl.
          etransitivity. apply le_max_mid. eapply MinMaxProps.le_max_l.
        * lapply hafter. intros [hle hwsc].
          eapply well_sorted_children_extends. rewrite combine_eq. apply hwsc.
          order. apply MinMaxProps.le_max_l. omega.
        * omega.
          -- rewrite well_sorted_equation.
             exists new_child_key. split. assumption.
             simpl. split. order.
             exists min_right. exists (key_max max_ptr0 k0). split3.
        * order.
        * assumption.
        * destruct children as [|[k n] children].
          simpl in ws_children |- *. apply MinMaxProps.max_le_compat_r. order.
          eapply well_sorted_children_extends.
          simpl in hi0, ws_children |- *.
          split. apply MinMaxProps.max_lub. exact (proj1 ws_children).
          apply (HdRel_inv hi0). apply (proj2 ws_children). order. apply MinMaxProps.le_max_l.
      - rewrite well_sorted_equation.
        exists (key_max max_ptr0 k0). split. assumption.
        destruct children as [|[k n] children].
        simpl. apply MinMaxProps.max_le_compat. simpl in ws_children. order. order.
        apply (well_sorted_children_extends _ (key_max max_ptr0 k0) M).
        simpl. split. apply MinMaxProps.max_lub. simpl in ws_children. easy.
        apply HdRel_inv in hi0. cbn in hi0. assumption.
        simpl in ws_children. easy. order. apply MinMaxProps.le_max_l.
        ++ clear hptr0.
           intros left [[new_child_key new_child_node]|] heqrec.
      - (* the hardest case, to do first to check that the induction hypothesis is strong enough *)
        set (new_children := (sublist 0 (i - 1) children ++
                                      (Znth (i - 1) (map fst children), left)
                                      :: (new_child_key, new_child_node) :: sublist i (Zlength children) children)) in *.
        
        rewrite Forall_forall in hchildren.
        specialize (hchildren (Znth (i - 1) (map snd children))  ltac:(apply Znth_In; rewrite ?Zlength_map; omega)).
        simpl in hchildren.
        destruct (well_sorted_children_select _ _ _ ws_children (i - 1) ltac:(omega)) as
            (hle & min_tc & max_tc & ws_tc & hmax_tc & hmin_tc & hnext).
        replace (i - 1 + 1) with i in hnext by omega.
        specialize (hchildren k0 e _ _ ws_tc).
        rewrite heqrec in hchildren. clear heqrec.
        destruct hchildren as (left_ws & min_right & hlt_min_right & right_ws).
        assert (new_children_wsc:
                  well_sorted_children max_ptr0 (key_max M k0) new_children).
        { 
          eapply well_sorted_children_app.
          + eapply well_sorted_children_split1. omega. omega.
            eassumption.
          + eapply well_sorted_children_cons.
          - eassumption.
          - eapply (well_sorted_children_cons _ (key_max max_tc k0)).
            eassumption.
            destruct (Z_lt_ge_dec i (Zlength children)) as [hlast|hnlast].
            -- eapply well_sorted_children_extends. 
               eapply well_sorted_children_split2. omega. omega.
               eapply well_sorted_children_extends. eassumption.
               apply OrderTac.le_refl.
               apply MinMaxProps.le_max_l.
               apply MinMaxProps.max_lub.
               apply hnext. omega.
               apply find_index_after. assumption.
               apply OrderTac.le_refl.
            -- rewrite sublist_nil_gen by omega. cbn.
               apply MinMaxProps.max_le_compat_r.
               assumption.
            -- order.
            -- order.
          - apply MinMaxProps.min_glb_lt.
            order.
            apply find_index_pos_before. omega.
          - order.
            + order.
        }
        destruct Z_gt_le_dec.
        -- rewrite <- (combine_eq new_children), Znth_combine by (do 2 rewrite Zlength_map; reflexivity).
           split.
           --- rewrite well_sorted_equation.
               exists max_ptr0. split.
               { eapply well_sorted_extends. eassumption.
                 apply MinMaxProps.le_min_l. order. }
               { rewrite combine_eq. eapply well_sorted_children_split1.
                 omega. omega.
                 apply new_children_wsc. }
           --- pose proof (well_sorted_children_select _ _ _ new_children_wsc min_fanout ltac:(omega))
                 as kn_facts.
               destruct kn_facts as (pre_ws & min_kn & max_kn & kn_ws & le_max_kn & lt_min_kn & kn_after).
               pose (kn := Znth min_fanout new_children).
               exists min_kn. split.
               assumption.
               {
                 rewrite well_sorted_equation.
                 exists max_kn. split.
                 assumption.
                 lapply kn_after.
                 intros [hle' hwsc].
                 eapply well_sorted_children_extends. rewrite combine_eq. apply hwsc.
                 assumption. order. omega.
               }
        -- (* new entry doesn't produce overflow *)
          rewrite well_sorted_equation.
          exists max_ptr0. split.
          eapply well_sorted_extends; try eassumption.
          apply MinMaxProps.le_min_l. order.
          apply new_children_wsc.
      - (* no new entry, just update *)
        rewrite well_sorted_equation.
        exists max_ptr0. split.
        eapply well_sorted_extends.
        eassumption. apply MinMaxProps.le_min_l. order.
        rewrite upd_Znth_unfold. simpl.
        rewrite Forall_forall in hchildren.
        specialize (hchildren (Znth (i - 1) (map snd children)) ltac:(apply Znth_In; rewrite Zlength_map; omega)).
        simpl in hchildren.
        destruct (well_sorted_children_select _ _ _ ws_children (i - 1) ltac:(omega)) as
            (hle & min_tc & max_tc & ws_tc & hmax_tc & hmin_tc & hnext).
        replace (i - 1 + 1) with i in hnext by omega.
        specialize (hchildren k0 e _ _ ws_tc).
        rewrite heqrec in hchildren. clear heqrec.
        eapply well_sorted_children_app. eassumption.
        replace (i - 1 + 1) with i by omega.
        eapply well_sorted_children_cons. eassumption.
        {
          destruct (Z_lt_ge_dec i (Zlength children)) as [hlast|hnlast].
          + eapply well_sorted_children_extends. 
            eapply well_sorted_children_split2. omega. omega.
            eapply well_sorted_children_extends. eassumption.
            apply OrderTac.le_refl.
            apply MinMaxProps.le_max_l.
            apply MinMaxProps.max_lub.
            apply hnext. omega.
            apply find_index_after. assumption.
            apply OrderTac.le_refl.
          + rewrite sublist_nil_gen by omega. cbn.
            apply MinMaxProps.max_le_compat_r.
            assumption. }
        apply MinMaxProps.min_glb_lt.
        assumption.
        apply find_index_before. omega.
        order.
        order.
    Qed.

    (* well_sortedness is conserved by insertions *)
    Theorem insert_well_sorted: forall root m M k0 e info,
        well_sorted m M root -> well_sorted (key_min m k0) (key_max M k0) (insert k0 e info root).
    Proof.
      intros * h.
      unfold insert.
      eapply (insert_aux_well_sorted root k0 e) in h. destruct insert_aux as [left [[right_k right_n]|]].
      + destruct h as (left_ws & min_right & lt_right & right_ws).
        rewrite well_sorted_equation. exists right_k. split.
        assumption.
        simpl. split. order.
        exists min_right. exists (key_max M k0). split3. order.
        assumption. order.
      + assumption.
    Qed.

    (* A node that is not the root has between min_fanout and 2*min_fanout entries *)
    Fixpoint well_sized (n: node): Prop :=
      match n with
      | leaf records _ => min_fanout <= Zlength records <= 2 * min_fanout
      | internal ptr0 children _ => well_sized ptr0 /\
                                   fold_right and True (map (well_sized oo snd) children) /\
                                   min_fanout <= Zlength children <= 2 * min_fanout
      end.

    Definition well_sized_children (children: entries node): Prop :=
      fold_right and True (map (well_sized oo snd) children).

    Lemma well_sized_equation: forall n,
        well_sized n = match n with
                       | leaf records _ => min_fanout <= Zlength records <= 2 * min_fanout
                       | internal ptr0 children _ => well_sized ptr0 /\
                                                    well_sized_children children /\
                                                    min_fanout <= Zlength children <= 2 * min_fanout
                       end.
    Proof. destruct n; reflexivity. Qed.

    Opaque well_sized.

    Lemma well_sized_children_cons: forall k n l,
        well_sized_children ((k, n) :: l) <-> (well_sized n /\ well_sized_children l).
    Proof. reflexivity. Qed.

    Lemma well_sized_children_sublist: forall l i j,
        well_sized_children l ->
        0 <= i <= j -> well_sized_children (sublist i j l).
    Proof.
      induction l as [|[k n] l].
      + intros * h hij. rewrite sublist_of_nil. trivial.
      + intros * h hij. rewrite well_sized_children_cons in h. destruct h as [n_wz rest_wz].
        destruct (Z.eq_dec i j). rewrite sublist_nil_gen by omega. cbn. trivial.
        destruct (Z.eq_dec i 0).
      - rewrite sublist_0_cons' by omega. rewrite well_sized_children_cons. split.
        assumption.
        destruct (Z.eq_dec j 1).
        -- rewrite sublist_nil_gen by omega. cbn. trivial.
        -- apply IHl. assumption. omega.
      - rewrite sublist_S_cons by omega. apply IHl. assumption. omega.
    Qed.

    Lemma well_sized_children_Znth: forall l i,
        well_sized_children l ->
        0 <= i < Zlength l ->
        well_sized (Znth i (map snd l)).
    Proof.
      induction l as [|[k n] l].
      + intros * h hlen. rewrite Zlength_nil in hlen; omega.
      + intros * h hlen.
        rewrite well_sized_children_cons in h.
        destruct (eq_dec i 0).
      - subst i. simpl. now rewrite Znth_0_cons.
      - simpl. rewrite Znth_pos_cons by omega. apply IHl. easy.
        rewrite Zlength_cons in hlen. omega.
    Qed.

    Lemma insert_aux_well_sized: forall root k0 e,
        well_sized root ->
        let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
        match oright with
        | None => well_sized left
        | Some (right_k, right_n) => well_sized left /\ well_sized right_n
        end.
    Proof.
      pose proof min_fanout_pos as min_fanout_pos.
      apply (node_ind (fun root => forall k0 e,
                           well_sized root ->
                           let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
                           match oright with
                           | None => well_sized left
                           | Some (right_k, right_n) => well_sized left /\ well_sized right_n
                           end)).
      + simpl. intros * h.
        rewrite well_sized_equation in h.
        pose proof (find_index_bounds k0 records).
        destruct sumbool_and.
      - rewrite well_sized_equation. rewrite upd_Znth_Zlength; omega.
      - destruct Z_gt_le_dec.
        -- do 2 rewrite well_sized_equation. split.
           rewrite Zlength_sublist; omega.
           rewrite Zlength_sublist by omega. split. omega.
           rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; omega.
        -- simpl. split. rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; omega. omega.
      + intros * hptr0 hchildren * h. rewrite well_sized_equation in h.
        destruct h as (wz_ptr0 & wz_children & hZlength_children).
        pose proof (find_index_bounds k0 children).
        rewrite get_cursor_equation. simpl.
        destruct (Z.eq_dec (find_index k0 children) 0).
      - clear hchildren.
        generalize (hptr0 k0 e wz_ptr0).
        destruct insert_aux as [left [[right_key right_node]|]].
        -- intros [left_wz right_wz]. destruct Z_gt_le_dec as [hoverflow|hoverflow].
           ++ rewrite <- (combine_eq (_ :: _)), Znth_combine by (do 2 rewrite Zlength_map; reflexivity).
              split; rewrite well_sized_equation, combine_eq.
              --- split3.
                  * easy.
                  * simpl. rewrite sublist_0_cons by omega. simpl. split.
                    easy. apply well_sized_children_sublist. assumption. omega.
                  * rewrite Zlength_sublist; omega.
              --- split3.
                  * simpl. rewrite Znth_pos_cons by omega.
                    apply well_sized_children_Znth. assumption. omega.
                  * simpl. rewrite sublist_S_cons by omega.
                    apply well_sized_children_sublist. assumption.
                    rewrite Zlength_cons. omega.
                  * rewrite Zlength_cons in hoverflow.
                    rewrite Zlength_sublist; rewrite ?Zlength_cons; omega.
           ++ rewrite well_sized_equation. split3.
              easy.
              now rewrite well_sized_children_cons.
              rewrite Zlength_cons in hoverflow |- *. omega.
        -- intro left_wz. rewrite well_sized_equation. split3.
           easy.
           easy.
           omega.
      - clear hptr0.
        set (i := find_index k0 children) in *.
        rewrite Forall_forall in hchildren.
        pose proof (well_sized_children_Znth children (i - 1) wz_children ltac:(omega)) as ith_wz.
        generalize (hchildren (Znth (i - 1) (map snd children)) ltac:(apply Znth_In; rewrite Zlength_map; omega) k0 e ith_wz).
        rewrite Znth_map by omega.
        destruct insert_aux as [left [[right_key right_node]|]]. 
        -- intros [left_wz right_wz].
           assert (wz_whole: well_sized_children
                               (sublist 0 (i - 1) children ++
                                        (Znth (i - 1) (map fst children), left) :: (right_key, right_node) :: sublist i (Zlength children) children)).
           { unfold well_sized_children. rewrite map_app, fold_right_and_app_low. split.
             apply well_sized_children_sublist. assumption. omega.
             simpl. split3. assumption. assumption.
             apply well_sized_children_sublist. assumption. omega. }
           destruct Z_gt_le_dec as [hoverflow|hoverflow].
           ++ rewrite <- (combine_eq (_ ++ _)), Znth_combine by (do 2 rewrite Zlength_map; omega).
              split.
              * rewrite well_sized_equation, combine_eq. split3.
                ** assumption.
                ** apply well_sized_children_sublist; [|omega].
                   apply wz_whole.
                ** rewrite Zlength_sublist; omega.
              * rewrite well_sized_equation, combine_eq. split3.
                ** eapply well_sized_children_Znth in wz_whole. eassumption.
                   omega.
                ** apply well_sized_children_sublist; [|omega].
                   apply wz_whole.
                ** rewrite Zlength_sublist. split. omega.
                   rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_cons, Zlength_sublist; omega.
                   omega. omega.
           ++ rewrite well_sized_equation. split3.
              assumption. apply wz_whole. split.
              rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_cons, Zlength_sublist; omega.
              omega.
        -- intro wz_left. rewrite well_sized_equation. split3. assumption.
           rewrite upd_Znth_unfold. simpl.
           unfold well_sized_children. rewrite map_app, fold_right_and_app_low. split.
           apply well_sized_children_sublist. assumption. omega.
           simpl. split. easy. apply well_sized_children_sublist. assumption.
           omega. rewrite upd_Znth_Zlength. omega. omega.
    Qed.

    (* The root has a maximum of 2*min_fanout entries *)
    Definition well_sized_root (root : node) : Prop :=
      match root with
      | leaf records _ => Zlength records <= 2 * min_fanout
      | internal ptr0 children _ =>
        well_sized ptr0 /\
        fold_right and True (map (well_sized oo snd) children) /\ Zlength children <= 2 * min_fanout
      end.

    (* the "well sized" property of a root is preserved by insertion *)
    (* This proof is essentially the same as the one above, with few modifications
       because the well_sized_root predicate is slightly different.
       There is no induction here, because well_sized_root is not inductive!
       I don't think code can be factorized. *)
    Theorem insert_well_sized_root: forall root k0 e info,
        well_sized_root root ->
        well_sized_root (insert k0 e info root).
    Proof.
      pose proof min_fanout_pos as min_fanout_pos.
      unfold insert. setoid_rewrite get_cursor_equation.
      intros [] * h.
      + simpl in h |- *.
        pose proof (find_index_bounds k0 records).
        destruct sumbool_and.
      - simpl. rewrite upd_Znth_Zlength; omega.
      - destruct Z_gt_le_dec.
        -- simpl. do 2 rewrite well_sized_equation. split3.
           rewrite Zlength_sublist; omega.
           rewrite Zlength_sublist by omega. rewrite and_True. split. omega.
           rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; omega.
           cbn. omega.
        -- simpl. omega.
      + simpl in h.
        destruct h as (wz_ptr0 & wz_children & hZlength_children).
        pose proof (find_index_bounds k0 children).
        simpl.
        destruct (Z.eq_dec (find_index k0 children) 0).
      - generalize (insert_aux_well_sized ptr0 k0 e wz_ptr0).
        destruct insert_aux as [left [[right_key right_node]|]].
        -- intros [left_wz right_wz]. destruct Z_gt_le_dec as [hoverflow|hoverflow].
           ++ rewrite <- (combine_eq (_ :: _)), Znth_combine by (do 2 rewrite Zlength_map; omega).
              rewrite Zlength_cons in hoverflow.
              simpl. rewrite and_True. split3.
              --- rewrite well_sized_equation, combine_eq. split3.
                  * easy.
                  * rewrite sublist_0_cons, well_sized_children_cons by omega. split.
                    easy. apply well_sized_children_sublist. assumption. omega.
                  * rewrite Zlength_sublist; rewrite ?Zlength_cons; omega.
              --- rewrite well_sized_equation, combine_eq. split3.
                  * rewrite Znth_pos_cons by omega.
                    apply well_sized_children_Znth. assumption. omega.
                  * rewrite sublist_S_cons by omega.
                    apply well_sized_children_sublist. assumption. rewrite Zlength_cons. omega.
                  * rewrite Zlength_sublist; rewrite ?Zlength_cons; omega.
              --- cbn. omega.
           ++ simpl. easy.
        -- intro left_wz. simpl. split3.
           easy.
           easy.
           omega.
      - set (i := find_index k0 children) in *.
        pose proof (well_sized_children_Znth children (i - 1) wz_children ltac:(omega)) as ith_wz.
        generalize ((insert_aux_well_sized (Znth (i - 1) (map snd children))) k0 e ith_wz).
        rewrite Znth_map by omega.
        destruct insert_aux as [left [[right_key right_node]|]]. 
        -- intros [left_wz right_wz].
           assert (wz_whole: well_sized_children
                               (sublist 0 (i - 1) children ++
                                        (Znth (i - 1) (map fst children), left) :: (right_key, right_node) :: sublist i (Zlength children) children)).
           { unfold well_sized_children. rewrite map_app, fold_right_and_app_low. split.
             apply well_sized_children_sublist. assumption. omega.
             simpl. split3. assumption. assumption.
             apply well_sized_children_sublist. assumption. omega. }
           destruct Z_gt_le_dec as [hoverflow|hoverflow].
           ++ rewrite <- (combine_eq (_ ++ _)), Znth_combine by (do 2 rewrite Zlength_map; omega).
              simpl. rewrite and_True.
              split3.
              * rewrite well_sized_equation, combine_eq. split3.
                ** assumption.
                ** apply well_sized_children_sublist; [|omega].
                   apply wz_whole.
                ** rewrite Zlength_sublist; omega.
              * rewrite well_sized_equation, combine_eq. split3.
                ** eapply well_sized_children_Znth in wz_whole. eassumption.
                   omega.
                ** apply well_sized_children_sublist; [|omega].
                   apply wz_whole.
                ** rewrite Zlength_sublist. split. omega.
                   rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_cons, Zlength_sublist; omega.
                   omega. omega.
              * cbn. omega.
           ++ simpl. split3.
              assumption. apply wz_whole. omega.
        -- intro wz_left. simpl. split3. assumption.
           rewrite upd_Znth_unfold. simpl.
           unfold well_sized_children. rewrite map_app, fold_right_and_app_low. split.
           apply well_sized_children_sublist. assumption. omega.
           simpl. split. easy. apply well_sized_children_sublist. assumption.
           omega. rewrite upd_Znth_Zlength. omega. omega.
    Qed.

  End Elt.
  Arguments node : clear implicits.

End Raw.

Module MyParams <: BPlusTreeParams.
  Module InfoTyp.
    Definition t := unit.
  End InfoTyp.
  Definition min_fanout: Z := 2.
  Lemma min_fanout_pos: min_fanout > 0. unfold min_fanout. omega. Qed.
End MyParams.

Require OrdersEx.
Module bt := Raw OrdersEx.Z_as_DT MyParams.

Section Tests.
  Check bt.insert.
  Instance Inhabitant_unit: Inhabitant unit := tt.
  Fixpoint insert_list (n: bt.node Z) (l: list (Z * Z)): bt.node Z :=
    match l with
    | nil => n
    | (k, v) :: tl => insert_list (bt.insert k v tt n) tl
    end.    
  
  Set Default Timeout 5.
  Definition test_node := insert_list (bt.leaf [] tt) (map (fun k => (k, k)) [5; 4; 3; 2; 1; 0; -2 ;34; 2; 75; 44; 4; 2; 3; 3; 3; 3; -1; 154]).
  Compute (bt.flatten test_node).

  Compute (bt.flatten (insert_list test_node [(5, 4); (4, 5); (-2, -1); (-2, 3)])).

End Tests.
