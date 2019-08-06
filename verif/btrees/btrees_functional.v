Require Orders OrdersTac.
Require GenericMinMax.
Require ZArith.Zcomplements VST.floyd.sublist VST.progs.conclib Coq.omega.Omega.

Require Import Recdef List SetoidList Morphisms Program.Basics Program.Combinators Relation_Definitions Sorting.Sorted.
Import ListNotations Classes.SetoidTactics.

Infix "oo" := compose (at level 54, right associativity).

Fixpoint wf_guard {A} {R : A -> A -> Prop}
      (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
    | 0 => wfR
    | S n => fun x =>
       Acc_intro x (fun y _ => wf_guard n (wf_guard n wfR) y)
    end.
Strategy 100 [wf_guard].

Module Type BPlusTreeParams.
  Module InfoTyp.
    Parameter t: Type.
  End InfoTyp.
  Parameter min_fanout: nat.
  Axiom min_fanout_pos: min_fanout > 0.
End BPlusTreeParams.

Module Raw (X: Orders.UsualOrderedTypeFull') (Params: BPlusTreeParams).

  Module Info := Params.InfoTyp.
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

  Definition entries (elt: Type): Type := list (key * elt).

  Section Elt.
    (* elt is the type of the values stored in the B+Tree *)
    Context {elt: Type}.
    
    Unset Elimination Schemes.
    
    Inductive node: Type :=
    | leaf: forall (records: entries elt) (info: Info.t), node
    | internal: forall (ptr0: node) (children: entries node) (info: Info.t), node.
    
    Lemma node_ind (P: node -> Prop)
          (hleaf: forall records info, P (leaf records info))
          (hinternal: forall ptr0 children info,
              P ptr0 ->
              Forall (P oo snd) children ->
              P (internal ptr0 children info)) :
      forall n, P n.
    Proof.
      fix hrec 1.
      intros [].
      apply hleaf.
      apply hinternal. apply hrec.
      induction children as [|[k n] children]. auto.
      constructor. apply hrec. assumption.
    Qed.
    
    Set Elimination Schemes.

    Inductive direct_subnode: relation node :=
    | subnode_ptr0: forall ptr0 records info,
        direct_subnode ptr0 (internal ptr0 records info)
    | subnode_entry: forall k n ptr0 children info,
        In (k, n) children ->
        direct_subnode n (internal ptr0 children info).
    
    Lemma Forall_range: forall (P: node -> Prop) (l: entries node),
        Forall (P oo snd) l ->
        forall k n, In (k, n) l -> P n.
    Proof. intros * h. rewrite Forall_forall in h. intros * hin.
           apply (h (k, n)). assumption. Qed.

    Lemma Forall_dom: forall (P: key -> Prop) (l: entries elt),
        Forall (P oo fst) l ->
        forall k n, In (k, n) l -> P k.
    Proof. intros * h. rewrite Forall_forall in h. intros * hin.
           apply (h (k, n)). assumption. Qed.
    
    Lemma direct_subnode_wf: well_founded direct_subnode.
    Proof.
      unfold well_founded.
      apply (node_ind (fun n => Acc direct_subnode n)).
      + constructor. intros n hn. inversion hn.
      + intros * hptr0 hchildren. constructor.
        intros n hn. inversion hn. assumption.
        eapply Forall_range; eassumption.
    Qed.
    
    Definition subnode: relation node := Relation_Operators.clos_refl_trans node direct_subnode.

    Inductive balanced: nat -> node -> Prop :=
    | balanced_leaf: forall {records info}, balanced 0 (leaf records info)
    | balanced_internal: forall {depth ptr0 children info},
        balanced depth ptr0 -> Forall (balanced depth oo snd) children ->
        balanced (S depth) (internal ptr0 children info). 

    Fixpoint well_sorted (min max: key) (n: node): Prop :=
      match n with
      | leaf records info => Sorted key_lt (map fst records) /\
                            key_le min max /\ (* in case records is empty *)
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

    Inductive well_sized: node -> Prop :=
    | ws_leaf: forall records info, Params.min_fanout <= length records <= 2 * Params.min_fanout -> well_sized (leaf records info)
    | ws_internal: forall ptr0 children info,
        Params.min_fanout <= length children <= 2 * Params.min_fanout ->
        well_sized ptr0 -> (forall k n, In (k, n) children -> well_sized n) ->
        well_sized (internal ptr0 children info).
    
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
      | internal ptr0 children _ => flatten ptr0 ++ flat_map (compose flatten snd) children
      end.
    
    Fixpoint cardinal (n: node): nat :=
      match n with
      | leaf children _ => Datatypes.length children
      | internal ptr0 children _ => cardinal ptr0 + fold_right Nat.add 0%nat (List.map (compose cardinal snd) children)
      end.

    Lemma cardinal_flatten_length: forall n, length (flatten n) = cardinal n.
    Proof.
      apply node_ind.
      + intros. reflexivity.
      + intros * hlength hchildren.
        simpl. rewrite app_length, hlength. f_equal.
        induction children as [|[k n] children].
        - reflexivity.
        - simpl. rewrite app_length.
          rewrite IHchildren by now inversion hchildren.
          apply Forall_inv in hchildren. rewrite hchildren. reflexivity.
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

    Lemma Sorted_app {A: Type}: forall (R: relation A) l1 l2,
        Sorted R l1 -> Sorted R l2 ->
        (forall x y, In x l1 -> In y l2 -> R x y) ->
        Sorted R (l1 ++ l2).
    Proof.
      intros * h1 h2 hbi.
      eapply SortA_app. apply eq_equivalence.
      assumption. assumption.
      intros x y hinax hinay.
      rewrite InA_alt in hinax, hinay.
      destruct hinax as (x' & hx' & hinx').
      destruct hinay as (y' & hy' & hiny').
      subst. apply hbi; assumption.
    Qed.     

    Lemma Forall_app {A: Type}: forall (P: A -> Prop) l1 l2,
        Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
    Proof.
      induction l1; intro l2.
      + split; intro h.
        - split. constructor. assumption.
        - easy.
      + simpl. split; intro h.
        - split. constructor. apply Forall_inv in h. assumption.
          refine (proj1 (proj1 (IHl1 _) _)). inversion h; eassumption.
          refine (proj2 (proj1 (IHl1 _) _)). inversion h; eassumption.
        - destruct h as [h1 h2]. constructor. now inversion h1.
          rewrite IHl1. split. now inversion h1. assumption.
    Qed.

    (* It is required to prove at the same time the bounds and the sortedness,
       because the bounds of l1 and l2 are needed for the sortedness of l1 ++ l2 *)
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
          enough (henough: Forall (fun k => key_lt max_ptr0 k /\ key_le k max) (map fst (flat_map (compose flatten snd) children)) /\
                           Sorted key_lt (map fst (flat_map (compose flatten snd) children))).
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

  Section ZSection.
    Import Omega sublist Zcomplements conclib. Open Scope Z_scope.

    Context {default_key: Inhabitant key} {default_elt: Inhabitant elt} {default_info: Inhabitant Info.t}.

    Instance Inhabitant_node: Inhabitant node := leaf [] default_info.

    Lemma HdRel_dec {A: Type} (R: relation A) (hR: forall a b, {R a b} + {~ R a b}):
      forall x l, {HdRel R x l} + {~ HdRel R x l}.
    Proof.
      destruct l as [|hd tl].
      + left. constructor.
      + destruct (hR x hd).
        - left. constructor. assumption.
        - right. intros hcontr%HdRel_inv. contradiction.
    Defined.

    Section FindIndex.
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
          key_lt (fst (Znth (i - 1) l)) k0.
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
          key_le k0 (fst (Znth i l)).
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
          key_lt (fst (Znth (i - 1) l)) k0.
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

      Definition insert_entry (k: key) (x: X) (i: Z) (children: entries X): entries X :=
        sublist 0 i children ++ (k, x) :: sublist i (Zlength children) children.

    End FindIndex.

(*
      Inductive child_fits (n: node) (k: key) (i: Z) (children: entries node):
        forall min max: key, Prop :=
      | child_fits_cons: forall max_n min max,
          well_sorted k max_n n ->
          well_sorted_children min k (sublist 0 i children) ->
          well_sorted_children max_n max (sublist i (Zlength children) children) ->
          child_fits n k i children (key_min min k) (key_max max k).

      Definition child_fits' (n: node) (k: key) (i: Z) (children: entries node): Prop :=
        exists max_n, well_sorted k max_n n /\
        exists min max, well_sorted_children min k (sublist 0 i children) /\
                   well_sorted_children max_n max (sublist i (Zlength children) children).

      Lemma well_sorted_insert_child: forall n k children min max,
          let i := find_index k children in
          child_fits n k i children min max ->
          well_sorted_children min max children.
      Proof.
        induction children as [|[k' n'] children].
        + intros * h. cbn. inversion h.
          subst.
*)
(*
    Lemma add_child_Sorted: forall k0 n0 entries,
        ~ In k0 entries ->
        add_child k0 n0 (find_index k0 entries + 1) entries = add k0 n0 entries.
    Proof.
      intros * hin.
      unfold add_child, find_child_index.
      induction entries as [|[k' n'] entries].
      + cbn; reflexivity.
      + simpl. destruct key_compare.
        - simpl.
          rewrite sublist_same; reflexivity.
        - exfalso. apply hin.
          eapply PX.In_eq. apply X.eq_sym. eassumption.
          exists n'. constructor. apply eqke_refl.
        - rewrite find_child_index_aux_add.
          pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
          rewrite sublist_0_cons, sublist_S_cons, <- Z.add_assoc, <- Z.add_sub_assoc by omega.
          simpl.
          rewrite Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
          rewrite IHentries. reflexivity.
          intros [n'' hn'']. apply hin. exists n''. apply InA_cons_tl. assumption.
    Qed.

    Definition add_record (k: key) (e: elt) (i: Z) (entries: t elt): t elt :=
      if X.eq_dec (fst (@Znth _ (k, e) i entries)) k then
        upd_Znth i entries (k, e)
      else
        sublist 0 i entries ++ (k, e) :: sublist i (Zlength entries) entries.

    Lemma add_record_correct: forall k0 e0 entries,
        add_record k0 e0 (find_record_index k0 entries) entries = add k0 e0 entries.
    Proof.
      intros.
      unfold add_record.
      induction entries as [|[k e] entries]; unfold find_record_index.
      + cbn; destruct X.eq_dec; reflexivity.
      + simpl. destruct key_compare.
        - rewrite Znth_0_cons. simpl. rewrite if_false by order.
          rewrite sublist_same; reflexivity.
        - rewrite Znth_0_cons. simpl. rewrite if_true by order.
          rewrite upd_Znth0, sublist_1_cons, Zlength_cons, <- Z.add_1_r,
          <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_same; reflexivity.
        - rewrite find_record_index_aux_add.
          pose proof (find_record_index_bounds k0 entries) as hb.
          unfold find_record_index in hb.
          rewrite Zlength_cons, Znth_pos_cons, upd_Znth_cons, sublist_0_cons', sublist_S_cons,
            <- Z.add_1_r by omega.
          do 2 rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
          rewrite <- IHentries. destruct X.eq_dec; reflexivity.
    Qed.

    Definition update_internal (ptr0: node) (entries: t node) (new: node) (i: Z):
      node * t node :=
      if Z_lt_ge_dec i 0 then (new, entries)
      else (ptr0, upd_Znth i entries (fst (Znth i entries), new)).

    Lemma update_internal_same_keys: forall ptr0 entries new i,
        i < Zlength entries ->
        eqlistA eqk (snd (update_internal ptr0 entries new i)) entries.
    Proof.
      intros.
      unfold update_internal.
      destruct Z_lt_ge_dec. reflexivity.
      simpl. rewrite eqlistA_altdef.
      erewrite <- (upd_Znth_triv i) by (try omega; reflexivity).
      unfold upd_Znth.
      apply Forall2_app. rewrite <- eqlistA_altdef. reflexivity.
      constructor. unfold eqk. reflexivity.
      rewrite <- eqlistA_altdef. reflexivity.
    Qed.      

    Lemma update_internal_correct_ptr0: forall ptr0 entries new k0,
        HdRel key_lt k0 (List.map fst entries) ->
        update_internal ptr0 entries new (find_child_index k0 entries) = (new, entries). 
    Proof.
      intros * h.
      enough (henough: find_child_index k0 entries = -1).
      + rewrite henough. reflexivity.
      + induction entries as [|[k n] entries].
      - reflexivity.
      - unfold find_child_index. simpl.
        apply HdRel_inv in h. simpl in h.
        destruct key_compare. reflexivity. order. order.
    Qed.
    
    Lemma update_internal_correct_entries: forall ptr0 entries new k0 k1,
        Sorted ltk entries ->
        In k1 entries -> key_le k1 k0 ->
        (* k1 is the highest key that is <= k0 *)
        Forall_dom (fun k2 => key_le k2 k0 -> key_le k2 k1) entries ->
        let pair := update_internal ptr0 entries new (find_child_index k0 entries) in
        fst pair = ptr0 /\ eqlistA eqke (snd pair) (add k1 new entries). 
    Proof.
      intros * hsort hin hle hsup.
      unfold update_internal, find_child_index.
      induction entries as [|[k n] entries].
      + destruct hin as [n1 hn1]. inversion hn1.
      + destruct hin as [n1 hin%InA_cons].
        destruct hin as [[eqk eqn]|hin].
      - simpl in eqk, eqn |- *.
        destruct (key_compare k1 k); try order.
        pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
        destruct (key_compare k0 k); cbn.
        -- repeat f_equal; order. 
        -- rewrite find_child_index_aux_add.
           rewrite if_false by omega.
           pose proof (hsup k (ex_intro _ n (InA_cons_hd _ (eqke_refl _))) ltac:(order)).
           replace (find_child_index_aux k0 entries 0) with (-1).
           rewrite upd_Znth0, sublist_1_cons, Zlength_cons, sublist_same by
               (try rewrite Zlength_cons; omega).
           simpl. split. reflexivity. constructor. split; simpl. order. reflexivity.
           reflexivity.
           (* unprovable, TODO: change for sth else than Leibniz equality *)
           { apply Sorted_inv in hsort.
             destruct entries as [|[k' n'] entries].
             + reflexivity.
             + simpl.
               pose proof (HdRel_inv (proj2 hsort)) as hlt.
               unfold ltk in hlt. simpl in hlt.
               destruct key_compare. reflexivity. order. order. }                 
        -- rewrite find_child_index_aux_add, if_false by omega.
           f_equal. replace (find_child_index_aux k0 entries 0) with (-1).
           rewrite Znth_0_cons, upd_Znth0, sublist_S_cons, sublist_same by (try rewrite Zlength_cons; omega).
           simpl. split. reflexivity. constructor. split; simpl. order. reflexivity. reflexivity.
           { apply Sorted_inv in hsort.
             destruct entries as [|[k' n'] entries].
             + reflexivity.
             + simpl.
               pose proof (HdRel_inv (proj2 hsort)) as hlt.
               unfold ltk in hlt. simpl in hlt. 
               specialize (hsup k' (ex_intro _ n' (InA_cons_tl _ (InA_cons_hd _ (eqke_refl _))))).
               destruct key_compare; try reflexivity; specialize (hsup ltac:(order)); order.
           } 
      - apply Sorted_inv in hsort. apply Forall_dom_inv in hsup.
        specialize (IHentries ltac:(easy) (ex_intro _ n1 hin) ltac:(easy)).
        apply InA_eqke_eqk in hin.
        pose proof (PX.Sort_Inf_In (proj1 hsort) (proj2 hsort) hin) as hlt.
        unfold ltk in hlt. simpl in hlt.
        simpl. destruct key_compare; try order.
        rewrite find_child_index_aux_add.
        pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
        enough (find_child_index_aux k0 entries 0 <> -1).
        ++ rewrite if_false in IHentries |- * by omega. destruct key_compare; try order.
           simpl in IHentries |- *.
           split. reflexivity.
           rewrite upd_Znth_cons, Znth_pos_cons, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
           constructor. reflexivity. easy.
        ++ destruct entries as [|[k' n'] entries]. inversion hin.
           pose proof (find_child_index_bounds k0 entries) as hb'. unfold find_child_index in hb'.
           simpl in hb' |- *. destruct key_compare; try rewrite find_child_index_aux_add; try omega.
           rewrite InA_cons in hin. destruct hin as [heq | hin].
        -- unfold eqk in heq. simpl in heq. order.
        -- enough (key_lt k' k1). order.
           destruct hsort as [hsort _]. apply Sorted_inv in hsort.
           epose proof (PX.Sort_Inf_In (proj1 hsort) (proj2 hsort) hin) as hlt'.
           unfold ltk in hlt'. simpl in hlt'. order.
    Qed.
*)
    
    Function get_cursor(k0: key) (root: node)
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
        rewrite Znth_map. rewrite <- surjective_pairing. apply Znth_In. omega. omega.
      + apply (wf_guard 32), direct_subnode_wf.
    Defined.

    Notation min_fanout := (Z.of_nat Params.min_fanout).
    
    Import Sumbool.
    Arguments sumbool_and {A} {B} {C} {D}.
    
    Fixpoint insert_aux (k0: key) (e: elt) (cursor: list (Z * node)):
      node * option (key * node) :=
      match cursor with
      | (i, leaf records info) :: _ =>
        if sumbool_and (Z_lt_ge_dec i (Zlength records)) (X.eq_dec k0 (fst (Znth i records))) then
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
                                       (fst (Znth (i - 1) children), to_update) ::
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
          else (internal ptr0 (upd_Znth (i - 1) children (fst (Znth (i - 1) children), to_update)) info, None)
        end
      | [] => (default, None)
      end.

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
        apply (subnode_entry k).
        unfold last_error in h2.
        destruct (nil_dec children) as [hnil | hnil].
      - subst. discriminate.
      - apply exists_last in hnil.
        destruct hnil as (children_prefix & [last_k last_child] & heq).
        subst. rewrite map_app in h2. simpl in h2. rewrite last_snoc in h2.
        inversion h2. subst. rewrite in_app_iff.
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
        cbn in hchildren. apply (hchildren (k, n)).
        apply last_error_In; assumption. assumption.
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
        well_sorted_children m (fst (Znth i l)) (sublist 0 i l).
    Proof.
      intros i hi.
      refine (natlike_ind (fun i => forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children m (fst (Znth i l)) (sublist 0 i l)) _ _ i hi).
      + intros * hlength h.
        destruct l as [|[k n] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl in h |- *.
          easy.
      + intros j hj hrec * hlength h.
        destruct l as [|[k child] l].
        - rewrite Zlength_nil in hlength. omega.
        - rewrite Znth_pos_cons, sublist_0_cons by omega.
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
        well_sorted_children (fst (Znth i l)) M (sublist i (Zlength l) l).
    Proof.
      intros i hi.
      refine (natlike_ind (fun i => forall m M l,
        i < Zlength l ->
        well_sorted_children m M l ->
        well_sorted_children (fst (Znth i l)) M (sublist i (Zlength l) l)) _ _ i hi).
      + intros * hlength h.
        destruct l as [|[k n] l].
        - rewrite Zlength_nil in hlength. omega.
        - simpl in h |- *.
          rewrite sublist_same by reflexivity. simpl. split.
          order. easy.
      + intros j hj hrec * hlength h.
        destruct l as [|[k child] l].
        - rewrite Zlength_nil in hlength. omega.
        - rewrite Znth_pos_cons, Zlength_cons, sublist_S_cons by omega.
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
    
    Lemma In_Sorted_le {X: Type} {_: Inhabitant (key * X)}: forall (l: entries X) i k x,
        0 <= i < Zlength l ->
        Sorted key_lt (map fst l) ->
        In (k, x) (sublist 0 i l) -> key_lt k (fst (Znth i l)).
    Proof.
      induction l as [|[k' x'] l]; intros * hi hsorted hin.
      + rewrite sublist_of_nil in hin; contradiction.
      + destruct (Z.eq_dec i 0).
      - subst. rewrite sublist_nil_gen in hin by omega. contradiction. 
      - rewrite Znth_pos_cons by omega.
        rewrite sublist_0_cons in hin by omega.
        rewrite Zlength_cons in hi.
        destruct hin as [hin|hin].
        -- inversion hin. subst.
           apply Sorted_StronglySorted in hsorted. simpl in hsorted.
           apply StronglySorted_inv in hsorted.
           rewrite Forall_forall in hsorted.
           destruct hsorted as [_ hforall].
           specialize (hforall (fst (Znth (i - 1) l))).
           lapply hforall. intro h. easy.
           apply in_map. apply Znth_In. omega.
           do 3 intro. order.
        -- eapply IHl.
           omega. now inversion hsorted. eassumption.
    Qed.

    Lemma well_sorted_children_select: forall children min max,
        well_sorted_children min max children ->
        forall i, 0 <= i < Zlength children ->
        well_sorted_children min (fst (Znth i children)) (sublist 0 i children) /\
        exists min_n max_n, well_sorted min_n max_n (snd (Znth i children)) /\
                       key_le max_n max /\
                       key_lt (fst (Znth i children)) min_n /\
                       (i + 1 < Zlength children -> key_le max_n (fst (Znth (i + 1) children)) /\
                       well_sorted_children (fst (Znth (i + 1) children)) max (sublist (i + 1) (Zlength children) children)).
    Proof.
      induction children as [|[k n] children].
      + intros * hminmax i hi. cbn in hi. omega.
      + intros * hchildren i hi.
        rewrite Zlength_cons in hi.
        destruct hchildren as (hle & min_n & max_n & hlt & n_ws & children_ws).
        specialize (IHchildren _ _ children_ws).
        destruct (Z.eq_dec i 0).
      - subst. simpl. rewrite Znth_pos_cons by omega.
        simpl. split. assumption.
        exists min_n. exists max_n. split3. assumption. apply well_sorted_children_facts in children_ws. easy.
        split. assumption. destruct children as [|[k' n'] children].
        cbn; omega.
        intros _. simpl. split.
        destruct children_ws. assumption.
        rewrite sublist_1_cons, Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_same by reflexivity.
        destruct children_ws. split.
        order. assumption.
      - rewrite Znth_pos_cons, sublist_0_cons, Znth_pos_cons by omega.
        specialize (IHchildren (i - 1) ltac:(omega)).
        replace (i - 1 + 1) with i in IHchildren by omega.
        replace (i + 1 - 1) with i by omega.
        destruct IHchildren as (pref & min_ith & max_ith & ith_ws & hmax_ith & hmin_ith & hafter).
        split.
        ++ simpl. split.
           order. exists min_n. exists max_n. split3; try order; assumption.
        ++ exists min_ith. exists max_ith. split3.
           easy. easy. split. assumption. intro h. rewrite Zlength_cons in h.
           rewrite sublist_S_cons, Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, <- Z.add_sub_assoc,
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
        remember (find_index k0 records) as i.
        pose proof (find_index_bounds k0 records) as hb.
        destruct h as (records_sorted & hmM & records_bounds).
        destruct sumbool_and as [h|].
        ++ (* mere update of a record *)
          rewrite well_sorted_equation. split3.
          - rewrite upd_Znth_unfold.
            rewrite map_app, map_app, map_sublist, map_sublist, (proj2 h), <- Znth_map by omega.
            simpl. erewrite <- upd_Znth_triv, upd_Znth_unfold, Zlength_map in records_sorted.
            apply records_sorted.
            rewrite Zlength_map; omega. reflexivity.
          - eapply OrderTac.le_trans.
            apply MinMaxProps.le_min_r. apply MinMaxProps.le_max_r.
          - rewrite <- upd_Znth_map. apply Forall_upd_Znth.
            refine (Forall_impl _ _ records_bounds).
            intros k [hk1 hk2]. split.
            pose proof (MinMaxProps.le_min_l m k0). order.
            pose proof (MinMaxProps.le_max_l M k0). order.
            cbn. split. apply MinMaxProps.le_min_r. apply MinMaxProps.le_max_r.
        ++ destruct Z_gt_le_dec. 
           - (* new entry triggers split *)
             split.
           admit.
           admit.
           - (* new entry doesn't trigger split *)
             rewrite well_sorted_equation.
             admit.
      + intros * hptr0 hchildren * h%well_sorted_equation.
        rewrite get_cursor_equation.
        destruct h as (max_ptr0 & ws_ptr0 & ws_children).
        simpl.
        set (i := find_index k0 children) in *.
        pose proof (find_index_bounds k0 children) as hb_index. fold i in hb_index.
        case_eq (insert_aux k0 e (get_cursor k0 (if Z.eq_dec i 0 then ptr0 else Znth (i - 1) (List.map snd children)))).
        destruct (Z.eq_dec i 0) as [hi0|].
        ++ intros left [[new_child_key new_child_node]|] heqrec.
           - admit.
           - specialize (hptr0 k0 e _ _ ws_ptr0).
             rewrite heqrec in hptr0. clear hchildren heqrec.
             rewrite well_sorted_equation.
             exists (key_max max_ptr0 k0). split. assumption.
             unfold i in hi0. rewrite find_index_HdRel in hi0.
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
           (fst (Znth (i - 1) children), left)
           :: (new_child_key, new_child_node) :: sublist i (Zlength children) children)) in *.
            
            rewrite Forall_forall in hchildren.
            specialize (hchildren (Znth (i - 1) children) ltac:(apply Znth_In; omega)).
            simpl in hchildren.
            destruct (well_sorted_children_select _ _ _ ws_children (i - 1) ltac:(omega)) as
            (hle & min_tc & max_tc & ws_tc & hmax_tc & hmin_tc & hnext).
            replace (i - 1 + 1) with i in hnext by omega.
            specialize (hchildren k0 e _ _ ws_tc).
            rewrite Znth_map in heqrec by omega. rewrite heqrec in hchildren. clear heqrec.
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
            -- rewrite (surjective_pairing (Znth _ _)).
               split.
               --- rewrite well_sorted_equation.
                   exists max_ptr0. split.
                   { eapply well_sorted_extends. eassumption.
                     apply MinMaxProps.le_min_l. order. }
                   { eapply well_sorted_children_split1.
                     omega. omega.
                     apply new_children_wsc. }
               --- pose proof Params.min_fanout_pos.
                   pose proof (well_sorted_children_select _ _ _ new_children_wsc min_fanout ltac:(omega))
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
                     eapply well_sorted_children_extends. apply hwsc.
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
          specialize (hchildren (Znth (i - 1) children) ltac:(apply Znth_In; omega)).
          simpl in hchildren.
          destruct (well_sorted_children_select _ _ _ ws_children (i - 1) ltac:(omega)) as
              (hle & min_tc & max_tc & ws_tc & hmax_tc & hmin_tc & hnext).
          replace (i - 1 + 1) with i in hnext by omega.
          specialize (hchildren k0 e _ _ ws_tc).
          rewrite Znth_map in heqrec by omega. rewrite heqrec in hchildren. clear heqrec.
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
    Admitted.

  End ZSection.
  End Elt.
  Arguments node : clear implicits.

End Raw.

Import VST.floyd.val_lemmas.

Module MyParams <: BPlusTreeParams.
  Module InfoTyp.
    Definition t := unit.
  End InfoTyp.
  Definition min_fanout: nat := 1.
  Lemma min_fanout_pos: (min_fanout > 0)%nat. unfold min_fanout. omega. Qed.
End MyParams.

Require OrdersEx.
Module bt := Raw OrdersEx.Z_as_DT MyParams.

Section Tests.
  Check bt.insert.
  Instance Inhabitant_unit: Inhabitant unit := tt.
  Fixpoint insert_list (n: bt.node unit) (l: list Z): bt.node unit :=
    match l with
    | nil => n
    | k :: tl => insert_list (bt.insert k tt tt n) tl
    end.    
  
  (* Definition test := insert_list (leaf nil tt) (map (Z.mul 2) (conclib.upto 100)). *)
  Set Default Timeout 5.
  Definition test' := insert_list (bt.leaf nil tt) (map (compose (Z.add 1) (Z.mul 2)) (rev (conclib.upto 8))).
  Compute test'.
  Definition test1 := insert_list test' ([5; 4; 3; 2; 1; 0; -2 ;34; 2; 75; 44; 4; 2; 3; 3; 3; 3; -1; 154]).
  Compute (map fst (bt.flatten test1)).
  Compute (bt.get_cursor 5 test').
  Compute (bt.insert_aux 5 _ ([(1, bt.internal (bt.leaf [(1, tt); (3, tt)] tt) [(3, bt.leaf [(5, tt); (7, tt)] tt)] tt);
       (0, bt.leaf [(5, tt); (7, tt)] tt)])).
  Compute (bt.insert 5 _ _ test').
  Compute (bt.get_cursor 1 test1).

Compute (bt.insert_aux 5 _ (bt.get_cursor 5 test1)).
  Compute (bt.get_cursor 5 test1).
  Compute bt.insert 219 tt tt test'.

End Tests.





    Fixpoint find_path (k0: key) (root: node) {struct root}: list (Z * node) :=
      match root with
      | leaf entries info =>
        let index := (fix get_index entries index :=
                        match entries with
                        | [] => index
                        | (k, r) :: entries =>
                          if Xf.lt_dec k k0 then get_index entries (index + 1) else index
                        end) entries 0 in [(index, root)]
      | internal ptr0 (((first_k, first_n) :: _) as entries) info =>
        if Xf.lt_dec k0 first_k then (-1, root) :: find_path k0 ptr0 else
          (fix get_cursor_entry entries index :=
             match entries with
             | [] => [] (* impossible case *)
             | [(k, n)] => (index, root) :: find_path k0 n
             | (k, n) :: (((k', n') :: _) as entries) =>
               if (sumbool_and (Z_le_dec k k0) (Z_lt_ge_dec k0 k')) then (index, root) :: find_path key n
               else get_cursor_entry entries (index + 1)
             end) entries 0
      | internal ptr0 [] p => (-1, root) :: find_path k0 ptr0
      end.

    Theorem find_path_leaf: forall key entries info,
        exists i, find_path key (leaf entries info) = [(i, leaf entries info)] /\
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

Theorem find_path_internal: forall key ptr0 entries info,
    exists i, find_path key (internal ptr0 entries info) =
         (i, internal ptr0 entries info) :: find_path key (@Znth _ ptr0 i (map snd entries)) /\
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
    - generalize (internal ptr0 ((first_k, first_n) :: entries) info) as root.
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
  + pose proof (find_path_leaf key entries info) as hleaf.
    destruct hleaf as [i (heq & _)].
    rewrite heq. exists nil. reflexivity.
  + pose proof (find_path_internal key ptr0 entries info) as hinternal.
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
    edestruct (find_path_internal key ptr0 entries info) as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq.
    case_eq (@Znth _ ptr0 i (map snd entries)).
  - intros entries' info' h.
    edestruct (find_path_leaf key entries' info') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. constructor. do 2 constructor.
    constructor. simpl. rewrite <- h.
    destruct (eq_dec i (-1)) as [hm1|hm1].
    rewrite hm1. compute. constructor.
    apply subnode_entry. apply Znth_In. rewrite Zlength_map; rep_omega.
  - intros ptr0' entries' info' h.
    edestruct (find_path_internal key ptr0' entries' info') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. simpl.
    destruct (eq_dec i (-1)) as [hm1 | hm1].
    * rewrite hm1 in *. compute in h. rewrite h.
      constructor. rewrite h, heq' in hptr0.
      assumption.
      constructor. constructor.
    * constructor. rewrite Forall_forall in hentries.
      specialize (hentries (internal ptr0' entries' info')).
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
  | (i, leaf entries info) :: _ =>
    if (sumbool_and (Z_lt_ge_dec i (Zlength entries)) (eq_dec (fst (Znth i entries)) key)) then
      (leaf (upd_Znth i entries (key, rec)) info, None)
    else
      let new_entries := sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_info := nullval in
        let new_node_left := leaf (sublist 0 param new_entries) info in
        let new_node_right := leaf (sublist param (2 * param + 1) new_entries) new_info in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (leaf new_entries info, None)
  | (i, internal ptr0 entries info) :: tl =>
    let (new_at_i, entry_to_add) := insert_aux key rec tl in
    let ptr0 := if eq_dec i (-1) then new_at_i else ptr0 in
    let entries := if Z_ge_lt_dec i 0 then upd_Znth i entries (fst (Znth i entries), new_at_i) else entries in
    match entry_to_add with
    | None => (internal ptr0 entries info, None)
    | Some (new_key, new_node) =>
      let new_entries := sublist 0 (i + 1) entries ++ (new_key, new_node) :: sublist (i + 1) (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_info := nullval in
        let new_node_left := internal ptr0 (sublist 0 param new_entries) new_info in
        let new_node_right := internal (snd (Znth param new_entries))
                                       (sublist (param + 1) (2 * param + 1) new_entries) info in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (internal ptr0 new_entries info, None)
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

Lemma Sorted_bounds {X} {inh: Inhabitant X} (l: list (Z * X)): forall m M,
  Zlength l > 0 ->
  Sorted ltk l ->
  m <= fst (Znth 0 l) ->
  fst (Znth (Zlength l - 1) l) < M ->
  Forall (fun k => m <= k < M) (map fst l).
Proof.
  induction l as [|[k n] l].
  + constructor.
  + simpl. intros * hlen hsort%Sorted_inv hm hM.
    clear hlen.
    destruct l as [|[k' n'] l].
    - constructor. cbn in hM. omega.
      constructor.
    - destruct hsort as [hsort hhdrel].
      apply HdRel_inv in hhdrel. unfold ltk in hhdrel. cbn in hhdrel.
      specialize (IHl m M ltac:(rewrite Zlength_cons; rep_omega)
                 hsort ltac:(cbn; rep_omega)).
      rewrite Zlength_cons, Znth_pos_cons in hM by (rewrite Zlength_cons; rep_omega).
      unfold Z.succ in hM. rewrite Z.add_simpl_r in hM.
      specialize (IHl hM). constructor. rewrite Forall_forall in IHl.
      specialize (IHl k' ltac:(cbn; constructor; reflexivity)). 
      omega. assumption.
Qed.

Lemma Sorted_bounds_sublist {X} {inh: Inhabitant X}: forall (l: list (Z * X)) i j,
    0 <= i < j -> j < Zlength l ->
    Sorted ltk l ->
    Forall (fun k => fst (Znth i l) <= k < fst (Znth j l)) (sublist i j (map fst l)).
Proof.
  intros * hij hj hsort.
  rewrite sublist_map.
  apply Sorted_bounds.
  rewrite Zlength_sublist; omega.
  now apply Sorted_sublist.
  rewrite Znth_sublist, Z.add_0_l by omega. easy.
  rewrite Zlength_sublist, Znth_sublist by omega.
  replace (j - i - 1 + i) with (j - 1) by omega.
  assert (hj': 0 < j < Zlength l) by omega. clear hj hij.
  generalize dependent j.
  induction l. rewrite Zlength_nil; intros; rep_omega.
  intros j hj. 
  destruct (eq_dec j 1). subst. rewrite Znth_0_cons, Znth_pos_cons by omega.
  simpl. apply Sorted_inv in hsort. destruct l. cbn in hj. omega.
  cbn. destruct hsort as [_ hhd]. now inversion hhd.
  rewrite Znth_pos_cons, Znth_pos_cons by omega. apply IHl.
  now inversion hsort. rewrite Zlength_cons in hj; omega.
Qed.

Lemma good_root_node:
  forall n, good_root n ->
       num_keys n >= param ->
       exists m M, good_node m M n.
Proof.
  intros * hn hkeys.
  pose (l := flatten n).
  destruct n as [|ptr0]; cbn in hn, hkeys, l; rewrite Zlength_map in hkeys.
  + exists (fst (Znth 0 l)). exists (fst (Znth (Zlength l - 1) l) + 1).
    destruct hn as [hnsorted hnlength].
    constructor. assumption. omega.
    apply Sorted_bounds. rep_omega.
    assumption. easy. unfold l. omega.
  + destruct hn as (min_ptr0 & max_ptr0 & max & hlen & hptr0 & hentries).
    exists min_ptr0. exists max.
    econstructor. 
    omega. eassumption. assumption.
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
                 try apply Sorted_bounds_sublist; try assumption; try rep_omega.
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
             +++ apply Sorted_bounds.
                 rewrite Zlength_sublist; rep_omega.
                 apply Sorted_sublist; assumption.
                 rewrite Znth_sublist, Z.add_0_l by rep_omega. omega.
                 rewrite Forall_forall in hforall.
                 unshelve eapply (proj2 (hforall _ _)).
                 rewrite <- Znth_map by (rewrite Zlength_sublist; rep_omega). eapply sublist_In.
                 rewrite map_sublist, map_app, map_sublist, map_cons, map_sublist.
                 apply Znth_In. rewrite Zlength_sublist, Zlength_sublist;
                 try rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; try rewrite Zlength_map; rep_omega.
       ++ intros [sorted_entries Zlength_entries]. split.
          -- apply Sorted_insert; auto.
             intros h. destruct o; omega.
          -- rep_omega.
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
   - intros (min_ptr0 & max_ptr0 & max & hZlength & hptr0 & hentries).
     destruct eq_dec, Z_ge_lt_dec.
     ++ simpl.
Admitted.

Corollary insert_good: forall key rec root,
    good_root root -> good_root (insert root key rec).
Proof.
  intros * h.
  unfold insert.
  pose proof (insert_aux_good key rec root) as haux.
  case_eq (insert_aux key rec (find_path key root)); intros n [[k ri]|] heq; rewrite heq in haux.
  + assert (hnode: exists m M, good_node m M root).
    {
      apply good_root_node. assumption.
      clear -heq.
      destruct root as [|ptr0]; unfold num_keys, keys; rewrite Zlength_map.
      + edestruct find_path_leaf as (i & heqpath & hb & hbefore & hafter).
        rewrite heqpath in heq. simpl in heq. destruct sumbool_and.
        discriminate. destruct Z_gt_le_dec. omega. discriminate.
      + edestruct find_path_internal as (i & heqpath & hb & hbefore & hafter).
        rewrite heqpath in heq. simpl in heq. destruct insert_aux as [new_at_i [[]|]].
        destruct Z_gt_le_dec as [h|h]. destruct Z_ge_lt_dec.
        rewrite upd_Znth_Zlength in h; omega. omega.
        discriminate. discriminate.
    }
    destruct hnode as (m & M & hnode).
    destruct (haux _ _ hnode) as [gptr0 gri].
    simpl.
    exists (Z.min m key). exists k. exists (Z.max M key).
    split3. rewrite Zlength_cons, Zlength_nil. rep_omega.
    assumption. econstructor. eassumption. constructor. omega.
  + auto.
Qed.


Require Import VST.floyd.functional_base.
Require Import VST.progs.conclib VST.floyd.sublist.

Section Values.
  Import VST.veric.val_lemmas.
  
  Definition V: Type := {p: val | is_pointer_or_null p}.
  Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

  Instance Inhabitant_V: Inhabitant V := nullV.

  Instance EqDecV: EqDec V.
  Proof. 
    intros [x hx] [y hy]. destruct (eq_dec x y) as [heq | hneq].
    + left. now apply exist_ext.
    + right. intro hcontr. apply hneq. inversion hcontr. reflexivity.
  Qed.
End Values.

Require FMapList FMapFacts Structures.OrderedTypeEx.
Require Import Sorting.Sorted.

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
