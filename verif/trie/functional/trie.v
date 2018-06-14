Require Import VST.floyd.functional_base.
Require Import common.
Require Import DB.lemmas.

Require Import DB.functional.kv.
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.

Import Lists.List.ListNotations.

Module TrieKey <: KEY_TYPE.
  Definition type: Type := string.
End TrieKey.

Module Trie.
  Definition key: Type := TrieKey.type.
  Variable value: Type.

  Inductive trie: Type :=
  | trienode_of: list (keyslice * (list link * option string * link)) -> trie
  with
  link: Type :=
  | value_of: value -> link
  | trie_of: trie -> link
  | nil: link.
  Hint Constructors trie: trie.

  Module BorderNodeValue <: VALUE_TYPE.
    Definition type := link.
    Definition default := nil.
    Definition inhabitant_value := nil.
  End BorderNodeValue.
  Module BorderNode := BorderNode BorderNodeValue.

  Module KeysliceType <: ORD_KEY_TYPE.
    Definition type := keyslice.
    Definition lt := Z.lt.
    Definition lt_dec := Z_lt_dec.
    Definition lt_trans := Z.lt_trans.
    Definition lt_neq: forall x y: type, lt x y -> x <> y.
    Proof.
      intros.
      change (lt x y) with (x < y) in H.
      omega.
    Qed.
    Definition ge_neq_lt: forall x y: type, ~ lt y x -> x <> y -> lt x y.
    Proof.
      intros.
      apply Znot_lt_ge in H.
      change (lt x y) with (x < y).
      omega.
    Qed.
    Definition EqDec: EqDec type := Z.eq_dec.
  End KeysliceType.

  Module TrieNodeValue <: VALUE_TYPE.
    Definition type := BorderNode.store.
    Definition default := BorderNode.empty.
    Definition inhabitant_value := BorderNode.empty.
  End TrieNodeValue.

  Module SortedListStore := SortedListStore KeysliceType TrieNodeValue.

  Inductive trie_invariant: trie -> Prop :=
  | invariant_trienode:
      forall trienode,
        SortedListStore.sorted trienode ->
        Forall (fun binding => bordernode_invariant (snd binding)) trienode ->
        trie_invariant (trienode_of trienode)
  with
  bordernode_invariant: BorderNode.store -> Prop :=
  | invariant_bordernode:
      forall prefixes (k: option string) v,
        Zlength prefixes = keyslice_length ->
        Forall (fun l =>
                  link_invariant l /\
                  match l with
                  | value_of _ => True
                  | trie_of _ => False
                  | nil => True
                  end
               ) prefixes ->
        (link_invariant v /\
         if k then
           match v with
           | value_of _ => True
           | trie_of _ => False
           | nil => True
           end
         else
           match v with
           | value_of _ => False
           | trie_of _ => True
           | nil => True
           end) ->
        bordernode_invariant (prefixes, k, v)
  with
  link_invariant: link -> Prop :=
  | invariant_value: forall v, link_invariant (value_of v)
  | invariant_trie: forall t, trie_invariant t -> link_invariant (trie_of t)
  | invariant_nil: link_invariant nil.
  Hint Constructors trie_invariant: trie.
  Hint Constructors bordernode_invariant: trie.
  Hint Constructors link_invariant: trie.
  
  Definition empty: trie := trienode_of [].

  Lemma empty_invariant: trie_invariant empty.
  Proof.
    constructor; auto with sortedstore.
  Qed.
  Hint Resolve empty_invariant: trie.

  (* Fixpoint trie_height (t: trie): nat := *)
  (*   match t with *)
  (*   | trienode_of trienode => *)
  (*     S (fold_right (fun binding => Nat.max (link_height (snd (snd binding)))) 0%nat trienode) *)
  (*   end *)
  (* with *)
  (* link_height (l: link): nat := *)
  (*   match l with *)
  (*   | value_of _ => 0 *)
  (*   | trie_of t' => trie_height t' *)
  (*   | nil => 0 *)
  (*   end. *)

  (* Lemma max_in_le {A: Type}: forall (f: A -> nat) (l: list A) (e: A), *)
  (*     In e l -> *)
  (*     (f e <= fold_right (fun e' => Nat.max (f e')) 0 l)%nat. *)
  (* Proof. *)
  (*   intros. *)
  (*   induction l. *)
  (*   - inversion H. *)
  (*   - simpl. *)
  (*     inversion H; subst; clear H. *)
  (*     + apply Nat.le_max_l. *)
  (*     + specialize (IHl H0). *)
  (*       apply Nat.max_le_iff. *)
  (*       right. *)
  (*       assumption. *)
  (* Qed. *)

  Function get (k: key) (t: trie) {measure length k}: option value :=
    let keyslice := get_keyslice k in 
    match t with
    | trienode_of trienode =>
      match SortedListStore.get keyslice trienode with
      | Some bordernode =>
        if Z_le_dec (Zlength k) keyslice_length then
          match BorderNode.get_prefix (Zlength k) bordernode with
          | value_of v => Some v
          | trie_of _ => None
          | nil => None
          end
        else
          if BorderNode.is_link bordernode then
            match BorderNode.get_suffix None bordernode with
            | value_of _ => None
            | trie_of t' => get (get_suffix k) t'
            | nil => None
            end
          else
            match BorderNode.get_suffix (Some (get_suffix k)) bordernode with
            | value_of v => Some v
            | trie_of _ => None
            | nil => None
            end
      | None =>
        None
      end
    end.
  Proof.
    intros.
    unfold get_suffix.
    rewrite Nat2Z.inj_lt.
    rewrite <- ?Zlength_correct.
    assert (Zlength k > keyslice_length) by (apply Znot_le_gt; assumption).
    rewrite Zlength_sublist by rep_omega.
    rep_omega.
  Defined.

  Definition create_pair_aux_dec {A: Type}: forall k1 k2: list A,
      {Zlength k1 <= keyslice_length \/ Zlength k2 <= keyslice_length} +
      {Zlength k1 > keyslice_length /\ Zlength k2 > keyslice_length}.
  Proof.
    intros.
    destruct (Z_le_gt_dec (Zlength k1) keyslice_length);
      destruct (Z_le_gt_dec (Zlength k2) keyslice_length);
        match goal with
        | [H: _ <= _ |- _] => left; omega
        | _ => right; omega
        end.
  Qed.

  Function create_pair (k1 k2: key) (v1 v2: link) {measure length k1} : trie :=
    let keyslice1 := get_keyslice k1 in
    let keyslice2 := get_keyslice k2 in
    if eq_dec keyslice1 keyslice2 then
      if create_pair_aux_dec k1 k2 then
        let tmp := BorderNode.put_value k1 v1 BorderNode.empty
        in trienode_of (
               SortedListStore.put keyslice2 (
                                     BorderNode.put_value k1 v2 tmp
                                   ) SortedListStore.empty
             )
      else
        trienode_of (
            SortedListStore.put keyslice1 (
                                  BorderNode.put_value k1 (
                                                         trie_of (create_pair (get_suffix k1) (get_suffix k2) v1 v2)
                                                       ) BorderNode.empty
                                ) SortedListStore.empty
          )
    else
      let tmp := SortedListStore.put keyslice1 (
                                       BorderNode.put_value k1 v1 BorderNode.empty
                                     ) SortedListStore.empty
      in trienode_of (
             SortedListStore.put keyslice2 (
                                   BorderNode.put_value k1 v2 BorderNode.empty
                                 ) tmp
           ).
  Proof.
    intros.
    intros.
    unfold get_suffix.
    rewrite Nat2Z.inj_lt.
    rewrite <- ?Zlength_correct.
    destruct anonymous0.
    rewrite Zlength_sublist; repeat first [split | rep_omega | omega].
  Defined.

  Function put (k: key) (v: value) (t: trie) {measure length k}: trie :=
    let keyslice := get_keyslice k in
    match t with
    | trienode_of trienode =>
      match SortedListStore.get keyslice trienode with
      | Some bordernode =>
        if Z_le_dec (Zlength k) (keyslice_length) then
          (* overwrite prefix *)
          trienode_of (
              SortedListStore.put keyslice (
                                    BorderNode.put_prefix (Zlength k) (value_of v) bordernode
                                  ) trienode
            )
        else
          if BorderNode.is_link bordernode then
            match BorderNode.get_suffix None bordernode with
            | value_of _ => empty
            | trie_of t' =>
              (* pass down to next layer *)
              trienode_of (
                  SortedListStore.put keyslice (
                                        BorderNode.put_suffix (None) (
                                                                trie_of (put (get_suffix k) v t')
                                                              ) bordernode
                                      ) trienode
                )
            | nil => empty
            end
          else
            if BorderNode.test_suffix (Some (get_suffix k)) bordernode then
              (* overwrite suffix *)
              trienode_of (
                  SortedListStore.put keyslice (
                                        BorderNode.put_suffix (Some (get_suffix k)) (value_of v) bordernode
                                      ) trienode
                )
            else
              (* new layer *)
              match BorderNode.get_suffix_pair bordernode with
              | (Some k', v') =>
                trienode_of (
                  SortedListStore.put keyslice (
                                        BorderNode.put_suffix
                                          None (
                                            trie_of (create_pair (get_suffix k) (get_suffix k') (value_of v) v')
                                          ) bordernode
                                      ) trienode
                )
              | (None, v') =>
                empty
              end
      | None =>
        (* new btree kv pair *)
        trienode_of (
            SortedListStore.put keyslice (
                                  BorderNode.put_value k (value_of v) BorderNode.empty
                                ) trienode
          )
      end
    end.
  Proof.
    intros.
    intros.
    unfold get_suffix.
    rewrite Nat2Z.inj_lt.
    rewrite <- ?Zlength_correct.
    assert (Zlength k > keyslice_length) by (apply Znot_le_gt; assumption).
    rewrite Zlength_sublist by rep_omega.
    rep_omega.
  Defined.

  Lemma create_pair_invariant: forall k1 k2 v1 v2,
      trie_invariant (create_pair k1 k2 v1 v2).


  Theorem put_invariant: forall k v t,
      Zlength k > 0 -> trie_invariant t -> trie_invariant (put k v t).
  Proof.
    intros.
    remember (Zlength k) as len.
    assert (Zlength k > 0) by omega.
    generalize H1.
    generalize Heqlen.
    generalize k.
    generalize dependent t.
    assert (1 <= len) by omega.
    generalize H0.
    clear k Heqlen H H1 H0.
    apply (Z_induction (fun len' => forall t, trie_invariant t -> forall k, len' = Zlength k -> Zlength k > 0 -> trie_invariant (put k v t)) 1 len).
    { intros ? H0 ? ? Hbound.
      destruct t.
      rewrite put_equation.
      remember (get_keyslice k) as keyslice.
      remember (SortedListStore.get keyslice l) as btree_result.
      destruct btree_result; repeat if_tac; try rep_omega.
      - inv H0.
        constructor.
        + auto with sortedstore.
        + apply SortedListStore.put_Prop; [ | assumption].
          symmetry in Heqbtree_result.
          apply SortedListStore.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H4.
          apply H4 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          constructor; [rewrite upd_Znth_Zlength; rep_omega | | assumption].
          apply Forall_upd_Znth.
          * rep_omega.
          * assumption.
          * auto with trie.
      - inv H0.
        constructor.
        + auto with sortedstore.
        + apply SortedListStore.put_Prop; [ | assumption].
          unfold BorderNode.put_value.
          rewrite if_true by rep_omega.
          constructor.
          * rewrite upd_Znth_Zlength; rewrite Zlength_list_repeat; rep_omega.
          * apply Forall_upd_Znth; [rewrite Zlength_list_repeat; rep_omega | | auto with trie].
            apply Forall_forall.
            intros.
            apply in_list_repeat in H0.
            subst.
            change BorderNode.default_val with nil.
            auto with trie.
          * change BorderNode.default_val with nil.
            auto with trie.
    }
    {
      intros ? Hinduction ? H0 ? ? Hbound.
      destruct t.
      rewrite put_equation.
      remember (get_keyslice k) as keyslice.
      remember (SortedListStore.get keyslice l) as btree_result.
      destruct btree_result; repeat if_tac.
      - inv H0.
        constructor.
        + auto with sortedstore.
        + apply SortedListStore.put_Prop; [ | assumption].
          symmetry in Heqbtree_result.
          apply SortedListStore.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H4.
          apply H4 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          constructor; [rewrite upd_Znth_Zlength; rep_omega | | assumption].
          apply Forall_upd_Znth.
          * rep_omega.
          * assumption.
          * auto with trie.
      - remember (BorderNode.get_suffix None v0) as link.
        destruct link; auto with trie.
        inv H0.
        constructor; [ auto with sortedstore | ].
        apply SortedListStore.put_Prop; [ | assumption].
        symmetry in Heqbtree_result.
        apply SortedListStore.get_in in Heqbtree_result; [ | assumption].
        rewrite Forall_forall in H5.
        apply H5 in Heqbtree_result.
        simpl in Heqbtree_result.
        inv Heqbtree_result.
        constructor; [rep_omega | assumption | ].
        split; auto.
        constructor.
        simpl in Heqlink.
        rewrite if_true in Heqlink by auto.
        rewrite <- Heqlink in *.
        destruct H3 as [? _].
        inv H3.
        apply Hinduction with (Zlength (get_suffix k)).
        + unfold get_suffix.
          rewrite Zlength_sublist by rep_omega.
          rep_omega.
        + assumption.
        + reflexivity.
        + unfold get_suffix.
          rewrite Zlength_sublist by rep_omega.
          rep_omega.
      - inv H0.
        constructor; [ auto with sortedstore | ].
        apply SortedListStore.put_Prop; [ | assumption].
        symmetry in Heqbtree_result.
        apply SortedListStore.get_in in Heqbtree_result; [ | assumption].
        rewrite Forall_forall in H6.
        apply H6 in Heqbtree_result.
        simpl in Heqbtree_result.
        inv Heqbtree_result.
        constructor; [omega | assumption | auto with trie ].
      - inv H0.
        destruct v0 as [[? []]]; [ | contradiction].
        simpl in *.
        assert (get_suffix k <> s) by (intro; apply H3; f_equal; assumption).
        clear H3.
        constructor; [ auto with sortedstore | ].
        apply SortedListStore.put_Prop; [ | assumption].
        symmetry in Heqbtree_result.
        apply SortedListStore.get_in in Heqbtree_result; [ | assumption].
        rewrite Forall_forall in H6.
        apply H6 in Heqbtree_result.
        simpl in Heqbtree_result.
        inv Heqbtree_result.
        constructor; [ omega | assumption | ].
        split; auto.
        constructor.
      - inv H0.
        constructor; [ auto with sortedstore | ].
        apply SortedListStore.put_Prop; [ | assumption].
        unfold BorderNode.put_value.
        if_tac.
        + constructor.
          * rewrite upd_Znth_Zlength; rewrite Zlength_list_repeat; rep_omega.
          * apply Forall_upd_Znth; [rewrite Zlength_list_repeat; rep_omega | | auto with trie].
            apply Forall_forall.
            intros.
            apply in_list_repeat in H0.
            subst.
            change BorderNode.default_val with nil.
            auto with trie.
          * change BorderNode.default_val with nil.
            auto with trie.
        + constructor.
          * rewrite Zlength_list_repeat; rep_omega.
          * apply Forall_forall.
            intros.
            apply in_list_repeat in H0.
            subst.
            change BorderNode.default_val with nil.
            auto with trie.
          * auto with trie.
    }
  Admitted. 
End Trie.
