Require Import VST.floyd.functional_base.
Require Import common.

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

  Module BorderNodeValue <: VALUE_TYPE.
    Definition type := link.
    Definition default := nil.
    Definition inhabitant_value := nil.
  End BorderNodeValue.
  Module BorderNode := BorderNode BorderNodeValue.

  Module KeysliceType <: ORD_KEY_TYPE.
    Definition type := keyslice.
    Definition le := Z.le.
    Definition le_dec := Z_le_dec.
    Definition le_antisym := Z.le_antisymm.
    Definition le_refl := Z.le_refl.
    Definition le_trans := Z.le_trans.
    Lemma gt_le: forall (x y: type),  ~ (le y x) -> le x y.
    Proof.
      intros.
      change (~ le y x) with (~ y <= x) in H.
      change (le x y) with (x <= y).
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

  Inductive sorted_trie: trie -> Prop :=
  | trienode_sorted:
      forall trienode,
        SortedListStore.sorted trienode ->
        Forall (fun binding => sorted_bordernode (snd binding)) trienode ->
        sorted_trie (trienode_of trienode)
  with
  sorted_bordernode: BorderNode.store -> Prop :=
  | bordernode_sorted:
      forall prefixes k v,
        Forall (sorted_link) prefixes ->
        sorted_link v ->
        sorted_bordernode (prefixes, k, v)
  with
  sorted_link: link -> Prop :=
  | value_sorted: forall v, sorted_link (value_of v)
  | trie_sorted: forall t, sorted_trie t -> sorted_link (trie_of t)
  | nil_sorted: sorted_link nil.
  
  Definition empty: trie := trienode_of [].

  Lemma empty_sorted: sorted_trie empty.
  Proof.
    constructor; auto with sortedstore.
  Qed.

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
          if BorderNode.is_suffix bordernode then
            match BorderNode.get_suffix (Some (get_suffix k)) bordernode with
            | value_of v => Some v
            | trie_of _ => None
            | nil => None
            end
          else
            match BorderNode.get_suffix None bordernode with
            | value_of _ => None
            | trie_of t' => get (get_suffix k) t'
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
          if BorderNode.is_suffix bordernode then
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
                                          (Some (get_suffix k)) (
                                            trie_of (create_pair (get_suffix k) (get_suffix k') (value_of v) v')
                                          ) bordernode
                                      ) trienode
                )
              | (None, v') =>
                empty
              end
          else
            match BorderNode.get_suffix None bordernode with
            | value_of _ => empty
            | trie_of t' =>
              (* pass down to next layer *)
              trienode_of (
                  SortedListStore.put keyslice (
                                        BorderNode.put_suffix (Some (get_suffix k)) (
                                                                trie_of (put (get_suffix k) v t')
                                                              ) bordernode
                                      ) trienode
                )
            | nil => empty
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
End Trie.
