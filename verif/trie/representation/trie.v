(** * rep/trie.v : Formalization for representation relation of trie *)
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Require Export VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import DB.common.

(* functional part *)
Require Import DB.functional.keyslice.
Require Import DB.functional.cursored_kv.
Require Import DB.functional.bordernode.
Require Import DB.functional.trie.

Require Import DB.representation.string.
Require Import DB.representation.bordernode.
Require Import DB.representation.btree.

Require Import DB.prog.

Module KeysliceType := Z_as_OT.

Module Trie.
  Include DB.functional.trie.Trie BTree.

  Definition link_to_val(l: @Trie.link val): val :=
    match l with
    | Trie.value_of v => v
    | Trie.trie_of _ => Vundef (* this constructor is not intended to be dealt with this function *)
    | Trie.nil => nullval
    end.

  Definition bnode_rep trie_rep (addr_bnode: val * @BorderNode.table (@Trie.link val)) :=
    match addr_bnode with
    | (addr, (prefixes, suffix_key, suffix_value)) =>
      (* prefixes *)
      !! (Forall is_pointer_or_null (map link_to_val prefixes)) &&
      field_at Tsh tbordernode [StructField _prefixLinks] (map link_to_val prefixes) addr *
      (* suffix key *)
      match suffix_key with
      | Some k =>
        EX p': val,
          field_at Tsh tbordernode [StructField _keySuffix] p' addr *
          field_at Tsh tbordernode [StructField _keySuffixLength] (Vint (Int.repr (Zlength k))) addr *
          cstring_len Tsh k p' *
          malloc_token Tsh (tarray tschar (Zlength k)) p'
      | None =>
        field_at Tsh tbordernode [StructField _keySuffix] nullval addr *
        field_at Tsh tbordernode [StructField _keySuffixLength] (Vint Int.zero) addr
      end *
      (* suffix value *)
      match suffix_value with
      | Trie.trie_of t' =>
        EX p': val,
          !! (is_pointer_or_null p') &&
          trie_rep t' p' * field_at Tsh tbordernode [StructField _suffixLink] p' addr
      | _ =>
        !! (is_pointer_or_null (link_to_val suffix_value)) &&
        field_at Tsh tbordernode [StructField _suffixLink] (link_to_val suffix_value) addr
      end *
      (* malloc *)
      malloc_token Tsh tbordernode addr
    end.

  Definition translate_bnode (bnode: @BorderNode.table (@link val)) (p': val): @BorderNode.table val :=
    match bnode with
    | (prefixes, suffix_key, trie_of _) =>
      (map link_to_val prefixes, suffix_key, p')
    | (prefixes, suffix_key, value_of v) =>
      (map link_to_val prefixes, suffix_key, v)
    | (prefixes, suffix_key, nil) =>
      (map link_to_val prefixes, suffix_key, nullval)
    end.

  Lemma translate_bnode_subtrie: forall table_rep addr prefixes suffix_key t',
      bnode_rep table_rep (addr, (prefixes, suffix_key, trie_of t')) =
      EX p': val,
        bordernode_rep Tsh (translate_bnode (prefixes, suffix_key, trie_of t') p') addr *
        malloc_token Tsh tbordernode addr *
        table_rep t' p'.
  Proof.
    intros.
    unfold bnode_rep, bordernode_rep.
    apply pred_ext.
    - Intros p'.
      Exists p'.
      simpl.
      entailer!.
    - Intros p'.
      Exists p'.
      simpl.
      entailer!.
  Qed.

  Lemma translate_bnode_value: forall table_rep addr prefixes suffix_key v auxp,
      bnode_rep table_rep (addr, (prefixes, suffix_key, value_of v)) =
      bordernode_rep Tsh (translate_bnode (prefixes, suffix_key, value_of v) auxp) addr *
      malloc_token Tsh tbordernode addr.
  Proof.
    intros.
    unfold bnode_rep, bordernode_rep.
    apply pred_ext.
    - simpl.
      entailer!.
    - simpl.
      entailer!.
  Qed.

  Lemma translate_bnode_nil: forall table_rep addr prefixes suffix_key auxp,
      bnode_rep table_rep (addr, (prefixes, suffix_key, nil)) =
      bordernode_rep Tsh (translate_bnode (prefixes, suffix_key, nil) auxp) addr *
      malloc_token Tsh tbordernode addr.
  Proof.
    intros.
    unfold bnode_rep, bordernode_rep.
    apply pred_ext.
    - simpl.
      entailer!.
    - simpl.
      entailer!.
  Qed.

  Definition key_inrange (k: Z): Prop :=
    0 <= k <= Ptrofs.max_unsigned.

  Fixpoint trie_rep (t: @Trie.table val) (p: val) {struct t}: mpred :=
    match t with
    | Trie.trienode_of addr tableform listform =>
      !! (addr = p) &&
      BTree.table_rep tableform p *
      iter_sepcon (compose (bnode_rep trie_rep) snd) listform &&
      !! (Forall (compose key_inrange fst) listform)
    end.

  Lemma trie_rep_local_facts: forall t pt,
      trie_rep t pt |-- !! isptr pt.
  Proof.
    intros.
    destruct t.
    simpl.
    entailer!.
  Qed.
  Hint Resolve trie_rep_local_facts: saturate_local.

  Lemma trie_rep_valid_pointer: forall t pt,
      trie_rep t pt |-- valid_pointer pt.
  Proof.
    intros.
    destruct t.
    simpl.
    normalize.
    sep_apply (BTree.table_rep_valid_pointer t pt).
    entailer!.
  Qed.

  Definition ttrie: type := BTree.tindex.
  Definition tindex: type := Tstruct _Trie_T noattr.


  (* TODO: the size field is not yet implemented *)
  Definition table_rep (t: trie) (p: val): mpred :=
    EX pt: val,
      trie_rep t pt *
      data_at Tsh tindex (pt, Vundef) p.

  Definition tcursor: type := Tstruct _Cursor_T noattr.
  Definition tcursor_slice: type := Tstruct _CursorSlice_T noattr.

  Definition cursor_slice_rep (slice: @Trie.table val * @BTree.cursor val * @BorderNode.table (@Trie.link val) * BorderNode.cursor) (concrete_cursor: val * (val * val)): mpred :=
    match concrete_cursor with
    | (pnode, (pnode_cursor, vbnode_cursor)) =>
      match slice with
      | (trienode_of addr _ _, node_cursor, _, bnode_cursor) =>
        !! (addr = pnode) &&
        !! (vbnode_cursor = Vint (Int.repr (BorderNode.cursor_to_int bnode_cursor))) &&
           BTree.cursor_rep node_cursor pnode_cursor
      end
    end.

  Definition cursor_rep (c: @Trie.cursor val) (p: val): mpred :=
    EX capacity: Z, EX p': val, EX lc: list (val * (val * val)),
      !! (capacity >= Zlength c) &&
      data_at Tsh tcursor (Vint (Int.repr capacity), (Vint (Int.repr (Zlength c)), p')) p *
      malloc_token Tsh tcursor p *
      data_at Tsh (tarray tcursor_slice capacity) (lc ++ list_repeat (Z.to_nat (capacity - (Zlength c))) (Vundef, (Vundef, Vundef))) p' *
      malloc_token Tsh (tarray tcursor_slice capacity) p' *
      iter_sepcon2 cursor_slice_rep c lc.

  Lemma btree_cursor_cursor_slice: forall addr listform tableform node_cursor bnode bnode_cursor pnode_cursor pbnode_cursor,
      pbnode_cursor = Vint (Int.repr (BorderNode.cursor_to_int bnode_cursor)) ->
      BTree.cursor_rep node_cursor pnode_cursor |--
                       cursor_slice_rep (trienode_of addr listform tableform, node_cursor, bnode, bnode_cursor) (addr, (pnode_cursor, pbnode_cursor)).
  Proof.
    intros.
    unfold cursor_slice_rep.
    entailer!.
  Qed.

  Ltac make_cursor_slice addr listform tableform bnode bnode_cursor pbnode_cursor :=
    match goal with
    | [ |- context[BTree.cursor_rep ?node_cursor ?pnode_cursor]] =>
      sep_apply (btree_cursor_cursor_slice addr listform tableform node_cursor bnode bnode_cursor pnode_cursor pbnode_cursor ltac:(auto))
    end.

  Instance inhabitant_trie_value: Inhabitant (keyslice * (val * (@BorderNode.table (@link val)))).
  Proof.
    refine (_, (_, _)).
    - apply 0.
    - apply nullval.
    - apply ([], None, nil).
  Defined.

  Lemma Forall_get_value {value: Type} P: forall addr c tableform listform,
      table_correct (value := value) (trienode_of addr tableform listform) ->
      Forall (P oo fst oo snd) listform ->
      BTree.abs_rel c tableform ->
      match (BTree.get_value c tableform) with
      | Some v => P v
      | None => True
      end.
  Proof.
    intros.
    inv H.
    pose proof (BTree.flatten_invariant tableform H5) as [? ?].
    unfold BTree.get_value.
    destruct (BTree.get c tableform) as [[] | ] eqn:Heqn; [ | auto].
    assert (BTree.get_key c tableform = Some k) by (unfold BTree.get_key; rewrite Heqn; reflexivity).
    pose proof (BTree.get_key_rel tableform _ _ H1 H3).
    specialize (H2 k c (BTree.Flattened.make_cursor k (BTree.flatten tableform))).
    specialize (H2 H4 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
    specialize (H2 H1 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
    rewrite H2 in Heqn.
    apply BTree.Flattened.get_in_weak in Heqn.
    apply in_map with (f := snd) in Heqn.
    simpl in Heqn.
    rewrite H8 in Heqn.
    apply Forall_map in H0.
    rewrite Forall_forall in H0.
    apply H0 in Heqn.
    assumption.
  Qed.

  Lemma Forall_get_key {value: Type} P: forall addr c tableform listform,
      table_correct (value := value) (trienode_of addr tableform listform) ->
      Forall (P oo fst) listform ->
      BTree.abs_rel c tableform ->
      match (BTree.get_key c tableform) with
      | Some k => P k
      | None => True
      end.
  Proof.
    intros.
    inv H.
    pose proof (BTree.flatten_invariant tableform H5) as [? ?].
    destruct (BTree.get_key c tableform) eqn:Heqn; [ | auto].
    pose proof (BTree.get_key_rel tableform _ _ H1 Heqn).
    specialize (H2 k c (BTree.Flattened.make_cursor k (BTree.flatten tableform))).
    specialize (H2 H3 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
    specialize (H2 H1 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
    unfold BTree.get_key in Heqn.
    rewrite H2 in Heqn.
    destruct (BTree.Flattened.get (BTree.Flattened.make_cursor k (BTree.flatten tableform)) (BTree.flatten tableform)) as [ [] | ] eqn:Heqn'; try congruence.
    inv Heqn.
    apply BTree.Flattened.get_in_weak in Heqn'.
    apply in_map with (f := fst) in Heqn'.
    simpl in Heqn'.
    rewrite H7 in Heqn'.
    apply Forall_map in H0.
    rewrite Forall_forall in H0.
    apply H0 in Heqn'.
    assumption.
  Qed.
End Trie.
