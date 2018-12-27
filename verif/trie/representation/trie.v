(** * rep/trie.v : Formalization for representation relation of trie *)
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Require Export VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import DB.common.
Require Import DB.tactics.

(* functional part *)
Require Import DB.functional.keyslice.
Require Import DB.functional.cursored_kv.
Require Import DB.functional.bordernode.
Require Import DB.functional.trie.

Require Import DB.representation.string.
Require Import DB.representation.btree.

Require Import DB.prog.

Module KeysliceType := Z_as_OT.

Module Trie.
  Include DB.functional.trie.Trie BTree.

  Definition value := val.

  Definition tbordernode := Tstruct _BorderNode noattr. 

  Fixpoint prefix_flags (prefixes: list (option value)): Z :=
    match prefixes with
    | Some _ :: rest => (prefix_flags rest) * 2 + 1
    | None :: rest => (prefix_flags rest) * 2
    | [] => 0
    end.

  Definition addr_of_trie (t: trie value): val :=
    match t with
    | trienode_of addr _ _ =>
      addr
    end.

  Definition bordernode_rep {trie_rep: trie value -> mpred} (addr_bnode: val * bordernode value) :=
    let (addr, bnode) := addr_bnode in
    let (prefixes, suffix) := bnode in
    malloc_token Ews tbordernode addr *
    field_at Ews tbordernode [StructField _prefixFlags] (vint (prefix_flags prefixes)) addr *
    field_at Ews tbordernode [StructField _prefixLinks] (map force_val prefixes) addr *
    match suffix with
    | None =>
      field_at Ews tbordernode [StructField _suffixLink] nullval addr *
      field_at Ews tbordernode [StructField _keySuffix] nullval addr *
      field_at Ews tbordernode [StructField _keySuffixLength] (vint 0) addr
    | Some (inl (k, v)) =>
      field_at Ews tbordernode [StructField _suffixLink] v addr *
      EX pkey: val,
        field_at Ews tbordernode [StructField _keySuffix] pkey addr *
        field_at Ews tbordernode [StructField _keySuffixLength] (vint (Zlength k)) addr *
        cstring_len Ews k pkey * malloc_token Ews (tarray tschar (Zlength k)) pkey
    | Some (inr t') =>
      field_at Ews tbordernode [StructField _suffixLink] (addr_of_trie t') addr *
      field_at Ews tbordernode [StructField _keySuffix] nullval addr *
      field_at Ews tbordernode [StructField _keySuffixLength] (vint 0) addr *
      trie_rep t'
    end.

  Fixpoint trie_rep (t: trie val): mpred :=
    match t with
    | Trie.trienode_of addr tableform listform =>
      BTree.table_rep tableform addr * (* that actually at this address we store a B+ tree *)
      iter_sepcon (compose (@bordernode_rep trie_rep) snd) listform
    end.

  Definition bnode_rep := @bordernode_rep trie_rep.


  Lemma put_same_addr: forall k v c t c' t', Trie.put k v c t c' t' -> addr_of_trie t = addr_of_trie t'.
    intros.
    inv H; simplify.
  Qed.

  Lemma bnode_rep_local_facts: forall pbnode bnode,
      bnode_rep (pbnode, bnode) |-- !! isptr pbnode.
  Proof.
    intros.
    destruct bnode.
    simpl.
    entailer!.
  Qed.
  Hint Resolve bnode_rep_local_facts: saturate_local.

  Lemma bnode_rep_valid_pointer: forall pbnode bnode,
      bnode_rep (pbnode, bnode) |-- valid_pointer pbnode.
  Proof.
    intros.
    destruct bnode.
    simpl.
    entailer!.
  Qed.
  Hint Resolve bnode_rep_valid_pointer: valid_pointer.

  Lemma trie_rep_local_facts: forall t,
      trie_rep t |-- !! isptr (addr_of_trie t).
  Proof.
    intros.
    destruct t.
    simpl.
    entailer!.
  Qed.
  Hint Resolve trie_rep_local_facts: saturate_local.

  Lemma trie_rep_valid_pointer: forall t,
      trie_rep t |-- valid_pointer (addr_of_trie t).
  Proof.
    intros.
    destruct t.
    simpl.
    normalize.
    sep_apply (BTree.table_rep_valid_pointer t v).
    entailer!.
  Qed.
  Hint Resolve trie_rep_valid_pointer: valid_pointer.

  Definition ttrie: type := BTree.tindex.
  Definition tindex: type := Tstruct _Trie_T noattr.

  (* TODO: the size field is not yet implemented *)
  Definition table_rep (t: trie value) (p: val): mpred :=
    trie_rep t *
    data_at Ews tindex ((addr_of_trie t), Vundef) p.

  Definition tcursor: type := Tstruct _Cursor_T noattr.
  Definition tcursor_slice: type := Tstruct _CursorSlice_T noattr.

  Definition cursor_slice_rep (slice: trie val * @BTree.cursor val * bordernode value * BorderNode.cursor) (concrete_slice: val * (val * val)): mpred :=
    match concrete_slice with
    | (pnode, (pnode_cursor, vbnode_cursor)) =>
      match slice with
      | (t, node_cursor, _, bnode_cursor) =>
        !! (addr_of_trie t = pnode) &&
        !! (vbnode_cursor = Vint (Int.repr (BorderNode.cursor_to_int bnode_cursor))) &&
           BTree.cursor_rep node_cursor pnode_cursor
      end
    end.

  Definition cursor_rep (c: cursor val) (p: val): mpred :=
    EX capacity: Z, EX p': val, EX lc: list (val * (val * val)),
      !! (capacity >= Zlength c) &&
      data_at Ews tcursor (Vint (Int.repr capacity), (Vint (Int.repr (Zlength c)), p')) p *
      malloc_token Ews tcursor p *
      data_at Ews (tarray tcursor_slice capacity) (lc ++ list_repeat (Z.to_nat (capacity - (Zlength c))) (Vundef, (Vundef, Vundef))) p' *
      malloc_token Ews (tarray tcursor_slice capacity) p' *
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

  (* Instance inhabitant_trie_value: Inhabitant (keyslice * (val * (@BorderNode.table (@link val)))). *)
  (* Proof. *)
  (*   refine (_, (_, _)). *)
  (*   - apply 0. *)
  (*   - apply nullval. *)
  (*   - apply ([], None, nil). *)
  (* Defined. *)

  Lemma Forall_get_value {value: Type} P: forall addr c tableform listform,
      trie_correct (value := value) (trienode_of addr tableform listform) ->
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
      trie_correct (value := value) (trienode_of addr tableform listform) ->
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
