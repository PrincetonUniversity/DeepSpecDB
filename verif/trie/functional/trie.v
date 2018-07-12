Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import VST.floyd.functional_base.
Require Import common.
Require Import DB.lemmas.

Require Import DB.functional.kv.
Require Import DB.functional.cursored_kv.
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.

Import Lists.List.ListNotations.

Module TrieKey <: UsualOrderedType.
  Definition t: Type := string.
  Definition eq := @eq t.
  Definition lt: t -> t -> Prop. Admitted.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End TrieKey.

Module KeysliceType := Z_as_OT.

(* On going rewrite:
 * 1. support cursor
 * 2. add addresses into the data type.
 *)

Module Trie (Node: FLATTENABLE_TABLE KeysliceType) <: FLATTENABLE_TABLE TrieKey.
  Definition key := TrieKey.t.

  Module Flattened := SortedListTable TrieKey.
  Module TrieKeyFacts := OrderedTypeFacts TrieKey.

  Section Types.
    Context {value: Type}.
    (* Notes: reason for removing the [val] from the constructor:
     *        originally the kvstore contains a cursor for it, therefore there is necessity for another struct,
     *        it's not the case in final impl, and therefore we directly use the btree as pointer to a trienode *)
    Inductive trie: Type :=
    | trienode_of: Node.table val -> (* The btree data *)
                   Node.Flattened.table (@BorderNode.table link) -> (* abstract data *)
                   trie
    with
    link: Type :=
    | value_of: value -> link
    | trie_of: trie -> link
    | nil: link.
    Definition table: Type := trie.
    Hint Constructors trie: trie.
    (* order of bordernode? *)
    (* first the prefixes, then the suffix? *)
    (* Placement of cursor:
     * For keys that already existed in the store, just place at the place
     * For keys that are not in the store, place them at the furtherest bordernode entry *)

    Inductive bordernode_cursor: Type :=
    | before_prefix: Z -> bordernode_cursor
    | before_suffix: bordernode_cursor
    | after_suffix: bordernode_cursor.

    Definition cursor: Type := list (trie * Node.cursor val * (@BorderNode.table link) * bordernode_cursor).
    Definition allocator: Type := list val.

    Definition consume (a: allocator) := (hd default a, tl a).

    Definition empty (a: allocator) :=
      let (empty_table, a) := Node.empty a in
      (trienode_of empty_table [], a).

    Instance inh_link: Inhabitant link := nil.
    Instance dft_link: DefaultValue link := nil.

    Fixpoint flatten_aux (prefix: string) (t: trie) {struct t}: Flattened.table value :=
      let flatten_link :=
        fun (prefix: string) (l: link) =>
          match l with
          | value_of v => [(prefix, v)]
          | trie_of t => flatten_aux prefix t
          | nil => []
          end
      in
        let flatten_prefix_array (prefix: string) (keyslice: KeysliceType.t) :=
            fix flatten_prefix_array (prefixes: list link) (idx: Z) :=
            match prefixes with
            | h :: t =>
              flatten_link (prefix ++ (reconstruct_keyslice (keyslice, idx))) h ++ flatten_prefix_array t (idx + 1)
            | [] => []
            end
      in
      let flatten_bordernode :=
          fun (prefix: string) (kv: KeysliceType.t * @BorderNode.table link) =>
          let (keyslice, bnode) := kv in
          match bnode with
          | (prefixes, Some suffix, l) =>
            flatten_prefix_array prefix keyslice prefixes 1 ++ flatten_link (prefix ++ suffix) l
          | (prefixes, None, v) =>
            flatten_prefix_array prefix keyslice prefixes 1 ++ flatten_link prefix v
          end
      in
      match t with
      (* the tableform is of no interest here *)
      | trienode_of _ listform =>
        flat_map (flatten_bordernode prefix) listform
      end.

    Definition flatten (t: trie): Flattened.table value := flatten_aux [] t.

    Parameter strict_first_cursor: trie -> option cursor.

    (* for this function, [after_suffix] actually means a fail *)
    Fixpoint next_cursor_bnode (bnode_cursor: bordernode_cursor) (bnode: BorderNode.table) (n: nat) :=
      match n with
      | S n' =>
        match bnode_cursor with
        | before_prefix len =>
          match (BorderNode.get_prefix len bnode) with
          | nil =>
            if Z_le_dec len keyslice_length then
              next_cursor_bnode (before_prefix (len + 1)) bnode n'
            else
              next_cursor_bnode after_suffix bnode n'
          | _ => before_prefix len
          end
        | before_suffix =>
          match (snd (BorderNode.get_suffix_pair bnode)) with
          | nil => before_suffix
          | _ => after_suffix
          end
        | after_suffix => after_suffix
        end
      | O => after_suffix
      end.

    (* This [next_cursor] returns a cursor when there is a next one,
     * also, it tries to eliminate an [after_suffix] cursor position *)
    Fixpoint strict_next_cursor (c: cursor): option cursor :=
      match c with
      | [] => None (* given an empty cursor, we can never return the next cursor *)
      | (t, table_cursor, bnode, bnode_cursor) :: c' =>
        match strict_next_cursor c' with
        (* if the subcursor can go next, then there is no need for ourselves to move *)
        | Some c'' => Some ((t, table_cursor, bnode, bnode_cursor) :: c'')
        (* if the subcursor cannot go on, then we need to move the current to the next *)
        | None =>
          (* try move inside the bnode first *)
          match next_cursor_bnode bnode_cursor bnode (Z.to_nat (keyslice_length + 2)) with
          | before_prefix len =>
            match (BorderNode.get_prefix len bnode) with
            | nil => (* impossible *) None
            | value_of _ => Some [(t, table_cursor, bnode, (before_prefix len))]
            | trie_of t' =>
              match strict_first_cursor t' with
              | Some c' =>
                Some ((t, table_cursor, bnode, (before_prefix len)) :: c')
              | None =>
                None
              end
            end
          | before_suffix =>
            match (snd (BorderNode.get_suffix_pair bnode)) with
            | nil => (* impossible *) None
            | value_of _ => Some [(t, table_cursor, bnode, before_suffix)]
            | trie_of t' =>
              match strict_first_cursor t' with
              | Some c' =>
                Some ((t, table_cursor, bnode, before_suffix) :: c')
              | None =>
                None
              end
            end
          | after_suffix =>
            None (* we cannot handle it at this level *)
          end
        end
      end.

    Function make_cursor (k: key) (t: trie) {measure length k}: cursor :=
      let keyslice := get_keyslice k in
      match t with
      | trienode_of tableform listform =>
        match Node.Flattened.get_value (Node.Flattened.make_cursor (keyslice) listform) listform with
        | Some bnode =>
          if (Z_le_dec (Zlength k) keyslice_length) then
          (* prefix case, which we need only to return the current cursor *)
            [(t, Node.make_cursor keyslice tableform, bnode, before_prefix (Zlength k))]
          else
            match fst (BorderNode.get_suffix_pair bnode) with
            | None =>
              match BorderNode.get_suffix None bnode with
              | value_of _ => []
              | nil => []
              | trie_of t' =>
                (t, Node.make_cursor keyslice tableform, bnode, before_suffix) :: make_cursor (get_suffix k) t'
              end
            | Some k' =>
              (* we need to compare the suffix here, if the key input is greater
               * then we need to move to next here
               * because the semantics of [get] need it *)
              if (TrieKeyFacts.lt_dec k' k) then
                [(t, Node.make_cursor keyslice tableform, bnode, after_suffix)]
              else
                [(t, Node.make_cursor keyslice tableform, bnode, before_suffix)]
            end
        | None =>
          []
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

    Definition get (c: cursor) (t: table): option (key * value). Admitted.
    Definition get_key (c: cursor) (t: table): option key :=
      match get c t with
      | Some (k, _) => Some k
      | None => None
      end.

    Definition get_value (c: cursor) (t: table): option value :=
      match get c t with
      | Some (_, v) => Some v
      | None => None
      end.

    Definition put (k: key) (v: value) (c: cursor) (table_with_allocator: (table * allocator)): cursor * (table * allocator). Admitted.

    Definition next_cursor (c: cursor) (t: table): cursor. Admitted.
    Definition prev_cursor (c: cursor) (t: table): cursor. Admitted.
    Definition first_cursor (t: table): cursor. Admitted.
    Definition last_cursor (t: table): cursor. Admitted.
    Definition cursor_correct (c: cursor): Prop. Admitted.
    Definition table_correct (t: table): Prop. Admitted.
    Definition abs_rel (c: cursor) (t: table): Prop. Admitted.
    Definition key_rel (k: key) (c: cursor) (t: table): Prop. Admitted.
    Definition eq_cursor (c1 c2: cursor) (t: table): Prop. Admitted.

    Section Specs.
      Variable t t1 t2: table.
      Variable c c1 c2 c3: cursor. 
      Variable k k1 k2 k3: key.
      Variable e e1 e2: value.
      Variable a: allocator.

      Axiom abs_correct: abs_rel c t -> cursor_correct c /\ table_correct t.

      (* table-cursor relations *)
      (* We need to make sure that the cursor and the table are actually working with each other *)
      (* This is actually implied by [make_cursor_key] *)
      (* Axiom make_cusor_abs: abs_rel (make_cursor k t) t. *)
      (* Do we need this? *)
      (* Axiom put_abs: *)
      (*   let (new_cursor, new_table) := put c e t in *)
      (*   abs_rel new_cursor new_table. *)
      (* TODO: What about at the end of range? *)
      Axiom next_cursor_abs: abs_rel c t -> abs_rel (next_cursor c t) t.
      Axiom prev_cursor_abs: abs_rel c t -> abs_rel (prev_cursor c t) t.
      Axiom first_cursor_abs: table_correct t -> abs_rel (first_cursor t) t.
      Axiom last_cursor_abs: table_correct t -> abs_rel (last_cursor t) t.
      Axiom put_correct: table_correct t -> table_correct (fst (snd (put k e c (t, a)))). 

      (* permute of get and insert operations *)
      (* Assume [key_rel] does entail [abs_rel] *)
      Axiom get_put_same:
        abs_rel c1 (fst (snd (put k e c2 (t, a)))) ->
        abs_rel c2 t ->
        key_rel k c1 (fst (snd (put k e c2 (t, a)))) ->
        get c1 (fst (snd (put k e c2 (t, a)))) = Some (k, e).
      Axiom get_put_diff:
        k1 <> k2 ->
        abs_rel c1 (fst (snd (put k2 e c2 (t, a)))) ->
        abs_rel c2 t ->
        abs_rel c3 t ->
        key_rel k1 c1 (fst (snd (put k2 e c2 (t, a)))) ->
        key_rel k1 c3 t ->
        get c1 (fst (snd (put k2 e c2 (t, a)))) = get c3 t.

      (* get in specific conditions *)
      Axiom get_last:
        get (last_cursor t) t = None.
      Axiom get_empty: 
        abs_rel c (fst (empty a)) -> get c (fst (empty a)) = None.

      (* Cursor and keys *)

      Axiom key_rel_eq_cursor:
        key_rel k c1 t ->
        key_rel k c2 t ->
        abs_rel c1 t ->
        abs_rel c2 t ->
        eq_cursor c1 c2 t.

      Axiom make_cursor_key:
        table_correct t -> key_rel k (make_cursor k t) t.
      Axiom make_cursor_abs:
          table_correct t -> abs_rel (make_cursor k t) t.
      
      (* cursor movement with respect to the order of key *)
      Axiom next_prev:
        abs_rel c t -> ~ eq_cursor c (last_cursor t) t -> eq_cursor c (prev_cursor (next_cursor c t) t) t.
      Axiom prev_next:
        abs_rel c t -> ~ eq_cursor c (first_cursor t) t -> eq_cursor c (next_cursor (prev_cursor c t) t) t.
      Axiom next_order:
        ~ eq_cursor c (last_cursor t) t -> key_rel k1 c t -> key_rel k2 (next_cursor c t) t -> TrieKey.lt k1 k2.
      Axiom prev_order:
        ~ eq_cursor c (first_cursor t) t -> key_rel k1 c t -> key_rel k2 (prev_cursor c t) t -> TrieKey.lt k2 k1.
      (* TODO: does this definition work? *)
      Axiom next_compact:
        ~ eq_cursor c (last_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (next_cursor c t) t ->
        ~ key_rel k3 c t -> TrieKey.lt k1 k3 /\ TrieKey.lt k3 k2.
      Axiom prev_compact:
        ~ eq_cursor c (first_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (prev_cursor c t) t ->
        ~ key_rel k3 c t -> TrieKey.lt k2 k3 /\ TrieKey.lt k3 k1.
    End Specs.

    Axiom flatten_invariant: forall t,
        table_correct t ->
        Flattened.table_correct (flatten t) /\
        forall (k: key) (c1: cursor) (c2: Flattened.cursor value),
          key_rel k c1 t -> Flattened.key_rel k c2 (flatten t) ->
          abs_rel c1 t -> Flattened.abs_rel c2 (flatten t) ->
          get c1 t = Flattened.get c2 (flatten t).
  End Types.
End Trie.
