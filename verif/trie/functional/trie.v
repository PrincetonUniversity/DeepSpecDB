Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import VST.floyd.functional_base.
Require Import common.
Require Import tactics.
Require Import DB.lemmas.

Require Import DB.functional.key.
Require Import DB.functional.cursored_kv.
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.

Import List.
Import Lists.List.ListNotations.

Module KeysliceType := Z_as_OT.
Module KeysliceFacts := OrderedTypeFacts Z_as_OT.
(* On going rewrite:
 * 1. support cursor
 * 2. add addresses into the data type.
 *)

Module Trie (Node: FLATTENABLE_TABLE KeysliceType) (* <: FLATTENABLE_TABLE TrieKey *).
  Definition key := TrieKey.t.

  Module Flattened := SortedListTable TrieKey.
  Module NodeFacts := FlattenableTableFacts KeysliceType Node.

  Section Types.
    Context {value: Type}.
    (* Notes: reason for removing the [val] from the constructor:
     *        originally the kvstore contains a cursor for it, therefore there is necessity for another struct,
     *        it's not the case in final impl, and therefore we directly use the btree as pointer to a trienode *)
    Inductive trie: Type :=
    | trienode_of: val ->
                   Node.table val -> (* The btree data *)
                   Node.Flattened.table (val * BorderNode.table value trie) -> (* abstract data *)
                   trie.
    Definition table: Type := option trie.
    Definition bordernode := BorderNode.table value trie.
    Hint Constructors trie: trie.

    (* this is only a pseudo height, cause we only care about termination *)
    (* some random hack so that it pass subterm check *)
    Definition bnode_height {trie_height: trie -> nat} (bnode: bordernode): nat :=
      match bnode with
      | (prefixes, Some (inr t')) =>
        trie_height t'
      | _ =>
        O
      end.
    Fixpoint trie_height (t: trie): nat :=
      match t with
      | trienode_of _ _ listform =>
        1 + fold_right Nat.max O (map (compose (@bnode_height trie_height) (compose snd snd)) listform)
      end.

    Lemma fold_max_le: forall x l, In x l -> (x <= fold_right Nat.max O l)%nat.
    Proof.
      intros.
      induction l.
      - inv H.
      - inv H.
        + simpl.
          apply Nat.le_max_l.
        + simpl.
          specialize (IHl H0).
          apply le_trans with (fold_right Nat.max 0 l)%nat.
          * assumption.
          * apply Nat.le_max_r.
    Qed.

    (* order of bordernode? *)
    (* first the prefixes, then the suffix? *)
    (* Placement of cursor:
     * For keys that already existed in the store, just place at the place
     * For keys that are not in the store, place them at the furtherest bordernode entry *)
    Definition cursor: Type := list (trie * Node.cursor val * bordernode * BorderNode.cursor).

    Definition empty (t: trie) :=
      match t with
      | trienode_of _ trieform listform =>
        Node.empty trieform /\ Node.Flattened.empty listform
      end.

    Fixpoint flatten_prefix_array (prefix: string) (keyslice: KeysliceType.t)
             (prefixes: list (option value)) (idx: Z): Flattened.table value :=
      match prefixes with
      | Some v :: t =>
        ((prefix ++ (reconstruct_keyslice (keyslice, idx))), v) :: flatten_prefix_array prefix keyslice t (idx + 1)
      | None :: t =>
        flatten_prefix_array prefix keyslice t (idx + 1)
      | [] => []
      end.

    Definition flatten_bordernode {flatten_trie_aux: TrieKey.t -> trie -> Flattened.table value}
             (prefix: string) (kv: KeysliceType.t * (val * bordernode)) :=
      let (keyslice, augmented_bnode) := kv in
      let (_, bnode) := augmented_bnode in
      let (prefixes, suffix) := bnode in
        flatten_prefix_array prefix keyslice prefixes 0 ++
      match suffix with
      | Some (inl (suffix_key, suffix_value)) => [(prefix ++ (reconstruct_keyslice (keyslice, keyslice_length)) ++ suffix_key, suffix_value)]
      | Some (inr t') =>
        flatten_trie_aux (prefix ++ (reconstruct_keyslice (keyslice, keyslice_length))) t'
      | None =>
        []
      end.

    Fixpoint flatten_aux (prefix: TrieKey.t) (t: trie) {struct t}: Flattened.table value :=
      match t with
      (* the tableform is of no interest here *)
      | trienode_of _ _ listform =>
        flat_map (@flatten_bordernode flatten_aux prefix) listform
      end.

    Definition flatten_bnode := @flatten_bordernode flatten_aux.

    Definition flatten (t: trie): Flattened.table value := flatten_aux [] t.

    Function strict_first_cursor (t: trie) {measure trie_height t}: option cursor :=
      match t with
      | trienode_of _ tableform listform =>
        match Node.Flattened.get_value (Node.Flattened.first_cursor listform) listform with
        | Some (_, bnode) =>
          match BorderNode.next_cursor (BorderNode.before_prefix 1) bnode with
          | BorderNode.before_prefix len =>
            match (BorderNode.get_prefix len bnode) with
            | Some _ =>
              Some [(t, Node.first_cursor tableform, bnode, BorderNode.before_prefix len)]
            | None => None
            end
          | BorderNode.before_suffix =>
            match snd bnode with
            | Some (inl _) =>
              Some [(t, Node.first_cursor tableform, bnode, BorderNode.before_suffix)]
            | Some (inr t') =>
              match strict_first_cursor t' with
              | Some c' => Some ((t, Node.first_cursor tableform, bnode, BorderNode.before_suffix) :: c')
              | None => None
              end
            | None =>
              None
            end
          | BorderNode.after_suffix => None
          end
        | None => None
        end
      end.
    Proof.
      intros.
      simpl.
      apply Nat.lt_succ_r.
      apply fold_max_le.
      subst.
      destruct bnode.
      simpl in teq3; subst.
      unfold Node.Flattened.get_value in teq0.
      match_tac in teq0; [ | congruence].
      destruct p.
      inv teq0.
      apply Node.Flattened.get_in_weak in H.
      match goal with
      | |- context [map ?f' listform] => apply in_map with (f := f') in H
      end.
      simpl in H.
      assumption.
    Defined.

    (* This [normalize_cursor] returns a cursor when the "next" kv locates,
     * also, it tries to eliminate an [BorderNode.after_suffix] cursor position *)
    Fixpoint normalize_cursor (c: cursor): option cursor :=
      match c with
      | [] => None (* given an empty cursor, we can never return the next cursor *)
      | (trienode_of addr tableform listform, table_cursor, bnode, bnode_cursor) :: c' =>
        let t := trienode_of addr tableform listform in
        match normalize_cursor c' with
        (* if the subcursor can go next, then there is no need for ourselves to move *)
        | Some c'' => Some ((t, table_cursor, bnode, bnode_cursor) :: c'')
        (* if the subcursor cannot go on, then we need to move the current to the next *)
        | None =>
          (* try move inside the bnode first *)
          match BorderNode.next_cursor bnode_cursor bnode with
          | BorderNode.before_prefix len =>
            Some [(t, table_cursor, bnode, (BorderNode.before_prefix len))]
          | BorderNode.before_suffix =>
            match snd bnode with
            | None => (* impossible *) None
            | Some (inl _) =>
              Some [(t, table_cursor, bnode, BorderNode.before_suffix)]
            | Some (inr t') =>
              match strict_first_cursor t' with
              | Some c' =>
                Some ((t, table_cursor, bnode, BorderNode.before_suffix) :: c')
              | None =>
                None
              end
            end
          | BorderNode.after_suffix =>
            (* try move to next cursor at node level *)
            let table_cursor' := Node.next_cursor table_cursor tableform in
            match Node.get_key table_cursor' tableform with
            | Some key =>
              match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
              | Some (_, bnode') =>
                (* no need to repeatedly move to next if we have maintained the invariant that no dead end exists
                 * in the trie *)
                match BorderNode.next_cursor (BorderNode.before_prefix 1) bnode' with
                | BorderNode.before_prefix len =>
                  match (BorderNode.get_prefix len bnode') with
                  | None => (* impossible *) None
                  | Some _ => Some [(t, table_cursor', bnode', (BorderNode.before_prefix len))]
                  end
                | BorderNode.before_suffix =>
                  match (snd bnode') with
                  | None => (* impossible *) None
                  | Some (inl _) => Some [(t, table_cursor', bnode', BorderNode.before_suffix)]
                  | Some (inr t') =>
                    match strict_first_cursor t' with
                    | Some c' =>
                      Some ((t, table_cursor', bnode', BorderNode.before_suffix) :: c')
                    | None =>
                      None
                    end
                  end
                | BorderNode.after_suffix => None
                end
              | None => None (* we cannot handle it at this level *)
              end
            | None => None
            end
          end
        end
      end.

    Function make_cursor (k: key) (t: trie) {measure length k}: cursor :=
      let keyslice := get_keyslice k in
      match t with
      | trienode_of _ tableform listform =>
        match Node.Flattened.get_exact keyslice listform with
        | Some (_, bnode) =>
          if (Z_le_dec (Zlength k) keyslice_length) then
          (* prefix case, which we need only to return the current cursor *)
            [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_prefix (Zlength k))]
          else
            match snd bnode with
            | None =>
              [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.after_suffix)]
            | Some (inl (k', _)) =>
              (* we need to compare the suffix here, if the key input is greater
               * then we need to move to next here
               * because the semantics of [get] need it *)
              if (TrieKeyFacts.lt_dec k' (get_suffix k)) then
                [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.after_suffix)]
              else
                [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_suffix)]
            | Some (inr t') =>
                (t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_suffix) :: make_cursor (get_suffix k) t'
            end
        | None =>
          (* either we get to the last cursor, or we does ont have a matched key *)
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

    Fixpoint get_raw (c: cursor): option (key * value) :=
      match c with
      | (trienode_of _ tableform _, table_cursor, bnode, bnode_cursor) :: c' =>
        match Node.get_key table_cursor tableform with
        | Some keyslice =>
          match bnode_cursor with
          | BorderNode.before_prefix len =>
            match BorderNode.get_prefix len bnode with
            | Some v => Some (reconstruct_keyslice (keyslice, len), v)
            | None => None
            end
          | BorderNode.before_suffix =>
            match (snd bnode) with
            | Some (inl (k, v)) => Some (reconstruct_keyslice (keyslice, keyslice_length) ++ k, v)
            | Some (inr t') =>
              match get_raw c' with
              | Some (k', v') => Some (reconstruct_keyslice (keyslice, keyslice_length) ++ k', v')
              | None => None
              end
            | None => None
            end
          | BorderNode.after_suffix => None
          end
        | None => None
        end
      | [] => None
      end.

    Definition get (c: cursor) (t: trie): option (key * value) :=
      match normalize_cursor c with
      | Some c' =>
        get_raw c'
      | None => None
      end.

    Definition get_key (c: cursor) (t: trie): option key :=
      match get c t with
      | Some (k, _) => Some k
      | None => None
      end.

    Definition get_value (c: cursor) (t: trie): option value :=
      match get c t with
      | Some (_, v) => Some v
      | None => None
      end.

    (* for now, the put function ignore the cursor input *)
    (* we might need some optimization later *)

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

    Inductive create_pair (k1 k2: key) (v1 v2: value): cursor -> trie -> Prop :=
    | create_pair_case1: forall emptylist emptytable listform tableform listcursor tablecursor bnode_addr addr,
        let keyslice1 := get_keyslice k1 in
        let keyslice2 := get_keyslice k2 in
        keyslice1 = keyslice2 ->
        Zlength k1 <= keyslice_length \/ Zlength k2 <= keyslice_length ->
        let bnode := BorderNode.put_value k1 v1 BorderNode.empty in
        let bnode := BorderNode.put_value k2 v2 bnode in
        Node.Flattened.empty emptylist ->
        Node.Flattened.put keyslice1 (bnode_addr, bnode)
                           (Node.Flattened.first_cursor emptylist) emptylist
                           listcursor listform ->
        Node.empty emptytable ->
        Node.put keyslice1 bnode_addr (Node.first_cursor emptytable) emptytable tablecursor tableform ->
        create_pair k1 k2 v1 v2
                    [(trienode_of addr tableform listform, tablecursor, bnode, BorderNode.length_to_cursor (Zlength k1))]
                    (trienode_of addr tableform listform)
    | create_pair_case2: forall emptylist emptytable listform tableform listcursor tablecursor bnode_addr c' t' addr,
        let keyslice1 := get_keyslice k1 in
        let keyslice2 := get_keyslice k2 in
        keyslice1 = keyslice2 ->
        Zlength k1 > keyslice_length /\ Zlength k2 > keyslice_length ->
        create_pair (get_suffix k1) (get_suffix k2) v1 v2 c' t' ->
        let bnode := BorderNode.put_link t' BorderNode.empty in
        Node.Flattened.empty emptylist ->
        Node.Flattened.put keyslice1 (bnode_addr, bnode)
                           (Node.Flattened.first_cursor emptylist) emptylist
                           listcursor listform ->
        Node.empty emptytable ->
        Node.put keyslice1 bnode_addr (Node.first_cursor emptytable) emptytable tablecursor tableform ->
        create_pair k1 k2 v1 v2
                    ((trienode_of addr tableform listform, tablecursor, bnode, BorderNode.before_suffix) :: c')
                    (trienode_of addr tableform listform)
    | create_pair_case3: forall emptylist emptytable listform1 listform2 tableform1 tableform2 listcursor1 listcursor2 tablecursor1 tablecursor2 bnode_addr1 bnode_addr2 addr,
        let keyslice1 := get_keyslice k1 in
        let keyslice2 := get_keyslice k2 in
        keyslice1 <> keyslice2 ->
        let bnode1 := BorderNode.put_value k1 v1 BorderNode.empty in
        let bnode2 := BorderNode.put_value k2 v2 BorderNode.empty in
        Node.Flattened.empty emptylist ->
        Node.Flattened.put keyslice2 (bnode_addr2, bnode2)
                           (Node.Flattened.first_cursor emptylist) emptylist
                           listcursor2 listform2 ->
        Node.Flattened.put keyslice1 (bnode_addr1, bnode1)
                           (Node.Flattened.first_cursor listform2) listform2
                           listcursor1 listform1 ->
        Node.empty emptytable ->
        Node.put keyslice2 bnode_addr2 (Node.first_cursor emptytable) emptytable tablecursor2 tableform2 ->
        Node.put keyslice1 bnode_addr1 (Node.first_cursor tableform2) tableform2 tablecursor1 tableform1 ->
        create_pair k1 k2 v1 v2
                    [(trienode_of addr tableform1 listform1, tablecursor1, bnode1, BorderNode.length_to_cursor (Zlength k1))]
                    (trienode_of addr tableform1 listform1).

    Inductive put (k: key) (v: value): cursor -> trie -> cursor -> trie -> Prop :=
    | put_case1: forall tableform listform listform' listcursor listcursor' bnode_addr bnode c addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = Some (bnode_addr, bnode) ->
        Zlength k <= keyslice_length ->
        let bnode := BorderNode.put_prefix (Zlength k) v bnode in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        let tablecursor := Node.make_cursor keyslice tableform in
        put k v c (trienode_of addr tableform listform)
            [(trienode_of addr tableform listform', tablecursor, bnode, BorderNode.before_prefix (Zlength k))]
            (trienode_of addr tableform listform')
    | put_case2: forall tableform listform listform' listcursor listcursor' bnode_addr bnode c t' c' t'' c'' addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = Some (bnode_addr, bnode) ->
        Zlength k > keyslice_length ->
        BorderNode.get_link bnode = Some t' ->
        put (get_suffix k) v c' t' c'' t'' ->
        let bnode := BorderNode.put_link t'' bnode in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        let tablecursor := Node.make_cursor keyslice tableform in
        put k v c (trienode_of addr tableform listform)
            ((trienode_of addr tableform listform', tablecursor, bnode, BorderNode.before_suffix) :: c'')
            (trienode_of addr tableform listform')
    | put_case3: forall tableform listform listform' listcursor listcursor' bnode_addr bnode c addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = Some (bnode_addr, bnode) ->
        Zlength k > keyslice_length ->
        snd bnode = None ->
        let bnode := BorderNode.put_suffix (get_suffix k) v bnode in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        let tablecursor := Node.make_cursor keyslice tableform in
        put k v c (trienode_of addr tableform listform)
            [(trienode_of addr tableform listform', tablecursor, bnode, BorderNode.before_suffix)]
            (trienode_of addr tableform listform')
    | put_case4: forall tableform listform listform' listcursor listcursor' bnode_addr bnode c addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = Some (bnode_addr, bnode) ->
        Zlength k > keyslice_length ->
        BorderNode.test_suffix (get_suffix k) bnode = true ->
        let bnode := BorderNode.put_suffix (get_suffix k) v bnode in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        let tablecursor := Node.make_cursor keyslice tableform in
        put k v c (trienode_of addr tableform listform)
            [(trienode_of addr tableform listform', tablecursor, bnode, BorderNode.before_suffix)]
            (trienode_of addr tableform listform')
    | put_case5: forall tableform listform listform' listcursor listcursor' bnode_addr bnode c c' t' k' v' addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = Some (bnode_addr, bnode) ->
        Zlength k > keyslice_length ->
        BorderNode.get_suffix_pair bnode = Some (k', v') ->
        get_suffix k <> k' ->
        create_pair (get_suffix k) k' v v' c' t' ->
        let bnode := BorderNode.put_link t' bnode in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        let tablecursor := Node.make_cursor keyslice tableform in
        put k v c (trienode_of addr tableform listform)
            ((trienode_of addr tableform listform', tablecursor, bnode, BorderNode.before_suffix) :: c')
            (trienode_of addr tableform listform')
    | put_case6: forall tableform tableform' listform listform' tablecursor tablecursor' listcursor listcursor' bnode_addr c addr,
        let keyslice := get_keyslice k in
        Node.Flattened.get_exact keyslice listform = None ->
        let bnode := BorderNode.put_value k v BorderNode.empty in
        Node.Flattened.abs_rel listcursor listform ->
        Node.Flattened.put keyslice (bnode_addr, bnode)
                           listcursor listform
                           listcursor' listform' ->
        Node.abs_rel tablecursor tableform ->
        Node.put keyslice bnode_addr
                           tablecursor tableform
                           tablecursor' tableform' ->
        put k v c (trienode_of addr tableform listform)
            [(trienode_of addr tableform' listform', tablecursor', bnode, BorderNode.before_suffix)]
            (trienode_of addr tableform' listform').

    (* This strict_next_cursor does not necessarily produce a valid position([BorderNode.after_suffix]) *)
    (* not sure if this work *)
    Fixpoint strict_next_cursor (c: cursor): cursor :=
      match c with
      | [] => []
      | [(trienode_of addr tableform listform, table_cursor, bnode, bnode_cursor)] =>
        match bnode_cursor with
        | BorderNode.before_prefix len =>
          if Z_lt_dec len keyslice_length then
            [(trienode_of addr tableform listform, table_cursor, bnode, BorderNode.before_prefix (len + 1))]
          else
            [(trienode_of addr tableform listform, table_cursor, bnode, BorderNode.after_suffix)]
        | BorderNode.before_suffix => [(trienode_of addr tableform listform, table_cursor, bnode, BorderNode.after_suffix)]
        | BorderNode.after_suffix =>
          let table_cursor' := Node.next_cursor table_cursor tableform in
          match Node.get_key table_cursor' tableform with
          | Some key =>
            match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
            | Some bnode' =>
              [(trienode_of addr tableform listform, table_cursor, bnode, BorderNode.before_prefix 1)]
            | None => []
            end
          | None => [] (* should not be the case in the only scenario of usage *)
          end
        end
      | current_slice :: c' =>
        current_slice :: (strict_next_cursor c')
      end.

    Definition next_cursor (c: cursor) (t: table): cursor :=
      match normalize_cursor c with
      | Some c' =>
        strict_next_cursor c'
      | None =>
        []
      end.

    Definition prev_cursor (c: cursor) (t: table): cursor. Admitted.
    Definition first_cursor (t: table): cursor. Admitted.
    Definition last_cursor (t: table): cursor. Admitted.

    Definition key_inrange (k: Z): Prop :=
      0 <= k <= Ptrofs.max_unsigned.

    (* optional invariant for table: there is no dead end in the trie
     * question: does empty root node count as dead end?
     * answer(informal): No. because it won't turn the result of any operation from
     *                   valid cursor to an invalid one
     *                   Dec. 4: I'm actually not sure about this now. *)
    Inductive trie_correct: trie -> Prop :=
    | table_correct_intro tableform listform: forall addr,
        Node.table_correct tableform ->
        Node.Flattened.table_correct listform ->
        map fst (Node.flatten tableform) = map fst listform ->
        map snd (Node.flatten tableform) = map (compose fst snd) listform ->
        Forall (compose bordernode_correct (compose snd snd)) listform ->
        Forall (compose key_inrange fst) listform ->
        Zlength listform > 1 -> (* no dead end *)
        trie_correct (trienode_of addr tableform listform)
    with
    bordernode_correct: bordernode -> Prop :=
    | bordernode_correct_nil prefixes:
        Zlength prefixes = keyslice_length -> (* no dead end *)
        Exists (fun v => v <> None) prefixes ->
        bordernode_correct (prefixes, None)
    | bordernode_correct_ext prefixes k v:
        Zlength prefixes = keyslice_length ->
        0 < Zlength k ->
        bordernode_correct (prefixes, Some (inl (k, v)))
    | bordernode_correct_int prefixes t':
        Zlength prefixes = keyslice_length ->
        trie_correct t' ->
        bordernode_correct (prefixes, Some (inr t')).
    Hint Constructors trie_correct: trie.

    Fixpoint cursor_correct_aux (c: cursor) (p: option trie): Prop :=
      match c with
      | (trienode_of addr tableform listform, table_cursor, bnode, bnode_cursor) :: c' =>
        match p with (* that the previous pointer actually points to this cursor slice *)
        | Some t => t = trienode_of addr tableform listform
        | None => True
        end /\
        (* trie_correct (trienode_of addr tableform listform) /\ *) (* that cursor correct entails trie correct *)
        Node.cursor_correct table_cursor /\ (* that the two component-cursors are actually correct *)
        BorderNode.cursor_correct bnode_cursor /\
        match Node.get_key table_cursor tableform with (* find the bordernode pointing to from the btree *)
        | Some key =>
          match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
          | Some (_, bnode') =>
            bnode' = bnode /\
            match bnode_cursor with (* go to next level of btree *)
            | BorderNode.before_prefix len =>
              c' = []
            | BorderNode.before_suffix =>
              match snd bnode with
              | Some (inr t') => cursor_correct_aux c' (Some t')
              | _ => c' = []
              end
            | BorderNode.after_suffix => c' = []
            end
          | None => False (* should not be the case in the only scenario of usage *)
          end
        | None => False (* there should be no cursor with a table cursor pointing at the end of table *)
        end
      | [] => True
      end.

    Definition cursor_correct (c: cursor): Prop := cursor_correct_aux c None.

    Definition cursor_trie_assoc (c: cursor) (t: trie): Prop :=
      cursor_correct c /\ trie_correct t /\
      match c with
      | (t', _, _, _) :: _ =>
        (* This should suffice because the [cursor_correct] regulates the structure *)
        t' = t
      | [] => True
      end.

    Definition key_rel (k: key) (c: cursor) (t: trie): Prop :=
      normalize_cursor c = normalize_cursor (make_cursor k t).

    Definition eq_cursor (c1 c2: cursor) (t: table): Prop. Admitted.

    Ltac simplify :=
      destruct_conjs;
      destruct_exists;
      repeat (match goal with
              | var: _ * _ |- _ => destruct var
              | H: (_, _) = (_, _) |- _ => inv H
              | H: ?f _ = ?f _ |- _ => injection H; intros; subst; clear H
              | H: ?f _ _ = ?f _ _ |- _ => injection H; intros; subst; clear H
              | H: _ /\ _ |- _ => destruct_conjs
              | |- _ /\ _ => split
              | H: fst ?p = _ |- _ => destruct p; simpl in H; subst
              | H: snd ?p = _ |- _ => destruct p; simpl in H; subst
              | H: _ = fst ?p |- _ => destruct p; simpl in H; subst
              | H: _ = snd ?p |- _ => destruct p; simpl in H; subst
              | H: match _ with _ => _ end |- _ => match_tac in H; subst
              | H: match _ with _ => _ end = _ |- _ => match_tac in H; subst
              | H: _ = match _ with _ => _ end |- _ => match_tac in H; subst
              | H: False |- _ => destruct H
              end; simpl in *);
      eauto;
      try discriminates.

    Lemma cursor_correct_aux_weaken: forall h c,
        cursor_correct_aux c (Some h) ->
        cursor_correct_aux c None.
    Proof.
      intros.
      destruct c.
      - firstorder.
      - simpl in *.
        destruct p as [[[[]]]].
        simplify.
    Qed.

    Lemma cursor_correct_subcursor_correct: forall h c,
        cursor_correct (h :: c) ->
        cursor_correct c.
    Proof.
      intros.
      unfold cursor_correct in H.
      simpl in H.
      simplify.
      eapply cursor_correct_aux_weaken; eauto.
    Qed.

    Lemma trie_correct_subtrie_correct: forall p tableform listform k v l t' c,
        trie_correct (trienode_of p tableform listform) ->
        Node.Flattened.get c listform = Some (k, (v, (l, Some (inr t')))) ->
        trie_correct t'.
    Proof.
      intros.
      inv H.
      apply Node.Flattened.get_in_weak in H0.
      eapply Forall_forall in H8; [ | eauto].
      simpl in H8.
      inv H8.
      assumption.
    Qed.

    Lemma cursor_correct_bnode_cursor_correct: forall t tc b bc c,
        cursor_correct ((t, tc, b, bc) :: c) ->
        BorderNode.cursor_correct bc.
    Proof.
      intros.
      unfold cursor_correct in H.
      simpl in H.
      simplify.
    Qed.

    Lemma strict_first_cursor_normalized: forall t c,
        trie_correct t ->
        strict_first_cursor t = Some c ->
        normalize_cursor c = Some c.
    Proof.
      intros.
      remember (trie_height t).
      generalize dependent t.
      generalize dependent c.
      induction n using (well_founded_induction lt_wf); intros.
      destruct t.
      rewrite strict_first_cursor_equation in H1.
      simplify.
      - simpl.
        erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
        reflexivity.
      - simpl.
        erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
        repeat match_tac; simplify.
        pose proof H2; unfold Node.Flattened.get_value in H2; simplify.
        apply Node.Flattened.get_in_weak in H6.
        apply H with (y := trie_height t1) in H4.
        + rewrite H4 in H1.
          simplify.
        + apply in_map with (f := compose (@bnode_height trie_height) (compose snd snd)) in H6.
          simpl in H6.
          apply fold_max_le in H6.
          unfold trie_height at 2.
          apply le_lt_n_Sm.
          assumption.
        + inv H0.
          eapply Forall_forall in H13; [ | eauto].
          simpl in H13.
          inv H13.
          assumption.
        + reflexivity.
    Qed.

    (* Lemma cursor_correct_bordernode_correct: forall t tc b bc c, *)
    (*     cursor_correct ((t, tc, b, bc) :: c) -> *)
    (*     bordernode_correct b. *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold cursor_correct in H. *)
    (*   simpl in H. *)
    (*   destruct t. *)
    (*   rename v into addr. *)
    (*   destruct H as [_ [? [_ [_ ?]]]]. *)
    (*   destruct (Node.get_key tc t) eqn:Heqn; try contradiction. *)
    (*   destruct (Node.Flattened.get_value (Node.Flattened.make_cursor k t0) t0) as [[] | ] eqn:Heqn'; *)
    (*     try contradiction. *)
    (*   inv H0. *)
    (*   assert (exists k', Node.Flattened.get (Node.Flattened.make_cursor k t0) t0 = Some (k', (v, b))). { *)
    (*     unfold Node.Flattened.get_value in Heqn'. *)
    (*     destruct (Node.Flattened.get (Node.Flattened.make_cursor k t0) t0) eqn:Heqn''. *)
    (*     - inv Heqn''. *)
    (*       destruct p as [k' ?]. *)
    (*       exists k'. *)
    (*       inv Heqn'. *)
    (*       assumption. *)
    (*     - inv Heqn'. *)
    (*   } *)
    (*   destruct H0 as [k' ?]. *)
    (*   inv H. *)
    (*   apply Node.Flattened.get_in_weak in H0. *)
    (*   rewrite Forall_forall in H9. *)
    (*   apply H9 in H0. *)
    (*   simpl in H0. *)
    (*   assumption. *)
    (* Qed. *)

    Lemma cursor_correct_aux_trie_assoc: forall t c,
        trie_correct t ->
        cursor_correct_aux c (Some t) ->
        cursor_trie_assoc c t.
    Proof.
      intros.
      unfold cursor_trie_assoc.
      repeat split.
      - eapply cursor_correct_aux_weaken.
        eauto.
      - assumption.
      - match_tac; simplify.
        simpl in H0.
        simplify.
    Qed.

    Lemma normalize_idempotent: forall c1 c2 t,
        cursor_trie_assoc c1 t ->
        cursor_trie_assoc c2 t ->
        normalize_cursor c1 = Some c2 ->
        normalize_cursor c2 = Some c2.
    Proof.
      intros.
      generalize dependent t.
      generalize dependent c2.
      induction c1; intros.
      - inv H1.
      - inv H.
        inv H0.
        unfold cursor_correct in H2.
        simpl in H2.
        simpl in H1.
        repeat (simplify; match_tac);
          try match goal with
              | H1: BorderNode.next_cursor ?bnode_cursor1 ?bnode = ?bnode_cursor2 |- _ =>
                match goal with
                | H2: BorderNode.next_cursor bnode_cursor2 bnode = ?bnode_cursor3 |- _ =>
                  apply BorderNode.next_cursor_idempotent in H1; rewrite H1 in H2; simplify
                end
              end; (* kill 56 goals *)
          try match goal with
              | H: context [Node.Flattened.get_value] |- _ => unfold Node.Flattened.get_value in H; match_tac in H; simplify
              end;
          try match goal with
              | H1: trie_correct (trienode_of _ _ ?listform) |- _ =>
                match goal with
                | H2: Node.Flattened.get _ listform = Some (_, (_, (_, Some (inr _)))) |- _ =>
                  pose proof H2; eapply trie_correct_subtrie_correct in H2; [ | eauto]
                end
              end;
          try match goal with
              | H1: strict_first_cursor ?t = Some ?c1 |- _ =>
                match goal with
                | H2: normalize_cursor c1 = Some ?c2 |- _ =>
                  eapply strict_first_cursor_normalized in H1; [ | eauto]; rewrite H1 in H2; simplify
                end
              end;
          try match goal with
              | H: cursor_correct (_ :: _) |- _ => unfold cursor_correct in H; simpl in H; simplify
              end.
        + specialize (IHc1 c3 eq_refl t ltac:(eapply cursor_correct_aux_trie_assoc; eauto) ltac:(eapply cursor_correct_aux_trie_assoc; eauto)).
          rewrite IHc1 in H1.
          simplify.
        + specialize (IHc1 c3 eq_refl t ltac:(eapply cursor_correct_aux_trie_assoc; eauto) ltac:(eapply cursor_correct_aux_trie_assoc; eauto)).
          rewrite IHc1 in H1.
          simplify.
        + specialize (IHc1 c3 eq_refl t ltac:(eapply cursor_correct_aux_trie_assoc; eauto) ltac:(eapply cursor_correct_aux_trie_assoc; eauto)).
          rewrite IHc1 in H1.
          simplify.
    Qed.

    (* [c1] associated with trie, [c2] associated with subtrie, [c3] associated with table *)
    (* Lemma get_subtrie: forall tableform listform bnode t' c1 c2 c3 ks k e, *)
    (*     cursor_correct c1 -> *)
    (*     key_rel (reconstruct_keyslice (ks, keyslice_length) ++ k) c1 (trienode_of tableform listform) -> *)
    (*     abs_rel c1 (trienode_of tableform listform) -> *)
    (*     key_rel k c2 t' -> *)
    (*     abs_rel c2 t' -> *)
    (*     Node.Flattened.key_rel ks c3 listform -> *)
    (*     Node.Flattened.abs_rel c3 listform -> *)
    (*     Node.Flattened.get c3 listform = Some (ks, bnode) /\ *)
    (*     BorderNode.get_suffix None bnode = trie_of t' /\ *)
    (*     get_raw c2 = Some (k, e) *)
    (*     <-> *)
    (*     get_raw c1 = Some (reconstruct_keyslice (ks, keyslice_length) ++ k, e). *)
    (* Proof. *)
    (*   intros. *)
    (*   remember (reconstruct_keyslice (ks, keyslice_length)) as prefix. *)
    (*   assert (get_keyslice (prefix ++ k) = ks) by admit. *)
    (*   assert (get_suffix (prefix ++ k) = k) by admit. (* for sure these is true *) *)
    (*   split; intros. *)
    (*   - destruct H8 as [? []]. *)
    (*     unfold key_rel in H0. *)
    (*     rewrite make_cursor_equation in H0. *)
    (*     rewrite H6 in H0. *)
    (*     unfold abs_rel in H1. *)
    (*     unfold Node.Flattened.get_exact in H0. *)
    (*     replace (Node.Flattened.get (Node.Flattened.make_cursor ks listform) listform) with *)
    (*         (Node.Flattened.get c3 listform) in H0 by trie_crush. *)
    (*     rewrite H8 in H0. *)
    (*     rewrite if_true in H0 by auto. *)
    (*     rewrite if_false in H0 by admit. *)
    (*     destruct bnode as [[prefixes suffix_key] suffix_value]. *)
    (*     simpl fst in H0. *)
    (*     destruct suffix_key as [suffix_key | ]; simpl in H8; try solve [inv H9]. *)
    (*     simpl in H9. *)
    (*     subst. *)
    (*     simpl BorderNode.get_suffix in H0. *)
    (*     cbv iota beta in H0. *)
    (*     rewrite H7 in H0. *)
    (*     repeat eliminate_hyp; subst. *)
    (*     + simpl in H0. *)
    (*       eliminate_hyp. *)
    (*       change (next_cursor_bnode BorderNode.before_suffix (prefixes, None, trie_of t') *)
    (*                                 (Z.to_nat (keyslice_length + 2))) with BorderNode.before_suffix in H0. *)
    (*       simpl in H0. *)
    (*       (* [strict_first_cursor] should be [Some] *) *)
    (*       admit. *)
    (*     + rename c0 into tc. *)
    (*       rename b into bc. *)
    (*       rename t into b. *)
    (*       simpl. *)
    (* Admitted. *)


    Ltac eliminate_hyp :=
      match goal with
      | [H: match ?e with _ => _ end |- _] =>
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: _ = match ?e with _ => _ end |- _] =>
        let H := fresh "Heqn" in
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: match ?e with _ => _ end = _ |- _] =>
        let H := fresh "Heqn" in
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: _ /\ _ |- _ ] => destruct H
      | [H: Some _ = Some _ |- _ ] => inv H
      | [H: trie_correct (trienode_of _ _ _) |- _ ] => inv H
      | [|- context[if _ then _ else _] ] =>
        first [
              rewrite if_true by (first [solve [eauto with trie] | KeysliceFacts.order])
            | rewrite if_false by (first [solve [eauto with trie] | KeysliceFacts.order])
          ]
      end.

    Hint Resolve Node.Flattened.make_cursor_abs: trie.
    Hint Resolve Node.Flattened.first_cursor_abs: trie.
    Hint Resolve Node.Flattened.last_cursor_abs: trie.
    Hint Resolve Node.Flattened.make_cursor_key: trie.
    Hint Resolve Node.Flattened.eq_cursor_get: trie.
    Hint Resolve Node.Flattened.key_rel_eq_cursor: trie.
    Hint Resolve Node.Flattened.put_correct: trie.
    Hint Resolve Node.Flattened.empty_correct: trie.
    Hint Resolve Node.Flattened.simple_empty_correct: trie.
    Hint Resolve Node.make_cursor_abs: trie.
    Hint Resolve Node.first_cursor_abs: trie.
    Hint Resolve Node.last_cursor_abs: trie.
    Hint Resolve Node.make_cursor_key: trie.
    Hint Resolve Node.eq_cursor_get: trie.
    Hint Resolve Node.key_rel_eq_cursor: trie.
    Hint Resolve Node.put_correct: trie.
    Hint Resolve Node.empty_correct: trie.
    Hint Resolve BorderNode.empty_invariant: trie.
    Hint Resolve BorderNode.put_prefix_invariant: trie.
    Hint Unfold Node.Flattened.get_key: trie.
    Hint Unfold Node.Flattened.get_value: trie.
    Hint Unfold Node.Flattened.get_exact: trie.

    Ltac basic_trie_solve :=
      autounfold with trie in *; repeat eliminate_hyp;
      try first [ solve [eauto 10 with trie] | rep_omega | congruence].

    Opaque Node.Flattened.put get_keyslice reconstruct_keyslice get_suffix.

    Lemma get_exact_correct: forall {value: Type} k (t: Node.Flattened.table value) bnode,
        Node.Flattened.get_exact k t = Some bnode ->
        Node.Flattened.get (Node.Flattened.make_cursor k t) t = Some (k, bnode).
    Proof.
      intros.
      basic_trie_solve; simplify.
    Qed.

    Lemma get_exact_correct_key: forall {value: Type} k (t: Node.Flattened.table value) bnode,
        Node.Flattened.get_exact k t = Some bnode ->
        Node.Flattened.get_key (Node.Flattened.make_cursor k t) t = Some k.
    Proof.
      intros.
      basic_trie_solve; simplify.
    Qed.

    Lemma get_exact_correct_value: forall {value: Type} k (t: Node.Flattened.table value) bnode,
        Node.Flattened.get_exact k t = Some bnode ->
        Node.Flattened.get_value (Node.Flattened.make_cursor k t) t = Some bnode.
    Proof.
      intros.
      basic_trie_solve; simplify.
    Qed.

    Lemma get_exact_correct_table_key: forall k addr tableform listform bnode,
        trie_correct (trienode_of addr tableform listform) ->
        Node.Flattened.get_exact k listform = Some bnode ->
        Node.get_key (Node.make_cursor k tableform) tableform = Some k.
    Proof.
      intros.
      basic_trie_solve.
      simplify.
      replace (Node.get_key (Node.make_cursor k0 tableform) tableform) with
          (Node.Flattened.get_key (Node.Flattened.make_cursor k0 (Node.flatten tableform)) (Node.flatten tableform)).
      - unfold Node.Flattened.get_key.
        replace (Some k0) with
            (Node.Flattened.get_key (Node.Flattened.make_cursor k0 listform) listform) by
            (unfold Node.Flattened.get_key; match_tac; simplify).
        pose proof (Node.flatten_invariant _ H3) as [? _].
        apply Node.Flattened.same_key_result with k0; basic_trie_solve.
      - symmetry.
        unfold Node.get_key, Node.Flattened.get_key.
        pose proof (Node.flatten_invariant _ H3) as [? ?].
        specialize (H0 k0
                       (Node.make_cursor k0 tableform)
                       (Node.Flattened.make_cursor k0 (Node.flatten tableform))).
        specialize (H0 ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve)).
        rewrite H0.
        reflexivity.
    Qed.

    Lemma table_key_list_key: forall k addr tableform listform,
        trie_correct (trienode_of addr tableform listform) ->
        Node.get_key (Node.make_cursor k tableform) tableform =
        Node.Flattened.get_key (Node.Flattened.make_cursor k listform) listform.
    Proof.
      intros.
      basic_trie_solve.
      pose proof (@Node.flatten_invariant val).
      specialize (H tableform ltac:(assumption)) as [? ?].
      replace (Node.get_key (Node.make_cursor k tableform) tableform) with
          (Node.Flattened.get_key (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)).
      2: {
        unfold Node.Flattened.get_key, Node.get_key.
        specialize (H0 k
                       (Node.make_cursor k tableform)
                       (Node.Flattened.make_cursor k (Node.flatten tableform))).
        specialize (H0 ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve)).
        rewrite H0.
        reflexivity.
      }
      apply Node.Flattened.same_key_result with k; basic_trie_solve.
    Qed.

    (* Lemma table_addr_list_addr: forall k tableform listform, *)
    (*     table_correct (trienode_of tableform listform) -> *)
    (*     Node.get_key (Node.make_cursor k tableform) tableform = *)
    (*     Node.Flattened.get_key (Node.Flattened.make_cursor k listform) listform -> *)
    (*     Node.get_value (Node.make_cursor k tableform) tableform = *)
    (*     match Node.Flattened.get_exact (Node.Flattened.make_cursor k listform) listform with *)
    (*     | Some (addr, _) => Some addr *)
    (*     | None => None *)
    (*     end. *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold Node.get_key, Node.get_value, Node.Flattened.get_exact, Node.Flattened.get_key in *. *)
    (*   basic_trie_solve. *)
    (*   -  *)
    (*   pose proof (@Node.flatten_invariant val). *)
    (*   specialize (H tableform ltac:(assumption)) as [? ?]. *)
    (*   replace (Node.get_key (Node.make_cursor k tableform) tableform) with *)
    (*       (Node.Flattened.get_key (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)). *)
    (*   2: { *)
    (*     unfold Node.Flattened.get_key, Node.get_key. *)
    (*     specialize (H0 k *)
    (*                    (Node.make_cursor k tableform) *)
    (*                    (Node.Flattened.make_cursor k (Node.flatten tableform))). *)
    (*     specialize (H0 ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve)). *)
    (*     rewrite H0. *)
    (*     reflexivity. *)
    (*   } *)
    (*   apply Node.Flattened.same_key_result with k; basic_trie_solve. *)
    (* Qed. *)

    Lemma leaves_correct_bordernode_correct: forall bnode listform c,
        Forall (compose bordernode_correct snd) listform ->
        Node.Flattened.get_value c listform = Some bnode ->
        bordernode_correct bnode.
    Proof.
      intros.
      unfold Node.Flattened.get_value in H0.
      destruct (Node.Flattened.get c listform) as [[] | ] eqn:Heqn; try congruence.
      inv H0.
      pose proof (Node.Flattened.get_in_weak listform c k bnode Heqn).
      rewrite Forall_forall in H.
      apply H in H0.
      simpl in H0.
      assumption.
    Qed.
    Hint Resolve leaves_correct_bordernode_correct: trie.

    Lemma leaves_correct_bordernode_correct': forall bnode listform k c v,
        Forall (compose bordernode_correct (compose (@snd val _) snd)) listform ->
        Node.Flattened.get c listform = Some (k, (v, bnode)) ->
        bordernode_correct bnode.
    Proof.
      intros.
      destruct (Node.Flattened.get c listform) as [[? []] | ] eqn:Heqn; try congruence.
      inv H0.
      pose proof (Node.Flattened.get_in_weak listform _ k (v, bnode) Heqn).
      rewrite Forall_forall in H.
      apply H in H0.
      simpl in H0.
      assumption.
    Qed.
    Hint Resolve leaves_correct_bordernode_correct': trie.

    Lemma bordernode_correct_invariant: forall bnode,
        bordernode_correct bnode -> BorderNode.invariant bnode.
    Proof.
      intros.
      inv H; unfold BorderNode.invariant; simpl; list_solve.
    Qed.
    Hint Resolve bordernode_correct_invariant: trie.

    Lemma bordernode_correct_subtrie_correct: forall prefixes t,
        bordernode_correct (prefixes, Some (inr t)) ->
        trie_correct t.
    Proof.
      intros.
      inv H.
      assumption.
    Qed.
    Hint Resolve bordernode_correct_subtrie_correct: trie.

    Ltac trie_solve :=
      repeat match goal with
      | [|- context [Node.Flattened.get_key (Node.Flattened.make_cursor _ _) _]] =>
        try solve [erewrite get_exact_correct_key by eauto];
        idtac
      | [|- context [Node.get_key (Node.make_cursor _ _) _]] =>
        try solve [erewrite get_exact_correct_table_key by eauto];
        idtac
      | [|- context [BorderNode.get_prefix _ (BorderNode.put_prefix _ _ _)]] =>
        try first [
              rewrite BorderNode.get_put_prefix_same by basic_trie_solve
            | rewrite BorderNode.get_put_prefix_diff by basic_trie_solve
            ]
      | [H: Node.Flattened.put _ _ _ _ _ ?l |- context [Node.Flattened.get _ ?l]] =>
        try first [
              erewrite Node.Flattened.get_put_same by basic_trie_solve
            ]
      | [H: Node.put _ _ _ _ _ ?l |- context [Node.get _ ?l]] =>
        try first [
              erewrite Node.get_put_same by basic_trie_solve
            ]
      end;
      basic_trie_solve.

    Lemma create_pair_normalized: forall k1 k2 v1 v2 c t,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        create_pair k1 k2 v1 v2 c t ->
        normalize_cursor (make_cursor k1 t) =
        Some (make_cursor k1 t).
    Proof.
      intros k1.
      remember (length k1) as n.
      generalize dependent k1.
      induction n using (well_founded_induction lt_wf); intros.
      inv H3;
        unfold keyslice1, keyslice2 in *; clear keyslice1 keyslice2.
      destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1];
        destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2];
        try omega; clear H5; subst bnode bnode0.
      - assert (Zlength k1 <> Zlength k2) by admit.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        unfold BorderNode.put_value.
        trie_solve.
        unfold normalize_cursor.
        rewrite BorderNode.next_cursor_terminate_permute1 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        trie_solve.
      - rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        trie_solve.
        rewrite BorderNode.next_cursor_terminate_permute2 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        trie_solve.
      - rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        rewrite ?if_false by auto.
        unfold BorderNode.put_value.
        trie_solve.
        simpl.
        rewrite if_false by TrieKeyFacts.order.
        simpl.
        change (BorderNode.next_cursor BorderNode.before_suffix
                                       (upd_Znth (Zlength k2 - 1) (list_repeat (Z.to_nat keyslice_length) None) (Some v2), Some (inl (get_suffix k1, v1))))
          with (BorderNode.before_suffix).
        reflexivity.
      - rewrite make_cursor_equation.
        simpl.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        eapply H with (y := length (get_suffix k1)) in H6;
          trie_solve;
          change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k) in *;
          simpl in *.
        + rewrite H6.
          reflexivity.
        + rewrite <- ?ZtoNat_Zlength.
          rewrite Zlength_sublist by rep_omega.
          apply Z2Nat.inj_lt; rep_omega.
        + rewrite Zlength_sublist; rep_omega.
        + rewrite Zlength_sublist; rep_omega.
        + admit.
      - subst bnode1 bnode2.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate; trie_solve.
        + unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          simpl.
          rewrite ?if_false by auto.
          simpl.
          change (BorderNode.next_cursor
                    BorderNode.before_suffix
                    (list_repeat (Z.to_nat keyslice_length) None, Some (inl (get_suffix k1, v1))))
            with (BorderNode.before_suffix).
          reflexivity.
    Admitted.

    Lemma make_cursor_put_normalized: forall k v c1 t1 c2 t2,
        Zlength k <> 0 ->
        trie_correct t1 ->
        put k v c1 t1 c2 t2 ->
        normalize_cursor (make_cursor k t2) = Some (make_cursor k t2).
    Proof.
      intros k.
      remember (length k) as n.
      generalize dependent k.
      induction n using (well_founded_induction lt_wf); intros.
      inv H2; inv H1.
      - unfold keyslice in *; clear keyslice.
        rewrite make_cursor_equation.
        simpl.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        subst bnode0.
        rewrite BorderNode.next_cursor_terminate; trie_solve.
      - unfold keyslice in *; clear keyslice.
        unfold bnode0 in *; clear bnode0.
        unfold BorderNode.get_link in *.
        destruct bnode as [? [[|]|]]; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        trie_solve.
        unfold BorderNode.get_suffix_pair.
        simpl.
        eapply H with (y := length (get_suffix k)) in H6; trie_solve.
        * rewrite H6.
          reflexivity.
        * rewrite <- ?ZtoNat_Zlength.
           change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
           rewrite Zlength_sublist by rep_omega.
           apply Z2Nat.inj_lt; rep_omega.
        * change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
          rewrite Zlength_sublist; rep_omega.
      - unfold keyslice in *; clear keyslice.
        unfold bnode0 in *; clear bnode0.
        destruct bnode as [? [|]]; simpl in *; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        trie_solve.
        unfold BorderNode.get_suffix_pair.
        simpl.
        trie_solve.
      - unfold keyslice in *; clear keyslice.
        unfold bnode0 in *; clear bnode0.
        unfold BorderNode.test_suffix in H5.
        destruct bnode as [? [[|]|]]; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        trie_solve.
        unfold BorderNode.get_suffix_pair; simpl.
        trie_solve.
      - unfold keyslice in *; clear keyslice.
        unfold bnode0 in *; clear bnode0.
        destruct bnode as [? [[|]|]]; simplify.
        rewrite make_cursor_equation.
        simpl.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        eapply create_pair_normalized in H7; change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k) in *; simpl in *.
        + rewrite H7.
          reflexivity.
        + rewrite Zlength_sublist; rep_omega.
        + assert (bordernode_correct (l, Some (inl (s, v0)))) by trie_solve.
          inv H1.
          simplify.
        + assumption.
      - unfold keyslice in *; clear keyslice.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        if_tac.
        + simpl.
          subst bnode.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate by trie_solve.
          reflexivity.
        + subst bnode.
          unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          unfold BorderNode.get_suffix_pair; simpl.
          trie_solve.
    Qed.

    (* Lemma create_pair_correct: forall k1 k2 v1 v2 a, *)
    (*     table_correct (fst (create_pair k1 k2 v1 v2 a)). *)
    (* Proof. *)
    (*   intros k1. *)
    (*   remember (length k1) as n. *)
    (*   generalize dependent k1. *)
    (*   induction n using (well_founded_induction lt_wf); intros. *)
    (*   rewrite create_pair_equation. *)
    (*   destruct (@Node.empty val a) eqn:Heqn_empty. *)
    (*   replace t with (fst (@Node.empty val a)) by (rewrite Heqn_empty; reflexivity). *)
    (*   destruct (consume a0) eqn:Heqn_consume0. *)
    (*   if_tac. *)
    (*   destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1]; *)
    (*     destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2]; *)
    (*     try if_tac; try omega. *)
    (*   - destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l)) *)
    (*       as [? []] eqn:Heqn_node_put. *)
    (*     replace t0 with *)
    (*       (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l)))) *)
    (*       by (rewrite Heqn_node_put; reflexivity). *)
    (*     simpl. *)
    (*     constructor; trie_solve. *)
    (*     + rewrite NodeFacts.simple_put_permute by trie_solve. *)
    (*       rewrite NodeFacts.empty_flatten_empty. *)
    (*       change (@Node.Flattened.put) with *)
    (*           (fun (elt : Type) (k : Node.Flattened.key) (v : elt) (c : Node.Flattened.cursor elt) *)
    (*              (table_with_allocator : Node.Flattened.table elt * Node.Flattened.allocator) => *)
    (*              let (t, a) := table_with_allocator in (c, (Node.Flattened.put_aux k v t, a)) *)
    (*           ). *)
    (*       simpl. *)
    (*       reflexivity. *)
    (*     + change (@Node.Flattened.put) with *)
    (*           (fun (elt : Type) (k : Node.Flattened.key) (v : elt) (c : Node.Flattened.cursor elt) *)
    (*              (table_with_allocator : Node.Flattened.table elt * Node.Flattened.allocator) => *)
    (*              let (t, a) := table_with_allocator in (c, (Node.Flattened.put_aux k v t, a)) *)
    (*           ). *)
    (*       simpl. *)
    (*       repeat constructor. *)
    (*       simpl. *)
    (*       admit. *)
    (*     + admit. *)
    (*   - *)
    (* Admitted. *)

    (* Lemma create_pair_abs: forall k1 k2 v1 v2 a, *)
    (*     0 < Zlength k1 -> *)
    (*     0 < Zlength k2 -> *)
    (*     k1 <> k2 -> *)
    (*     abs_rel (make_cursor k1 (fst (create_pair k1 k2 v1 v2 a))) (fst (create_pair k1 k2 v1 v2 a)). *)
    (* Proof. *)
    (*   intros. *)

    Lemma get_create_same1: forall k1 k2 c' v1 v2 c t,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        create_pair k1 k2 v1 v2 c t ->
        cursor_trie_assoc c' t ->
        key_rel k1 c' t ->
        get c' t = Some (k1, v1).
    Proof.
      intros k1.
      remember (length k1) as n.
      generalize dependent k1.
      induction n using (well_founded_induction lt_wf); intros.
      unfold get.
      unfold key_rel in H5.
      rewrite H5.
      inv H3.
      destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1];
        destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2];
        try omega; clear H7; subst bnode bnode0.
      - unfold keyslice1 in *; clear keyslice1.
        assert (Zlength k1 <> Zlength k2) by admit.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        trie_solve.
        rewrite BorderNode.next_cursor_terminate_permute1 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        trie_solve.
        simpl.
        unfold Node.get_key.
        trie_solve.
        rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
        rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
        admit.
      - unfold keyslice1, keyslice2 in *; clear keyslice1 keyslice2.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        trie_solve.
        rewrite BorderNode.next_cursor_terminate_permute2 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        trie_solve.
        simpl.
        unfold Node.get_key.
        trie_solve.
        rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
        admit.
      - unfold keyslice1, keyslice2 in *; clear keyslice1 keyslice2.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        rewrite ?if_false by auto.
        unfold BorderNode.put_value.
        trie_solve.
        simpl.
        rewrite if_false by TrieKeyFacts.order.
        simpl.
        change (BorderNode.next_cursor
                  BorderNode.before_suffix
                  (upd_Znth (Zlength k2 - 1) (list_repeat (Z.to_nat keyslice_length) None) (Some v2), Some (inl (get_suffix k1, v1))))
          with (BorderNode.before_suffix).
        simpl.
        unfold Node.get_key.
        trie_solve.
        admit.
      - unfold keyslice1, keyslice2 in *; clear keyslice1 keyslice2.
        rewrite make_cursor_equation.
        simpl.
        unfold Node.Flattened.get_exact.
        trie_solve.
        simpl.
        pose proof H8.
        eapply create_pair_normalized in H8;
          try solve [
                change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                simpl;
                rewrite ?Zlength_sublist; rep_omega].
        2: { admit. } (* [get_suffix k1 <> get_suffix k2] *)
        rewrite H8.
        simpl.
        unfold Node.get_key.
        trie_solve.
        unfold get in H.
        assert (match normalize_cursor (make_cursor (get_suffix k1) t') with
                | Some c'0 => get_raw c'0
                | None => None
                end = Some (get_suffix k1, v1)). {
          eapply H with (y := length (get_suffix k1)) (k2 := (get_suffix k2)) (v2 := v2) in H13;
          try solve [
                change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                simpl;
                rewrite <- ?ZtoNat_Zlength;
                rewrite ?Zlength_sublist; rep_omega].
          - apply H13.
          - admit.
          - admit. (* result of [make_cursor_abs] *)
          - admit. (* result of [make_cursor_key] *)
        }
        eapply create_pair_normalized in H13;
          try solve [
                change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                simpl;
                rewrite ?Zlength_sublist; rep_omega].
        2: { admit. }
        rewrite H13 in H14.
        rewrite H14.
        admit.
      - unfold keyslice1, keyslice2 in *; clear keyslice1 keyslice2.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        trie_solve.
        subst bnode1.
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate; trie_solve.
          simpl.
          unfold Node.get_key.
          trie_solve.
          rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
          admit.
        + unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          simpl.
          rewrite ?if_false by auto.
          simpl.
          change (BorderNode.next_cursor
                    BorderNode.before_suffix
                    (list_repeat (Z.to_nat keyslice_length) None, Some (inl (get_suffix k1, v1))))
            with (BorderNode.before_suffix).
          simpl.
          unfold Node.get_key.
          trie_solve.
          admit.
    Admitted.

    Theorem get_put_same: forall t1 t2 c1 c2 c3 k v,
        Zlength k <> 0 ->
        put k v c1 t1 c2 t2 ->
        cursor_trie_assoc c1 t1 ->
        cursor_trie_assoc c3 t2 ->
        key_rel k c3 t2 ->
        get c3 t2 = Some (k, v).
    Proof.
      intros.
      destruct H1 as [? []].
      clear H1 H5.
      remember (length k) as n.
      generalize dependent t1.
      generalize dependent t2.
      generalize dependent c1.
      generalize dependent c2.
      generalize dependent c3.
      generalize dependent v.
      generalize dependent k.
      induction n using (well_founded_induction lt_wf); intros.
      unfold get.
      unfold key_rel in H3.
      rewrite H3.
      inv H1.
      - subst bnode0 keyslice.
        inv H4.
        simpl.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        rewrite ?if_true by auto.
        simpl.
        rewrite BorderNode.next_cursor_terminate by trie_solve.
        simpl.
        erewrite get_exact_correct_table_key by eauto with trie.
        rewrite BorderNode.get_put_prefix_same by trie_solve.
        f_equal.
        admit.
      - subst keyslice bnode0.
        unfold BorderNode.get_link in H7.
        destruct bnode as [? [ [|] | ]]; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        rewrite ?if_false by auto.
        unfold BorderNode.get_suffix_pair, BorderNode.get_suffix.
        simpl.
        pose proof H8.
        eapply make_cursor_put_normalized in H8;
          try solve [ trie_solve
                    | change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                     simpl; rewrite ?Zlength_sublist; rep_omega].
        rewrite H8.
        simpl.
        erewrite get_exact_correct_table_key by eauto with trie.
        unfold get in H.
        assert (match normalize_cursor (make_cursor (get_suffix k) t'') with
                | Some c' => get_raw c'
                | None => None
                end = Some (get_suffix k, v)). {
          eapply H with
              (y := (length (get_suffix k)))
              (c3 := (make_cursor (get_suffix k) t'')) in H1;
            try solve [ trie_solve
                      | change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                        simpl; rewrite ?Zlength_sublist; rep_omega].
          - change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k); simpl.
            rewrite <- ?ZtoNat_Zlength.
            rewrite Zlength_sublist by rep_omega.
            apply Z2Nat.inj_lt; rep_omega.
          - admit. (* result of [make_cursor_abs] *)
        }
        eapply make_cursor_put_normalized in H1;
          try solve [ trie_solve
                    | change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                     simpl; rewrite ?Zlength_sublist; rep_omega].
        rewrite H1 in H7.
        rewrite H7.
        f_equal.
        f_equal.
        admit.
      - subst keyslice bnode0.
        destruct bnode as [? [ | ]]; simpl in *; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        rewrite ?if_false by auto.
        simpl.
        rewrite ?if_false by auto.
        simpl.
        change (BorderNode.next_cursor BorderNode.before_suffix (l, Some (inl (get_suffix k, v)))) with
            (BorderNode.before_suffix).
        simpl.
        erewrite get_exact_correct_table_key by eauto with trie.
        f_equal.
        admit.
      - subst keyslice bnode0.
        simpl.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        rewrite ?if_false by auto.
        destruct bnode as []; simplify.
        simpl.
        rewrite ?if_false by auto.
        simpl.
        change (BorderNode.next_cursor BorderNode.before_suffix (l, Some (inl (get_suffix k, v)))) with
            (BorderNode.before_suffix).
        simpl.
        erewrite get_exact_correct_table_key by eauto with trie.
        f_equal.
        admit.
      - subst keyslice bnode0.
        destruct bnode as [? [ [|] | ]]; simplify.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        rewrite ?if_false by auto.
        simpl.
        pose proof H5.
        apply get_exact_correct in H5.
        apply Node.Flattened.get_in_weak in H5.
        pose proof H4.
        inv H4.
        eapply Forall_forall in H20; [ | solve [eauto]].
        simpl in H20.
        inv H20.
        unfold BorderNode.get_suffix_pair in H7.
        simplify.
        pose proof H9.
        eapply create_pair_normalized in H9;
          try solve [ trie_solve
                    | change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                      simpl; rewrite ?Zlength_sublist; rep_omega].
        rewrite H9.
        simpl.
        erewrite get_exact_correct_table_key by eauto with trie.
        eapply get_create_same1 in H4;
          try solve [ trie_solve
                    | change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                      simpl; rewrite ?Zlength_sublist; rep_omega].
        + unfold get in H4.
          rewrite H9 in H4.
          rewrite H4.
          f_equal.
          admit.
        + admit. (* result of [make_cursor_abs] *)
        + admit. (* result of [make_cursor_key] *)
      - subst keyslice bnode.
        rewrite make_cursor_equation.
        unfold Node.Flattened.get_exact.
        erewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by KeysliceFacts.order.
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate by trie_solve.
          simpl.
          unfold Node.get_key.
          erewrite Node.get_put_same by trie_solve.
          rewrite upd_Znth_same by list_solve.
          f_equal.
          admit.
        + unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          simpl.
          rewrite ?if_false by TrieKeyFacts.order.
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix (list_repeat (Z.to_nat keyslice_length) None, Some (inl (get_suffix k, v))))
            with (BorderNode.before_suffix).
          simpl.
          unfold Node.get_key.
          erewrite Node.get_put_same by trie_solve.
          f_equal.
          admit.
    Admitted.

    Theorem table_exact_list_exact_none: forall addr tableform listform k,
        trie_correct (trienode_of addr tableform listform) ->
        Node.get_exact k tableform = None <->
        Node.Flattened.get_exact k listform = None.
    Proof.
      intros.
      inv H.
      split; intros.
      - rewrite NodeFacts.get_exact_eq in H by assumption.
        unfold Node.Flattened.get_exact in *.
        pose proof (Node.flatten_invariant tableform H3) as [? ?].
        pose proof (Node.Flattened.same_key_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k (Node.flatten tableform))
                      (Node.Flattened.make_cursor k listform)
                      k
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)).
        unfold Node.Flattened.get_key in H2.
        destruct (Node.Flattened.get (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)) as [[] | ] eqn:Heqn;
          destruct (Node.Flattened.get (Node.Flattened.make_cursor k listform) listform) as [[? []] | ] eqn:Heqn'; try reflexivity.
        + inv H2.
          if_tac in H; congruence.
        + inv H2.
      - rewrite NodeFacts.get_exact_eq by assumption.
        unfold Node.Flattened.get_exact in *.
        pose proof (Node.flatten_invariant tableform H3) as [? ?].
        pose proof (Node.Flattened.same_key_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k (Node.flatten tableform))
                      (Node.Flattened.make_cursor k listform)
                      k
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)).
        unfold Node.Flattened.get_key in H2.
        destruct (Node.Flattened.get (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)) as [[] | ] eqn:Heqn;
          destruct (Node.Flattened.get (Node.Flattened.make_cursor k listform) listform) as [[? []] | ] eqn:Heqn'; try reflexivity.
        + inv H2.
          if_tac in H; congruence.
        + inv H2.
    Qed.

    Theorem table_exact_list_exact_some: forall addr tableform listform k bnode_addr,
        trie_correct (trienode_of addr tableform listform) ->
        Node.get_exact k tableform = Some bnode_addr <->
        exists bnode: bordernode, Node.Flattened.get_exact k listform = Some (bnode_addr, bnode).
    Proof.
      intros.
      inv H.
      split; intros.
      - rewrite NodeFacts.get_exact_eq in H by assumption.
        unfold Node.Flattened.get_exact in *.
        pose proof (Node.flatten_invariant tableform H3) as [? ?].
        pose proof (Node.Flattened.same_key_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k (Node.flatten tableform))
                      (Node.Flattened.make_cursor k listform)
                      k
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)).
        pose proof H2.
        unfold Node.Flattened.get_key in H2.
        destruct (Node.Flattened.get (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)) as [[] | ] eqn:Heqn;
          destruct (Node.Flattened.get (Node.Flattened.make_cursor k listform) listform) as [[? []] | ] eqn:Heqn'; try congruence.
        inv H2.
        if_tac in H; try congruence.
        subst.
        inv H.
        pose proof (Node.Flattened.same_value_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k1 (Node.flatten tableform))
                      (Node.Flattened.make_cursor k1 listform)
                      k1
                      fst
                      (v0, t)
                      ltac:(assumption)
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(assumption)).
        specialize (H ltac:(unfold Node.Flattened.get_value; rewrite Heqn'; reflexivity)).
        simpl in H.
        exists t.
        unfold Node.Flattened.get_value in H.
        rewrite Heqn in H.
        inv H.
        reflexivity.
      - destruct H as [bnode ?].
        rewrite NodeFacts.get_exact_eq by assumption.
        unfold Node.Flattened.get_exact in *.
        pose proof (Node.flatten_invariant tableform H3) as [? ?].
        pose proof (Node.Flattened.same_key_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k (Node.flatten tableform))
                      (Node.Flattened.make_cursor k listform)
                      k
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)).
        pose proof H2.
        unfold Node.Flattened.get_key in H2.
        destruct (Node.Flattened.get (Node.Flattened.make_cursor k (Node.flatten tableform)) (Node.flatten tableform)) as [[] | ] eqn:Heqn;
          destruct (Node.Flattened.get (Node.Flattened.make_cursor k listform) listform) as [[? []] | ] eqn:Heqn'; try congruence.
        inv H2.
        if_tac in H; try congruence.
        subst.
        inv H.
        pose proof (Node.Flattened.same_value_result
                      (Node.flatten tableform) listform
                      (Node.Flattened.make_cursor k1 (Node.flatten tableform))
                      (Node.Flattened.make_cursor k1 listform)
                      k1
                      fst
                      (bnode_addr, bnode)
                      ltac:(assumption)
                      ltac:(assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(apply Node.Flattened.make_cursor_key; assumption)
                      ltac:(apply Node.Flattened.make_cursor_abs; assumption)
                      ltac:(assumption)).
        specialize (H ltac:(unfold Node.Flattened.get_value; rewrite Heqn'; reflexivity)).
        simpl in H.
        unfold Node.Flattened.get_value in H.
        rewrite Heqn in H.
        inv H.
        reflexivity.
    Qed.
  End Types.

  Arguments bordernode: clear implicits.
  Arguments trie: clear implicits.
  Arguments cursor: clear implicits.
End Trie.
