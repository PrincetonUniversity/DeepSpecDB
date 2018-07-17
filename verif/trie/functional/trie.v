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

    (* this is only a pseudo height, cause we only care about termination *)
    Fixpoint trie_height (t: trie): nat :=
      let link_height (l: link): nat :=
      match l with
      | value_of _ => O
      | trie_of t => trie_height t
      | nil => O
      end
      in
      let bnode_height (bnode: BorderNode.table): nat :=
      match bnode with
      | (prefixes, _, suffix) =>
        Nat.max O (link_height suffix)
      end
      in
      match t with
      | trienode_of tableform listform =>
        1 + fold_right Nat.max O (map (compose bnode_height snd) listform)
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

    (* for this function, [after_suffix] actually means a fail *)
    Fixpoint next_cursor_bnode (bnode_cursor: bordernode_cursor) (bnode: BorderNode.table) (n: nat) :=
      match n with
      | S n' =>
        match bnode_cursor with
        | before_prefix len =>
          match (BorderNode.get_prefix len bnode) with
          | nil =>
            if Z_lt_dec len keyslice_length then
              next_cursor_bnode (before_prefix (len + 1)) bnode n'
            else
              next_cursor_bnode before_suffix bnode n'
          | _ => before_prefix len
          end
        | before_suffix =>
          match (snd (BorderNode.get_suffix_pair bnode)) with
          | nil => after_suffix
          | _ => before_suffix
          end
        | after_suffix => after_suffix
        end
      | O => after_suffix
      end.

    Function strict_first_cursor (t: trie) {measure trie_height t}: option cursor :=
      match t with
      | trienode_of tableform listform =>
        match Node.Flattened.get_value (Node.Flattened.first_cursor listform) listform with
        | Some bnode =>
          match next_cursor_bnode (before_prefix 0) bnode (Z.to_nat (keyslice_length + 2)) with
          | before_prefix len =>
            match (BorderNode.get_prefix len bnode) with
            | trie_of t' => None (* ill-formed *)
            | value_of _ =>
              Some [(t, Node.first_cursor tableform, bnode, before_prefix len)]
            | nil => None
            end
          | before_suffix =>
            match snd (BorderNode.get_suffix_pair bnode) with
            | trie_of t' =>
              match strict_first_cursor t' with
              | Some c' => Some ((t, Node.first_cursor tableform, bnode, before_suffix) :: c')
              | None => None
              end
            | value_of _ =>
              Some [(t, Node.first_cursor tableform, bnode, before_suffix)]
            | nil => None
            end
          | after_suffix => None
          end
        | None => None
        end
      end.
    Proof.
      intros.
      simpl.
      apply Nat.lt_succ_r.
      apply fold_max_le.
      clear teq1.
      assert (exists k, Node.Flattened.get (Node.Flattened.first_cursor listform) listform = Some (k, bnode)). {
        unfold Node.Flattened.get_value in teq0.
        destruct (Node.Flattened.get (Node.Flattened.first_cursor listform) listform) eqn:Heqn.
        + destruct p.
          exists k.
          inv teq0.
          reflexivity.
        + inv teq0.
      }
      destruct H.
      apply Node.Flattened.get_in_weak in H.
      + apply in_map with (f :=
                             (compose
                                (fun bnode0 : BorderNode.table =>
                                   let (p, suffix) := bnode0 in
                                   let (_, _) := p in match suffix with
                                                      | trie_of t0 => trie_height t0
                                                      | _ => 0%nat
                                                      end) snd)) in H.
        simpl in H.
        unfold BorderNode.get_suffix_pair in teq2.
        destruct bnode as [[]].
        simpl in teq2.
        subst.
        assumption.
      + (* we need a stronger theorem about [first_cursor] and [abs_rel] for the list impl *)
        admit.
    Admitted.

    (* This [normalize_cursor] returns a cursor when there is a next one,
     * also, it tries to eliminate an [after_suffix] cursor position *)
    Fixpoint normalize_cursor (c: cursor): option cursor :=
      match c with
      | [] => None (* given an empty cursor, we can never return the next cursor *)
      | (trienode_of tableform listform, table_cursor, bnode, bnode_cursor) :: c' =>
        let t := trienode_of tableform listform in
        match normalize_cursor c' with
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
            | trie_of t' => None
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
            (* try move to next cursor at node level *)
            let table_cursor' := Node.next_cursor table_cursor tableform in
            match Node.get_key table_cursor' tableform with
            | Some key =>
              match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
              | Some bnode' =>
                (* no need to repeatedly move to next if we have maintained the invariant that no dead end exists
                 * in the trie *)
                match next_cursor_bnode (before_prefix 0) bnode' (Z.to_nat (keyslice_length + 2)) with
                | before_prefix len =>
                  match (BorderNode.get_prefix len bnode') with
                  | nil => (* impossible *) None
                  | value_of _ => Some [(t, table_cursor', bnode', (before_prefix len))]
                  | trie_of t' => None
                  end
                | before_suffix =>
                  match (snd (BorderNode.get_suffix_pair bnode')) with
                  | nil => (* impossible *) None
                  | value_of _ => Some [(t, table_cursor', bnode', before_suffix)]
                  | trie_of t' =>
                    match strict_first_cursor t' with
                    | Some c' =>
                      Some ((t, table_cursor', bnode', before_suffix) :: c')
                    | None =>
                      None
                    end
                  end
                | after_suffix => None
                end
              | None => None (* we cannot handle it at this level *)
              end
            | None => None
            end
          end
        end
      end.

    Definition list_get_error k t: option (@BorderNode.table link) :=
      match Node.Flattened.get (Node.Flattened.make_cursor k t) t with
      | Some (k', v) =>
        if KeysliceType.eq_dec k k' then
          Some v
        else
          None
      | None => None
      end.

    Function make_cursor (k: key) (t: trie) {measure length k}: cursor :=
      let keyslice := get_keyslice k in
      match t with
      | trienode_of tableform listform =>
        match list_get_error keyslice listform with
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

    Fixpoint reconstruct_key (c: cursor): key :=
      match c with
      | (trienode_of tableform _, table_cursor, _, bnode_cursor) :: c' =>
        let len := match bnode_cursor with
                   | before_prefix len => len
                   (* [after_suffix] does not make sense here *)
                   | _ => keyslice_length
                   end
        in 
        match Node.get_key table_cursor tableform with
        | Some keyslice =>
          reconstruct_keyslice (keyslice, len) ++ reconstruct_key c'
        | None =>
          []
        end
      | _ => []
      end.

    Fixpoint get_value_raw (c: cursor): option value :=
      match c with
      | (_, _, bnode, bnode_cursor) :: c' =>
        match bnode_cursor with
        | before_prefix len =>
          match BorderNode.get_prefix len bnode with
          | value_of v => Some v
          | trie_of t' => None (* impossible *)
          | nil => None
          end
        | before_suffix =>
          match (snd (BorderNode.get_suffix_pair bnode)) with
          | value_of v => Some v
          | trie_of t' => get_value_raw c'
          | nil => None
          end
        | after_suffix => None
        end
      | [] => None
      end.

    Definition get (c: cursor) (t: table): option (key * value) :=
      match normalize_cursor c with
      | Some c' =>
        match get_value_raw c' with
        | Some v => Some (reconstruct_key c', v)
        | None => None
        end
      | None => None
      end.

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

    Function create_pair (k1 k2: key) (v1 v2: value) (a: allocator) {measure length k1} : trie * allocator :=
      let keyslice1 := get_keyslice k1 in
      let keyslice2 := get_keyslice k2 in
      let emptylist := fst (Node.Flattened.empty []) in
      let (emptytable, a) := Node.empty a in
      if eq_dec keyslice1 keyslice2 then
        if create_pair_aux_dec k1 k2 then
          let bnode := BorderNode.put_value k1 (value_of v1) BorderNode.empty in
          let bnode := BorderNode.put_value k2 (value_of v2) bnode in
          let (bnode_addr, a) := consume a in
          let listform :=
              fst (snd (Node.Flattened.put keyslice1 bnode (Node.Flattened.first_cursor emptylist) (emptylist, [])))
          in
          let (tableform, a) := snd (Node.put keyslice1 bnode_addr (Node.first_cursor emptytable) (emptytable, a)) in
          (trienode_of tableform listform, a)
        else
          let (t', a) := create_pair (get_suffix k1) (get_suffix k2) v1 v2 a in
          let bnode := BorderNode.put_suffix None (trie_of t') BorderNode.empty in
          let (bnode_addr, a) := consume a in
          let listform :=
              fst (snd (Node.Flattened.put keyslice1 bnode (Node.Flattened.first_cursor emptylist) (emptylist, [])))
          in
          let (tableform, a) := snd (Node.put keyslice1 bnode_addr (Node.first_cursor emptytable) (emptytable, a)) in
          (trienode_of tableform listform, a)
      else
        let bnode1 := BorderNode.put_value k1 (value_of v1) BorderNode.empty in
        let bnode2 := BorderNode.put_value k2 (value_of v2) BorderNode.empty in
        let (bnode_addr1, a) := consume a in
        let (bnode_addr2, a) := consume a in
        let listform :=
            fst (snd (Node.Flattened.put keyslice1 bnode1 (Node.Flattened.first_cursor emptylist) (emptylist, []))) in
        let listform :=
            fst (snd (Node.Flattened.put keyslice2 bnode2 (Node.Flattened.first_cursor listform) (listform, []))) in
        let (tableform, a) := snd (Node.put keyslice1 bnode_addr1 (Node.first_cursor emptytable) (emptytable, a)) in
        let (tableform, a) := snd (Node.put keyslice2 bnode_addr2 (Node.first_cursor emptytable) (emptytable, a)) in
        (trienode_of tableform listform, a).
    Proof.
      intros.
      intros.
      unfold get_suffix.
      rewrite Nat2Z.inj_lt.
      rewrite <- ?Zlength_correct.
      destruct anonymous0.
      rewrite Zlength_sublist; repeat first [split | rep_omega | omega].
    Defined.

    Function put (k: key) (v: value) (c: cursor) (trie_with_allocator: trie * allocator) {measure length k}: (cursor * (trie * allocator)) :=
      let (t, a) := trie_with_allocator in
      let keyslice := get_keyslice k in
      match t with
      | trienode_of tableform listform =>
        match list_get_error keyslice listform with
        | Some bnode =>
          if (Z_le_dec) (Zlength k) (keyslice_length) then
            let bnode := BorderNode.put_prefix (Zlength k) (value_of v) bnode in
            let listform :=
                fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, [])))
            in
            (* overwrite prefix *)
            (c, (trienode_of tableform listform, a))
          else
            if BorderNode.is_link bnode then
              match BorderNode.get_suffix None bnode with
              | value_of _ => (c, empty a)
              | trie_of t' =>
                (* pass down to next layer *)
                let (t', a) := snd (put (get_suffix k) v c (t', a)) in
                let bnode := BorderNode.put_suffix None (trie_of t') bnode in
                let listform :=
                    fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, [])))
                in
                (c, (trienode_of tableform listform, a))
              | nil =>
                (* new suffix *)
                let bnode := BorderNode.put_suffix (Some (get_suffix k)) (value_of v) bnode in
                let listform :=
                    fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, [])))
                in
                (c, (trienode_of tableform listform, a))
              end
            else
              if BorderNode.test_suffix (Some (get_suffix k)) bnode then
                (* overwrite suffix *)
                let bnode := BorderNode.put_suffix (Some (get_suffix k)) (value_of v) bnode in
                let listform :=
                    fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, [])))
                in
                (c, (trienode_of tableform listform, a))
              else
                (* new layer with two suffix *)
                match BorderNode.get_suffix_pair bnode with
                | (Some k', l') =>
                  match l' with
                  | value_of v' =>
                    let (t', a) := create_pair (get_suffix k) k' v v' a in 
                    let bnode := BorderNode.put_suffix (Some (get_suffix k)) (trie_of t') bnode in
                    let listform :=
                        fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, [])))
                    in
                    (c, (trienode_of tableform listform, a))
                  | _ => (c, empty a)
                  end
                | (None, v') =>
                  (c, empty a)
                end
        | None =>
          (* TODO: new btree kv pair *)
          let bnode := BorderNode.put_value k (value_of v) BorderNode.empty in
          let listform :=
              fst (snd (Node.Flattened.put keyslice bnode (Node.Flattened.first_cursor listform) (listform, []))) in
          let (bnode_addr, a) := consume a in
          let (tableform, a) := snd (Node.put keyslice bnode_addr (Node.first_cursor tableform) (tableform, a)) in
          (c, (trienode_of tableform listform, a))
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

    (* This strict_next_cursor does not necessarily produce a valid position([after_suffix]) *)
    (* not sure if this work *)
    Fixpoint strict_next_cursor (c: cursor): cursor :=
      match c with
      | [] => []
      | [(trienode_of tableform listform, table_cursor, bnode, bnode_cursor)] =>
        match bnode_cursor with
        | before_prefix len =>
          if Z_lt_dec len keyslice_length then
            [(trienode_of tableform listform, table_cursor, bnode, before_prefix (len + 1))]
          else
            [(trienode_of tableform listform, table_cursor, bnode, after_suffix)]
        | before_suffix => [(trienode_of tableform listform, table_cursor, bnode, after_suffix)]
        | after_suffix =>
          let table_cursor' := Node.next_cursor table_cursor tableform in
          match Node.get_key table_cursor' tableform with
          | Some key =>
            match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
            | Some bnode' =>
              [(trienode_of tableform listform, table_cursor, bnode, before_prefix 0)]
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

    Definition is_value_or_nil (l: link) :=
      match l with
      | trie_of _ => False
      | _ => True
      end.

    Inductive table_correct: table -> Prop :=
    | table_correct_intro tableform listform:
        Node.table_correct tableform ->
        Node.Flattened.table_correct listform ->
        map fst (Node.flatten tableform) = map fst listform ->
        Forall (compose bordernode_correct snd) listform ->
        (* optional: no dangling(dead end) in the tree, useful for [next_cursor] and [first_cursor] *)
        Zlength listform > 0 ->
        table_correct (trienode_of tableform listform)
    with
    bordernode_correct: @BorderNode.table link -> Prop :=
    | bordernode_correct_intro prefixes (k: option string) l:
        Zlength prefixes = keyslice_length ->
        Forall (fun l => is_value_or_nil l) prefixes ->
        (k = None -> subtrie_correct l) ->
        (k <> None -> is_value_or_nil l) ->
        (* optional: no dangling(dead end) in the tree, useful for [next_cursor] and [first_cursor] *)
        (l <> nil \/ Exists (fun l => l <> nil) prefixes) ->
        bordernode_correct (prefixes, k, l)
    with
    subtrie_correct: link -> Prop :=
    | nil_correct: subtrie_correct nil
    | subtrie_correct_intro t:
        table_correct t ->
        subtrie_correct (trie_of t).

    Definition bordernode_cursor_correct (bnode_cursor: bordernode_cursor): Prop :=
      match bnode_cursor with
      | before_prefix len => 0 < len <= keyslice_length
      | _ => True
      end.

    Fixpoint cursor_correct_aux (c: cursor) (p: option trie): Prop :=
      match c with
      | (trienode_of tableform listform, table_cursor, bnode, bnode_cursor) :: c' =>
        match p with
        | Some t => t = trienode_of tableform listform
        | None => True
        end /\
        table_correct (trienode_of tableform listform) /\
        Node.cursor_correct table_cursor /\
        bordernode_cursor_correct bnode_cursor /\
        match Node.get_key table_cursor tableform with
        | Some key =>
          match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
          | Some bnode' =>
            bnode' = bnode /\
            match bnode_cursor with
            | before_prefix len =>
              match BorderNode.get_prefix len bnode with
              | trie_of t' => False
              | _ => c' = []
              end
            | before_suffix =>
              match (snd (BorderNode.get_suffix_pair bnode)) with
              | trie_of t' => cursor_correct_aux c' (Some t')
              | _ => c' = []
              end
            | after_suffix => c' = []
            end
          | None => False (* should not be the case in the only scenario of usage *)
          end
        | None => False (* there should be no cursor with a table cursor pointing at the end of table *)
        end
      | [] => True
      end.

    Definition cursor_correct (c: cursor): Prop := cursor_correct_aux c None.

    Definition abs_rel (c: cursor) (t: table): Prop :=
      cursor_correct c /\ table_correct t /\
      match c with
      | (t', _, _, _) :: _ =>
        (* This should suffice because the [cursor_correct] regulates the structure *)
        t' = t
      | [] => True
      end.

    Definition key_rel (k: key) (c: cursor) (t: table): Prop :=
      normalize_cursor c = normalize_cursor (make_cursor k t).
    Definition eq_cursor (c1 c2: cursor) (t: table): Prop. Admitted.

    Lemma next_cursor_bnode_prefix: forall bnode_cursor bnode len n,
        next_cursor_bnode bnode_cursor bnode n = before_prefix len ->
        BorderNode.get_prefix len bnode <> nil.
    Proof.
      intros.
      generalize dependent bnode_cursor.
      induction n; intros.
      - inv H.
      - simpl in H.
        destruct bnode_cursor.
        + destruct (BorderNode.get_prefix z bnode) eqn:Heqn; try congruence.
          if_tac in H.
          * apply IHn in H.
            assumption.
          * destruct n; simpl in H; try congruence.
            destruct (snd (BorderNode.get_suffix_pair bnode)); try congruence.
        + destruct (snd (BorderNode.get_suffix_pair bnode)); congruence.
        + congruence.
    Qed.

    Lemma next_cursor_bnode_suffix: forall bnode_cursor bnode n,
        next_cursor_bnode bnode_cursor bnode n = before_suffix ->
        snd (BorderNode.get_suffix_pair bnode) <> nil.
    Proof.
      intros.
      generalize dependent bnode_cursor.
      induction n; intros.
      - inv H.
      - simpl in H.
        destruct bnode_cursor.
        + destruct (BorderNode.get_prefix z bnode) eqn:Heqn; try congruence.
          if_tac in H.
          * apply IHn in H.
            assumption.
          * destruct n; simpl in H; try congruence.
            destruct (snd (BorderNode.get_suffix_pair bnode)); try congruence.            
        + destruct (snd (BorderNode.get_suffix_pair bnode)); congruence.
        + congruence.
    Qed.

    Definition bnode_cursor_to_nat (bnode_cursor: bordernode_cursor): nat :=
      match bnode_cursor with
      | before_prefix len => Z.to_nat len
      | before_suffix => Z.to_nat (keyslice_length + 1)
      | after_suffix => Z.to_nat (keyslice_length + 2)
      end.

    Lemma next_cursor_bnode_idempotent: forall bnode_cursor bnode_cursor' bnode,
        next_cursor_bnode bnode_cursor bnode (Z.to_nat (keyslice_length + 2)) = bnode_cursor' ->
        next_cursor_bnode bnode_cursor' bnode (Z.to_nat (keyslice_length + 2)) = bnode_cursor'.
    Proof.
      intros.
      remember (Z.to_nat (keyslice_length + 2)).
      clear Heqn.
      destruct n.
      - simpl in H.
        simpl.
        congruence.
      - simpl in *. subst.
        destruct bnode_cursor; simpl.
        + destruct (BorderNode.get_prefix z bnode) eqn:Heqn; rewrite ?Heqn in *; try congruence.
          if_tac.
          * destruct (next_cursor_bnode (before_prefix (z + 1)) bnode n) eqn:Heqn';
              try congruence.
            -- apply next_cursor_bnode_prefix in Heqn'.
               destruct (BorderNode.get_prefix z0 bnode) eqn:Heqn''; congruence.
            -- apply next_cursor_bnode_suffix in Heqn'.
               destruct (snd (BorderNode.get_suffix_pair bnode)) eqn:Heqn''; congruence.
          * destruct n; simpl; try congruence.
            destruct (snd (BorderNode.get_suffix_pair bnode)) eqn:Heqn'; congruence.
        + destruct (snd (BorderNode.get_suffix_pair bnode)); reflexivity.
        + reflexivity.
    Qed.

    Lemma cursor_correct_aux_weaken: forall h c,
        cursor_correct_aux c (Some h) ->
        cursor_correct_aux c None.
    Proof.
      intros.
      destruct c.
      - firstorder.
      - simpl in *.
        destruct p as [[[[]]]].
        destruct H as [? [? [? ?]]].
        auto.
    Qed.

    Lemma cursor_correct_subcursor_correct: forall h c,
        cursor_correct (h :: c) ->
        cursor_correct c.
    Proof.
      intros.
      unfold cursor_correct in H.
      simpl in H.
      destruct h as [[[[]]]].
      destruct H as [_ [_ [_ [_ ?]]]].
      destruct (Node.get_key c0 t) eqn:Heqn.
      - destruct (Node.Flattened.get_value (Node.Flattened.make_cursor k t0) t0) eqn:Heqn'.
        + inv H.
          destruct b.
          * destruct (BorderNode.get_prefix z t1) eqn:Heqn''.
            -- subst.
               firstorder.
            -- inv H1.
            -- subst.
               firstorder.
          * destruct (snd (BorderNode.get_suffix_pair t1)) eqn:Heqn''.
            -- subst.
               firstorder.
            -- eapply cursor_correct_aux_weaken; eauto.
            -- subst.
               firstorder.
          * subst.
            firstorder.
        + contradiction.
      - contradiction.
    Qed.

    Lemma next_cursor_bnode_correct: forall bc b n,
        bordernode_cursor_correct bc ->
        bordernode_cursor_correct (next_cursor_bnode bc b n).
    Proof.
      intros.
      generalize dependent b.
      generalize dependent bc.
      induction n; intros.
      - firstorder.
      - simpl.
        destruct bc.
        + destruct (BorderNode.get_prefix z b).
          * assumption.
          * assumption.
          * if_tac.
            -- apply IHn.
               simpl.
               simpl in H.
               omega.
            -- firstorder.
        + destruct (snd (BorderNode.get_suffix_pair b)); auto.
        + auto.
    Qed.

    Lemma cursor_correct_bnode_cursor_correct: forall t tc b bc c,
        cursor_correct ((t, tc, b, bc) :: c) ->
        bordernode_cursor_correct bc.
    Proof.
      intros.
      unfold cursor_correct in H.
      simpl in H.
      destruct t.
      destruct H as [_ [_ [_ [? _]]]].
      assumption.
    Qed.

    Lemma strict_first_cursor_normalized: forall t c,
        table_correct t ->
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
      destruct (Node.Flattened.get_value (Node.Flattened.first_cursor t0) t0) eqn:Heqn';
        try congruence.
      destruct (next_cursor_bnode (before_prefix 0) t1 (Z.to_nat (keyslice_length + 2))) eqn:Heqn'';
        try congruence.
      - destruct (BorderNode.get_prefix z t1) eqn:Heqn'''; try congruence.
        inv H1.
        simpl.
        erewrite next_cursor_bnode_idempotent; [ | eassumption].
        rewrite Heqn'''.
        reflexivity.
      - destruct (snd (BorderNode.get_suffix_pair t1)) eqn:Heqn'''.
        + inv H1.
          simpl.
          erewrite next_cursor_bnode_idempotent; [ | eassumption].
          rewrite Heqn'''.
          reflexivity.
        + destruct (strict_first_cursor t2) eqn:Heqn''''; try congruence.
          inv H1.
          apply H with (y := trie_height t2) in Heqn''''.
          * simpl.
            rewrite Heqn''''.
            reflexivity.
          * assert (exists k, Node.Flattened.get (Node.Flattened.first_cursor t0) t0 = Some (k, t1)). {
              unfold Node.Flattened.get_value in Heqn'.
              destruct (Node.Flattened.get (Node.Flattened.first_cursor t0) t0) eqn:Heqn'''''.
              - inv Heqn'''''.
                destruct p as [k ?].
                exists k.
                inv Heqn'.
                assumption.
              - inv Heqn'.
            }
            destruct H1 as [k ?].
            apply Node.Flattened.get_in_weak in H1;
              [ | apply Node.Flattened.first_cursor_abs; inv H0; assumption].
            pose (link_height (l: link) :=
                    match l with
                    | value_of _ => O
                    | trie_of t => trie_height t
                    | nil => O
                    end).
            pose (bnode_height (bnode: BorderNode.table) :=
              match bnode with
              | (prefixes, _, suffix) =>
                Nat.max O (link_height suffix)
              end).
            apply in_map with (f := compose bnode_height snd) in H1.
            simpl in H1.
            apply fold_max_le in H1.
            subst bnode_height.
            simpl in H1.
            destruct t1 as [[]].
            subst link_height.
            simpl in H1.
            unfold BorderNode.get_suffix_pair in Heqn'''.
            simpl in Heqn'''.
            subst.
            simpl.
            apply le_lt_n_Sm.
            assumption.
          * inv H0.
            assert (exists k, Node.Flattened.get (Node.Flattened.first_cursor t0) t0 = Some (k, t1)). {
              unfold Node.Flattened.get_value in Heqn'.
              destruct (Node.Flattened.get (Node.Flattened.first_cursor t0) t0) eqn:Heqn'''''.
              - inv Heqn'''''.
                destruct p as [k ?].
                exists k.
                inv Heqn'.
                assumption.
              - inv Heqn'.
            }
            destruct H0 as [k ?].
            apply Node.Flattened.get_in_weak in H0;
              [ | apply Node.Flattened.first_cursor_abs; assumption].
            rewrite Forall_forall in H6.
            apply H6 in H0.
            simpl in H0.
            inv H0.
            destruct k0.
            -- specialize (H9 ltac:(congruence)).
               simpl in Heqn'''.
               subst.
               inv H9.
            -- simpl in Heqn'''.
               subst.
               specialize (H8 eq_refl).
               inv H8.
               assumption.
          * reflexivity.
        + inv H1.
    Qed.

    Lemma cursor_correct_bordernode_correct: forall t tc b bc c,
        cursor_correct ((t, tc, b, bc) :: c) ->
        bordernode_correct b.
    Proof.
      intros.
      unfold cursor_correct in H.
      simpl in H.
      destruct t.
      destruct H as [_ [? [_ [_ ?]]]].
      destruct (Node.get_key tc t) eqn:Heqn; try contradiction.
      destruct (Node.Flattened.get_value (Node.Flattened.make_cursor k t0) t0) eqn:Heqn';
        try contradiction.
      inv H0.
      assert (exists k', Node.Flattened.get (Node.Flattened.make_cursor k t0) t0 = Some (k', b)). {
        unfold Node.Flattened.get_value in Heqn'.
        destruct (Node.Flattened.get (Node.Flattened.make_cursor k t0) t0) eqn:Heqn''.
        - inv Heqn''.
          destruct p as [k' ?].
          exists k'.
          inv Heqn'.
          assumption.
        - inv Heqn'.
      }
      destruct H0 as [k' ?].
      inv H.
      apply Node.Flattened.get_in_weak in H0; [ | apply Node.Flattened.make_cursor_abs; assumption].
      rewrite Forall_forall in H7.
      apply H7 in H0.
      simpl in H0.
      assumption.
    Qed.

    Lemma normalize_idempotent: forall c1 c2,
        cursor_correct c1 ->
        normalize_cursor c1 = Some c2 ->
        normalize_cursor c2 = Some c2.
    Proof.
      intros.
      generalize dependent c2.
      induction c1; intros.
      - inv H0.
      - simpl in H0.
        destruct (normalize_cursor c1) eqn:Heqn.
        + destruct a as [[[[]]]].
          destruct c2.
          * inv H0.
          * rewrite <- Heqn in IHc1. 
            inv H0.
            apply IHc1 in Heqn.
            simpl.
            rewrite Heqn.
            f_equal.
            eapply cursor_correct_subcursor_correct; eauto.
        + destruct a as [[[[]]]].
          destruct (next_cursor_bnode b t1 (Z.to_nat (keyslice_length + 2))) eqn:Heqn_bnode.
          * pose proof (next_cursor_bnode_prefix b t1 z _ Heqn_bnode).
            destruct (BorderNode.get_prefix z t1) eqn:Heqn_link; try congruence.
            inv H0.
            simpl.
            rewrite (next_cursor_bnode_idempotent _ _ _ Heqn_bnode).
            rewrite Heqn_link.
            reflexivity.
          * destruct (snd (BorderNode.get_suffix_pair t1)) eqn:Heqn_link.
            -- inv H0.
               simpl.
               rewrite (next_cursor_bnode_idempotent _ _ _ Heqn_bnode).
               rewrite Heqn_link.
               reflexivity.
            -- destruct (strict_first_cursor t2) eqn:Heqn_fcursor; try congruence.
               inv H0.
               simpl.
               apply strict_first_cursor_normalized in Heqn_fcursor;
                 [ rewrite Heqn_fcursor; reflexivity | ].
               apply cursor_correct_bordernode_correct in H.
               inv H.
               simpl in Heqn_link.
               subst.
               destruct k.
               ++ specialize (H3 ltac:(congruence)).
                  inv H3.
               ++ specialize (H2 eq_refl).
                  inv H2.
                  assumption.
            -- congruence.
          * destruct (Node.get_key (Node.next_cursor c t) t) eqn:Heqn'; try congruence.
            destruct (Node.Flattened.get_value (Node.Flattened.make_cursor k t0) t0) eqn:Heqn'';
              try congruence.
            destruct (next_cursor_bnode (before_prefix 0) t2 (Z.to_nat (keyslice_length + 2))) eqn:Heqn''';
              try congruence.
            -- destruct (BorderNode.get_prefix z t2) eqn:Heqn''''; try congruence.
               inv H0.
               simpl.
               erewrite next_cursor_bnode_idempotent; [ | eassumption].
               rewrite Heqn''''.
               reflexivity.
            -- destruct (snd (BorderNode.get_suffix_pair t2)) eqn:Heqn''''; try congruence.
               ++ inv H0.
                  simpl.
                  erewrite next_cursor_bnode_idempotent; [ | eassumption].
                  rewrite Heqn''''.
                  reflexivity.
               ++ destruct (strict_first_cursor t3) eqn:Heqn'''''; try congruence.
                  inv H0.
                  simpl.
                  apply strict_first_cursor_normalized in Heqn''''';
                    [ rewrite Heqn'''''; reflexivity | ].
                  assert (exists k', Node.Flattened.get (Node.Flattened.make_cursor k t0) t0 = Some (k', t2)). {
                    unfold Node.Flattened.get_value in Heqn''.
                    destruct (Node.Flattened.get (Node.Flattened.make_cursor k t0) t0) eqn:Heqn''''''.
                    - inv Heqn''.
                      destruct p as [k' ?].
                      exists k'.
                      inv H1.
                      reflexivity.
                    - inv Heqn''.
                  }
                  inv H.
                  destruct H2 as [? _].
                  inv H.
                  destruct H0 as [k' ?].
                  apply Node.Flattened.get_in_weak in H; [ | apply Node.Flattened.make_cursor_abs; assumption].
                  rewrite Forall_forall in H7.
                  apply H7 in H.
                  simpl in H.
                  inv H.
                  simpl in Heqn''''.
                  subst.
                  destruct k0.
                  ** specialize (H9 ltac:(congruence)).
                     inv H9.
                  ** specialize (H3 eq_refl).
                     inv H3.
                     assumption.
    Qed.

    Lemma get_subtrie: forall tableform listform bnode t' c1 c2 c3 ks k e,
        key_rel k c1 (trienode_of tableform listform) ->
        abs_rel c1 (trienode_of tableform listform) ->
        key_rel (reconstruct_keyslice (ks, keyslice_length) ++ k) c2 t' ->
        abs_rel c2 t' ->
        Node.Flattened.key_rel ks c3 listform ->
        Node.Flattened.abs_rel c3 listform ->
        Node.Flattened.get c3 listform = Some (ks, bnode) /\
        BorderNode.get_suffix None bnode = trie_of t' /\
        get c2 t' = Some (k, e)
        <->
        get c1 (trienode_of tableform listform) = Some (reconstruct_keyslice (ks, keyslice_length) ++ k, e).
    Proof.
      intros; split; intros.
      - destruct H5 as [? []].
        unfold get.
    Admitted.

    Theorem get_put_same: forall t c1 c2 k e a,
        abs_rel c1 (fst (snd (put k e c2 (t, a)))) ->
        abs_rel c2 t ->
        key_rel k c1 (fst (snd (put k e c2 (t, a)))) ->
        get c1 (fst (snd (put k e c2 (t, a)))) = Some (k, e).
    Proof.
      intros.
      generalize dependent c1.
      generalize dependent c2.
      generalize dependent k.
      generalize dependent e.
      generalize dependent a.
      induction t; intros.
    Admitted.
      
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
