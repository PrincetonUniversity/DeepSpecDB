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
  Module NodeFacts := FlattenableTableFacts KeysliceType Node.

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

    Definition cursor: Type := list (trie * Node.cursor val * (@BorderNode.table link) * BorderNode.cursor).
    Definition allocator: Type := list val.

    Definition consume (a: allocator) := (hd default a, tl a).

    Definition empty (a: allocator) :=
      let (empty_table, a) := Node.empty a in
      (trienode_of empty_table [], a).

    Instance inh_link: Inhabitant link := nil.
    Instance bnode_link: BorderNodeValue link.
    Proof.
      refine (Build_BorderNodeValue _ nil _).
      intros; destruct a; first [ left; congruence | right; congruence].
    Defined.

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

    Definition nil_or_not: forall v : link, {v = default_val} + {v <> default_val}.
      change default_val with nil; destruct v; try first [left; congruence | right; congruence].
    Defined.
      
    Function strict_first_cursor (t: trie) {measure trie_height t}: option cursor :=
      match t with
      | trienode_of tableform listform =>
        match Node.Flattened.get_value (Node.Flattened.first_cursor listform) listform with
        | Some bnode =>
          match BorderNode.next_cursor (BorderNode.before_prefix 0) bnode with
          | BorderNode.before_prefix len =>
            match (BorderNode.get_prefix len bnode) with
            | trie_of t' => None (* ill-formed *)
            | value_of _ =>
              Some [(t, Node.first_cursor tableform, bnode, BorderNode.before_prefix len)]
            | nil => None
            end
          | BorderNode.before_suffix =>
            match snd (BorderNode.get_suffix_pair bnode) with
            | trie_of t' =>
              match strict_first_cursor t' with
              | Some c' => Some ((t, Node.first_cursor tableform, bnode, BorderNode.before_suffix) :: c')
              | None => None
              end
            | value_of _ =>
              Some [(t, Node.first_cursor tableform, bnode, BorderNode.before_suffix)]
            | nil => None
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
      unfold Node.Flattened.get, Node.Flattened.first_cursor in H.
      epose proof (@Znth_In (option (Node.Flattened.key * BorderNode.table)) (@Node.Flattened.option_binding_inh (@BorderNode.table link)) 0 (map Some listform)).
      assert (Zlength (map Some listform) <> 0). {
        intro.
        apply Zlength_nil_inv in H1.
        rewrite H1 in *.
        rewrite data_at_rec_lemmas.Znth_nil in H.
        inv H.
      }
      rewrite Zlength_map in *.
      specialize (H0 ltac:(list_solve)).
      rewrite H in H0.
      assert (In (x, bnode) listform). {
        clear -H0.
        induction listform.
        - inv H0.
        - inv H0.
          + inv H.
            left.
            reflexivity.
          + right.
            apply IHlistform.
            apply H.
      }
      apply in_map with (f :=
                           (compose
                              (fun bnode0 : BorderNode.table =>
                                 let (p, suffix) := bnode0 in
                                 let (_, _) := p in match suffix with
                                                    | trie_of t0 => trie_height t0
                                                    | _ => 0%nat
                                                    end) snd)) in H2.
      simpl in H2.
      destruct bnode as [[]].
      simpl in teq2.
      subst.
      assumption.
    Defined.

    (* This [normalize_cursor] returns a cursor when there is a next one,
     * also, it tries to eliminate an [BorderNode.after_suffix] cursor position *)
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
          match BorderNode.next_cursor bnode_cursor bnode with
          | BorderNode.before_prefix len =>
            match (BorderNode.get_prefix len bnode) with
            | nil => (* impossible *) None
            | value_of _ => Some [(t, table_cursor, bnode, (BorderNode.before_prefix len))]
            | trie_of t' => None
            end
          | BorderNode.before_suffix =>
            match (snd (BorderNode.get_suffix_pair bnode)) with
            | nil => (* impossible *) None
            | value_of _ => Some [(t, table_cursor, bnode, BorderNode.before_suffix)]
            | trie_of t' =>
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
              | Some bnode' =>
                (* no need to repeatedly move to next if we have maintained the invariant that no dead end exists
                 * in the trie *)
                match BorderNode.next_cursor (BorderNode.before_prefix 0) bnode' with
                | BorderNode.before_prefix len =>
                  match (BorderNode.get_prefix len bnode') with
                  | nil => (* impossible *) None
                  | value_of _ => Some [(t, table_cursor', bnode', (BorderNode.before_prefix len))]
                  | trie_of t' => None
                  end
                | BorderNode.before_suffix =>
                  match (snd (BorderNode.get_suffix_pair bnode')) with
                  | nil => (* impossible *) None
                  | value_of _ => Some [(t, table_cursor', bnode', BorderNode.before_suffix)]
                  | trie_of t' =>
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
            [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_prefix (Zlength k))]
          else
            match fst (BorderNode.get_suffix_pair bnode) with
            | None =>
              match BorderNode.get_suffix None bnode with
              | value_of _ => []
              | nil => []
              | trie_of t' =>
                (t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_suffix) :: make_cursor (get_suffix k) t'
              end
            | Some k' =>
              (* we need to compare the suffix here, if the key input is greater
               * then we need to move to next here
               * because the semantics of [get] need it *)
              if (TrieKeyFacts.lt_dec k' (get_suffix k)) then
                [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.after_suffix)]
              else
                [(t, Node.make_cursor keyslice tableform, bnode, BorderNode.before_suffix)]
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
      | (trienode_of tableform _, table_cursor, bnode, bnode_cursor) :: c' =>
        match Node.get_key table_cursor tableform with
        | Some keyslice =>
          match bnode_cursor with
          | BorderNode.before_prefix len =>
            match BorderNode.get_prefix len bnode with
            | value_of v => Some (reconstruct_keyslice (keyslice, len), v)
            | trie_of t' => None (* impossible *)
            | nil => None
            end
          | BorderNode.before_suffix =>
            match (snd (BorderNode.get_suffix_pair bnode)) with
            | value_of v => Some (reconstruct_keyslice (keyslice, keyslice_length), v)
            | trie_of t' =>
              match get_raw c' with
              | Some (k', v') => Some (reconstruct_keyslice (keyslice, keyslice_length) ++ k', v')
              | None => None
              end
            | nil => None
            end
          | BorderNode.after_suffix => None
          end
        | None => None
        end
      | [] => None
      end.

    Definition get (c: cursor) (t: table): option (key * value) :=
      match normalize_cursor c with
      | Some c' =>
        get_raw c'
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
        let (tableform, a) := snd (Node.put keyslice2 bnode_addr2 (Node.first_cursor tableform) (tableform, a)) in
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
                    let bnode := BorderNode.put_suffix None (trie_of t') bnode in
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

    (* This strict_next_cursor does not necessarily produce a valid position([BorderNode.after_suffix]) *)
    (* not sure if this work *)
    Fixpoint strict_next_cursor (c: cursor): cursor :=
      match c with
      | [] => []
      | [(trienode_of tableform listform, table_cursor, bnode, bnode_cursor)] =>
        match bnode_cursor with
        | BorderNode.before_prefix len =>
          if Z_lt_dec len keyslice_length then
            [(trienode_of tableform listform, table_cursor, bnode, BorderNode.before_prefix (len + 1))]
          else
            [(trienode_of tableform listform, table_cursor, bnode, BorderNode.after_suffix)]
        | BorderNode.before_suffix => [(trienode_of tableform listform, table_cursor, bnode, BorderNode.after_suffix)]
        | BorderNode.after_suffix =>
          let table_cursor' := Node.next_cursor table_cursor tableform in
          match Node.get_key table_cursor' tableform with
          | Some key =>
            match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
            | Some bnode' =>
              [(trienode_of tableform listform, table_cursor, bnode, BorderNode.before_prefix 0)]
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

    Definition is_value (l: link) :=
      match l with
      | value_of _ => True
      | _ => False
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
        Forall (fun l => is_value l \/ l = nil) prefixes ->
        (k = None -> subtrie_correct l) ->
        (k <> None -> is_value l) ->
        match k with
        | Some k' => 0 < Zlength k'
        | None => True
        end ->
        (* optional: no dangling(dead end) in the tree, useful for [next_cursor] and [first_cursor] *)
        (l <> nil \/ Exists (fun l => l <> nil) prefixes) ->
        bordernode_correct (prefixes, k, l)
    with
    subtrie_correct: link -> Prop :=
    | nil_correct: subtrie_correct nil
    | subtrie_correct_intro t:
        table_correct t ->
        subtrie_correct (trie_of t).
    Hint Constructors table_correct: trie.

    Fixpoint cursor_correct_aux (c: cursor) (p: option trie): Prop :=
      match c with
      | (trienode_of tableform listform, table_cursor, bnode, bnode_cursor) :: c' =>
        match p with
        | Some t => t = trienode_of tableform listform
        | None => True
        end /\
        table_correct (trienode_of tableform listform) /\
        Node.cursor_correct table_cursor /\
        BorderNode.cursor_correct bnode_cursor /\
        match Node.get_key table_cursor tableform with
        | Some key =>
          match Node.Flattened.get_value (Node.Flattened.make_cursor key listform) listform with
          | Some bnode' =>
            bnode' = bnode /\
            match bnode_cursor with
            | BorderNode.before_prefix len =>
              match BorderNode.get_prefix len bnode with
              | trie_of t' => False
              | _ => c' = []
              end
            | BorderNode.before_suffix =>
              match (snd (BorderNode.get_suffix_pair bnode)) with
              | trie_of t' => cursor_correct_aux c' (Some t')
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
          destruct c1.
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

    Lemma cursor_correct_bnode_cursor_correct: forall t tc b bc c,
        cursor_correct ((t, tc, b, bc) :: c) ->
        BorderNode.cursor_correct bc.
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
      destruct (BorderNode.next_cursor (BorderNode.before_prefix 0) t1) eqn:Heqn'';
        try congruence.
      - destruct (BorderNode.get_prefix z t1) eqn:Heqn'''; try congruence.
        inv H1.
        simpl.
        erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
        rewrite Heqn'''.
        reflexivity.
      - destruct (snd (BorderNode.get_suffix_pair t1)) eqn:Heqn'''.
        + inv H1.
          simpl.
          erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
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
            apply Node.Flattened.get_in_weak in H1.
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
            apply Node.Flattened.get_in_weak in H0.
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
      apply Node.Flattened.get_in_weak in H0.
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
          destruct (BorderNode.next_cursor c0 t1) eqn:Heqn_bnode.
          * pose proof (BorderNode.next_cursor_prefix_correct c0 t1 z Heqn_bnode).
            destruct (BorderNode.get_prefix z t1) eqn:Heqn_link; try congruence.
            inv H0.
            simpl.
            rewrite (BorderNode.next_cursor_idempotent _ _ _ Heqn_bnode).
            rewrite Heqn_link.
            reflexivity.
          * destruct (snd (BorderNode.get_suffix_pair t1)) eqn:Heqn_link.
            -- inv H0.
               simpl.
               rewrite (BorderNode.next_cursor_idempotent _ _ _ Heqn_bnode).
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
            destruct (BorderNode.next_cursor (BorderNode.before_prefix 0) t2) eqn:Heqn''';
              try congruence.
            -- destruct (BorderNode.get_prefix z t2) eqn:Heqn''''; try congruence.
               inv H0.
               simpl.
               erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
               rewrite Heqn''''.
               reflexivity.
            -- destruct (snd (BorderNode.get_suffix_pair t2)) eqn:Heqn''''; try congruence.
               ++ inv H0.
                  simpl.
                  erewrite BorderNode.next_cursor_idempotent; [ | eassumption].
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
                  apply Node.Flattened.get_in_weak in H.
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
    (*     unfold list_get_error in H0. *)
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
        let H := fresh "Heqn" in
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: _ = match ?e with _ => _ end |- _] =>
        let H := fresh "Heqn" in
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: match ?e with _ => _ end = _ |- _] =>
        let H := fresh "Heqn" in
        destruct e eqn:H; rewrite ?H in *; try congruence; try contradiction
      | [H: _ /\ _ |- _ ] => destruct H
      | [H: table_correct (trienode_of _ _) |- _ ] => inv H
      | [H: Some _ = Some _ |- _ ] => inv H
      | [|- context[if _ then _ else _] ] => try first [
                                                 rewrite if_true by eauto with trie
                                               | rewrite if_false by eauto with trie
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
    Hint Unfold list_get_error: trie.
    
    Ltac basic_trie_solve :=
      autounfold with trie in *; repeat eliminate_hyp;
      change default_val with nil in *;
      try first [ solve [eauto 10 with trie] | rep_omega | congruence].

    Opaque Node.Flattened.put get_keyslice reconstruct_keyslice get_suffix.

    Lemma list_get_error_correct: forall k t bnode,
        list_get_error k t = Some bnode ->
        Node.Flattened.get (Node.Flattened.make_cursor k t) t = Some (k, bnode).
    Proof.
      intros.
      basic_trie_solve.
    Qed.

    Lemma list_get_error_correct_key: forall k t bnode,
        list_get_error k t = Some bnode ->
        Node.Flattened.get_key (Node.Flattened.make_cursor k t) t = Some k.
    Proof.
      intros.
      basic_trie_solve.
    Qed.

    Lemma list_get_error_correct_value: forall k t bnode,
        list_get_error k t = Some bnode ->
        Node.Flattened.get_value (Node.Flattened.make_cursor k t) t = Some bnode.
    Proof.
      intros.
      basic_trie_solve.
    Qed.

    Lemma list_get_error_correct_table_key: forall k tableform listform bnode,
        table_correct (trienode_of tableform listform) ->
        list_get_error k listform = Some bnode ->
        Node.get_key (Node.make_cursor k tableform) tableform = Some k.
    Proof.
      intros.
      basic_trie_solve.
      replace (Node.get_key (Node.make_cursor k0 tableform) tableform) with
          (Node.Flattened.get_key (Node.Flattened.make_cursor k0 (Node.flatten tableform)) (Node.flatten tableform)).
      - replace (Some k0) with
            (Node.Flattened.get_key (Node.Flattened.make_cursor k0 listform) listform) by
            (unfold Node.Flattened.get_key; rewrite Heqn; reflexivity).
        pose proof (Node.flatten_invariant _ H3) as [? _].
        apply Node.Flattened.same_key_result with k0; basic_trie_solve.
        - symmetry.
        unfold Node.get_key, Node.Flattened.get_key.
        pose proof (Node.flatten_invariant _ H3) as [? ?].
        specialize (H0 k0
                       (Node.make_cursor k0 tableform)
                       (Node.Flattened.make_cursor k0 (Node.flatten tableform))).
        specialize (H0 ltac:(basic_trie_solve) ltac:(basic_trie_solve) ltac:(basic_trie_solve)
                       ltac:(basic_trie_solve)).
        rewrite H0.
        reflexivity.
    Qed.

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

    Lemma leaves_correct_bordernode_correct': forall bnode listform k c,
        Forall (compose bordernode_correct snd) listform ->
        Node.Flattened.get c listform = Some (k, bnode) ->
        bordernode_correct bnode.
    Proof.
      intros.
      destruct (Node.Flattened.get c listform) as [[] | ] eqn:Heqn; try congruence.
      inv H0.
      pose proof (Node.Flattened.get_in_weak listform _ k bnode Heqn).
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
      inv H.
      unfold BorderNode.invariant.
      simpl.
      list_solve.
    Qed.
    Hint Resolve bordernode_correct_invariant: trie.

    Lemma bordernode_correct_subtrie_correct: forall prefixes suffix_key t,
        bordernode_correct (prefixes, suffix_key, trie_of t) ->
        table_correct t.
    Proof.
      intros.
      inv H.
      destruct suffix_key.
      - specialize (H6 ltac:(congruence)).
        inv H6.
      - specialize (H5 eq_refl).
        inv H5.
        assumption.
    Qed.
    Hint Resolve bordernode_correct_subtrie_correct: trie.

    (* Hint Rewrite BorderNode.get_put_prefix_diff using basic_trie_solve: trie. *)
    (* Hint Rewrite BorderNode.get_put_prefix_same using basic_trie_solve: trie. *)
    (* Hint Rewrite (@Node.Flattened.get_put_same (@BorderNode.table link)) using basic_trie_solve: trie. *)
    (* Hint Rewrite (@Node.Flattened.get_put_diff (@BorderNode.table link)) using basic_trie_solve: trie. *)

    Ltac trie_solve :=
      repeat match goal with
      | [|- context [Node.Flattened.get_key (Node.Flattened.make_cursor _ _) _]] =>
        try solve [erewrite list_get_error_correct_key by eauto];
        idtac
      | [|- context [Node.get_key (Node.make_cursor _ _) _]] =>
        try solve [erewrite list_get_error_correct_table_key by eauto];
        idtac
      | [|- context [BorderNode.get_prefix _ (BorderNode.put_prefix _ _ _)]] =>
        try first [
              rewrite BorderNode.get_put_prefix_same by basic_trie_solve
            | rewrite BorderNode.get_put_prefix_diff by basic_trie_solve
            ]
      | [|- context [Node.Flattened.get _ (fst (snd (Node.Flattened.put _ _ _ _)))]] =>
        try first [
              rewrite Node.Flattened.get_put_same by basic_trie_solve
            | rewrite Node.Flattened.get_put_diff by basic_trie_solve
            ]
      | [|- context [Node.get _ (fst (snd (Node.put _ _ _ _)))]] =>
        try first [
              rewrite Node.get_put_same by basic_trie_solve
            | rewrite Node.get_put_diff by basic_trie_solve
            ]
      end;
      basic_trie_solve.

    Lemma create_pair_normalized: forall k1 k2 v1 v2 a,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        normalize_cursor (make_cursor k1 (fst (create_pair k1 k2 v1 v2 a))) =
        Some (make_cursor k1 (fst (create_pair k1 k2 v1 v2 a))).
    Proof.
      intros k1.
      remember (length k1) as n.
      generalize dependent k1.
      induction n using (well_founded_induction lt_wf); intros.
      rewrite create_pair_equation.
      destruct (@Node.empty val a) eqn:Heqn_empty.
      destruct (consume a0) eqn:Heqn_consume0.
      if_tac.
      destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1];
        destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2];
        try if_tac; try omega.
      - assert (Zlength k1 <> Zlength k2) by admit.
        destruct (Node.put (get_keyslice k1) v (Node.first_cursor t) (t, l)) as [? []] eqn:Heqn_node_put.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        rewrite ?if_true by auto.
        rewrite BorderNode.next_cursor_terminate_permute1 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        trie_solve.
      - destruct (Node.put (get_keyslice k1) v (Node.first_cursor t) (t, l)) as [? []] eqn:Heqn_node_put.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        trie_solve.
        rewrite BorderNode.next_cursor_terminate_permute2 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        rewrite BorderNode.get_put_non_interference1.
        trie_solve.
      - destruct (Node.put (get_keyslice k1) v (Node.first_cursor t) (t, l)) as [? []] eqn:Heqn_node_put.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
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
                  (upd_Znth (Zlength k2 - 1) (list_repeat (Z.to_nat keyslice_length) nil) (value_of v2), 
                   Some (get_suffix k1), value_of v1))
          with (BorderNode.before_suffix).
        simpl.
        reflexivity.
      - destruct (create_pair (get_suffix k1) (get_suffix k2) v1 v2 a0) eqn:Heqn_create_pair.
        destruct (consume a1) eqn:Heqn_consume1.
        destruct (snd (Node.put (get_keyslice k1) v0 (Node.first_cursor t) (t, l0))) eqn:Heqn_node_put.
        rewrite make_cursor_equation.
        simpl.
        unfold list_get_error.
        trie_solve.
        simpl.
        replace t0
          with (fst (create_pair (get_suffix k1) (get_suffix k2) v1 v2 a0))
          by (rewrite Heqn_create_pair; reflexivity).
        rewrite H with (y := length (get_suffix k1)); trie_solve;
          change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k); simpl.
        + subst.
          rewrite <- ?ZtoNat_Zlength.
          rewrite Zlength_sublist by rep_omega.
          apply Z2Nat.inj_lt; rep_omega.
        + rewrite Zlength_sublist; rep_omega.
        + rewrite Zlength_sublist; rep_omega.
        + admit.
      - destruct (consume l) eqn:Heqn_consume1.
        destruct (Node.put (get_keyslice k1) v (Node.first_cursor t) (t, l0)) as [? []] eqn:Heqn_node_put1.
        simpl.
        destruct (Node.put (get_keyslice k2) v0 (Node.first_cursor t0) (t0, a1)) as [? []] eqn:Heqn_node_put2.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        erewrite (Node.Flattened.get_put_diff
                   (elt := @BorderNode.table link))
          with
            (c3 := Node.Flattened.make_cursor
                     (get_keyslice k1)
                     (fst (snd (Node.Flattened.put (get_keyslice k1)
                                                   (BorderNode.put_value k1 (value_of v1) BorderNode.empty)
                                                   (Node.Flattened.first_cursor []) ([], []))))); trie_solve.
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
                    (list_repeat (Z.to_nat keyslice_length) nil, Some (get_suffix k1), value_of v1))
            with (BorderNode.before_suffix).
          simpl.
          reflexivity.
    Admitted.

    Lemma make_cursor_put_normalized: forall t c k e a,
        Zlength k <> 0 ->
        table_correct t ->
        normalize_cursor (make_cursor k (fst (snd (put k e c (t, a))))) = Some (make_cursor k (fst (snd (put k e c (t, a))))).
    Proof.
      intros.
      remember (length k) as n.
      generalize dependent c.
      generalize dependent k.
      generalize dependent t.
      generalize dependent a.
      induction n using (well_founded_induction lt_wf); intros.
      rewrite put_equation.
      destruct t as [tableform listform].
      case_eq (list_get_error (get_keyslice k) listform); intros.
      - inv H0.
        repeat (if_tac; try first [rewrite if_true by auto | rewrite if_false by auto]).
        + (* unfold [make_cursor] *)
          rewrite make_cursor_equation.
          simpl.
          unfold list_get_error.
          rewrite Node.Flattened.get_put_same by trie_solve.
          rewrite ?if_true by auto.
          (* unfold [normalize_cursor] *)
          simpl.
          rewrite BorderNode.next_cursor_terminate; trie_solve.
        + destruct t as [[prefixes suffix_key] suffix_value].
          simpl in H3.
          subst.
          unfold BorderNode.get_suffix.
          simpl.
          destruct suffix_value.
          * assert (bordernode_correct (prefixes, None, value_of v)) by trie_solve.
            inv H3.
            specialize (H14 eq_refl).
            inv H14.
          * destruct (put (get_suffix k) e c (t, a)) as [? [[tableform' listform'] ?]] eqn:Hnew_trie.
            simpl.
            rewrite make_cursor_equation.
            unfold list_get_error.
            rewrite Node.Flattened.get_put_same by trie_solve.
            rewrite ?if_true by auto.
            rewrite ?if_false by auto.
            unfold BorderNode.get_suffix_pair.
            simpl.
            replace (trienode_of tableform' listform') with
                (fst (snd (put (get_suffix k) e c (t, a)))) by (rewrite Hnew_trie; reflexivity).
            rewrite H with (y := length (get_suffix k)); trie_solve.
            -- rewrite <- ?ZtoNat_Zlength.
               change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
               rewrite Zlength_sublist by rep_omega.
               apply Z2Nat.inj_lt; rep_omega.
            -- change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
               rewrite Zlength_sublist; rep_omega.
          * simpl.
            rewrite make_cursor_equation.
            unfold list_get_error.
            rewrite Node.Flattened.get_put_same by trie_solve.
            rewrite ?if_true by auto.
            rewrite ?if_false by auto.
            unfold BorderNode.get_suffix_pair.
            simpl.
            rewrite ?if_false by (TrieKeyFacts.order).
            simpl.
            change (BorderNode.next_cursor BorderNode.before_suffix (prefixes, Some (get_suffix k), value_of e))
              with (BorderNode.before_suffix).
            simpl.
            reflexivity.
        + destruct t as [[prefixes suffix_key] suffix_value].
          simpl in H4.
          subst.
          simpl in H3.
          clear H3.
          rewrite make_cursor_equation.
          simpl.
          unfold list_get_error.
          rewrite Node.Flattened.get_put_same by trie_solve.
          rewrite ?if_true by eauto.
          rewrite ?if_false by eauto.
          unfold BorderNode.get_suffix_pair; simpl.
          rewrite if_false by (TrieKeyFacts.order).
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix (prefixes, Some (get_suffix k), value_of e))
            with (BorderNode.before_suffix).
          simpl.
          reflexivity.
        + destruct t as [[prefixes suffix_key] suffix_value].
          simpl.
          simpl in H3.
          simpl in H4.
          destruct suffix_key; [ | congruence].
          assert (bordernode_correct (prefixes, Some s, suffix_value)) by trie_solve.
          inv H10.
          specialize (H17 ltac:(congruence)).
          destruct suffix_value; try inv H17.
          destruct (create_pair (get_suffix k) s e v a) eqn:Heqn_create_pair.
          rewrite make_cursor_equation.
          simpl.
          unfold list_get_error.
          trie_solve.
          simpl.
          rewrite ?if_false by TrieKeyFacts.order.
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix (prefixes, Some (get_suffix k), trie_of t))
            with (BorderNode.before_suffix).
          simpl.
          replace t with (fst (create_pair (get_suffix k) s e v a)) by (rewrite Heqn_create_pair; reflexivity).
          rewrite create_pair_normalized; trie_solve;
            change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k); simpl.
          rewrite Zlength_sublist; rep_omega.
      - destruct (consume a) eqn:Heqn'.
        destruct (Node.put (get_keyslice k) v (Node.first_cursor tableform) (tableform, l)) as
            [? []] eqn:Heqn''.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        rewrite Node.Flattened.get_put_same by trie_solve.
        rewrite ?if_true by auto.
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate by trie_solve.
          rewrite BorderNode.get_put_prefix_same by trie_solve.
          reflexivity.
        + unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          unfold BorderNode.get_suffix_pair; simpl.
          rewrite ?if_false by (TrieKeyFacts.order).
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix
                                         (list_repeat (Z.to_nat keyslice_length) default_val, Some (get_suffix k), value_of e))
            with (BorderNode.before_suffix).
          reflexivity.
    Admitted.

    Lemma create_pair_correct: forall k1 k2 v1 v2 a,
        table_correct (fst (create_pair k1 k2 v1 v2 a)).
    Proof.
      intros k1.
      remember (length k1) as n.
      generalize dependent k1.
      induction n using (well_founded_induction lt_wf); intros.
      rewrite create_pair_equation.
      destruct (@Node.empty val a) eqn:Heqn_empty.
      replace t with (fst (@Node.empty val a)) by (rewrite Heqn_empty; reflexivity).
      destruct (consume a0) eqn:Heqn_consume0.
      if_tac.
      destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1];
        destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2];
        try if_tac; try omega.
      - destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))
          as [? []] eqn:Heqn_node_put.
        replace t0 with
          (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))))
          by (rewrite Heqn_node_put; reflexivity).
        simpl.
        constructor; trie_solve.
        + rewrite NodeFacts.simple_put_permute by trie_solve.
          rewrite NodeFacts.empty_flatten_empty.
          change (@Node.Flattened.put) with
              (fun (elt : Type) (k : Node.Flattened.key) (v : elt) (c : Node.Flattened.cursor elt)
                 (table_with_allocator : Node.Flattened.table elt * Node.Flattened.allocator) =>
                 let (t, a) := table_with_allocator in (c, (Node.Flattened.put_aux k v t, a))
              ).
          simpl.
          reflexivity.
        + change (@Node.Flattened.put) with
              (fun (elt : Type) (k : Node.Flattened.key) (v : elt) (c : Node.Flattened.cursor elt)
                 (table_with_allocator : Node.Flattened.table elt * Node.Flattened.allocator) =>
                 let (t, a) := table_with_allocator in (c, (Node.Flattened.put_aux k v t, a))
              ).
          simpl.
          repeat constructor.
          simpl.
          admit.
        + admit.
      -
    Admitted.

    Lemma create_pair_abs: forall k1 k2 v1 v2 a,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        abs_rel (make_cursor k1 (fst (create_pair k1 k2 v1 v2 a))) (fst (create_pair k1 k2 v1 v2 a)).
    Proof.
      intros.

    Lemma get_create_same1: forall k1 k2 c v1 v2 a,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        abs_rel c (fst (create_pair k1 k2 v1 v2 a)) ->
        key_rel k1 c (fst (create_pair k1 k2 v1 v2 a)) ->
        get c (fst (create_pair k1 k2 v1 v2 a)) = Some (k1, v1).
    Proof.
      intros k1.
      remember (length k1) as n.
      generalize dependent k1.
      induction n using (well_founded_induction lt_wf); intros.
      unfold get.
      unfold key_rel in H4.
      rewrite H4.
      rewrite create_pair_equation.
      destruct (@Node.empty val a) eqn:Heqn_empty.
      replace t with (fst (@Node.empty val a)) by (rewrite Heqn_empty; reflexivity).
      destruct (consume a0) eqn:Heqn_consume0.
      if_tac.
      destruct (Z_le_gt_dec (Zlength k1) keyslice_length) as [Hmath1 | Hmath1];
        destruct (Z_le_gt_dec (Zlength k2) keyslice_length) as [Hmath2 | Hmath2];
        try if_tac; try omega.
      - assert (Zlength k1 <> Zlength k2) by admit.
        destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))
          as [? []] eqn:Heqn_node_put.
        replace t0 with
          (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))))
          by (rewrite Heqn_node_put; reflexivity).
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        rewrite ?if_true by auto.
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
      - destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))
          as [? []] eqn:Heqn_node_put.
        replace t0 with
          (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))))
          by (rewrite Heqn_node_put; reflexivity).
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        trie_solve.
        simpl.
        unfold BorderNode.put_value.
        trie_solve.
        rewrite BorderNode.next_cursor_terminate_permute2 by
            first [
                solve [trie_solve]
              | apply BorderNode.next_cursor_terminate; trie_solve ].
        rewrite BorderNode.get_put_non_interference1.
        trie_solve.
        simpl.
        unfold Node.get_key.
        trie_solve.
        rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
        admit.
      - destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))
          as [? []] eqn:Heqn_node_put.
        replace t0 with
          (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l))))
          by (rewrite Heqn_node_put; reflexivity).
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
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
                  (upd_Znth (Zlength k2 - 1) (list_repeat (Z.to_nat keyslice_length) nil) (value_of v2), 
                   Some (get_suffix k1), value_of v1))
          with (BorderNode.before_suffix).
        simpl.
        unfold Node.get_key.
        trie_solve.
        admit.
      - destruct (create_pair (get_suffix k1) (get_suffix k2) v1 v2 a0) eqn:Heqn_create_pair.
        destruct (consume a1) eqn:Heqn_consume1.
        destruct (Node.put (get_keyslice k1) v0 (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l0))
          as [? []] eqn:Heqn_node_put.
        replace t1 with
            (fst (snd (Node.put (get_keyslice k1) v0 (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l0))))
          by (rewrite Heqn_node_put; reflexivity).
        simpl.
        rewrite make_cursor_equation.
        simpl.
        unfold list_get_error.
        trie_solve.
        simpl.
        replace t0 with
            (fst (create_pair (get_suffix k1) (get_suffix k2) v1 v2 a0))
          by (rewrite Heqn_create_pair; reflexivity).
        rewrite create_pair_normalized;
          (try solve [
                 change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                 simpl;
                 rewrite ?Zlength_sublist; rep_omega]).
        2: { admit. } (* [get_suffix k1 <> get_suffix k2] *)
        simpl.
        unfold Node.get_key.
        trie_solve.
        unfold get in H.
        assert (match normalize_cursor (make_cursor (get_suffix k1) (fst (create_pair (get_suffix k1) (get_suffix k2) v1 v2 a0))) with
                | Some c' => get_raw c'
                | None => None
                end = Some (get_suffix k1, v1)). {
          subst.
          eapply H with (y := length (get_suffix k1)) (k2 := (get_suffix k2)) (v2 := v2) (a := a0);
            try solve [
                  change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                  simpl;
                  rewrite <- ?ZtoNat_Zlength;
                  rewrite ?Zlength_sublist; try rep_omega
                ].
          - admit.
          - admit.
          - admit.
        }
        rewrite create_pair_normalized in H8;
          (try solve [
                 change get_suffix with (fun (k: string) => sublist keyslice_length (Zlength k) k);
                 simpl;
                 rewrite ?Zlength_sublist; rep_omega]).
        2: { admit. }
        rewrite H8.
        admit.
      - destruct (consume l) eqn:Heqn_consume1.
        destruct (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l0))
          as [? []] eqn:Heqn_node_put1.
        simpl.
        destruct (Node.put (get_keyslice k2) v0 (Node.first_cursor t0) (t0, a1))
          as [? []] eqn:Heqn_node_put2.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        erewrite (Node.Flattened.get_put_diff
                   (elt := @BorderNode.table link))
          with
            (c3 := Node.Flattened.make_cursor
                     (get_keyslice k1)
                     (fst
                        (snd
                           (Node.Flattened.put (get_keyslice k1)
                                               (BorderNode.put_value k1 (value_of v1) BorderNode.empty)
                                               (Node.Flattened.first_cursor []) ([], []))))); trie_solve.
        replace t1 with
            (fst (snd (Node.put (get_keyslice k2) v0 (Node.first_cursor t0) (t0, a1))))
          by (rewrite Heqn_node_put2; reflexivity).
        replace t0 with
            (fst (snd (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a))) (fst (Node.empty a), l0))))
          by (rewrite Heqn_node_put1; reflexivity).
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite ?if_true by auto.
          rewrite BorderNode.next_cursor_terminate; trie_solve.
          simpl.
          unfold Node.get_key.
          erewrite (Node.get_put_diff
                   (elt := val))
          with
            (c3 := Node.make_cursor
                     (get_keyslice k1)
                     (fst
                       (snd
                          (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a)))
                                    (fst (Node.empty a), l0))))); trie_solve.
          rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; rewrite ?Zlength_list_repeat; rep_omega).
          admit.
        + unfold BorderNode.put_value.
          rewrite ?if_false by auto.
          simpl.
          rewrite ?if_false by auto.
          simpl.
          change (BorderNode.next_cursor
                    BorderNode.before_suffix
                    (list_repeat (Z.to_nat keyslice_length) nil, Some (get_suffix k1), value_of v1))
            with (BorderNode.before_suffix).
          simpl.
          unfold Node.get_key.
          erewrite (Node.get_put_diff
                   (elt := val))
          with
            (c3 := Node.make_cursor
                     (get_keyslice k1)
                     (fst
                       (snd
                          (Node.put (get_keyslice k1) v (Node.first_cursor (fst (Node.empty a)))
                                    (fst (Node.empty a), l0))))); trie_solve.
          admit.
    Admitted.   

    Theorem get_put_same: forall t c1 c2 k e a,
        Zlength k <> 0 ->
        abs_rel c1 (fst (snd (put k e c2 (t, a)))) ->
        abs_rel c2 t ->
        key_rel k c1 (fst (snd (put k e c2 (t, a)))) ->
        get c1 (fst (snd (put k e c2 (t, a)))) = Some (k, e).
    Proof.
      intros.
      destruct H1 as [? []].
      clear H1 H4.
      generalize dependent c1.
      generalize dependent c2.
      generalize dependent e.
      generalize dependent a.
      generalize dependent t.
      remember (length k) as n.
      generalize dependent k.
      induction n using (well_founded_induction lt_wf); intros.
      unfold get.
      unfold key_rel in H2.
      rewrite H2.
      rewrite put_equation.
      destruct t as [tableform listform].
      case_eq (list_get_error (get_keyslice k) listform); intros.
      - inv H3.
        repeat if_tac.
        + simpl.
          rewrite make_cursor_equation.
          unfold list_get_error.
          rewrite Node.Flattened.get_put_same by trie_solve.
          rewrite if_true by auto.
          rewrite if_true by auto.
          simpl.
          rewrite BorderNode.next_cursor_terminate by trie_solve.
          rewrite BorderNode.get_put_prefix_same by trie_solve.
          simpl.
          erewrite list_get_error_correct_table_key by eauto with trie.
          rewrite BorderNode.get_put_prefix_same by trie_solve.
          f_equal.
          admit.
        + destruct t as [[prefixes suffix_key] suffix_value].
          simpl in H5.
          subst.
          unfold BorderNode.get_suffix.
          rewrite if_true by auto.
          destruct suffix_value.
          * assert (bordernode_correct (prefixes, None, value_of v)) by trie_solve.
            inv H5.
            specialize (H16 eq_refl).
            inv H16.
          * destruct (put (get_suffix k) e c2 (t, a)) as [? []] eqn:Heqn.
            simpl.
            rewrite make_cursor_equation.
            unfold list_get_error.
            rewrite Node.Flattened.get_put_same by trie_solve.
            rewrite if_true by auto.
            rewrite if_false by auto.
            unfold BorderNode.get_suffix_pair, BorderNode.get_suffix.
            simpl.
            replace t0 with (fst (snd (put (get_suffix k) e c2 (t, a)))) by (rewrite Heqn; reflexivity).
            rewrite make_cursor_put_normalized.
            -- simpl.
               erewrite list_get_error_correct_table_key by eauto with trie.
               unfold get in H.
               assert (match normalize_cursor
                               (make_cursor (get_suffix k) (fst (snd (put (get_suffix k) e c2 (t, a))))) with
                       | Some c' => get_raw c'
                       | None => None
                       end = Some (get_suffix k, e)). {
                 eapply H with
                     (y := (length (get_suffix k)))
                     (c1 := make_cursor (get_suffix k) (fst (snd (put (get_suffix k) e c2 (t, a)))));
                   change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k); simpl.
                 - rewrite <- ?ZtoNat_Zlength.
                   rewrite Zlength_sublist by rep_omega.
                   apply Z2Nat.inj_lt; rep_omega.
                 - rewrite Zlength_sublist; rep_omega.
                 - reflexivity.
                 - assert (table_correct t) by trie_solve.
                   eassumption.
                 - admit.
                 - admit.
               }
               rewrite make_cursor_put_normalized in H5.
               ++ rewrite H5.
                  admit.
               ++ change (get_suffix) with (fun (k: string) => sublist keyslice_length (Zlength k) k).
                  simpl.
                  rewrite Zlength_sublist; rep_omega.
               ++ trie_solve.
            -- change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
               rewrite Zlength_sublist; rep_omega.
            -- trie_solve.
          * simpl.
            rewrite make_cursor_equation.
            unfold list_get_error.
            rewrite Node.Flattened.get_put_same by trie_solve.
            rewrite ?if_true by auto.
            rewrite ?if_false by auto.
            simpl.
            rewrite ?if_false by auto.
            simpl.
            change (BorderNode.next_cursor BorderNode.before_suffix (prefixes, Some (get_suffix k), value_of e)) with
                (BorderNode.before_suffix).
            simpl.
            erewrite list_get_error_correct_table_key by eauto with trie.
            f_equal.
            admit.
        + simpl.
          rewrite make_cursor_equation.
          unfold list_get_error.
          rewrite Node.Flattened.get_put_same by trie_solve.
          rewrite ?if_true by auto.
          rewrite ?if_false by auto.
          destruct t as [[prefixes ?] ?].
          simpl.
          rewrite ?if_false by auto.
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix (prefixes, Some (get_suffix k), value_of e)) with
              (BorderNode.before_suffix).
          simpl.
          erewrite list_get_error_correct_table_key by eauto with trie.
          f_equal.
          admit.
        + destruct t as [[prefixes suffix_key] suffix_value].
          simpl in *.
          destruct suffix_key; try congruence.
          assert (bordernode_correct (prefixes, Some s, suffix_value)) by trie_solve.
          inv H12.
          specialize (H19 ltac:(congruence)).
          destruct suffix_value; inv H19.
          destruct (create_pair (get_suffix k) s e v a) eqn:Heqn_create_pair.
          simpl.
          rewrite make_cursor_equation.
          unfold list_get_error.
          rewrite Node.Flattened.get_put_same by trie_solve.
          rewrite ?if_true by auto.
          rewrite ?if_false by auto.
          simpl.
          replace t with (fst (create_pair (get_suffix k) s e v a)) by (rewrite Heqn_create_pair; reflexivity).
          rewrite create_pair_normalized.
          * simpl.
            erewrite list_get_error_correct_table_key by eauto with trie.
            admit.
          * change (get_suffix k) with (sublist keyslice_length (Zlength k) k).
            rewrite Zlength_sublist; rep_omega.
          * rep_omega.
          * intro.
            subst.
            auto.
      - unfold abs_rel in H1.
        destruct H1 as [? []].
        inv H5.
        destruct (consume a).
        destruct (snd (Node.put (get_keyslice k) v (Node.first_cursor tableform) (tableform, l)))
                 eqn:Heqn'.
        simpl.
        rewrite make_cursor_equation.
        unfold list_get_error.
        rewrite Node.Flattened.get_put_same by trie_solve.
        rewrite if_true by auto.
        if_tac.
        + simpl.
          unfold BorderNode.put_value.
          rewrite if_true by auto.
          rewrite BorderNode.next_cursor_terminate by trie_solve.
          rewrite BorderNode.get_put_prefix_same; [ | constructor | list_solve ].
          simpl.
          replace t with (fst (snd (Node.put (get_keyslice k) v (Node.first_cursor tableform) (tableform, l)))) by (rewrite Heqn'; reflexivity).
          unfold Node.get_key.
          rewrite Node.get_put_same by trie_solve.
          rewrite upd_Znth_same by list_solve.
          f_equal.
          admit.
        + unfold BorderNode.put_value.
          rewrite if_false by auto.
          simpl.
          rewrite if_false by TrieKeyFacts.order.
          simpl.
          change (BorderNode.next_cursor BorderNode.before_suffix
                                         (list_repeat (Z.to_nat keyslice_length) nil, Some (get_suffix k), value_of e))
            with (BorderNode.before_suffix).
          simpl.
          unfold Node.get_key.
          replace t with (fst (snd (Node.put (get_keyslice k) v (Node.first_cursor tableform) (tableform, l)))) by (rewrite Heqn'; reflexivity). 
          rewrite Node.get_put_same by trie_solve.
          f_equal.
          admit.
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
