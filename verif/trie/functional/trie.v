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
                  | trie_of t' =>
                    match strict_first_cursor t' with
                    | Some c' =>
                      Some ((t, table_cursor', bnode', (before_prefix len)) :: c')
                    | None =>
                      None
                    end
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

    Definition list_get_error k t: option (@BorderNode.table link) :=
      match Node.Flattened.get (Node.Flattened.make_cursor k t) t with
      | Some (k', v) =>
        if KeysliceType.eq_dec k k' then
          Some v
        else
          None
      | None => None
      end.

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
