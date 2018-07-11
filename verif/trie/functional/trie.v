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
    Definition cursor: Type := list (trie * Node.cursor val * option Z).
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

    Function make_cursor (k: key) (t: trie) {measure length k}: cursor :=
      let keyslice := get_keyslice k in
      match t with
      | trienode_of tableform listform =>
        match Node.Flattened.get_value (Node.Flattened.make_cursor (keyslice) listform) listform with
        | Some bnode =>
          if (Z_le_dec (Zlength k) keyslice_length) then
          (* prefix case, which we need only to return the current cursor *)
            [(t, Node.make_cursor keyslice tableform, Some (Zlength k))]
          else
            if BorderNode.is_link bnode then
              match BorderNode.get_suffix None bnode with
              | value_of _ => []
              | nil => []
              | trie_of t' =>
                (t, Node.make_cursor keyslice tableform, None) :: make_cursor (get_suffix k) t'
              end
            else
              [(t, Node.make_cursor keyslice tableform, None)]
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

    Fixpoint get_key (c: cursor) (t: trie): option key :=
      match c with
      | (_, _, inr (Some _)) :: _ :: _ => (* invalid cursor: suffix portion but not last slice *)
        None
      | (_, _, inl _) :: _ :: _ => (* invalid cursor: prefix portion but not last slice *)
        None
      | [] => (* invalid cursor: reach the end of cursor slices without ending in either prefix of suffix *)
        None
      | [(_, table_cursor, inr (Some suffix))] => (* valid cursor: at the end we reach a suffix portion *)
        Some suffix
      | [(t, table_cursor, inl len)] => (* valid cursor: at the end we reach a prefix portion *)
        let (_, tableform, _) := t in
        match NodeTable.get_key table_cursor tableform with
        | Some keyslice => Some (reconstruct_keyslice (keyslice, len))
        | None => None
        end
      | (t, table_cursor, inr None) :: c' => (* recursive part *)
        let (_, tableform, listform) := t in
        match NodeTable.get_key table_cursor tableform with
        | Some keyslice =>
          match NodeTable.Flattened.get keyslice listform with
          | Some bnode =>
            match BorderNode.get_suffix None bnode with
            | value_of _ => None
            | nil => None
            | trie_of t' =>
              match get_key c' t' with
              | Some k' => Some ((reconstruct_keyslice (keyslice, keyslice_length)) ++ k')
              | None => None
              end
            end
          | None => None (* impossible *)
          end
        | None => None
        end
      end.

    Fixpoint get (c: cursor) (t: trie): option value :=
      match c with
      | (_, _, inr (Some _)) :: _ :: _ => (* invalid cursor: suffix portion but not last slice *)
        None
      | (_, _, inl _) :: _ :: _ => (* invalid cursor: prefix portion but not last slice *)
        None
      | [] => (* invalid cursor: reach the end of cursor slices without ending in either prefix of suffix *)
        None
      | [(t, table_cursor, inr (Some suffix))] => (* valid cursor: at the end we reach a suffix portion *)
        let (_, tableform, listform) := t in
        match NodeTable.get_key table_cursor tableform with
        | Some keyslice =>
          match NodeTable.Flattened.get keyslice listform with
          | Some bnode =>
            match BorderNode.get_suffix (Some suffix) bnode with
            | value_of v => Some v
            | nil => None
            | trie_of _ => None
            end
          | None => None (* impossible *)
          end
        | None => None
        end
      | [(t, table_cursor, inl len)] => (* valid cursor: at the end we reach a prefix portion *)
        let (_, tableform, listform) := t in
        match NodeTable.get_key table_cursor tableform with
        | Some keyslice =>
          match NodeTable.Flattened.get keyslice listform with
          | Some bnode =>
            match BorderNode.get_prefix len bnode with
            | value_of v => Some v
            | nil => None
            | trie_of _ => None
            end
          | None => None (* impossible *)
          end
        | None => None
        end
      | (t, table_cursor, inr None) :: c' => (* recursive part *)
        let (_, tableform, listform) := t in
        match NodeTable.get_key table_cursor tableform with
        | Some keyslice =>
          match NodeTable.Flattened.get keyslice listform with
          | Some bnode =>
            match BorderNode.get_suffix None bnode with
            | value_of _ => None
            | nil => None
            | trie_of t' =>
              match get c' t' with
              | Some v => Some v
              | None => None
              end
            end
          | None => None (* impossible *)
          end
        | None => None
        end
      end.

    (* For now, the definition of put ignore the cursor for simplicity *)

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

    Definition consume_addr (l: list val) :=
      (hd default l, tl l).


    Function create_pair (k1 k2: key) (v1 v2: link) (l: list val) {measure length k1} : trie :=
      let keyslice1 := get_keyslice k1 in
      let keyslice2 := get_keyslice k2 in
      if eq_dec keyslice1 keyslice2 then
        if create_pair_aux_dec k1 k2 then
          let bnode := BorderNode.put_value k2 v2 (BorderNode.put_value k1 v1 BorderNode.empty) in
          let (trie_addr, l) := consume_addr l in
          let (bnode_addr, l) := consume_addr l in
          trienode_of trie_addr
                      (NodeTable.put keyslice2 bnode_addr l (NodeTable.first_cursor NodeTable.empty) NodeTable.empty)
                      (NodeTable.Flattened.put keyslice2 bnode NodeTable.Flattened.empty)
        else
          trienode_of (
              NodeTable.Flattened.put keyslice1 (
                                    BorderNode.put_suffix None (
                                                            trie_of (create_pair (get_suffix k1) (get_suffix k2) v1 v2)
                                                          ) BorderNode.empty
                                  ) NodeTable.Flattened.empty
            )
      else
        let tmp := NodeTable.Flattened.put keyslice1 (
                                         BorderNode.put_value k1 v1 BorderNode.empty
                                       ) NodeTable.Flattened.empty
        in trienode_of (
               NodeTable.Flattened.put keyslice2 (
                                     BorderNode.put_value k2 v2 BorderNode.empty
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
        match NodeTable.Flattened.get keyslice trienode with
        | Some bordernode =>
          if Z_le_dec (Zlength k) (keyslice_length) then
            (* overwrite prefix *)
            trienode_of (
                NodeTable.Flattened.put keyslice (
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
                    NodeTable.Flattened.put keyslice (
                                          BorderNode.put_suffix (None) (
                                                                  trie_of (put (get_suffix k) v t')
                                                                ) bordernode
                                        ) trienode
                  )
              | nil =>
                (* new suffix *)
                trienode_of (
                    NodeTable.Flattened.put keyslice (
                                          BorderNode.put_suffix (Some (get_suffix k)) (value_of v) BorderNode.empty
                                        ) NodeTable.Flattened.empty
                  )
              end
            else
              if BorderNode.test_suffix (Some (get_suffix k)) bordernode then
                (* overwrite suffix *)
                trienode_of (
                    NodeTable.Flattened.put keyslice (
                                          BorderNode.put_suffix (Some (get_suffix k)) (value_of v) bordernode
                                        ) trienode
                  )
              else
                (* new layer with two suffix *)
                match BorderNode.get_suffix_pair bordernode with
                | (Some k', v') =>
                  trienode_of (
                      NodeTable.Flattened.put keyslice (
                                            BorderNode.put_suffix
                                              None (
                                                trie_of (create_pair (get_suffix k) k' (value_of v) v')
                                              ) bordernode
                                          ) trienode
                    )
                | (None, v') =>
                  empty
                end
        | None =>
          (* new btree kv pair *)
          trienode_of (
              NodeTable.Flattened.put keyslice (
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

    Definition next_cursor (c: cursor) (t: trie): cursor. Admitted.
    Definition prev_cursor (c: cursor) (t: trie): cursor. Admitted.
    Definition first_cursor (t: trie): cursor. Admitted.
    Definition last_cursor (t: trie): cursor. Admitted.

    Definition abs_rel (c: cursor) (t: trie): Prop. Admitted.
    Definition key_rel (k: key) (c: cursor) (t: trie): Prop :=
      abs_rel c t /\ get_key c t = Some k.
    Definition eq_cursor (c1 c2: cursor) (t: table) :=
      abs_rel c1 t /\ abs_rel c2 t /\ get_key c1 t = get_key c2 t.

    Definition cursor_correct (c: cursor): Prop := True.

    Inductive trie_invariant: trie -> Prop :=
    | invariant_trienode:
        forall v btreeform listform,
          NodeTable.Flattened.sorted listform ->
          Forall (fun binding => bordernode_invariant (snd binding)) listform ->
          map fst (NodeTable.flatten btreeform) = map fst listform ->
          trie_invariant (trienode_of v btreeform listform)
    with
    bordernode_invariant: BorderNode.table -> Prop :=
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
           match k with
           | Some s =>
             match v with
             | value_of _ => True
             | trie_of _ => False
             | nil => False
             end /\ Zlength s > 0
           | None =>
             match v with
             | value_of _ => False
             | trie_of _ => True
             | nil => True
             end
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

    Lemma empty_invariant: forall t, trie_invariant empty.
    Proof.
      constructor; auto with sortedtable.
    Qed.
    Hint Resolve empty_invariant: trie.

    Definition table_correct (t: table): Prop. Admitted.
    Section Specs.
      Variable t: table elt.
      Variable c c1 c2 c3: cursor elt.
      Variable k k1 k2 k3: key.
      Variable e e1 e2: elt.

      Axiom abs_correct: abs_rel c t -> cursor_correct c /\ table_correct t.
      
      Hypothesis Htable_correct: table_correct t.
      Axiom make_cusor_binded: abs_rel (make_cursor k t) t.
      Axiom put_bind:
        let (new_cursor, new_table) := put c e t in
        abs_rel new_cursor new_table.
      Axiom next_cursor_bind: abs_rel c t -> abs_rel (next_cursor c t) t.
      Axiom prev_cursor_bind: abs_rel c t -> abs_rel (prev_cursor c t) t.
      Axiom first_cursor_bind: abs_rel (first_cursor t) t.
      Axiom last_cursor_bind: abs_rel (last_cursor t) t.
      Axiom get_put_same:
        key_rel k c1 (snd (put c2 e t)) ->
        key_rel k c2 t ->
        get c1 (snd (put c2 e t)) = Some e.
      Axiom get_put_diff:
        k1 <> k2 ->
        key_rel k1 c1 (snd (put c2 e t)) ->
        key_rel k2 c2 t ->
        key_rel k1 c3 t ->
        get c1 (snd (put c2 e t)) = get c3 t.

      Axiom get_last:
        get (last_cursor t) t = None.
      Axiom get_empty:
        abs_rel c t -> empty t -> get c t = None.

      Axiom make_cursor_key:
        key_rel k (make_cursor k t) t.
      Axiom next_prev:
        abs_rel c t -> ~ eq_cursor c (last_cursor t) t -> eq_cursor c (prev_cursor (next_cursor c t) t) t.
      Axiom prev_next:
        abs_rel c t -> ~ eq_cursor c (first_cursor t) t -> eq_cursor c (next_cursor (prev_cursor c t) t) t.
      Axiom next_order:
        ~ eq_cursor c (last_cursor t) t -> key_rel k1 c t -> key_rel k2 (next_cursor c t) t -> KeyType.lt k1 k2.
      Axiom prev_order:
        ~ eq_cursor c (first_cursor t) t -> key_rel k1 c t -> key_rel k2 (prev_cursor c t) t -> KeyType.lt k2 k1.
      Axiom next_compact:
        ~ eq_cursor c (last_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (next_cursor c t) t ->
        ~ key_rel k3 c t -> KeyType.lt k1 k3 /\ KeyType.lt k3 k2.
      Axiom prev_compact:
        ~ eq_cursor c (first_cursor t) t ->
        key_rel k1 c t -> key_rel k2 (prev_cursor c t) t ->
        ~ key_rel k3 c t -> KeyType.lt k2 k3 /\ KeyType.lt k3 k1.
    End Specs.
  End Types.
End Trie.
    Function get (k: key) (t: trie) {measure length k}: option value :=
      let keyslice := get_keyslice k in 
      match t with
      | trienode_of trienode =>
        match SortedListTable.get keyslice trienode with
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

    Lemma create_pair_invariant: forall k1 k2 v1 v2,
        Zlength k1 > 0 ->
        Zlength k2 > 0 ->
        trie_invariant (create_pair k1 k2 (value_of v1) (value_of v2)).
    Proof.
      intros.
      remember (Zlength k1) as len1.
      generalize dependent k2.
      generalize H.
      generalize dependent k1.
      assert (1 <= len1) by omega.
      generalize H0.
      clear H0 H.
      apply (Z_induction (fun len' => forall k1, len' = Zlength k1 -> len' > 0 -> forall k2 : list byte, Zlength k2 > 0 -> trie_invariant (create_pair k1 k2 (value_of v1) (value_of v2))) 1).
      {
        intros.
        destruct k1 as [ | ? [ | ]].
        - rewrite Zlength_correct in H.
          simpl in H.
          congruence.
        - clear H H0.
          rewrite create_pair_equation.
          repeat if_tac.
          + constructor; [ auto with sortedtable | ].
            apply SortedListTable.put_Prop; [ | constructor].
            unfold BorderNode.put_value.
            repeat if_tac;
              constructor;
              repeat first [
                       apply Forall_upd_Znth |
                       solve [repeat first [
                                       rewrite upd_Znth_Zlength |
                                       rewrite Zlength_list_repeat |
                                       replace (Zlength [i]) with 1 by list_solve; rep_omega
                             ]] |
                       apply Forall_list_repeat |
                       solve [auto with trie] |
                       split3; first [ rewrite Zlength_sublist; rep_omega | auto with trie]
                     ].
          + replace (Zlength [i]) with 1 in H0 by list_solve.
            rep_omega.
          + constructor; [ auto with sortedtable | ].
            (* amazingly, constructor can solve equation with Zlength, list_repeat and some opaque constants *)
            repeat first  [
                     apply SortedListTable.put_Prop |
                     constructor
                   ].
            unfold BorderNode.put_value.
            repeat if_tac;
              constructor;
              repeat first [
                       apply Forall_upd_Znth |
                       solve [repeat first [
                                       rewrite upd_Znth_Zlength |
                                       rewrite Zlength_list_repeat |
                                       rep_omega
                             ]] |
                       apply Forall_list_repeat |
                       solve [auto with trie] |
                       split3; first [ rewrite Zlength_sublist; rep_omega | auto with trie]
                     ].
        - rewrite ?Zlength_cons in H.
          list_solve.
      }
      {
        intros.
        rewrite create_pair_equation.
        repeat if_tac.
        + constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | constructor].
          unfold BorderNode.put_value.
          repeat if_tac;
            constructor;
            repeat first [
                     apply Forall_upd_Znth |
                     apply Forall_list_repeat |
                     solve [
                         repeat first [
                                  rewrite upd_Znth_Zlength |
                                  rewrite Zlength_list_repeat |
                                  rep_omega
                                ]
                       ] |
                     solve [auto with trie] |
                     split3; first [ rewrite Zlength_sublist; rep_omega | auto with trie]
                   ].
        + constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | constructor].
          unfold BorderNode.put_value.
          repeat if_tac;
            constructor;
            repeat first [
                     apply Forall_upd_Znth |
                     apply Forall_list_repeat |
                     solve [
                         repeat first [
                                  rewrite upd_Znth_Zlength |
                                  rewrite Zlength_list_repeat |
                                  rep_omega
                                ]
                       ] |
                     solve [auto with trie] |
                     split3; first [ rewrite Zlength_sublist; rep_omega | auto with trie]
                   ].
          constructor.
          apply H with (Zlength (get_suffix k1)); unfold get_suffix; rewrite ?Zlength_sublist; rep_omega.
        + constructor; [auto with sortedtable | ].
          repeat first  [
                   apply SortedListTable.put_Prop |
                   constructor
                 ];
            unfold BorderNode.put_value;
            repeat if_tac;
            constructor;
            repeat first [
                     apply Forall_upd_Znth |
                     solve [repeat first [
                                     rewrite upd_Znth_Zlength |
                                     rewrite Zlength_list_repeat |
                                     rep_omega
                           ]] |
                     apply Forall_list_repeat |
                     solve [auto with trie] |
                     split3; first [ rewrite Zlength_sublist; rep_omega | auto with trie]
                   ].
      }
    Qed.
    
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
        remember (SortedListTable.get keyslice t) as btree_result.
        destruct btree_result; repeat if_tac; try rep_omega.
        - inv H0.
          constructor.
          + auto with sortedtable.
          + apply SortedListTable.put_Prop; [ | assumption].
            symmetry in Heqbtree_result.
            apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
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
          + auto with sortedtable.
          + apply SortedListTable.put_Prop; [ | assumption].
            unfold BorderNode.put_value.
            rewrite if_true by rep_omega.
            constructor.
            * rewrite upd_Znth_Zlength; rewrite Zlength_list_repeat; rep_omega.
            * apply Forall_upd_Znth; [rewrite Zlength_list_repeat; rep_omega | | auto with trie].
              apply Forall_forall.
              intros.
              apply in_list_repeat in H0.
              subst.
              change default_val with nil.
              auto with trie.
            * change default_val with nil.
              auto with trie.
      }
      {
        intros ? Hinduction ? H0 ? ? Hbound.
        destruct t.
        rewrite put_equation.
        remember (get_keyslice k) as keyslice.
        remember (SortedListTable.get keyslice t) as btree_result.
        destruct btree_result; repeat if_tac.
        - inv H0.
          constructor.
          + auto with sortedtable.
          + apply SortedListTable.put_Prop; [ | assumption].
            symmetry in Heqbtree_result.
            apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
            rewrite Forall_forall in H4.
            apply H4 in Heqbtree_result.
            simpl in Heqbtree_result.
            inv Heqbtree_result.
            constructor; [rewrite upd_Znth_Zlength; rep_omega | | assumption].
            apply Forall_upd_Znth.
            * rep_omega.
            * assumption.
            * auto with trie.
        - remember (BorderNode.get_suffix None t0) as link.
          destruct link; auto with trie.
          inv H0.
          constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | assumption].
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
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
          + constructor; [ auto with sortedtable | ].
            apply SortedListTable.put_Prop; [ | constructor].
            constructor.
            * rewrite Zlength_list_repeat; rep_omega.
            * apply Forall_list_repeat.
              change default_val with nil.
              auto with trie.
            * split3; first [ unfold get_suffix; rewrite Zlength_sublist; rep_omega | auto with trie].
        - inv H0.
          constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | assumption].
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H6.
          apply H6 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          constructor; [omega | assumption | ].
          split3; auto with trie.
          unfold get_suffix.
          rewrite Zlength_sublist by rep_omega.
          apply Znot_le_gt in H1.
          omega.
        - inv H0.
          destruct t0 as [[? []]]; [ | contradiction].
          simpl in *.
          assert (get_suffix k <> s) by (intro; apply H3; f_equal; assumption).
          clear H3.
          constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | assumption].
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H6.
          apply H6 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          constructor; [ omega | assumption | ].
          split; auto.
          constructor.
          destruct H9 as [? []]; destruct l0; try contradiction.
          apply create_pair_invariant;
            repeat first [
                     unfold get_suffix; rewrite Zlength_sublist |
                     rep_omega
                   ].
        - inv H0.
          constructor; [ auto with sortedtable | ].
          apply SortedListTable.put_Prop; [ | assumption].
          unfold BorderNode.put_value.
          if_tac.
          + constructor.
            * rewrite upd_Znth_Zlength; rewrite Zlength_list_repeat; rep_omega.
            * apply Forall_upd_Znth; [rewrite Zlength_list_repeat; rep_omega | | auto with trie].
              apply Forall_forall.
              intros.
              apply in_list_repeat in H0.
              subst.
              change default_val with nil.
              auto with trie.
            * change default_val with nil.
              auto with trie.
          + constructor.
            * rewrite Zlength_list_repeat; rep_omega.
            * apply Forall_forall.
              intros.
              apply in_list_repeat in H0.
              subst.
              change default_val with nil.
              auto with trie.
            * split3; auto with trie.
              rewrite Zlength_sublist by rep_omega.
              apply Znot_le_gt in H.
              omega.
      }
    Qed.

    Theorem get_empty: forall k, get k empty = None.
    Proof.
      intros.
      rewrite get_equation.
      reflexivity.
    Qed.

    Lemma get_create_pair_same1: forall k1 k2 v1 v2,
        0 < Zlength k1 ->
        0 < Zlength k2 ->
        k1 <> k2 ->
        get k1 (create_pair k1 k2 (value_of v1) (value_of v2)) = Some v1.
    Proof.
      intros.
      generalize dependent k2.
      remember (Zlength k1) as len.
      generalize dependent k1.
      generalize H.
      assert (1 <= len) by omega.
      generalize H0.
      clear H H0.
      apply (Z_induction (fun len => 0 < len -> forall k1, len = Zlength k1 -> forall k2, 0 < Zlength k2 -> k1 <> k2 -> get k1 (create_pair k1 k2 (value_of v1) (value_of v2)) = Some v1) 1).
      {
        intros.
        destruct k1 as [ | ? [ | ]].
        - rewrite Zlength_correct in H0.
          simpl in H0.
          congruence.
        - clear H0 H.
          rewrite create_pair_equation.
          repeat if_tac.
          + rewrite get_equation.
            rewrite H.
            rewrite SortedListTable.get_put_same.
            rewrite if_true by (replace (Zlength [i]) with 1 by list_solve; rep_omega).
            unfold BorderNode.put_value.
            if_tac.
            * rewrite BorderNode.get_put_prefix_diff; replace (Zlength [i]) with 1 by list_solve; try rep_omega.
              -- rewrite if_true by rep_omega.
                 rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
              -- rewrite if_true by rep_omega.
                 apply BorderNode.put_prefix_invariant; [ apply BorderNode.empty_invariant | rep_omega].
              -- pose proof (keyslice_inj1 _ _ H2 H H0).
                 replace (Zlength [i]) with 1 in * by list_solve.
                 rep_omega.
            * rewrite BorderNode.get_put_non_interference1.
              replace (Zlength [i]) with 1 by list_solve.
              rewrite if_true by rep_omega.
              rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
          + replace (Zlength [i]) with 1 in H0 by list_solve.
            rep_omega.
          + rewrite get_equation.
            rewrite SortedListTable.get_put_diff by auto.
            rewrite SortedListTable.get_put_same.
            assert (Zlength [i] = 1) by list_solve.
            rewrite if_true by rep_omega.
            unfold BorderNode.put_value.
            rewrite if_true by rep_omega.
            rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
        - rewrite ?Zlength_cons in H0.
          list_solve.
      }
      {
        intros.
        rewrite create_pair_equation.
        repeat if_tac.
        - rewrite get_equation.
          rewrite H4.
          rewrite SortedListTable.get_put_same.
          destruct H5.
          + rewrite if_true by rep_omega.
            unfold BorderNode.put_value.
            if_tac.
            * rewrite BorderNode.get_put_prefix_diff; try rep_omega.
              -- rewrite if_true by rep_omega.
                 rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
              -- rewrite if_true by rep_omega.
                 apply BorderNode.put_prefix_invariant; [ apply BorderNode.empty_invariant | rep_omega].
              -- pose proof (keyslice_inj1 _ _ H3 H4 ltac:(eauto)).
                 rep_omega.
            * rewrite BorderNode.get_put_non_interference1.
              rewrite if_true by rep_omega.
              rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
          + if_tac.
            * unfold BorderNode.put_value.
              rewrite if_true by rep_omega.
              rewrite BorderNode.get_put_prefix_diff; try rep_omega.
              -- rewrite if_true by rep_omega.
                 rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
              -- rewrite if_true by rep_omega.
                 apply BorderNode.put_prefix_invariant; [ apply BorderNode.empty_invariant | rep_omega].
              -- pose proof (keyslice_inj1 _ _ H3 H4 ltac:(eauto)).
                 rep_omega.
            * unfold BorderNode.put_value.
              rewrite if_false;
                repeat first [
                         rewrite if_true by rep_omega |
                         rewrite if_false by rep_omega
                       ]; simpl; [ | congruence].
              unfold get_suffix.
              rewrite if_true by auto.
              reflexivity.
        - rewrite get_equation.
          rewrite SortedListTable.get_put_same.
          destruct H5.
          rewrite if_false by rep_omega.
          rewrite if_true by auto.
          rewrite BorderNode.get_put_suffix_same.
          apply H with (Zlength (get_suffix k1)); unfold get_suffix; rewrite ?Zlength_sublist; try rep_omega.
          apply (keyslice_inj3); auto.
        - rewrite get_equation.
          rewrite SortedListTable.get_put_diff by auto.
          rewrite SortedListTable.get_put_same.
          unfold BorderNode.put_value.
          if_tac.
          + rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
          + rewrite if_false by (simpl; congruence).
            rewrite BorderNode.get_put_suffix_same.
            reflexivity.
      }
    Qed.

    Theorem get_put_same: forall k v s,
        trie_invariant s ->
        0 < Zlength k ->
        get k (put k v s) = Some v.
    Proof.
      intros.
      remember (Zlength k) as len.
      generalize dependent s.
      generalize dependent k.
      assert (1 <= len) by omega.
      generalize H0.
      generalize H.
      clear H0 H.
      apply (Z_induction (fun len' => 0 < len' -> forall k, len' = Zlength k -> forall s: trie, trie_invariant s -> get k (put k v s) = Some v) 1).
      {
        intros.
        rewrite put_equation.
        destruct s.
        inv H1.
        remember (get_keyslice k) as keyslice.
        remember (SortedListTable.get keyslice t) as btree_result.
        destruct btree_result; repeat if_tac; rewrite get_equation; try rep_omega.
        - rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          rewrite if_true by auto.
          rewrite BorderNode.get_put_prefix_same; [ reflexivity | | rep_omega].
          destruct t0 as [[]].
          unfold BorderNode.invariant.
          simpl.
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H4.
          apply H4 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          assumption.
        - rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          rewrite if_true by rep_omega.
          unfold BorderNode.put_value.
          rewrite if_true by rep_omega.
          rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
      }
      {
        intros.
        rewrite put_equation.
        destruct s.
        inv H2.
        remember (get_keyslice k) as keyslice.
        remember (SortedListTable.get keyslice t) as btree_result.
        destruct btree_result; repeat if_tac; rewrite get_equation.
        - rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          rewrite if_true by auto.
          rewrite BorderNode.get_put_prefix_same; [ reflexivity | | rep_omega].
          destruct t0 as [[]].
          unfold BorderNode.invariant.
          simpl.
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H5.
          apply H5 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          assumption.
        - symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H5.
          apply H5 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          simpl in H2.
          subst.
          simpl.
          destruct v0; try solve [destruct H7; contradiction].
          + rewrite SortedListTable.get_put_same.
            rewrite if_false by rep_omega.
            rewrite if_true by auto.
            simpl.
            destruct t0.
            destruct H7.
            inv H2.
            apply H with (Zlength (get_suffix k));
              first [
                  rep_omega |
                  unfold get_suffix; rewrite Zlength_sublist; rep_omega |
                  auto
                ].
          + simpl.
            rewrite if_true by auto.
            rewrite if_false by rep_omega.
            rewrite if_false by (simpl; congruence).
            simpl.
            rewrite if_true by auto.
            reflexivity.
        - rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          rewrite if_false by rep_omega.
          destruct t0 as [[]].
          simpl.
          rewrite if_true by auto.
          reflexivity.
        - destruct t0 as [[]].
          simpl in *.
          destruct o; try contradiction.
          rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          rewrite if_false by rep_omega.
          rewrite if_true by auto.
          simpl.
          symmetry in Heqbtree_result.
          apply SortedListTable.get_in in Heqbtree_result; [ | assumption].
          rewrite Forall_forall in H5.
          apply H5 in Heqbtree_result.
          simpl in Heqbtree_result.
          inv Heqbtree_result.
          destruct l0; try (destruct H11 as [ ? []]; contradiction).
          rewrite get_create_pair_same1.
          + reflexivity.
          + unfold get_suffix.
            rewrite Zlength_sublist; rep_omega.
          + rep_omega.
          + congruence.
        - rewrite Heqkeyslice.
          rewrite SortedListTable.get_put_same.
          unfold BorderNode.put_value.
          if_tac.
          + rewrite BorderNode.get_put_prefix_same; [ reflexivity | apply BorderNode.empty_invariant | rep_omega].
          + rewrite if_false by (simpl; congruence).
            rewrite BorderNode.get_put_suffix_same.
            reflexivity.
      }
    Qed.

    Theorem get_put_diff: forall k1 k2 v s,
        k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
    Proof.
    Admitted.
  End Parametrized.
End Trie.
