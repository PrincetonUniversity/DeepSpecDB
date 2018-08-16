(** * verif_put.v: Correctness proof of Trie.put *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.wand_frame.
Require Import DB.common.
Require Import DB.tactics.
Require Import DB.lemmas.

Require Import DB.functional.bordernode.
Require Import DB.functional.keyslice.

Require Import DB.representation.bordernode.
Require Import DB.representation.string.
Require Import DB.representation.key.
Require Import DB.representation.btree.
Require Import DB.representation.trie.

Require Import DB.specs.

Import Coq.Lists.List.ListNotations.

Definition Gprog : funspecs :=
  ltac:(with_library prog [
          UTIL_GetNextKeySlice_spec;
          surely_malloc_spec;
          BN_NewBorderNode_spec;
          BN_GetPrefixValue_spec;
          BN_GetSuffixValue_spec;
          BN_TestSuffix_spec;
          BN_GetLink_spec;
          BN_SetLink_spec;
          BN_HasSuffix_spec;
          BN_CompareSuffix_spec;
          BN_SetValue_spec;
          move_key_spec; new_key_spec; free_key_spec;
          push_cursor_spec; pop_cursor_spec;
          Imake_cursor_spec; Iget_value_spec; Iget_key_spec; Ifree_cursor_spec; Ifirst_cursor_spec;
          Iput_spec; Iempty_spec;
          bordernode_next_cursor_spec;
          strict_first_cursor_spec;
          create_pair_spec
       ]).

Tactic Notation "unwrap_get" "in" hyp(H) :=
      match type of H with
      | context[BTree.get_value ?c ?t = None] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.get_value in H;
        destruct (BTree.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.get_value ?c ?t = Some ?v] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.get_value in H;
        destruct (BTree.get c t) as [[] | ] eqn:Heqn; try congruence;
        inv H
      | context[BTree.get_key ?c ?t = None] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.get_key in H;
        destruct (BTree.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.get_key ?c ?t = Some _] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.get_key in H;
        destruct (BTree.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.Flattened.get_value ?c ?t = None] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.Flattened.get_value in H;
        destruct (BTree.Flattened.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.Flattened.get_value ?c ?t = Some _] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.Flattened.get_value in H;
        destruct (BTree.Flattened.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.Flattened.get_key ?c ?t = None] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.Flattened.get_key in H;
        destruct (BTree.Flattened.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      | context[BTree.Flattened.get_key ?c ?t = Some _] =>
        let Heqn := fresh "Heqn" in
        unfold BTree.Flattened.get_key in H;
        destruct (BTree.Flattened.get c t) as [[] | ] eqn:Heqn; try congruence;
        clear H
      end.

Lemma body_create_pair: semax_body Vprog Gprog f_create_pair create_pair_spec.
Proof.
  start_function.
  forward_call (Tsh, pk1, k1).
  forward_call (Tsh, pk2, k2).
  forward_if.
  - assert_PROP (0 <= Zlength k1 <= Int.max_unsigned) by (unfold cstring_len; entailer!).
    assert_PROP (0 <= Zlength k2 <= Int.max_unsigned) by (unfold cstring_len; entailer!).
    assert_PROP (get_keyslice k1 = get_keyslice k2). {
      unfold cstring_len.
      entailer!.
      apply repr_inj_unsigned;
        first [ apply get_keyslice_inrange | assumption ].
    }
    forward_if (temp _t'12 (if Trie.create_pair_aux_dec k1 k2 then Vint Int.one else Vint Int.zero)).
    {
      forward.
      entailer!.
      if_tac.
      - reflexivity.
      - rep_omega.
    }
    {
      forward.
      entailer!.
      if_tac.
      + assert (Zlength k2 <= keyslice_length) by rep_omega.
        destruct (Int.ltu (Int.repr 4) (Int.repr (Zlength k2))) eqn:Heqn.
        * apply ltu_inv in Heqn.
          rewrite ?Int.unsigned_repr in Heqn by rep_omega.
          rep_omega.
        * reflexivity.
      + destruct (Int.ltu (Int.repr 4) (Int.repr (Zlength k2))) eqn:Heqn.
        * reflexivity.
        * apply ltu_false_inv in Heqn.
          rewrite ?Int.unsigned_repr in Heqn by rep_omega.
          rep_omega.
    }
    forward_if.
    + if_tac in H7; try solve [inv H7].
      forward_call tt.
      Intros pbnode.
      forward_call (k1, pk1).
      Intros pk1'.
      forward_call (Tsh, k1, pk1', Tsh, @BorderNode.empty val _, pbnode, v1).
      forward_call (k2, pk2).
      Intros pk2'.
      forward_call (Tsh, k2, pk2', Tsh, (BorderNode.put_value k1 v1 BorderNode.empty), pbnode, v2).
      forward_call (k1, pk1').
      forward_call (k2, pk2').
      forward_call tt.
      Intros vret.
      destruct vret as [t pt].
      simpl fst in *.
      simpl snd in *.
      pose proof (BTree.empty_correct _ H9).
      forward_call (t, pt).
      Intros pc.
      forward_call ((get_keyslice k1), pbnode, t, pt, (BTree.first_cursor t), pc).
      { apply BTree.first_cursor_abs; assumption. }
      Intros vret.
      destruct vret as [tableform tablecursor].
      simpl fst in *.
      simpl snd in *.
      forward_call (tablecursor, pc).
      forward.
      pose (bnode := BorderNode.put_value k2 (Trie.value_of v2)
                                          (BorderNode.put_value k1 (Trie.value_of v1) BorderNode.empty)).
      pose (listform := BTree.Flattened.put_aux (get_keyslice k1) (pbnode, bnode) []).
      Exists (Trie.trienode_of pt tableform listform).
      Exists pt.
      Exists [(Trie.trienode_of pt tableform listform, tablecursor, bnode, BorderNode.length_to_cursor (Zlength k1))].
      entailer!.
      * eapply Trie.create_pair_case1 with (listform0 := listform);
          unfold BTree.Flattened.put, BTree.Flattened.empty, listform;
          repeat match goal with
                 | [|- _ /\ _] =>
                   split
                 end;
          eauto.
      * unfold listform.
        simpl.
        entailer!.
        -- unfold Trie.key_inrange.
           repeat first [ apply get_keyslice_inrange | constructor ].
        -- unfold bnode, BorderNode.put_value.
           simpl.
           if_tac; if_tac;
             simpl;
             rewrite ?Forall_map;
             rewrite <- ?upd_Znth_map;
             rewrite ?map_list_repeat;
             simpl;
             entailer!;
             repeat match goal with
                    | |- _ /\ _ => split
                    | |- Forall _ (upd_Znth _ _ _) =>
                      apply Forall_upd_Znth; [list_solve | | ]
                    | |- Forall _ (list_repeat _ _) =>
                      apply Forall_list_repeat
                    | _ => solve [auto]
                    end.
    + if_tac in H7; try solve [inv H7].
      forward_call tt.
      Intros pbnode.
      rewrite (cstring_len_split _ k1 pk1 keyslice_length) by rep_omega.
      rewrite (cstring_len_split _ k2 pk2 keyslice_length) by rep_omega.
      Intros.
      forward_call ((sublist keyslice_length (Zlength k1) k1),
                    (sublist keyslice_length (Zlength k2) k2),
                    (field_address (tarray tschar (Zlength k1)) [ArraySubsc keyslice_length] pk1),
                    (field_address (tarray tschar (Zlength k2)) [ArraySubsc keyslice_length] pk2),
                    v1, v2).
      {
        entailer!.
        rewrite ?field_address_offset by (auto with field_compatible).
        rewrite ?Zlength_sublist by rep_omega.
        repeat constructor.
      }
      {
        rewrite ?Zlength_sublist by rep_omega.
        repeat first [ split | rep_omega | auto ].
      }
      Intros vret.
      destruct vret as [[t' pt'] c'].
      simpl fst in *.
      simpl snd in *.
      forward_call (Tsh, @BorderNode.empty val _, pbnode, pt').
      forward_call tt.
      Intros vret.
      destruct vret as [t pt].
      simpl fst in *.
      simpl snd in *.
      pose proof (BTree.empty_correct _ H12).
      forward_call (t, pt).
      Intros pc.
      forward_call ((get_keyslice k1), pbnode, t, pt, (BTree.first_cursor t), pc).
      { apply BTree.first_cursor_abs; assumption. }
      Intros vret.
      destruct vret as [tableform tablecursor].
      simpl fst in *.
      simpl snd in *.
      forward_call (tablecursor, pc).
      forward.
      pose (bnode := BorderNode.put_suffix None (Trie.trie_of t') BorderNode.empty).
      pose (listform := BTree.Flattened.put_aux (get_keyslice k1) (pbnode, bnode) []).
      Exists (Trie.trienode_of pt tableform listform).
      Exists pt.
      Exists ((Trie.trienode_of pt tableform listform, tablecursor, bnode, BorderNode.before_suffix) :: c').
      entailer!.
      * eapply Trie.create_pair_case2 with (listform0 := listform);
          unfold BTree.Flattened.put, BTree.Flattened.empty, listform;
          repeat match goal with
                 | [|- _ /\ _] =>
                   split
                 end;
          eauto; rep_omega.
      * unfold listform.
        simpl.
        entailer!.
        -- unfold Trie.key_inrange.
           repeat first [ apply get_keyslice_inrange | constructor ].
        -- unfold bnode, BorderNode.put_value.
           simpl.
           Exists pt'.
           rewrite (cstring_len_split _ k1 pk1 keyslice_length) by rep_omega.
           rewrite (cstring_len_split _ k2 pk2 keyslice_length) by rep_omega.
           entailer!.
  - forward_call tt.
    Intros pbnode1.
    forward_call (k1, pk1).
    Intros pk1'.
    forward_call (Tsh, k1, pk1', Tsh, @BorderNode.empty val _, pbnode1, v1).
    forward_call tt.
    Intros pbnode2.
    forward_call (k2, pk2).
    Intros pk2'.
    forward_call (Tsh, k2, pk2', Tsh, @BorderNode.empty val _, pbnode2, v2).
    forward_call (k1, pk1').
    forward_call (k2, pk2').
    forward_call tt.
    Intros vret.
    destruct vret as [t pt].
    simpl fst in *.
    simpl snd in *.
    pose proof (BTree.empty_correct _ H4).
    forward_call (t, pt).
    Intros pc2.
    forward_call ((get_keyslice k2), pbnode2, t, pt, (BTree.first_cursor t), pc2).
    { apply BTree.first_cursor_abs; assumption. }
    Intros vret.
    destruct vret as [tableform2 tablecursor2].
    simpl fst in *.
    simpl snd in *.
    forward_call (tablecursor2, pc2).
    pose proof H6.
    apply BTree.put_correct in H6; [ | apply BTree.first_cursor_abs; assumption ].
    forward_call (tableform2, pt).
    Intros pc1.
    forward_call ((get_keyslice k1), pbnode1, tableform2, pt, (BTree.first_cursor tableform2), pc1).
    { apply BTree.first_cursor_abs; assumption. }
    Intros vret.
    destruct vret as [tableform1 tablecursor1].
    simpl fst in *.
    simpl snd in *.
    forward_call (tablecursor1, pc1).
    forward.
    pose (bnode1 := BorderNode.put_value k1 (Trie.value_of v1) BorderNode.empty).
    pose (bnode2 := BorderNode.put_value k2 (Trie.value_of v2) BorderNode.empty).
    pose (listform2 := BTree.Flattened.put_aux (get_keyslice k2) (pbnode2, bnode2) []).
    pose (listform1 := BTree.Flattened.put_aux (get_keyslice k1) (pbnode1, bnode1) listform2).
    Exists (Trie.trienode_of pt tableform1 listform1).
    Exists pt.
    Exists [(Trie.trienode_of pt tableform1 listform1, tablecursor1, bnode1, BorderNode.length_to_cursor (Zlength k1))].
    assert (get_keyslice k1 <> get_keyslice k2). {
      intro.
      apply H3.
      f_equal.
      assumption.
    }
    entailer!.
    + eapply Trie.create_pair_case3 with (listform3 := listform1) (listform4 := listform2);
        unfold BTree.Flattened.put, BTree.Flattened.empty, listform1, listform2;
        repeat match goal with
        | [|- _ /\ _] =>
          split
        end;
        eauto.
    + unfold listform1, listform2.
      simpl.
      if_tac.
      * entailer!.
        -- unfold Trie.key_inrange.
           repeat first [ apply get_keyslice_inrange | constructor ].
        -- unfold iter_sepcon.
           unfold bnode1, bnode2, BorderNode.put_value.
           simpl.
           repeat if_tac;
             rewrite ?Forall_map;
             rewrite <- ?upd_Znth_map;
             rewrite ?map_list_repeat;
             simpl;
             entailer!;
             repeat match goal with
                    | |- _ /\ _ => split
                    | |- Forall _ (upd_Znth _ _ _) =>
                      apply Forall_upd_Znth; [list_solve | | ]
                    | |- Forall _ (list_repeat _ _) =>
                      apply Forall_list_repeat
                    | _ => solve [auto]
                    end.
      * entailer!.
        rewrite ?if_false by auto.
        -- unfold Trie.key_inrange.
           repeat first [ apply get_keyslice_inrange | constructor ].
        -- unfold iter_sepcon.
           unfold bnode1, bnode2, BorderNode.put_value.
           rewrite ?(if_false _ (BTree.Flattened.KeyFacts.eq_dec (get_keyslice k1) (get_keyslice k2))) by auto.
           simpl.
           repeat if_tac;
             rewrite ?Forall_map;
             rewrite <- ?upd_Znth_map;
             rewrite ?map_list_repeat;
             simpl;
             entailer!;
             repeat match goal with
                    | |- _ /\ _ => split
                    | |- Forall _ (upd_Znth _ _ _) =>
                      apply Forall_upd_Znth; [list_solve | | ]
                    | |- Forall _ (list_repeat _ _) =>
                      apply Forall_list_repeat
                    | _ => solve [auto]
                    end.
Qed.
