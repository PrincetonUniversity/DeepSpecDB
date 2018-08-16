(** * verif_make_cursor.v: Correctness proof of Trie.make_cursor *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.new_tactics.
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
          BN_GetPrefixValue_spec;
          BN_GetSuffixValue_spec;
          BN_TestSuffix_spec;
          BN_GetLink_spec;
          BN_HasSuffix_spec;
          BN_CompareSuffix_spec;
          move_key_spec; new_key_spec; free_key_spec;
          push_cursor_spec;
          Imake_cursor_spec; Iget_value_spec; Iget_key_spec; Ifree_cursor_spec;
          make_cursor_spec
       ]).

Lemma body_make_cursor: semax_body Vprog Gprog f_make_cursor make_cursor_spec.
Proof.
  start_function.
  unfold key_rep.
  Intros pk'.
  forward.
  forward.
  forward_call (Tsh, pk', k).
  forward.
  destruct t as [addr tableform listform].
  unfold Trie.trie_rep; fold Trie.trie_rep.
  Intros.
  subst addr.
  pose proof H as H'.
  inv H.
  pose proof get_keyslice_inrange k.
  forward_call (get_keyslice k, tableform, pt).
  Intros pnode_cursor.
  forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor, tableform, pt, v_obtained_keyslice).
  { apply BTree.make_cursor_abs. assumption. }
  forward_if (temp _t'8 match (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) with
                         | Some k' => if eq_dec k' (get_keyslice k) then Vint Int.one else Vint Int.zero
                         | None => Vint Int.zero
                         end).
  {
    (* if true *)
    destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) eqn:Heqn; try solve [inv H1].
    forward.
    forward.
    entailer!.
    if_tac.
    - subst.
      rewrite Int.eq_true.
      reflexivity.
    - rewrite Int.eq_false; [ reflexivity | ].
      intro.
      apply repr_inj_unsigned in H15.
      + congruence.
      + rep_omega.
      + pose proof (@BTree.flatten_invariant val).
        specialize (H16 tableform ltac:(assumption)) as [? ?].
        specialize (H17 (get_keyslice k)
                        (BTree.make_cursor (get_keyslice k) tableform)
                        (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))).
        specialize (H17 ltac:(apply BTree.make_cursor_key; assumption)).
        specialize (H17 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H17 ltac:(apply BTree.make_cursor_abs; assumption)).
        specialize (H17 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        unfold BTree.get_key in Heqn.
        rewrite H17 in Heqn.
        destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                                      (BTree.flatten tableform)) as [[] | ] eqn:Heqn'; try congruence.
        inv Heqn.
        pose proof (BTree.Flattened.get_in_weak
                      (BTree.flatten tableform)
                      (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                      k0
                      v
                      Heqn').
        apply in_map with (f := fst) in H18.
        simpl in H18.
        apply Forall_map in H0.
        change Z with BTree.Flattened.key in H0.
        rewrite <- H6 in H0.
        rewrite Forall_forall in H0.
        apply H0 in H18.
        unfold Trie.key_inrange in H18.
        rep_omega.
  }
  {
    (* if false *)
    destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) eqn:Heqn; try solve [inv H1].
    forward.
    entailer!.
  }
  deadvars.
  forward_if (
    PROP ()
         LOCAL (temp _node_cursor pnode_cursor;
                lvar _ret_value (tptr tvoid) v_ret_value;
                lvar _obtained_keyslice tuint v_obtained_keyslice)
    SEP (BTree.table_rep tableform pt;
         match BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform with
         | Some k0 => data_at Tsh tuint (Vint (Int.repr k0)) v_obtained_keyslice
         | None => data_at_ Tsh tuint v_obtained_keyslice
         end;
         data_at_ Tsh (tptr tvoid) v_ret_value;
         iter_sepcon (Trie.bnode_rep Trie.trie_rep oo snd) listform;
         Trie.cursor_rep (c ++ (Trie.make_cursor k (Trie.trienode_of pt tableform listform))) pc;
         key_rep Tsh k pk)).
  {
    (* if true *)
    destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) eqn:Heqn; try solve [inv H1].
    if_tac in H1; try solve [inv H1].
    subst.
    assert (exists bnode_addr bnode, Trie.list_get_exact (get_keyslice k) listform = Some (bnode_addr, bnode)). {
      unfold Trie.list_get_exact.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) pt tableform listform ltac:(auto)).
      unfold BTree.Flattened.get_key in H2.
      rewrite Heqn in H2.
      destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) listform) listform)
        as [[? []] | ] eqn:Heqn'; try congruence.
      inv H2.
      exists v.
      exists t.
      rewrite if_true by auto.
      reflexivity.
    }
    destruct H2 as [pbnode [bnode ?]].
    forward.
    forward_if (
     PROP ()
     LOCAL (temp _node_cursor pnode_cursor;
            lvar _ret_value (tptr tvoid) v_ret_value;
            lvar _obtained_keyslice tuint v_obtained_keyslice)
     SEP (BTree.table_rep tableform pt;
          data_at Tsh tuint (Vint (Int.repr (get_keyslice k))) v_obtained_keyslice;
          data_at_ Tsh (tptr tvoid) v_ret_value;
          iter_sepcon (Trie.bnode_rep Trie.trie_rep oo snd) listform;
          Trie.cursor_rep (c ++ (Trie.make_cursor k (Trie.trienode_of pt tableform listform))) pc;
          key_rep Tsh k pk)).
    - forward.
      Trie.make_cursor_slice pt
                             tableform
                             listform
                             bnode
                             (BorderNode.before_prefix (Zlength k))
                             (Vint (Int.repr (Zlength k))).
      forward_call ((Trie.trienode_of pt tableform listform, (BTree.make_cursor (get_keyslice k) tableform),
                     bnode, BorderNode.before_prefix (Zlength k)),
                    pt, pnode_cursor, (Vint (Int.repr (Zlength k))), c, pc).
      assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
      entailer!.
      rewrite Trie.make_cursor_equation.
      rewrite H2.
      rewrite Int.unsigned_repr in H3 by rep_omega.
      rewrite if_true by rep_omega.
      fold_keyrep.
      cancel.
    - forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor,
                    tableform, pt, v_ret_value).
      { apply BTree.make_cursor_abs. assumption. }
      unfold BTree.get_key in Heqn. unfold BTree.get_value.
      destruct (BTree.get (BTree.make_cursor (get_keyslice k) tableform) tableform) as [[] | ] eqn:Heqn';
        try congruence.
      inv Heqn.
      assert (v = pbnode). {
        unfold Trie.list_get_exact in H2.
        pose proof (BTree.Flattened.same_value_result
                      (BTree.flatten tableform) listform
                      (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                      (BTree.Flattened.make_cursor (get_keyslice k) listform)
                      (get_keyslice k)
                      fst
                      (pbnode, bnode)).
        specialize (H9 H6 H7).
        pose proof (BTree.flatten_invariant tableform ltac:(auto)) as [? ?].
        specialize (H9 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H9 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        specialize (H9 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H9 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        specialize (H11 (get_keyslice k)
                        (BTree.make_cursor (get_keyslice k) tableform)
                        (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))).
        specialize (H11 ltac:(apply BTree.make_cursor_key; assumption)).
        specialize (H11 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H11 ltac:(apply BTree.make_cursor_abs; assumption)).
        specialize (H11 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        rewrite H11 in Heqn'.
        clear H11.
        unfold BTree.Flattened.get_key in H9.
        rewrite Heqn' in H9.
        destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) listform) listform)
          as [[? []] | ] eqn:Heqn''; try congruence.
        if_tac in H2; try congruence.
        subst.
        inv H2.
        specialize (H9 eq_refl).
        unfold BTree.Flattened.get_value in H9.
        rewrite Heqn'' in H9.
        rewrite Heqn' in H9.
        specialize (H9 eq_refl).
        inv H9.
        reflexivity.
      }
      subst v.
      unfold Trie.list_get_exact in H2.
      destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) listform) listform)
        as [[? []] | ] eqn:Heqn''; try congruence.
      if_tac in H2; try congruence.
      subst.
      inv H2.
      pose proof (BTree.Flattened.get_in_weak listform _ (get_keyslice k) (pbnode, bnode) Heqn'').
      sep_apply (iter_in_wand (get_keyslice k, (pbnode, bnode))
                              listform
                              (Trie.bnode_rep Trie.trie_rep oo snd)
                              H2).
      deadvars.
      assert (Trie.bordernode_correct bnode). {
        rewrite Forall_forall in H8.
        apply H8 in H2.
        simpl in H2.
        assumption.
      }
      change ((Trie.bnode_rep Trie.trie_rep oo snd) (get_keyslice k, (pbnode, bnode))) with
          (Trie.bnode_rep Trie.trie_rep (pbnode, bnode)).
      destruct bnode as [[prefixes suffix_key] suffix_value].
      inv H9.
      destruct suffix_value.
      + pose proof (Trie.translate_bnode_value Trie.trie_rep pbnode prefixes suffix_key v nullval)
          as Htranslate.
        change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
            (@BorderNode.table (@Trie.link val)) in Htranslate.
        rewrite Htranslate.
        Intros.
        forward.
        forward.
        forward_call (Tsh,
                      (Trie.translate_bnode (prefixes, suffix_key, Trie.value_of v) nullval),
                      pbnode).
        if_tac.
        * simpl in H9.
          subst.
          specialize (H15 eq_refl).
          inv H15.
        * simpl in H9.
          destruct suffix_key; try congruence.
          forward_if; [ | assert_PROP (False) by entailer!; contradiction ].
          assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
          rewrite Int.unsigned_repr in H3 by rep_omega.
          fold_keyrep.
          forward_call (Tsh, k, pk, Tsh,
                        (Trie.translate_bnode (prefixes, Some s, Trie.value_of v) nullval), pbnode).
          { split3; first [ rep_omega | solve [auto] ]. }
          simpl (match _ with | Some _ => _ | None => _ end).
          forward_if.
          -- if_tac in H12; try solve [inv H12].
             Trie.make_cursor_slice pt tableform listform
                                    (prefixes, Some s, Trie.value_of v)
                                    (BorderNode.before_suffix)
                                    (Vint (Int.repr (keyslice_length + 1))).
             forward_call ((Trie.trienode_of pt tableform listform,
                            (BTree.make_cursor (get_keyslice k) tableform),
                            (prefixes, Some s, Trie.value_of v), BorderNode.before_suffix),
                           pt, pnode_cursor, (Vint (Int.repr (keyslice_length + 1))), c, pc).
             gather_SEP 2 3.
             rewrite <- Htranslate.
             match goal with
             | |- context rest[ ?P -* ?Q] =>
               let term := context rest[emp] in
                 match term with
                 | context[P] =>
                   sep_apply (wand_frame_elim P Q)
                 end
             end.
             entailer!.
             apply sepcon_derives; [ apply derives_refl | ].
             rewrite Trie.make_cursor_equation.
             unfold Trie.list_get_exact.
             rewrite Heqn''.
             rewrite if_true by auto.
             rewrite if_false by rep_omega.
             simpl.
             rewrite if_false by functional.key.TrieKeyFacts.order.
             apply derives_refl.
          -- if_tac in H12; try solve [inv H12].
             Trie.make_cursor_slice pt tableform listform
                                    (prefixes, Some s, Trie.value_of v)
                                    (BorderNode.after_suffix)
                                    (Vint (Int.repr (keyslice_length + 2))).
             forward_call ((Trie.trienode_of pt tableform listform,
                            (BTree.make_cursor (get_keyslice k) tableform),
                            (prefixes, Some s, Trie.value_of v), BorderNode.after_suffix),
                           pt, pnode_cursor, (Vint (Int.repr (keyslice_length + 2))), c, pc).
             gather_SEP 2 3.
             rewrite <- Htranslate.
             match goal with
             | |- context rest[ ?P -* ?Q] =>
               let term := context rest[emp] in
                 match term with
                 | context[P] =>
                   sep_apply (wand_frame_elim P Q)
                 end
             end.
             entailer!.
             apply sepcon_derives; [ apply derives_refl | ].
             rewrite Trie.make_cursor_equation.
             unfold Trie.list_get_exact.
             rewrite Heqn''.
             rewrite if_true by auto.
             rewrite if_false by rep_omega.
             simpl.
             rewrite if_true by functional.key.TrieKeyFacts.order.
             apply derives_refl.
      + rename t into t'.
        pose proof (Trie.translate_bnode_subtrie Trie.trie_rep pbnode prefixes suffix_key t')
          as Htranslate.
        change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
            (@BorderNode.table (@Trie.link val)) in Htranslate.
        rewrite Htranslate at 1.
        Intros pt'.
        forward.
        forward.
        forward_call (Tsh,
                      (Trie.translate_bnode (prefixes, suffix_key, Trie.trie_of t') pt'),
                      pbnode).
        if_tac.
        * simpl in H9.
          subst.
          forward_if; [ assert_PROP (False) by entailer!; contradiction | ].
          assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
          rewrite Int.unsigned_repr in H3 by rep_omega.
          fold_keyrep.
          forward_call (Tsh, (Trie.translate_bnode (prefixes, None, Trie.trie_of t') pt'), pbnode).
          simpl BorderNode.get_suffix.
          assert_PROP (isptr pt') by entailer!.
          forward_if; [ | | assert_PROP (False) by entailer!; contradiction ].
          {
            apply denote_tc_test_eq_split; entailer!.
            sep_apply (Trie.trie_rep_valid_pointer t' pt').
            entailer!.
          }
          Trie.make_cursor_slice pt tableform listform
                                 (prefixes, (@None string), Trie.trie_of t')
                                 (BorderNode.before_suffix)
                                 (Vint (Int.repr (keyslice_length + 1))).
          forward_call ((Trie.trienode_of pt tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         (prefixes, @None string, Trie.trie_of t'), BorderNode.before_suffix),
                        pt, pnode_cursor, (Vint (Int.repr (keyslice_length + 1))), c, pc).
          clear pk'.
          unfold key_rep.
          Intros pk'.
          forward.
          forward.
          rewrite (cstring_len_split _ k pk' keyslice_length) by rep_omega.
          Intros.
          forward_call ((sublist keyslice_length (Zlength k) k),
                        (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk')).
          {
            entailer!.
            split.
            - rewrite field_address_offset by auto with field_compatible.
              reflexivity.
            - rewrite Zlength_sublist by rep_omega.
              reflexivity.
          }
          Intros p_subkey.
          forward.
          deadvars.
          forward_call ((c ++
                           [(Trie.trienode_of pt tableform listform,
                             BTree.make_cursor (get_keyslice k) tableform,
                             (prefixes, None, Trie.trie_of t'),
                             BorderNode.before_suffix)]),
                        pc,
                        (sublist keyslice_length (Zlength k) k),
                        p_subkey,
                        t',
                        pt'
                       ).
          {
            specialize (H15 eq_refl).
            inv H15.
            assumption.
          }
          forward_call ((sublist keyslice_length (Zlength k) k), p_subkey).
          assert (
              forall p', bordernode_rep Tsh (Trie.translate_bnode (prefixes, None, Trie.trie_of t') p') pbnode * malloc_token Tsh tbordernode pbnode * Trie.trie_rep t' p' |-- Trie.bnode_rep Trie.trie_rep (pbnode, (prefixes, None, Trie.trie_of t'))). {
            intros.
            change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
                (@BorderNode.table (@Trie.link val)).
            rewrite Htranslate.
            Exists p'.
            cancel.
          }
          change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
              (@BorderNode.table (@Trie.link val)) in H20.
          sep_apply (H20 pt').
          match goal with
          | |- context rest[ ?P -* ?Q] =>
            let term := context rest[emp] in
            match term with
            | context[P] =>
              sep_apply (wand_frame_elim P Q)
            end
          end.
          unfold key_rep.
          Exists pk'.
          rewrite (cstring_len_split _ k pk' keyslice_length) by rep_omega.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation with (k0 := k).
          unfold Trie.list_get_exact.
          rewrite Heqn''.
          rewrite if_true by auto.
          rewrite if_false by rep_omega.
          simpl.
          unfold get_suffix.
          rewrite <- app_assoc.
          simpl.
          apply derives_refl.
        * simpl in H9.
          specialize (H16 ltac:(congruence)).
          inv H16.
      + pose proof (Trie.translate_bnode_nil Trie.trie_rep pbnode prefixes suffix_key nullval)
          as Htranslate.
        change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
            (@BorderNode.table (@Trie.link val)) in Htranslate.
        rewrite Htranslate.
        Intros.
        forward.
        forward.
        forward_call (Tsh,
                      (Trie.translate_bnode (prefixes, suffix_key, Trie.nil) nullval),
                      pbnode).
        if_tac.
        * simpl in H9.
          subst.
          forward_if; [ assert_PROP (False) by entailer!; contradiction | ].
          assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
          rewrite Int.unsigned_repr in H3 by rep_omega.
          fold_keyrep.
          forward_call (Tsh, (Trie.translate_bnode (prefixes, None, Trie.nil) nullval), pbnode).
          simpl BorderNode.get_suffix.
          forward_if; [ contradiction | ].
          Trie.make_cursor_slice pt tableform listform
                                 (prefixes, (@None string), @Trie.nil val)
                                 (BorderNode.after_suffix)
                                 (Vint (Int.repr (keyslice_length + 2))).
          forward_call ((Trie.trienode_of pt tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         (prefixes, @None string, @Trie.nil val), BorderNode.after_suffix),
                        pt, pnode_cursor, (Vint (Int.repr (keyslice_length + 2))), c, pc).
          gather_SEP 1 3.
          rewrite <- Htranslate.
          match goal with
          | |- context rest[ ?P -* ?Q] =>
            let term := context rest[emp] in
            match term with
            | context[P] =>
              sep_apply (wand_frame_elim P Q)
            end
          end.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation.
          unfold Trie.list_get_exact.
          rewrite Heqn''.
          rewrite if_true by auto.
          rewrite if_false by rep_omega.
          simpl.
          apply derives_refl.
        * simpl in H9.
          specialize (H16 ltac:(congruence)).
          inv H16.
  }
  {
    (* if false *)
    forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor).
    entailer!.
    destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) eqn:Heqn.
    if_tac in H1.
    - inv H1.
    - rewrite Trie.make_cursor_equation.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) pt tableform listform ltac:(auto)).
      unfold Trie.list_get_exact.
      unfold BTree.Flattened.get_key in H13.
      rewrite Heqn in H13.
      destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) listform) listform)
        as [[] | ] eqn:Heqn'; try congruence.
      inv H13.
      rewrite if_false by auto.
      rewrite app_nil_r.
      fold_keyrep.
      cancel.
    - rewrite Trie.make_cursor_equation.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) pt tableform listform ltac:(auto)).
      rewrite Heqn in H12.
      unfold BTree.Flattened.get_key in H12.
      unfold Trie.list_get_exact.
      destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) listform) listform)
        as [[] | ] eqn:Heqn'; try congruence.
      rewrite app_nil_r.
      fold_keyrep.
      cancel.
  }
  forward.
  entailer!.
  destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform); entailer!.
Qed.
