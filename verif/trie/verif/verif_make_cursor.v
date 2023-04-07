(** * verif_make_cursor.v: Correctness proof of Trie.make_cursor *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.wand_frame.
Require Import DB.common.
Require Import DB.tactics.
Require Import DB.lemmas.

Require Import DB.functional.bordernode.
Require Import DB.functional.keyslice.

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
  forward_call (Ews, pk', k). (* UTIL_GetNextKeySlice *)
  forward.
  destruct t as [addr tableform listform].
  unfold Trie.trie_rep; fold Trie.trie_rep.
  Intros.
  pose proof H as H'.
  inv H.
  pose proof get_keyslice_inrange k.
  forward_call (get_keyslice k, tableform, addr).
  Intros pnode_cursor.
  forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor, tableform, addr, v_obtained_keyslice, Tsh).
  { split; [ apply BTree.make_cursor_abs; assumption | auto ]. }
  forward_if (temp _t'8 match (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) with
                         | Some k' => if eq_dec k' (get_keyslice k) then Vint Int.one else Vint Int.zero
                         | None => Vint Int.zero
                        end).
  {
    (* if true *)
    destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform) eqn:Heqn; try solve [inv H0].
    forward.
    forward.
    entailer!.
    if_tac.
    - subst.
      rewrite Int.eq_true.
      reflexivity.
    - rewrite Int.eq_false; [ reflexivity | ].
      intro.
      apply repr_inj_unsigned in H17.
      + congruence.
      + rep_lia.
      + pose proof (@BTree.flatten_invariant val).
        specialize (H18 tableform ltac:(assumption)) as [? ?].
        specialize (H19 (get_keyslice k)
                        (BTree.make_cursor (get_keyslice k) tableform)
                        (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))).
        specialize (H19 ltac:(apply BTree.make_cursor_key; assumption)).
        specialize (H19 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H19 ltac:(apply BTree.make_cursor_abs; assumption)).
        specialize (H19 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        unfold BTree.get_key in Heqn.
        rewrite H19 in Heqn.
        destruct (BTree.Flattened.get (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                                      (BTree.flatten tableform)) as [[] | ] eqn:Heqn'; try congruence.
        inv Heqn.
        pose proof (BTree.Flattened.get_in_weak
                      (BTree.flatten tableform)
                      (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                      k0
                      v
                      Heqn').
        apply in_map with (f := fst) in H20.
        simpl in H20.
        apply Forall_map in H8.
        change Z with BTree.Flattened.key in H8.
        rewrite <- H5 in H8.
        rewrite Forall_forall in H8.
        apply H8 in H20.
        unfold Trie.key_inrange in H20.
        rep_lia.
  }
  {
    (* if false *)
    match_tac; simplify.
    forward.
    entailer!.
  }
  deadvars.
  forward_if (
    PROP ()
         LOCAL (temp _node_cursor pnode_cursor;
                lvar _subindex (tptr tvoid) v_subindex;
                lvar _ret_value (tptr tvoid) v_ret_value;
                lvar _obtained_keyslice tuint v_obtained_keyslice)
    SEP (BTree.table_rep tableform addr;
         match BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform with
         | Some k0 => data_at Tsh tuint (Vint (Int.repr k0)) v_obtained_keyslice
         | None => data_at_ Tsh tuint v_obtained_keyslice
         end;
         data_at_ Tsh (tptr tvoid) v_subindex;
         data_at_ Tsh (tptr tvoid) v_ret_value;
         iter_sepcon (Trie.bnode_rep oo snd) listform;
         Trie.cursor_rep (c ++ (Trie.make_cursor k (Trie.trienode_of addr tableform listform))) pc;
         key_rep Ews k pk)).
  {
    (* if true *)
    match_tac; simplify.
    if_tac in H0; simplify.
    subst.
    assert (exists bnode_addr bnode, BTree.Flattened.get_exact (get_keyslice k) listform = Some (bnode_addr, bnode)). {
      unfold BTree.Flattened.get_exact.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) addr tableform listform ltac:(auto)).
      unfold BTree.Flattened.get_key in H10.
      rewrite H1 in H10.
      match_tac; simplify.
      exists v.
      exists t.
      rewrite if_true by reflexivity.
      reflexivity.
    }
    destruct H10 as [pbnode [bnode ?]].
    forward.
    forward_if.
    - forward.
      Trie.make_cursor_slice addr
                             tableform
                             listform
                             bnode
                             (BorderNode.before_prefix (Zlength k))
                             (Vint (Int.repr (Zlength k))).
      forward_call ((Trie.trienode_of addr tableform listform, (BTree.make_cursor (get_keyslice k) tableform),
                     bnode, BorderNode.before_prefix (Zlength k)),
                    addr, pnode_cursor, (Vint (Int.repr (Zlength k))), c, pc).
      assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
      entailer!.
      rewrite Trie.make_cursor_equation.
      rewrite H10.
      rewrite Int.unsigned_repr in H11 by rep_lia.
      rewrite if_true by rep_lia.
      fold_keyrep.
      cancel.
      apply derives_refl.
    - forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor,
                    tableform, addr, v_ret_value, Tsh).
      { split; [ apply BTree.make_cursor_abs; assumption | auto ]. }
      unfold BTree.get_key in H1. unfold BTree.get_value.
      match_tac; simplify.
      clear e H12.
      assert (v = pbnode). {
        unfold BTree.Flattened.get_exact in H10.
        pose proof (BTree.Flattened.same_value_result
                      (BTree.flatten tableform) listform
                      (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))
                      (BTree.Flattened.make_cursor (get_keyslice k) listform)
                      (get_keyslice k)
                      fst
                      (pbnode, bnode)).
        specialize (H1 H5 H6).
        pose proof (BTree.flatten_invariant tableform ltac:(auto)) as [? ?].
        specialize (H1 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H1 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        specialize (H1 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H1 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        specialize (H14 (get_keyslice k)
                        (BTree.make_cursor (get_keyslice k) tableform)
                        (BTree.Flattened.make_cursor (get_keyslice k) (BTree.flatten tableform))).
        specialize (H14 ltac:(apply BTree.make_cursor_key; assumption)).
        specialize (H14 ltac:(apply BTree.Flattened.make_cursor_key; assumption)).
        specialize (H14 ltac:(apply BTree.make_cursor_abs; assumption)).
        specialize (H14 ltac:(apply BTree.Flattened.make_cursor_abs; assumption)).
        rewrite H14 in H13.
        clear H14.
        unfold BTree.Flattened.get_key in H1.
        rewrite H13 in H1.
        match_tac in H1; simplify.
        unfold BTree.Flattened.get_value in H1.
        match_tac in H1; simplify.
        specialize (H1 eq_refl eq_refl).
        match_tac in H1; simplify.
      }
      subst v.
      unfold BTree.Flattened.get_exact in H10.
      match_tac in H10; simplify.
      pose proof (BTree.Flattened.get_in_weak listform _ (get_keyslice k) (pbnode, bnode) H1).
      erewrite iter_in_wand with (a := (get_keyslice k, (pbnode, bnode))) by assumption.
      deadvars.
      assert (Trie.bordernode_correct bnode). {
        rewrite Forall_forall in H7.
        apply H7 in H10.
        simpl in H10.
        assumption.
      }
      change ((Trie.bordernode_rep oo snd) (get_keyslice k, (pbnode, bnode))) with
          (Trie.bnode_rep (pbnode, bnode)).
      Intros.
      forward.
      forward.
      forward_call (bnode, pbnode).
      forward_if.
      + destruct bnode as [prefixes suffix].
        simpl Trie.bnode_rep at 1.
        simpl in H15.
        if_tac in H15; simplify.
        deadvars.
        Intros pkey.
        assert_PROP (keyslice_length < Zlength k <= Ptrofs.max_unsigned). {
          unfold cstring_len.
          Intros.
          rewrite Int.unsigned_repr in H11 by rep_lia.
          entailer!.
        }
        lazymatch goal with
        | H: Trie.bordernode_correct ?bnode |- _ =>          
          forward_call (Ews, k, pk, bnode, pbnode)
        end.
        {
          unfold key_rep.
          Exists pk'.
          entailer!.
          simpl Trie.bnode_rep at 2.
          Exists pkey.
          cancel.
        }
        { split; [ auto | rep_lia]. }
        forward_if.
        * if_tac in H17; simplify.
          lazymatch goal with
          | H: Trie.bordernode_correct ?b |- _ =>
            pose (bnode := b)
          end.
          Trie.make_cursor_slice addr tableform listform
                                 bnode
                                 (BorderNode.before_suffix)
                                 (Vint (Int.repr (keyslice_length + 1))).
          forward_call ((Trie.trienode_of addr tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         bnode, BorderNode.before_suffix),
                        addr, pnode_cursor, (Vint (Int.repr (keyslice_length + 1))), c, pc).
          lazymatch goal with
          | |- context rest[ ?P -* ?Q] =>
              sep_apply (wand_frame_elim P Q)
          end.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation.
          unfold BTree.Flattened.get_exact.
          rewrite H1.
          rewrite if_true by reflexivity.
          rewrite if_false by rep_lia.
          simpl.
          rewrite if_false by functional.key.TrieKeyFacts.order.
          apply derives_refl.
        * if_tac in H17; simplify.
          lazymatch goal with
          | H: Trie.bordernode_correct ?b |- _ =>
            pose (bnode := b)
          end.
          Trie.make_cursor_slice addr tableform listform
                                 bnode
                                 (BorderNode.after_suffix)
                                 (Vint (Int.repr (keyslice_length + 2))).
          forward_call ((Trie.trienode_of addr tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         bnode, BorderNode.after_suffix),
                        addr, pnode_cursor, (Vint (Int.repr (keyslice_length + 2))), c, pc).
          match goal with
          | |- context rest[ ?P -* ?Q] =>
            sep_apply (wand_frame_elim P Q)
          end.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation.
          unfold BTree.Flattened.get_exact.
          rewrite H1.
          rewrite if_true by reflexivity.
          rewrite if_false by rep_lia.
          simpl.
          rewrite if_true by functional.key.TrieKeyFacts.order.
          apply derives_refl.
      + if_tac in H15; simplify.
        deadvars.
        forward_call (bnode, pbnode, v_subindex, Tsh).
        if_tac.
        * destruct bnode as [? [ [ | ] | ]]; simpl in H16, H17; simplify.
          forward_if; [ | assert_PROP (False) by entailer!; contradiction ].
          assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
          rewrite Int.unsigned_repr in H11 by rep_lia.
          fold_keyrep.
          lazymatch goal with
          | H: Trie.bordernode_correct ?b |- _ =>
            pose (bnode := b)
          end.
          Trie.make_cursor_slice addr tableform listform
                                 bnode
                                 (BorderNode.before_suffix)
                                 (Vint (Int.repr (keyslice_length + 1))).
          forward_call ((Trie.trienode_of addr tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         bnode, BorderNode.before_suffix),
                        addr, pnode_cursor, (Vint (Int.repr (keyslice_length + 1))), c, pc).
          clear pk'.
          unfold key_rep.
          Intros pk'.
          forward.
          forward.
          rewrite (cstring_len_split _ k pk' keyslice_length) by rep_lia.
          Intros.
          forward_call ((sublist keyslice_length (Zlength k) k),
                        (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk')).
          {
            entailer!.
            split.
            - rewrite field_address_offset by auto with field_compatible.
              reflexivity.
            - rewrite Zlength_sublist by rep_lia.
              reflexivity.
          }
          Intros p_subkey.
          forward.
          deadvars.
          simpl Trie.bnode_rep at 1.
          Intros.
          forward.
          forward_call ((c ++
                           [(Trie.trienode_of addr tableform listform,
                             BTree.make_cursor (get_keyslice k) tableform,
                             bnode,
                             BorderNode.before_suffix)]),
                        pc,
                        (sublist keyslice_length (Zlength k) k),
                        p_subkey,
                        t).
          {
            inv H14.
            simplify.
          }
          forward_call ((sublist keyslice_length (Zlength k) k), p_subkey).
          (* assert ( *)
          (*     forall p', bordernode_rep Ews (Trie.translate_bnode (prefixes, None, Trie.trie_of t') p') pbnode * malloc_token Ews tbordernode pbnode * Trie.trie_rep t' p' |-- Trie.bnode_rep Trie.trie_rep (pbnode, (prefixes, None, Trie.trie_of t'))). { *)
          (*   intros. *)
          (*   change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with *)
          (*       (@BorderNode.table (@Trie.link val)). *)
          (*   rewrite Htranslate. *)
          (*   Exists p'. *)
          (*   cancel. *)
          (* } *)
          (* change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with *)
          (*     (@BorderNode.table (@Trie.link val)) in H20. *)
          (* sep_apply (H20 addr'). *)
          gather_SEP 6 7 8 9.
          simpl Trie.bnode_rep.
          match goal with
          | |- context rest[ ?P -* ?Q] =>
            sep_apply (wand_frame_elim P Q)
          end.
          unfold key_rep.
          Exists pk'.
          rewrite (cstring_len_split _ k pk' keyslice_length) by rep_lia.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation with (k0 := k).
          unfold BTree.Flattened.get_exact.
          rewrite H1.
          rewrite if_true by reflexivity.
          rewrite if_false by rep_lia.
          simpl.
          unfold get_suffix.
          rewrite <- app_assoc.
          simpl.
          apply derives_refl.
        * forward_if; [ assert_PROP (False) by entailer!; contradiction | ].
          assert_PROP (0 <= Zlength k <= Ptrofs.max_unsigned) by (unfold cstring_len; entailer!).
          rewrite Int.unsigned_repr in H11 by rep_lia.
          destruct bnode as [? [ [|] | ]]; simpl in H17, H16; simplify.
          match goal with
          | H: Trie.bordernode_correct ?b |- _ =>
            pose (bnode := b)
          end.
          Trie.make_cursor_slice addr tableform listform
                                 bnode
                                 (BorderNode.after_suffix)
                                 (Vint (Int.repr (keyslice_length + 2))).
          forward_call ((Trie.trienode_of addr tableform listform,
                         (BTree.make_cursor (get_keyslice k) tableform),
                         bnode, BorderNode.after_suffix),
                        addr, pnode_cursor, (Vint (Int.repr (keyslice_length + 2))), c, pc).
          match goal with
          | |- context rest[ ?P -* ?Q] =>
            sep_apply (wand_frame_elim P Q)
          end.
          fold_keyrep.
          entailer!.
          apply sepcon_derives; [ apply derives_refl | ].
          rewrite Trie.make_cursor_equation.
          unfold BTree.Flattened.get_exact.
          rewrite H1.
          rewrite if_true by reflexivity.
          rewrite if_false by rep_lia.
          simpl.
          apply derives_refl.
  }
  {
    (* if false *)
    forward_call ((BTree.make_cursor (get_keyslice k) tableform), pnode_cursor).
    entailer!.
    match_tac in H0; simplify.
    - if_tac in H0; inv H0.
      rewrite Trie.make_cursor_equation.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) addr tableform listform ltac:(auto)).
      unfold BTree.Flattened.get_exact.
      unfold BTree.Flattened.get_key in H0.
      rewrite H16 in H0.
      match_tac in H0; simplify.
      rewrite if_false by auto.
      rewrite app_nil_r.
      fold_keyrep.
      cancel.
      apply derives_refl.
    - rewrite Trie.make_cursor_equation.
      pose proof (@Trie.table_key_list_key val (get_keyslice k) addr tableform listform ltac:(auto)).
      rewrite H16 in H18.
      unfold BTree.Flattened.get_key in H18.
      unfold BTree.Flattened.get_exact.
      match_tac in H18; simplify.
      rewrite app_nil_r.
      fold_keyrep.
      cancel.
      apply derives_refl.
  }
  forward.
  entailer!.
  destruct (BTree.get_key (BTree.make_cursor (get_keyslice k) tableform) tableform); entailer!; apply derives_refl.
Qed.
