(** * verif_first_cursor.v: Correctness proof of Trie.first_cursor *)
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
          push_cursor_spec; pop_cursor_spec;
          Imake_cursor_spec; Iget_value_spec; Iget_key_spec; Ifree_cursor_spec; Ifirst_cursor_spec;
          bordernode_next_cursor_spec;
          strict_first_cursor_spec
       ]).

Lemma body_strict_first_cursor: semax_body Vprog Gprog f_strict_first_cursor strict_first_cursor_spec.
Proof.
  start_function.
  destruct t as [addr tableform listform].
  unfold Trie.trie_rep; fold Trie.trie_rep.
  inv H.
  Intros.
  forward_call (tableform, addr).
  Intros pnode_cursor.
  forward_call (BTree.first_cursor tableform, pnode_cursor, tableform, addr, v_ret_value, Tsh).
  { split; [apply BTree.first_cursor_abs; assumption | auto ]. }
  forward_if.
  - if_tac in H; simplify.
    unfold BTree.get_value in H0; simplify.
    assert (BTree.get_key (BTree.first_cursor tableform) tableform = Some k) by
        (unfold BTree.get_key; rewrite H1; reflexivity).
    assert (BTree.key_rel k (BTree.first_cursor tableform) tableform). {
      apply BTree.get_key_rel.
      - apply BTree.first_cursor_abs.
        assumption.
      - assumption.
    }
    rename v into pbnode.
    assert (exists bnode, BTree.Flattened.get (BTree.Flattened.first_cursor listform) listform = Some (k, (pbnode, bnode))). {
      admit.
    }
    destruct H10 as [bnode ?].
    assert (In (k, (pbnode, bnode)) listform) by (eapply BTree.Flattened.get_in_weak; eauto).
    rewrite iter_in_wand with (a := (k, (pbnode, bnode))) by assumption.
    Intros.
    change ((Trie.bordernode_rep oo snd) (k, (pbnode, bnode))) with
        (Trie.bnode_rep (pbnode, bnode)).
    assert (Trie.bordernode_correct bnode). {
        rewrite Forall_forall in H7.
        apply H7 in H11.
        simpl in H11.
        assumption.
      }
    forward.
    forward.
    forward_call (bnode, pbnode, BorderNode.before_prefix 1).
    {
      simpl.
      rep_lia.
    }
    assert (1 <= (BorderNode.cursor_to_int (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)) <= Int.max_unsigned). {
      pose proof (BorderNode.next_cursor_bnode_correct (BorderNode.before_prefix 1)
                                                       bnode
                                                       ltac:(simpl; rep_lia)).
      unfold BorderNode.cursor_correct in H13.
      destruct (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode); simpl; rep_lia.
    }
    forward_if.
    + Trie.make_cursor_slice addr tableform listform
                             bnode
                             (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)
                             (vint (BorderNode.cursor_to_int (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode))).
      forward_call ((Trie.trienode_of addr tableform listform,
                     (BTree.first_cursor tableform),
                     bnode,
                     (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)),
                    addr,
                    pnode_cursor,
                    (vint (BorderNode.cursor_to_int (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode))),
                    c, pc).
      match goal with
      | |- context rest[ ?P -* ?Q] =>
          sep_apply (wand_frame_elim P Q)
      end.
      forward.
      rewrite Trie.strict_first_cursor_equation.
      unfold BTree.Flattened.get_value.
      rewrite H10.
      match_tac; simplify; simpl in H14; try rep_lia.
      2: {
        apply BorderNode.next_cursor_prefix_correct in H20.
        congruence.
      }
      entailer!.
    + forward_if.
      * assert (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode = BorderNode.before_suffix). {
          destruct (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode) eqn:Heqn'.
          - simpl in *.
            change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H15.
            apply repr_inj_unsigned in H15; try rep_lia.
            subst.
            pose proof (BorderNode.next_cursor_bnode_correct (BorderNode.before_prefix 1)
                                                       bnode
                                                       ltac:(simpl; rep_lia)).
            rewrite Heqn' in H15.
            simpl in H15.
            rep_lia.
          - reflexivity.
          - change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H15.
            simpl in H15.
            apply repr_inj_unsigned in H15; rep_lia.
        }
        Trie.make_cursor_slice addr tableform listform
                               bnode
                               (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)
                               (vint (BorderNode.cursor_to_int (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode))).
        forward_call ((Trie.trienode_of addr tableform listform,
                       (BTree.first_cursor tableform),
                       bnode,
                       (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)),
                      addr,
                      pnode_cursor,
                      (vint (BorderNode.cursor_to_int (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode))),
                      c, pc).
        forward_call (bnode, pbnode).
        forward_if.
        -- match goal with
           | |- context rest[ ?P -* ?Q] =>
             sep_apply (wand_frame_elim P Q)
           end.
           forward.
           apply repr_inj_unsigned in H15; [ | rep_lia | rep_lia ].
           rewrite Trie.strict_first_cursor_equation.
           unfold BTree.Flattened.get_value.
           destruct bnode as [? [[ | ] | ]]; if_tac in H17; simplify.
           unfold BorderNode.get_suffix_pair in H22; simpl in H22; simplify.
           rewrite H10.
           rewrite H16.
           simpl.
           entailer!.
        -- forward_call (bnode, pbnode, v_subindex, Tsh).
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H15.
           apply repr_inj_unsigned in H15; [ | rep_lia | rep_lia ].
           if_tac in H17; simplify.
           deadvars.
           match_tac; simpl Trie.bnode_rep at 1.
           ++ destruct bnode as [? [ [|] | ]]; simplify.
              Intros.
              unfold BorderNode.get_link in H20; simplify.
              forward.
              forward_call (c ++
                              [(Trie.trienode_of addr tableform listform, BTree.first_cursor tableform, (l, Some (inr t)),
                                BorderNode.next_cursor (BorderNode.before_prefix 1) (l, Some (inr t)))],
                            pc,
                            t).
              { inv H12; simplify. }
              forward_if.
              ** forward.
                 if_tac in H20; simplify.
                 rewrite Trie.strict_first_cursor_equation.
                 unfold BTree.Flattened.get_value.
                 rewrite H10.
                 rewrite H16.
                 simpl.
                 match_tac; simplify.
                 match goal with
                 | |- context rest[ ?P -* ?Q] =>
                   sep_apply (wand_frame_elim P Q)
                 end.
                 entailer!.
                 rewrite <- app_assoc.
                 rewrite <- semax_lemmas.cons_app.
                 apply derives_refl.
              ** if_tac in H20; simplify.
                 rewrite app_nil_r.
                 forward_call ((c ++
                                  [(Trie.trienode_of addr tableform listform, BTree.first_cursor tableform, (l, Some (inr t)),
                                    BorderNode.next_cursor (BorderNode.before_prefix 1) (l, Some (inr t)))]),
                               pc).
                 rewrite removelast_app by congruence.
                 simpl removelast.
                 rewrite app_nil_r.
                 forward.
                 rewrite Trie.strict_first_cursor_equation.
                 unfold BTree.Flattened.get_value.
                 rewrite H10.
                 rewrite H16.
                 simpl.
                 match_tac; simplify.
                 match goal with
                 | |- context rest[ ?P -* ?Q] =>
                   sep_apply (wand_frame_elim P Q)
                 end.
                 entailer!.
                 rewrite app_nil_r.
                 apply derives_refl.
           ++ apply BorderNode.next_cursor_suffix_correct in H16.
              destruct bnode; unfold BorderNode.get_link in H20; simpl in H16; simplify.
      * change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H15.
        apply repr_neq_e in H15.
        forward_call (BTree.first_cursor tableform, pnode_cursor).
        match goal with
        | |- context rest[ ?P -* ?Q] =>
          sep_apply (wand_frame_elim P Q)
        end.
        forward.
        rewrite Trie.strict_first_cursor_equation.
        unfold BTree.Flattened.get_value.
        rewrite H10.
        assert (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode = BorderNode.after_suffix). {
          assert (BorderNode.cursor_correct (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode)). {
            apply BorderNode.next_cursor_bnode_correct.
            simpl.
            rep_lia.
          }
          destruct (BorderNode.next_cursor (BorderNode.before_prefix 1) bnode) eqn:Heqn.
          - simpl in *.
            rep_lia.
          - simpl in *.
            rep_lia.
          - reflexivity.
        }
        rewrite H19.
        entailer!.
        rewrite app_nil_r.
        cancel.
  - forward_call (BTree.first_cursor tableform, pnode_cursor).
    forward.
    if_tac in H; simplify.
    unfold BTree.get_value in H11; match_tac in H11; simplify.
    pose proof H12.
    apply BTree.first_cursor_get_empty in H12; [ | assumption].
    apply BTreeFacts.empty_flatten_empty in H12.
    rewrite H12 in *.
    destruct listform; simpl in H5; simplify.
Admitted.
