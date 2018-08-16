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
          push_cursor_spec; pop_cursor_spec;
          Imake_cursor_spec; Iget_value_spec; Iget_key_spec; Ifree_cursor_spec; Ifirst_cursor_spec;
          bordernode_next_cursor_spec;
          strict_first_cursor_spec
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

Lemma body_strict_first_cursor: semax_body Vprog Gprog f_strict_first_cursor strict_first_cursor_spec.
Proof.
  start_function.
  destruct t as [addr tableform listform].
  unfold Trie.trie_rep; fold Trie.trie_rep.
  inv H.
  Intros.
  subst addr.
  forward_call (tableform, pt).
  Intros pnode_cursor.
  forward_call (BTree.first_cursor tableform, pnode_cursor, tableform, pt, v_ret_value).
  { apply BTree.first_cursor_abs. assumption. }
  forward_if.
  - destruct (BTree.get_value (BTree.first_cursor tableform) tableform) as [pbnode | ] eqn:Heqn;
      try solve [inv H0].
    unwrap_get in Heqn.
    assert (BTree.get_key (BTree.first_cursor tableform) tableform = Some k) by
        (unfold BTree.get_key; rewrite Heqn0; reflexivity).
    assert (BTree.key_rel k (BTree.first_cursor tableform) tableform). {
      apply BTree.get_key_rel.
      - apply BTree.first_cursor_abs.
        assumption.
      - assumption.
    }
    assert (exists bnode, BTree.Flattened.get (BTree.Flattened.first_cursor listform) listform = Some (k, (pbnode, bnode))). {
      admit.
    }
    destruct H8 as [bnode ?].
    assert (In (k, (pbnode, bnode)) listform) by (eapply BTree.Flattened.get_in_weak; eauto).
    sep_apply (iter_in_wand (k, (pbnode, bnode))
                            listform
                            (Trie.bnode_rep Trie.trie_rep oo snd)
                            H9).
    Intros.
    change ((Trie.bnode_rep Trie.trie_rep oo snd) (k, (pbnode, bnode))) with
        (Trie.bnode_rep Trie.trie_rep (pbnode, bnode)).
    assert (Trie.bordernode_correct bnode). {
        rewrite Forall_forall in H7.
        apply H7 in H9.
        simpl in H9.
        assumption.
      }
    destruct bnode as [[prefixes suffix_key] suffix_value].
    inv H10.
    forward.
    {
      simpl Trie.bnode_rep.
      Intros.
      entailer!.
    }
    forward.
    forward_call ((prefixes, suffix_key, suffix_value), pbnode, BorderNode.before_prefix 1).
    {
      simpl.
      rep_omega.
    }
    assert (1 <= (BorderNode.cursor_to_int
                   (BorderNode.next_cursor
                      (BorderNode.before_prefix 1)
                      (prefixes, suffix_key, suffix_value))) <= Int.max_unsigned). {
      pose proof (BorderNode.next_cursor_bnode_correct (BorderNode.before_prefix 1)
                                                       (prefixes, suffix_key, suffix_value)
                                                       ltac:(simpl; rep_omega)).
      unfold BorderNode.cursor_correct in H10.
      destruct (BorderNode.next_cursor (BorderNode.before_prefix 1)
                                       (prefixes, suffix_key, suffix_value)); simpl; rep_omega.
    }
    forward_if.
    + Trie.make_cursor_slice pt tableform listform
                             (prefixes, suffix_key, suffix_value)
                             (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value))
                             (Vint (Int.repr
                                      (BorderNode.cursor_to_int
                                         (BorderNode.next_cursor
                                            (BorderNode.before_prefix 1)
                                            (prefixes, suffix_key, suffix_value))))).
      forward_call ((Trie.trienode_of pt tableform listform,
                     (BTree.first_cursor tableform),
                     (prefixes, suffix_key, suffix_value),
                     (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value))),
                    pt,
                    pnode_cursor,
                    (Vint (Int.repr
                             (BorderNode.cursor_to_int
                                (BorderNode.next_cursor
                                   (BorderNode.before_prefix 1)
                                   (prefixes, suffix_key, suffix_value))))),
                    c, pc).
      match goal with
      | |- context rest[ ?P -* ?Q] =>
        let term := context rest[emp] in
        match term with
        | context[P] =>
          sep_apply (wand_frame_elim P Q)
        end
      end.
      forward.
      rewrite Trie.strict_first_cursor_equation.
      unfold BTree.Flattened.get_value.
      rewrite H8.
      destruct (BorderNode.next_cursor (BorderNode.before_prefix 1)
                                       (prefixes, suffix_key, suffix_value)) eqn:Heqn';
        simpl in H11; try rep_omega.
      apply BorderNode.next_cursor_prefix_correct in Heqn'.
      change default_val with (@Trie.nil val) in Heqn'.
      assert (In (BorderNode.get_prefix z (prefixes, suffix_key, suffix_value)) prefixes). {
        simpl.
        apply Znth_In.
        rewrite H14.
        simpl in H10.
        rep_omega.
      }
      rewrite Forall_forall in H15.
      apply H15 in H20.
      unfold Trie.is_value in H20.
      destruct (BorderNode.get_prefix z (prefixes, suffix_key, suffix_value)) eqn:Heqn'';
        try solve [congruence | destruct H20; [contradiction | congruence] ].
      entailer!.
    + forward_if.
      * assert (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value) = BorderNode.before_suffix). {
          destruct (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value)) eqn:Heqn'.
          - simpl in *.
            change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H12.
            apply repr_inj_unsigned in H12; try rep_omega.
            subst.
            pose proof (BorderNode.next_cursor_bnode_correct (BorderNode.before_prefix 1)
                                                       (prefixes, suffix_key, suffix_value)
                                                       ltac:(simpl; rep_omega)).
            rewrite Heqn' in H12.
            simpl in H12.
            rep_omega.
          - reflexivity.
          - change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H12.
            simpl in H12.
            apply repr_inj_unsigned in H12; rep_omega.
        }
        Trie.make_cursor_slice pt tableform listform
                               (prefixes, suffix_key, suffix_value)
                               (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value))
                               (Vint (Int.repr
                                        (BorderNode.cursor_to_int
                                           (BorderNode.next_cursor
                                              (BorderNode.before_prefix 1)
                                              (prefixes, suffix_key, suffix_value))))).
        forward_call ((Trie.trienode_of pt tableform listform,
                       (BTree.first_cursor tableform),
                       (prefixes, suffix_key, suffix_value),
                       (BorderNode.next_cursor (BorderNode.before_prefix 1) (prefixes, suffix_key, suffix_value))),
                      pt,
                      pnode_cursor,
                      (Vint (Int.repr
                               (BorderNode.cursor_to_int
                                  (BorderNode.next_cursor
                                     (BorderNode.before_prefix 1)
                                     (prefixes, suffix_key, suffix_value))))),
                      c, pc).
        destruct suffix_value.
        -- pose proof (Trie.translate_bnode_value Trie.trie_rep pbnode prefixes suffix_key v nullval)
            as Htranslate.
           change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
               (@BorderNode.table (@Trie.link val)) in Htranslate.
           rewrite Htranslate at 1.
           Intros.
           forward_call (Tsh,
                         (Trie.translate_bnode (prefixes, suffix_key, Trie.value_of v) nullval),
                         pbnode).
           forward_if.
           2: {
             destruct suffix_key; try solve [inv H20].
             specialize (H16 eq_refl).
             inv H16.
           }
           destruct suffix_key; try congruence.
           simpl BorderNode.is_link.
           rewrite if_false by (simpl; congruence).
           symmetry in Htranslate.
           sep_apply Htranslate.
           match goal with
           | |- context rest[ ?P -* ?Q] =>
             let term := context rest[emp] in
             match term with
             | context[P] =>
               sep_apply (wand_frame_elim P Q)
             end
           end.
           forward.
           rewrite Trie.strict_first_cursor_equation.
           unfold BTree.Flattened.get_value.
           rewrite H8.
           unfold inh_link, bnode_link in *.
           rewrite H13.
           simpl.
           entailer!.
        -- rename t into t'.
           pose proof (Trie.translate_bnode_subtrie Trie.trie_rep pbnode prefixes suffix_key t')
            as Htranslate.
           change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
               (@BorderNode.table (@Trie.link val)) in Htranslate.
           rewrite Htranslate at 1.
           Intros pt'.
           forward_call (Tsh,
                         (Trie.translate_bnode (prefixes, suffix_key, Trie.trie_of t') pt'),
                         pbnode).
           forward_if.
           {
             destruct suffix_key; try congruence.
             specialize (H17 ltac:(congruence)).
             inv H17.
           }
           destruct suffix_key; try solve [inv H20].
           rewrite if_true by reflexivity.
           forward_call (Tsh, (Trie.translate_bnode (prefixes, None, Trie.trie_of t') pt'), pbnode).
           forward_call ((c ++
                            [(Trie.trienode_of pt tableform listform,
                              BTree.first_cursor tableform,
                              (prefixes, None, Trie.trie_of t'),
                              BorderNode.next_cursor (BorderNode.before_prefix 1)
                                                     (prefixes, None, Trie.trie_of t'))]),
                         pc, t', pt').
           { specialize (H16 eq_refl). inv H16. assumption. }
           assert (forall p': val,
                      bordernode_rep Tsh (Trie.translate_bnode (prefixes, None, Trie.trie_of t') p') pbnode * malloc_token Tsh tbordernode pbnode * Trie.trie_rep t' p' |-- Trie.bnode_rep Trie.trie_rep (pbnode, (prefixes, None, Trie.trie_of t'))). {
             intros.
             change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
                 (@BorderNode.table (@Trie.link val)).
             rewrite Htranslate.
             Exists p'.
             cancel.
           }
           sep_apply (H21 pt').
           change (prod (prod (list (@Trie.link val)) (option string)) (@Trie.link val)) with
               (@BorderNode.table (@Trie.link val)).
           match goal with
           | |- context rest[ ?P -* ?Q] =>
             let term := context rest[emp] in
             match term with
             | context[P] =>
               sep_apply (wand_frame_elim P Q)
             end
           end.
           forward_if; destruct (Trie.strict_first_cursor t') eqn:Heqn'; try solve [inv H22].
           ++ forward.
              rewrite Trie.strict_first_cursor_equation.
              unfold BTree.Flattened.get_value.
              rewrite H8.
              unfold inh_link, bnode_link in *.
              rewrite H13.
              simpl.
              rewrite Heqn'.
              entailer!.
              rewrite <- app_assoc.
              simpl.
              apply derives_refl.
           ++ rewrite app_nil_r.
              forward_call ((c ++
                               [(Trie.trienode_of pt tableform listform,
                                 BTree.first_cursor tableform,
                                 (prefixes, None, Trie.trie_of t'),
                                 BorderNode.next_cursor (BorderNode.before_prefix 1)
                                                        (prefixes, None, Trie.trie_of t'))]),
                            pc).
              rewrite removelast_app by congruence.
              rewrite app_nil_r.
              forward.
              rewrite Trie.strict_first_cursor_equation.
              unfold BTree.Flattened.get_value.
              rewrite H8.
              unfold inh_link, bnode_link in *.
              rewrite H13.
              simpl.
              rewrite Heqn'.
              rewrite app_nil_r.
              entailer!.
        -- apply BorderNode.next_cursor_suffix_correct in H13.
           change (default_val) with (@Trie.nil val) in H13.
           simpl in H13.
           congruence.
      * forward_call ((BTree.first_cursor tableform), pnode_cursor).
        match goal with
        | |- context rest[ ?P -* ?Q] =>
          let term := context rest[emp] in
          match term with
          | context[P] =>
            sep_apply (wand_frame_elim P Q)
          end
        end.
        forward.
        rewrite Trie.strict_first_cursor_equation.
        unfold BTree.Flattened.get_value.
        rewrite H8.
        destruct (BorderNode.next_cursor (BorderNode.before_prefix 1)
                                         (prefixes, suffix_key, suffix_value)) eqn:Heqn'.
        {
          pose proof (BorderNode.next_cursor_bnode_correct (BorderNode.before_prefix 1)
                                                       (prefixes, suffix_key, suffix_value)
                                                       ltac:(simpl; rep_omega)).
          unfold inh_link, bnode_link in H21.
          rewrite Heqn' in H21.
          simpl in H21.
          simpl in H11.
          rep_omega.
        }
        {
          simpl in H12.
          exfalso.
          apply H12.
          reflexivity.
        }
        rewrite app_nil_r.
        entailer!.
  - destruct (BTree.get_value (BTree.first_cursor tableform) tableform) eqn:Heqn; try solve [inv H0].
    forward_call (BTree.first_cursor tableform, pnode_cursor).
    forward.
    rewrite Trie.strict_first_cursor_equation.
    unwrap_get in Heqn.
    apply BTree.first_cursor_get_empty in Heqn0; [ | assumption ].
    apply BTreeFacts.empty_flatten_empty in Heqn0.
    rewrite Heqn0 in *.
    assert (listform = []) by (destruct listform; [ reflexivity | inv H5]).
    subst.
    unfold BTree.Flattened.get_value.
    rewrite BTree.Flattened.get_empty;
      [ | reflexivity | apply BTree.Flattened.first_cursor_abs; assumption ].
    rewrite app_nil_r.
    entailer!.
Admitted.
