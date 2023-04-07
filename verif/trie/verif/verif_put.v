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
          BN_SetPrefixValue_spec;
          BN_GetSuffixValue_spec;
          BN_SetSuffixValue_spec;
          BN_ExportSuffixValue_spec;
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
          create_pair_spec;
          put_spec
       ]).

Ltac crush :=
  unfold BorderNode.put_value, Trie.key_inrange;
  repeat if_tac;
  simpl;
  rewrite ?Forall_map;
  rewrite <- ?upd_Znth_map;
  rewrite ?map_list_repeat;
  simpl;
  try entailer!;
  repeat match goal with
         | |- _ /\ _ => split
         | |- Forall _ (upd_Znth _ _ _) =>
           apply Forall_upd_Znth; [list_solve | | ]
         | |- Forall _ (list_repeat _ _) =>
           apply Forall_list_repeat
         | _ => solve [auto]
         | |- Forall _ (BTree.Flattened.put_aux _ _ _) =>
           apply BTree.Flattened.Forall_put; [eauto | | eauto]
         end.

Ltac elim_wand :=
  match goal with
  | |- context rest[ ?P -* ?Q] =>
    sep_apply (wand_frame_elim P Q)
  end.

Ltac allp_left x :=
  match goal with
  | |- context [ allp ?P ] => sep_apply (allp_instantiate P x)
  end.

Lemma body_put: semax_body Vprog Gprog f_put put_spec.
Proof.
  start_function.
  destruct t as [addr tableform listform].
  unfold Trie.trie_rep; fold Trie.trie_rep.
  pose proof H1 as Hcorrect.
  inv H1.
  Intros.
  forward_call (Ews, pk, k).
  pose proof (get_keyslice_inrange k).
  forward_call (get_keyslice k, tableform, addr).
  Intros pc. 
  forward_call ((BTree.make_cursor (get_keyslice k) tableform), pc, tableform, addr, v_obtained_keyslice, Tsh).
  { split; [apply BTree.make_cursor_abs; assumption | auto]. }
  forward_if (temp _t'11 (if BTree.get_exact (get_keyslice k) tableform then Vint Int.one else Vint Int.zero)).
  {
    if_tac in H2; simplify.
    pose proof H3.
    erewrite Trie.table_key_list_key in H3 by eassumption.
    unfold BTree.Flattened.get_key in H3; simplify.
    unfold BTree.get_key in *; simplify.
    forward.
    forward.
    entailer!.
    unfold BTree.get_exact.
    rewrite H3.
    if_tac.
    - if_tac in H20; simplify.
      rewrite Int.eq_true.
      reflexivity.
    - if_tac in H20; simplify.
      assert (Int.repr k0 <> Int.repr (get_keyslice k)). {
        intro.
        apply repr_inj_unsigned in H22; try rep_lia.
        apply BTree.Flattened.get_in_weak in H13.
        rewrite Forall_forall in H10.
        apply H10 in H13.
        simpl in H13.
        unfold Trie.key_inrange in H13.
        rep_lia.
      }
      rewrite Int.eq_false by assumption.
      reflexivity.
  }
  {
    unfold BTree.get_key, BTree.get_exact in *.
    if_tac in H2; simplify.
    forward.
    entailer!.
  }
  forward_if.
  - if_tac in H2; simplify.
    rename v0 into pbnode.
    pose proof H3.
    unfold BTree.get_exact in H3; match_tac in H3; simplify.
    forward_call (BTree.make_cursor (get_keyslice k) tableform, pc, tableform, addr, v_ret_value, Tsh).
    { split; [apply BTree.make_cursor_abs; assumption | auto ]. }
    unfold BTree.get_value, BTree.get_key.
    rewrite H13.
    pose proof H12.
    rewrite @Trie.table_exact_list_exact_some with (addr := addr) (listform := listform) in H12 by assumption.
    destruct H12 as [bnode ?].
    pose proof (BTree.Flattened.iter_sepcon_get_put (Trie.bnode_rep oo snd)
                                                    listform
                                                    (get_keyslice k)
                                                    ltac:(assumption)).
    change (BorderNode.table val (Trie.trie val)) with (Trie.bordernode Trie.value) in *.
    rewrite H12 in H15.
    change ((Trie.bnode_rep oo snd) (get_keyslice k, (pbnode, bnode))) with
        (Trie.bnode_rep (pbnode, bnode)).
    assert (Trie.bordernode_correct bnode). {
      unfold BTree.Flattened.get_exact in H12.
      match_tac in H12; simplify.
      apply BTree.Flattened.get_in_weak in H16.
      rewrite Forall_forall in H9.
      apply H9 in H16.
      auto.
    }
    change (@Trie.bordernode_rep Trie.trie_rep) with Trie.bnode_rep.
    sep_apply H15.
    Intros.
    change ((Trie.bnode_rep oo snd) (get_keyslice k, (pbnode, bnode))) with (Trie.bnode_rep (pbnode, bnode)).
    forward.
    forward_call (BTree.make_cursor (get_keyslice k) tableform, pc).
    assert_PROP (0 <= Zlength k <= Int.max_unsigned) by (unfold cstring_len; entailer!).
    forward_if.
    + deadvars.
      forward_call ((Zlength k), bnode, pbnode, v).
      { rep_lia. }
      allp_left (pbnode, BorderNode.put_prefix (Zlength k) v bnode).
      change ((Trie.bnode_rep oo snd) (_, ?bnode)) with (Trie.bnode_rep bnode).
      elim_wand.
      forward.
      pose (bnode' := BorderNode.put_prefix (Zlength k) v bnode).
      pose (listform' := (BTree.Flattened.put_aux (get_keyslice k) (pbnode, bnode') listform)).
      Exists (Trie.trienode_of addr tableform listform').
      Exists [(Trie.trienode_of addr tableform listform', BTree.make_cursor (get_keyslice k) tableform,
               bnode', BorderNode.before_prefix (Zlength k))].
      entailer!.
      * eapply (Trie.put_case1) with (bnode_addr := pbnode) (listcursor := BTree.Flattened.first_cursor listform); simplify.
        -- rep_lia.
        -- apply BTree.Flattened.first_cursor_abs. assumption.
        -- subst bnode' listform'.
           constructor; reflexivity.
      * subst bnode' listform'.
        simpl Trie.trie_rep.
        cancel.
        apply derives_refl.
    + forward_call (bnode, pbnode).
      forward_if.
      * forward_call (k, pk).
        Intros pk'.
        forward_call (Ews, k, pk', bnode, pbnode).
        { split; [ auto | rep_lia ]. }
        forward_if.
        -- forward_call (k, pk').
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           Intros.
           forward_call (Ews, sublist keyslice_length (Zlength k) k,
                         (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk),
                         bnode, pbnode, v).
           {
             entailer!.
             rewrite Zlength_sublist by rep_lia.
             rewrite field_address_offset by auto with field_compatible.
             split; reflexivity.
           }
           deadvars.
           allp_left (pbnode, BorderNode.put_suffix (sublist keyslice_length (Zlength k) k) v bnode).
           change ((Trie.bnode_rep oo snd) (_, ?bnode)) with (Trie.bnode_rep bnode).
           elim_wand.
           forward.
           remember (BorderNode.put_suffix (sublist keyslice_length (Zlength k) k) v bnode) as bnode'.
           remember (BTree.Flattened.put_aux (get_keyslice k) (pbnode, bnode') listform) as listform'.
           Exists (Trie.trienode_of addr tableform listform').
           Exists [(Trie.trienode_of addr tableform listform', BTree.make_cursor (get_keyslice k) tableform,
                    bnode', BorderNode.before_suffix)].
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           unfold Trie.trie_rep.
           entailer!.
           ++ eapply (Trie.put_case4) with (bnode_addr := pbnode) (listcursor := BTree.Flattened.first_cursor listform); simplify.
              ** rep_lia.
              ** apply BTree.Flattened.first_cursor_abs. assumption.
              ** constructor; reflexivity.
           ++ apply derives_refl.
        -- if_tac in H19; simplify.
           forward_call (k, pk').
           forward_call (bnode, pbnode, Tsh, v_k2, Tsh, v_v2).
           { unfold tkeybox, tkey. cancel. }
           { split3; [auto | congruence | auto]. }
           deadvars.
           match_tac; simplify.
           Intros.
           unfold keybox_rep.
           Intros pk2.
           unfold key_rep.
           Intros pk2'.
           forward.
           forward.
           forward.
           forward.
           assert_PROP (isptr v0) by admit. (* assignment to void * requires isptr or null, not sure if this works for non-pointer values *)
           forward.
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           Intros.
           assert_PROP (0 < Zlength s <= Ptrofs.max_unsigned). {
             unfold cstring_len.
             entailer!.
           }
           forward_call (sublist keyslice_length (Zlength k) k,
                         s,
                         (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk),
                         pk2',
                         v, v0).
           {
             entailer!.
             rewrite Zlength_sublist by rep_lia.
             rewrite field_address_offset by auto with field_compatible.
             split; reflexivity.
           }
           {
             rewrite Zlength_sublist by rep_lia.
             repeat split; auto; rep_lia.
           }
           Intros vret.
           destruct vret as [t' c'].
           destruct bnode as [? [ [ | ] | ]]; simplify.
           simpl fst.
           forward.
           remember (l, None) as bnode'.
           forward_call (bnode', pbnode, t').
           allp_left (pbnode, BorderNode.put_link t' bnode').
           change ((Trie.bnode_rep oo snd) (_, ?bnode)) with (Trie.bnode_rep bnode).
           elim_wand.
           forward.
           fold_keyrep.
           forward_call (s, pk2).
           forward.
           remember (BorderNode.put_link t' (l, Some (inl (s0, v1)))) as bnode'.
           remember (BTree.Flattened.put_aux (get_keyslice k) (pbnode, bnode') listform) as listform'.
           Exists (Trie.trienode_of addr tableform listform').
           Exists ([(Trie.trienode_of addr tableform listform', BTree.make_cursor (get_keyslice k) tableform,
                     bnode', BorderNode.before_suffix)] ++ c').
           entailer!.
           ++ eapply (Trie.put_case5) with (bnode_addr := pbnode) (listcursor := BTree.Flattened.first_cursor listform); simplify.
              ** rep_lia.
              ** simpl in H23, H20.
                 if_tac in H20; simplify.
              ** apply BTree.Flattened.first_cursor_abs. assumption.
              ** constructor; reflexivity.
           ++ rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
              simpl.
              unfold Trie.bnode_rep.
              entailer!.
      * forward_call (bnode, pbnode, v_subindex__1, Tsh).
        forward_if.
        -- match_tac; simplify.
           deadvars.
           simpl Trie.bnode_rep at 1.
           destruct bnode as [? [ [|] | ]]; simplify.
           simpl in H21; simplify.
           Intros.
           forward.
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           Intros.
           forward_call (sublist keyslice_length (Zlength k) k,
                         (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk),
                         v, t, c).
           {
             entailer!.
             rewrite Zlength_sublist by rep_lia.
             rewrite field_address_offset by auto with field_compatible.
             split; reflexivity.
           }
           {
             rewrite Zlength_sublist by rep_lia.
             inv H16.
             repeat split; auto; rep_lia. 
           }
           Intros vret.
           destruct vret as [t' c'].
           simpl fst in *. simpl snd in *.
           erewrite Trie.put_same_addr by eassumption.
           gather_SEP 1 2 3 4 5 6 7.
           match goal with
           | |- context [Trie.trie_rep t' * ?b] =>
             assert (Trie.trie_rep t' * b = Trie.bnode_rep (pbnode, BorderNode.put_link t' (l, Some (inr t))))
           end. {
             simpl.
             apply pred_ext; cancel.
           }
           rewrite H23; clear H23.
           allp_left (pbnode, BorderNode.put_link t' (l, Some (inr t))).
           change ((Trie.bnode_rep oo snd) (get_keyslice k, (pbnode, BorderNode.put_link t' (l, Some (inr t))))) with
               (Trie.bnode_rep (pbnode, BorderNode.put_link t' (l, Some (inr t)))).
           elim_wand.
           forward.
           match goal with
           | |- context [(pbnode, ?b)] =>
             remember b as bnode'
           end.
           match goal with
           | |- context [iter_sepcon _ ?l] =>
             remember l as listform'
           end.
           Exists (Trie.trienode_of addr tableform listform').
           Exists ((Trie.trienode_of addr tableform listform', BTree.make_cursor (get_keyslice k) tableform,
                    bnode', BorderNode.before_suffix) :: c').
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           entailer!.
           ++ change (l, Some (inr t')) with (BorderNode.put_link t' (l, Some (inr t))).
              eapply (Trie.put_case2) with (bnode_addr := pbnode) (listcursor := BTree.Flattened.first_cursor listform); simplify.
              ** rep_lia.
              ** reflexivity.
              ** apply BTree.Flattened.first_cursor_abs. assumption.
              ** constructor; reflexivity.
           ++ simpl.
              cancel.
              apply derives_refl.
        -- match_tac; simplify.
           deadvars.
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           Intros.
           forward_call (Ews, sublist keyslice_length (Zlength k) k,
                         (field_address (tarray tschar (Zlength k)) [ArraySubsc keyslice_length] pk),
                         bnode, pbnode, v).
           {
             entailer!.
             rewrite Zlength_sublist by rep_lia.
             rewrite field_address_offset by auto with field_compatible.
             split; reflexivity.
           }
           allp_left (pbnode, BorderNode.put_suffix (sublist keyslice_length (Zlength k) k) v bnode).
           change ((Trie.bnode_rep oo snd) (_, ?bnode)) with (Trie.bnode_rep bnode).
           elim_wand.
           forward.
           match goal with
           | |- context [(pbnode, ?b)] =>
             remember b as bnode'
           end.
           match goal with
           | |- context [iter_sepcon _ ?l] =>
             remember l as listform'
           end.
           Exists (Trie.trienode_of addr tableform listform').
           Exists ([(Trie.trienode_of addr tableform listform', BTree.make_cursor (get_keyslice k) tableform,
                     bnode', BorderNode.before_suffix)]).
           rewrite (cstring_len_split _ k pk keyslice_length) by rep_lia.
           entailer!.
           ++ eapply (Trie.put_case3) with (bnode_addr := pbnode) (listcursor := BTree.Flattened.first_cursor listform); simplify.
              ** rep_lia.
              ** destruct bnode as [? [ [ | ] | ]]; simpl in *; simplify.
              ** apply BTree.Flattened.first_cursor_abs. assumption.
              ** constructor; reflexivity.
           ++ simpl.
              cancel.
              apply derives_refl.
  - deadvars.
    if_tac in H2; simplify.
    pose proof H3.
    eapply Trie.table_exact_list_exact_none in H3; [ | eassumption].
    forward_call tt.
    Intros pbnode.
    forward_call (k, pk).
    Intros pk'.
    forward_call (Ews, k, pk', @BorderNode.empty val (Trie.trie val), pbnode, v).
    forward_call (k, pk').
    forward_call ((get_keyslice k), pbnode, tableform, addr, (BTree.make_cursor (get_keyslice k) tableform), pc).
    { apply BTree.make_cursor_abs; assumption. }
    Intros vret.
    destruct vret as [tableform' tablecursor'].
    simpl fst in *.
    simpl snd in *.
    forward_call (tablecursor', pc).
    forward.
    lazymatch goal with
    | |- context [BTree.table_rep _ _ * ?e * cstring_len _ _ _] =>
      change e with (Trie.bnode_rep (pbnode, BorderNode.put_value k v BorderNode.empty))
    end.
    match goal with
    | |- context [(pbnode, ?b)] =>
      remember b as bnode'
    end.
    pose (listform' := BTree.Flattened.put_aux (get_keyslice k) (pbnode, bnode') listform).
    Exists (Trie.trienode_of addr tableform' listform').
    Exists [(Trie.trienode_of addr tableform' listform', tablecursor', bnode', BorderNode.before_suffix)].
    entailer!.
    + eapply Trie.put_case6 with (listcursor := (BTree.Flattened.first_cursor listform))
                                 (bnode_addr := pbnode); simplify.
      * apply BTree.Flattened.first_cursor_abs. assumption.
      * constructor; reflexivity.
      * apply BTree.make_cursor_abs. assumption.
    + subst listform'.
      simpl.
      entailer!.
      * match goal with
        | |- context [(pbnode, ?b)] =>
          remember b as bnode'
        end.
        pose proof (BTree.Flattened.iter_sepcon_put (Trie.bnode_rep oo snd)
                                                    listform
                                                    (get_keyslice k)
                                                    (pbnode, bnode')
                                                    ltac:(assumption)).
        lazymatch goal with (* why always this??? *)
        | H0: context [match ?e with _ => _ end * _] |- _ =>
          let H := fresh in
          assert (H: e = None) by assumption; rewrite H in H0; clear H
        end.
        unfold Trie.bnode_rep in H20.
        rewrite emp_sepcon in H20.
        change (BorderNode.table val (Trie.trie val)) with (Trie.bordernode Trie.value) in *.
        match goal with
        | |- _ |-- ?e =>
          match goal with
          | H: _ * _ = ?f |- _ =>
            change e with f
          end
        end.
        rewrite <- H20.
        simpl.
        cancel.
Admitted.

Lemma body_create_pair: semax_body Vprog Gprog f_create_pair create_pair_spec.
Proof.
Admitted.
(*   start_function. *)
(*   forward_call (Tsh, pk1, k1). *)
(*   forward_call (Tsh, pk2, k2). *)
(*   forward_if. *)
(*   - assert_PROP (0 <= Zlength k1 <= Int.max_unsigned) by (unfold cstring_len; entailer!). *)
(*     assert_PROP (0 <= Zlength k2 <= Int.max_unsigned) by (unfold cstring_len; entailer!). *)
(*     assert_PROP (get_keyslice k1 = get_keyslice k2). { *)
(*       unfold cstring_len. *)
(*       entailer!. *)
(*       apply repr_inj_unsigned; *)
(*         first [ apply get_keyslice_inrange | assumption ]. *)
(*     } *)
(*     forward_if (temp _t'12 (if Trie.create_pair_aux_dec k1 k2 then Vint Int.one else Vint Int.zero)). *)
(*     { *)
(*       forward. *)
(*       entailer!. *)
(*       if_tac. *)
(*       - reflexivity. *)
(*       - rep_lia. *)
(*     } *)
(*     { *)
(*       forward. *)
(*       entailer!. *)
(*       if_tac. *)
(*       + assert (Zlength k2 <= keyslice_length) by rep_lia. *)
(*         destruct (Int.ltu (Int.repr 4) (Int.repr (Zlength k2))) eqn:Heqn. *)
(*         * apply ltu_inv in Heqn. *)
(*           rewrite ?Int.unsigned_repr in Heqn by rep_lia. *)
(*           rep_lia. *)
(*         * reflexivity. *)
(*       + destruct (Int.ltu (Int.repr 4) (Int.repr (Zlength k2))) eqn:Heqn. *)
(*         * reflexivity. *)
(*         * apply ltu_false_inv in Heqn. *)
(*           rewrite ?Int.unsigned_repr in Heqn by rep_lia. *)
(*           rep_lia. *)
(*     } *)
(*     forward_if. *)
(*     + if_tac in H7; try solve [inv H7]. *)
(*       forward_call tt. *)
(*       Intros pbnode. *)
(*       forward_call (k1, pk1). *)
(*       Intros pk1'. *)
(*       forward_call (Tsh, k1, pk1', Tsh, @BorderNode.empty val _, pbnode, v1). *)
(*       forward_call (k2, pk2). *)
(*       Intros pk2'. *)
(*       forward_call (Tsh, k2, pk2', Tsh, (BorderNode.put_value k1 v1 BorderNode.empty), pbnode, v2). *)
(*       forward_call (k1, pk1'). *)
(*       forward_call (k2, pk2'). *)
(*       forward_call tt. *)
(*       Intros vret. *)
(*       destruct vret as [t pt]. *)
(*       simpl fst in *. *)
(*       simpl snd in *. *)
(*       pose proof (BTree.empty_correct _ H9). *)
(*       forward_call (t, pt). *)
(*       Intros pc. *)
(*       forward_call ((get_keyslice k1), pbnode, t, pt, (BTree.first_cursor t), pc). *)
(*       { apply BTree.first_cursor_abs; assumption. } *)
(*       Intros vret. *)
(*       destruct vret as [tableform tablecursor]. *)
(*       simpl fst in *. *)
(*       simpl snd in *. *)
(*       forward_call (tablecursor, pc). *)
(*       forward. *)
(*       pose (bnode := BorderNode.put_value k2 (Trie.value_of v2) *)
(*                                           (BorderNode.put_value k1 (Trie.value_of v1) BorderNode.empty)). *)
(*       pose (listform := BTree.Flattened.put_aux (get_keyslice k1) (pbnode, bnode) []). *)
(*       Exists (Trie.trienode_of pt tableform listform). *)
(*       Exists pt. *)
(*       Exists [(Trie.trienode_of pt tableform listform, tablecursor, bnode, BorderNode.length_to_cursor (Zlength k1))]. *)
(*       entailer!. *)
(*       * eapply Trie.create_pair_case1 with (listform0 := listform); *)
(*           unfold BTree.Flattened.put, BTree.Flattened.empty, listform; *)
(*           repeat match goal with *)
(*                  | [|- _ /\ _] => *)
(*                    split *)
(*                  end; *)
(*           eauto. *)
(*       * unfold listform. *)
(*         simpl. *)
(*         entailer!. *)
(*         -- unfold Trie.key_inrange. *)
(*            repeat first [ apply get_keyslice_inrange | constructor ]. *)
(*         -- unfold bnode, BorderNode.put_value. *)
(*            simpl. *)
(*            if_tac; if_tac; *)
(*              simpl; *)
(*              rewrite ?Forall_map; *)
(*              rewrite <- ?upd_Znth_map; *)
(*              rewrite ?map_list_repeat; *)
(*              simpl; *)
(*              entailer!; *)
(*              repeat match goal with *)
(*                     | |- _ /\ _ => split *)
(*                     | |- Forall _ (upd_Znth _ _ _) => *)
(*                       apply Forall_upd_Znth; [list_solve | | ] *)
(*                     | |- Forall _ (list_repeat _ _) => *)
(*                       apply Forall_list_repeat *)
(*                     | _ => solve [auto] *)
(*                     end. *)
(*     + if_tac in H7; try solve [inv H7]. *)
(*       forward_call tt. *)
(*       Intros pbnode. *)
(*       rewrite (cstring_len_split _ k1 pk1 keyslice_length) by rep_lia. *)
(*       rewrite (cstring_len_split _ k2 pk2 keyslice_length) by rep_lia. *)
(*       Intros. *)
(*       forward_call ((sublist keyslice_length (Zlength k1) k1), *)
(*                     (sublist keyslice_length (Zlength k2) k2), *)
(*                     (field_address (tarray tschar (Zlength k1)) [ArraySubsc keyslice_length] pk1), *)
(*                     (field_address (tarray tschar (Zlength k2)) [ArraySubsc keyslice_length] pk2), *)
(*                     v1, v2). *)
(*       { *)
(*         entailer!. *)
(*         rewrite ?field_address_offset by (auto with field_compatible). *)
(*         rewrite ?Zlength_sublist by rep_lia. *)
(*         repeat constructor. *)
(*       } *)
(*       { *)
(*         rewrite ?Zlength_sublist by rep_lia. *)
(*         repeat first [ split | rep_lia | auto ]. *)
(*       } *)
(*       Intros vret. *)
(*       destruct vret as [[t' pt'] c']. *)
(*       simpl fst in *. *)
(*       simpl snd in *. *)
(*       forward_call (Tsh, @BorderNode.empty val _, pbnode, pt'). *)
(*       forward_call tt. *)
(*       Intros vret. *)
(*       destruct vret as [t pt]. *)
(*       simpl fst in *. *)
(*       simpl snd in *. *)
(*       pose proof (BTree.empty_correct _ H12). *)
(*       forward_call (t, pt). *)
(*       Intros pc. *)
(*       forward_call ((get_keyslice k1), pbnode, t, pt, (BTree.first_cursor t), pc). *)
(*       { apply BTree.first_cursor_abs; assumption. } *)
(*       Intros vret. *)
(*       destruct vret as [tableform tablecursor]. *)
(*       simpl fst in *. *)
(*       simpl snd in *. *)
(*       forward_call (tablecursor, pc). *)
(*       forward. *)
(*       pose (bnode := BorderNode.put_suffix None (Trie.trie_of t') BorderNode.empty). *)
(*       pose (listform := BTree.Flattened.put_aux (get_keyslice k1) (pbnode, bnode) []). *)
(*       Exists (Trie.trienode_of pt tableform listform). *)
(*       Exists pt. *)
(*       Exists ((Trie.trienode_of pt tableform listform, tablecursor, bnode, BorderNode.before_suffix) :: c'). *)
(*       entailer!. *)
(*       * eapply Trie.create_pair_case2 with (listform0 := listform); *)
(*           unfold BTree.Flattened.put, BTree.Flattened.empty, listform; *)
(*           repeat match goal with *)
(*                  | [|- _ /\ _] => *)
(*                    split *)
(*                  end; *)
(*           eauto; rep_lia. *)
(*       * unfold listform. *)
(*         simpl. *)
(*         entailer!. *)
(*         -- unfold Trie.key_inrange. *)
(*            repeat first [ apply get_keyslice_inrange | constructor ]. *)
(*         -- unfold bnode, BorderNode.put_value. *)
(*            simpl. *)
(*            Exists pt'. *)
(*            rewrite (cstring_len_split _ k1 pk1 keyslice_length) by rep_lia. *)
(*            rewrite (cstring_len_split _ k2 pk2 keyslice_length) by rep_lia. *)
(*            entailer!. *)
(*   - forward_call tt. *)
(*     Intros pbnode1. *)
(*     forward_call (k1, pk1). *)
(*     Intros pk1'. *)
(*     forward_call (Tsh, k1, pk1', Tsh, @BorderNode.empty val _, pbnode1, v1). *)
(*     forward_call tt. *)
(*     Intros pbnode2. *)
(*     forward_call (k2, pk2). *)
(*     Intros pk2'. *)
(*     forward_call (Tsh, k2, pk2', Tsh, @BorderNode.empty val _, pbnode2, v2). *)
(*     forward_call (k1, pk1'). *)
(*     forward_call (k2, pk2'). *)
(*     forward_call tt. *)
(*     Intros vret. *)
(*     destruct vret as [t pt]. *)
(*     simpl fst in *. *)
(*     simpl snd in *. *)
(*     pose proof (BTree.empty_correct _ H4). *)
(*     forward_call (t, pt). *)
(*     Intros pc2. *)
(*     forward_call ((get_keyslice k2), pbnode2, t, pt, (BTree.first_cursor t), pc2). *)
(*     { apply BTree.first_cursor_abs; assumption. } *)
(*     Intros vret. *)
(*     destruct vret as [tableform2 tablecursor2]. *)
(*     simpl fst in *. *)
(*     simpl snd in *. *)
(*     forward_call (tablecursor2, pc2). *)
(*     pose proof H6. *)
(*     apply BTree.put_correct in H6; [ | apply BTree.first_cursor_abs; assumption ]. *)
(*     forward_call (tableform2, pt). *)
(*     Intros pc1. *)
(*     forward_call ((get_keyslice k1), pbnode1, tableform2, pt, (BTree.first_cursor tableform2), pc1). *)
(*     { apply BTree.first_cursor_abs; assumption. } *)
(*     Intros vret. *)
(*     destruct vret as [tableform1 tablecursor1]. *)
(*     simpl fst in *. *)
(*     simpl snd in *. *)
(*     forward_call (tablecursor1, pc1). *)
(*     forward. *)
(*     pose (bnode1 := BorderNode.put_value k1 (Trie.value_of v1) BorderNode.empty). *)
(*     pose (bnode2 := BorderNode.put_value k2 (Trie.value_of v2) BorderNode.empty). *)
(*     pose (listform2 := BTree.Flattened.put_aux (get_keyslice k2) (pbnode2, bnode2) []). *)
(*     pose (listform1 := BTree.Flattened.put_aux (get_keyslice k1) (pbnode1, bnode1) listform2). *)
(*     Exists (Trie.trienode_of pt tableform1 listform1). *)
(*     Exists pt. *)
(*     Exists [(Trie.trienode_of pt tableform1 listform1, tablecursor1, bnode1, BorderNode.length_to_cursor (Zlength k1))]. *)
(*     assert (get_keyslice k1 <> get_keyslice k2). { *)
(*       intro. *)
(*       apply H3. *)
(*       f_equal. *)
(*       assumption. *)
(*     } *)
(*     entailer!. *)
(*     + eapply Trie.create_pair_case3 with (listform3 := listform1) (listform4 := listform2); *)
(*         unfold BTree.Flattened.put, BTree.Flattened.empty, listform1, listform2; *)
(*         repeat match goal with *)
(*         | [|- _ /\ _] => *)
(*           split *)
(*         end; *)
(*         eauto. *)
(*     + unfold listform1, listform2. *)
(*       simpl. *)
(*       if_tac. *)
(*       * entailer!. *)
(*         -- unfold Trie.key_inrange. *)
(*            repeat first [ apply get_keyslice_inrange | constructor ]. *)
(*         -- unfold iter_sepcon. *)
(*            unfold bnode1, bnode2, BorderNode.put_value. *)
(*            simpl. *)
(*            repeat if_tac; *)
(*              rewrite ?Forall_map; *)
(*              rewrite <- ?upd_Znth_map; *)
(*              rewrite ?map_list_repeat; *)
(*              simpl; *)
(*              entailer!; *)
(*              repeat match goal with *)
(*                     | |- _ /\ _ => split *)
(*                     | |- Forall _ (upd_Znth _ _ _) => *)
(*                       apply Forall_upd_Znth; [list_solve | | ] *)
(*                     | |- Forall _ (list_repeat _ _) => *)
(*                       apply Forall_list_repeat *)
(*                     | _ => solve [auto] *)
(*                     end. *)
(*       * entailer!. *)
(*         rewrite ?if_false by auto. *)
(*         -- unfold Trie.key_inrange. *)
(*            repeat first [ apply get_keyslice_inrange | constructor ]. *)
(*         -- unfold iter_sepcon. *)
(*            unfold bnode1, bnode2, BorderNode.put_value. *)
(*            rewrite ?(if_false _ (BTree.Flattened.KeyFacts.eq_dec (get_keyslice k1) (get_keyslice k2))) by auto. *)
(*            simpl. *)
(*            repeat if_tac; *)
(*              rewrite ?Forall_map; *)
(*              rewrite <- ?upd_Znth_map; *)
(*              rewrite ?map_list_repeat; *)
(*              simpl; *)
(*              entailer!; *)
(*              repeat match goal with *)
(*                     | |- _ /\ _ => split *)
(*                     | |- Forall _ (upd_Znth _ _ _) => *)
(*                       apply Forall_upd_Znth; [list_solve | | ] *)
(*                     | |- Forall _ (list_repeat _ _) => *)
(*                       apply Forall_list_repeat *)
(*                     | _ => solve [auto] *)
(*                     end. *)
(* Qed. *)
