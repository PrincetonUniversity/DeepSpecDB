(** * verif_movetonext.v : Correctness proof of firstpointer, moveToNext and RL_MoveToNext *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.

Lemma body_lastpointer: semax_body Vprog Gprog f_lastpointer lastpointer_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'1=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward.                    (* t'3=node->numKeys *)
    forward.                    (* return *)
    destruct isLeaf; try inv H0.
    entailer!.               (* return *)
    fold n. rewrite unfold_btnode_rep with (n:=n). unfold n.
      Exists ent_end. entailer!.
  -
    destruct isLeaf; try inv H0.
    forward.                    (* t'2=node->numKeys *)
    pose proof (node_wf_numKeys _ H). simpl in H0.
    forward.                    (* return *)
    entailer!.
    (*+ simpl. normalize.
    +*) Exists ent_end. fold (iter_sepcon entry_rep). fold btnode_rep. apply derives_refl.
Qed.

Lemma partial_cursor_correct_cons {X} (c: cursor X) (r: relation X) (n: node X) (i: Z): 
  partial_cursor_correct_rel ((n, i)::c) r -> partial_cursor_correct_rel c r.
Proof.
  intro h. 
  unfold partial_cursor_correct_rel in h|-*. destruct c. easy.
  destruct p as [n0 i0]; case_eq (nth_node i0 n0); case_eq (nth_node i n).
  + intros n1 h1 n2 h2. rewrite h1 in h. simpl in h|-*. easy.
  + intros hnone n1 h1. rewrite hnone in h. contradiction.
  + intros n1 h1 hnone. rewrite h1 in h. simpl in h.
    destruct h as [[_ h] _]. rewrite h in hnone. discriminate.
  + intros hnone1 hnone2.
    rewrite hnone1 in h. contradiction.
Qed.

Lemma complete_sublist_partial: forall (X:Type) {_: Inhabitant X} (c:cursor X) r i,
    i >= 1 ->
    complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (sublist i (Zlength c) c) r.
Proof.
  intros X inhx c r i hi hcomplete.
  destruct c as [|[n ii]]; try easy.
  unfold complete_cursor_correct_rel in hcomplete. simpl in hcomplete.
  case_eq (Znth_option ii (node_le n)); [| intro hnone; rewrite hnone in hcomplete; contradiction].
  intros e he. rewrite he in hcomplete. destruct e; try contradiction.
  rewrite Zlength_cons.
  destruct (Z_ge_dec i (Z.succ (Zlength c))) as [hge | hnge].
 - unfold sublist. rewrite firstn_same. rewrite skipn_short. simpl; auto.
    clear - hge hi. rewrite Zlength_correct in hge. simpl. zify;lia.
    clear - hge hi. rewrite Zlength_correct in *. simpl. zify;lia.
  - apply Znot_ge_lt in hnge.
    assert (hi': 1 <= i <= Zlength c) by lia. clear hi hnge. pose proof hi' as hi''.
    revert hi'. apply Z_lt_induction with (x := i);[|lia].
  clear hi'' i.
  intros i hind hi.
  destruct (eq_dec i 1) as [he1 | he1]. rewrite he1.
  rewrite sublist_1_cons. replace (Z.succ (Zlength c) - 1) with (Zlength c) by lia.
  rewrite sublist_same by lia. unfold partial_cursor_correct_rel.
  destruct c; try easy. destruct p as [n' i']. simpl in hcomplete |-*.
  destruct (Znth_option ii (node_le n)); try contradiction. inv he.
  destruct hcomplete as [[? ?] ?]. rewrite H0. auto.
  inv he.
  assert (h: partial_cursor_correct_rel (sublist (i-1) (Z.succ (Zlength c)) ((n, ii) :: c)) r).
  apply hind; lia.
  rewrite sublist_split with (mid := i) in h; [|lia|rewrite Zlength_cons; lia].
  remember (i-1) as j. replace i with (j+1) in h by lia.
  rewrite sublist_len_1 in h; [|rewrite Zlength_cons; lia]. unfold app in h.
  destruct (Znth j ((n, ii) :: c)). apply partial_cursor_correct_cons in h.
  replace (j+1) with i in h by lia. auto.
Qed.

Lemma sublist_tl: forall (A:Type) (a0: Inhabitant A) c i (a:A) c',
    0 <= i < Zlength c ->
    sublist i (Zlength c) c = a :: c' ->
    c' = sublist (i+1) (Zlength c) c.
Proof.
  intros A a0 c i a c' hi hsub.
  rewrite sublist_split with (mid := i+1) in hsub.
  rewrite sublist_len_1 in hsub.
  unfold app in hsub. inversion hsub. auto.
  lia. lia. lia.
Qed.

Lemma up_at_last_range: forall (X:Type) (c:cursor X) m,
    0 <= Zlength c - 1 < m ->
    0 <= Zlength (up_at_last c) - 1 < m.
Proof.
  intros.
  induction c.
  - simpl in H. lia.
  - destruct a as [n i]. simpl. destruct c.
    + simpl. lia.
    + destruct(Z.eqb i (lastpointer n)).
      * apply IHc. split. rewrite Zlength_cons. rewrite Zsuccminusone. apply Zlength_nonneg.
        rewrite Zlength_cons in H. lia.
      * auto.
Qed.

Lemma complete_partial_upatlast: forall (X:Type) (c:cursor X) r,
    partial_cursor_correct_rel c r \/ complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (up_at_last c) r \/ complete_cursor_correct_rel (up_at_last c) r.
Proof.
  intros.
  induction c.
  - simpl. left. auto.
  - simpl. destruct a as [n i].
    destruct c.
    + auto.
    + destruct(Z.eqb i (lastpointer n)).
      * apply IHc. destruct H.
        { left. apply partial_cursor_correct_cons with (n0 := n) (i0 := i). auto. }
        { left. unfold complete_cursor_correct_rel, complete_cursor_correct, getCEntry in H.
          destruct (Znth_option i (node_le n)) eqn:?H; try contradiction.
          destruct e; try contradiction. destruct H as [H _]. destruct p.
          unfold partial_cursor_correct_rel. simpl in H. rewrite (proj2 H).
          auto.
        }
      * auto.
Qed.

Lemma index_eqb_false: forall (i1 i2: Z),
    i1 <> i2 <-> Z.eqb i1 i2 = false.
Proof.
  intros i1 i2.
  unfold Z.eqb. symmetry; apply Z.eqb_neq.
Qed.


Lemma upatlast_correct: forall c r,
    complete_cursor c r ->
    ne_partial_cursor (up_at_last c) r  /\ isValid (up_at_last c) r = true 
    \/ complete_cursor (up_at_last c) r.
Proof.
intros ? ? ?.
assert (ne_partial_cursor c r /\ isValid c r = true  \/ complete_cursor c r) by auto.
clear H; rename H0 into H.
induction c as [|[??]]; simpl; intros; auto.
destruct c as [|[??]]; auto.
spec IHc. { clear IHc.
  left.
  split.
  2:{ destruct H. destruct H.
    -
     clear - H. destruct H as [? _]. hnf in H.
     destruct (nth_node z n); try contradiction.
     simpl in H. destruct H as [[??]?]. unfold isValid. simpl.
     destruct n0; auto. destruct Last; auto.
     simpl in H0. destruct entryzero; try discriminate. destruct isLeaf; try discriminate.
     destruct (z0 =? Zlength le) eqn:?H; auto.
     apply Z.eqb_eq in H2. subst.
     rewrite if_false in H0 by list_solve.
     apply nth_node_le_some in H0; lia.
   - 
     clear - H. destruct H as [? _]. hnf in H. simpl in H.
     destruct (Znth_option z (node_le n)) as [[?|?]|] eqn:?H; try contradiction.
     destruct H as [[??]?]. unfold isValid. simpl.
     destruct n0; auto. destruct Last; auto.
     simpl in H0. destruct entryzero; try discriminate. destruct isLeaf; try discriminate.
     simpl in H1. 
     destruct (z0 =? Zlength le) eqn:?H; auto.
     apply Z.eqb_eq in H3. subst.
     rewrite if_false in H1 by list_solve.
     apply nth_node_le_some in H1; lia.
  }
  split; [  |list_solve].
  destruct H as [[[? _]?]|[??]].
  simpl in H|-*.
  destruct (nth_node z n) eqn:?H; auto; try contradiction.
  destruct H as [[??]?]. rewrite H2; auto.
  hnf in H.
  simpl in H|-*.
  destruct (Znth_option z (node_le n)) as [[?|?]|] eqn:?H; try contradiction.
  destruct H as [[??]?]. rewrite H2; auto.
}
 destruct (z =? lastpointer n) eqn:?H; auto.
Qed.


Lemma next_cursor_correct: forall c r,
    ne_partial_cursor c r/\ isValid c r = true \/ complete_cursor c r ->
    ne_partial_cursor (next_cursor c) r \/ complete_cursor (next_cursor c) r.
Proof.
intros.
destruct c as [|[??]]; simpl in *; auto.
destruct H; auto.
destruct H; auto.
destruct H as [[??]|?].
-
left.
destruct H; split; auto.
unfold isValid in H0.
simpl in H0.
hnf in H|-*.
unfold partial_cursor_correct in *; fold @partial_cursor_correct in *.
forget (get_root r) as root. clear r.
clear H1.
destruct (nth_node z n) eqn:?H; try contradiction.
destruct H as [? _].
destruct (nth_node (Z.succ z) n) eqn:?H; auto.
destruct n; simpl in *.
destruct entryzero; try discriminate.
destruct isLeaf; try discriminate.
destruct Last.
destruct (z =? Zlength le) eqn:?H; try discriminate.
apply Z.eqb_neq in H3.
if_tac in H2; try discriminate.
if_tac in H1.
subst.
symmetry in H1; inv H1.
clear H3 H4.
Abort.

Lemma movetonext_correct: forall c r,
    complete_cursor c r -> isValid c r = true ->
    ne_partial_cursor (next_cursor (up_at_last c)) r \/ complete_cursor (next_cursor(up_at_last c)) r.
 (* This is not true!  If the cursor is at the very end of the relation, then it fails.
   The solution is to weaken the conclusion slightly; probably by changing
   the definitions of ne_partial_cursor and complete_cursor;  which in turn
  changes many other things... *)
Proof.
  intros c r hcomplete hvalid.
  assert (hint:  root_integrity (get_root r)) by apply hcomplete.
  unfold ne_partial_cursor.
  remember (next_cursor (up_at_last c)) as nxt.
  unfold complete_cursor in hcomplete|-*.
  unshelve epose proof (complete_partial_upatlast val c r _) as hual. now right.
  destruct c as [|[n i] c]. easy.
  assert (hleaf: is_true (node_isLeaf n)) by now apply (complete_leaf n i c r).
  assert (hcomplete' := hcomplete).
  unfold complete_cursor_correct_rel, complete_cursor_correct, getCEntry in hcomplete.
  case_eq (Znth_option i (node_le n)); [|intros hnone; now rewrite hnone in hcomplete].
  intros e he; rewrite he in hcomplete. destruct e; try easy.
  simpl in Heqnxt, hual.
  case_eq (Z.eqb i (lastpointer n)); intro h; fold (@up_at_last val) in Heqnxt, hual.
  - left.
    rewrite h in Heqnxt, hual.
    apply Z.eqb_eq in h. subst i.
    destruct n; simpl in he. hnf in hleaf. destruct isLeaf; try contradiction.
    apply Znth_option_some in he. lia.
  - right. rewrite h in *. apply Z.eqb_neq in h.
    assert (hnxt : nxt = (n, Z.succ i) :: c).
    { rewrite Heqnxt. now destruct c. }
    rewrite hnxt. split; [|easy].
    unfold complete_cursor_correct_rel, getCEntry.
    destruct (zeq i (Z.pred (Zlength (node_le n)))).
    2:{ 
    unshelve eassert (h1 := Znth_option_in_range (Z.succ i) (node_le n) _).
    -- destruct n as [ptr0 le [] First Last x]; try easy.
       apply Znth_option_some in he. simpl in he,n0,h|-*. lia.
    -- destruct h1 as [e' he'].
       rewrite he'.
       unshelve eassert (h2 := integrity_nth_leaf _ _ _ _ hleaf he').
       { apply hint.
         replace n with (currNode ((n, i) :: c) r) by reflexivity.
         now apply complete_cursor_subnode. }
       destruct h2 as [k' [v' [x' he'']]]. rewrite he''.
       simpl.
       rewrite he'' in he'. rewrite he'. easy.
    }
  elimtype False. subst i. rewrite Z.succ_pred in *.
  clear h.
  admit.
all: fail.
Admitted.


Lemma movetonext_complete : forall c r,
    complete_cursor c r ->
    complete_cursor (moveToNext c r) r.
Proof.
intros.
pose proof (complete_valid _ _ H).
pose proof (movetonext_correct _ _ H H0).
hnf in H|-*.
destruct H.
split; auto.
hnf in H|-*.
destruct (getCEntry c) as [[|] | ] eqn:?H; try contradiction.
unfold moveToNext.
rewrite H0.
destruct (next_cursor (up_at_last c)) as [ | [? ?]] eqn:?H.
-
destruct H1; hnf in H1.
destruct H1. autorewrite with sublist in H5.  lia.
destruct H1 as [? _].
hnf in H1. contradiction.
-
destruct (isnodeleaf n) eqn:?H.
simpl.
destruct (Znth_option_in_range z (node_le n)) as [e ?].
admit.
destruct (integrity_nth_leaf n e z) as [k' [v' [x' ?]]]; auto.
admit.
clear - H5; admit. 
subst e.
rewrite H6.
split; auto.
destruct H1 as [[? ?]|[? ?]].
simpl in H1.
destruct (nth_node z n) eqn:?H; try contradiction.
destruct H1; auto.
hnf in H1.
simpl in H1.
rewrite H6 in H1.
destruct H1; auto.
destruct (nth_node z n).
+
admit.
+
destruct H1 as [[? ?]|[? ?]].
simpl in H1|-*.
destruct (nth_node z n) eqn:?H; try contradiction.
destruct H1 as [? _].
Admitted.

Lemma length_next_cursor: forall (X:Type) (c:cursor X),
    Zlength (next_cursor c) = Zlength c.
Proof.
  intros. destruct c. simpl. auto. simpl. destruct p.
  rewrite Zlength_cons. rewrite Zlength_cons. auto.
Qed.

Lemma fst_next_cursor: forall (X:Type) (c:cursor X),
    map fst c = map fst (next_cursor c).
Proof.
  intros. destruct c. simpl. auto. destruct p. simpl. auto.
Qed.

Lemma upd_Znth_rev: forall (X:Type) (l:list X) v,
    l <> [] ->
    upd_Znth (Zlength l -1) (rev l) v = rev(upd_Znth 0 l v).
Proof.
  intros. destruct l.
  - exfalso. apply H. auto.
  - simpl. rewrite Zlength_cons. rewrite Zsuccminusone.
    rewrite upd_Znth_app2. rewrite Zlength_rev, Zminus_diag, ! upd_Znth0; trivial.
    rewrite Zlength_rev, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma body_moveToNext: semax_body Vprog Gprog f_moveToNext moveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c']. { inv H. inv H3. }
  set (c:=(n,i)::c').
  assert (H99: Forall (Z.le  (-1)) (map snd c)). {
     fold c in H; clearbody c. clear - H. 
     destruct H as [? _]. hnf in H.
     destruct (getCEntry c) as [[?|?]|]; try contradiction.
     apply complete_correct_indexes in H.
     apply Forall_map. eapply Forall_impl; try apply H.
     intros [? ?]; simpl; intros. apply H0.
   }
  unfold cursor_rep.
  Intros anc_end. Intros idx_end. unfold r.

  (*NEW*) assert_PROP (value_fits tcursor (prel,
           (Vint (Int.repr (Zlength c - 1)),
           (rev (map (fun x : node val * Z => Vint (Int.repr (snd x))) c) ++
            idx_end, rev (map getval (map fst c)) ++ anc_end)))) as VF by entailer!.
          apply value_fits_tcursor_props in VF. rewrite !Zlength_app, ! Zlength_rev, ! Zlength_map in VF; destruct VF as [IL AL].
  
  forward_call(r,c,pc).         (* t'1=isValid(cursor) *)
  { unfold relation_rep, cursor_rep, r. Exists anc_end idx_end. cancel. }
  forward_if.                              (* if t'1 == 0 *)
  { Ltac entailer_for_return ::= idtac.
    forward.                    (* return *)
    fold c in H3. fold r in H3.
    destruct (isValid c r) eqn:INVALID.
    + inv H3.
    + fold c. fold r.
      replace (moveToNext c r) with c.
      entailer!.
      unfold moveToNext; rewrite INVALID; auto. }
  assert (VALID: isValid c r = true).
  { fold c in H3; fold r in H3. destruct (isValid c r). auto. inv H3. } rewrite VALID.
  clear H3; set (H3:=True).
   deadvars!.
  forward_loop
    (EX i:Z, PROP(up_at_last c = up_at_last (sublist i (Zlength c) c); 0 <= i <= Zlength c)
             LOCAL (temp _cursor pc)
             SEP (relation_rep r; cursor_rep (sublist i (Zlength c) c) r pc))
    break:(EX i:Z, PROP(up_at_last c = sublist i (Zlength c) c; 0 <= i <= Zlength c;
                                   Zlength c - i  <= 1 \/
                                   entryIndex (sublist i (Zlength c) c) <> lastpointer (currNode  (sublist i (Zlength c) c) r))
           LOCAL (temp _cursor pc)
           SEP (relation_rep r; cursor_rep (up_at_last c) r pc)).
  - Exists 0. autorewrite with sublist. entailer!.
  - Intros i0.
    set (subc:=sublist i0 (Zlength c) c).
    unfold cursor_rep.
    Intros anc_end0 idx_end0. unfold r.
    forward.                    (* t'16 = cursor->level *)
    gather_SEP (malloc_token _ _ pc) (data_at _ _ _ pc). replace_SEP 0 (cursor_rep subc r pc).
    { entailer!.
      (*NEW*) apply value_fits_tcursor_props in H8. rewrite ! Zlength_app, ! Zlength_rev, ! Zlength_map in H8; destruct H8 as [IL' AL'].
       unfold cursor_rep. Exists anc_end0 idx_end0. unfold r. cancel. }
    forward_if (PROP ( )
     LOCAL (temp _t'16 (Vint (Int.repr (Zlength subc - 1)));
            temp _cursor pc;
            temp _t'2 (Val.of_bool (andb (Z.gtb (Zlength subc - 1) 0) (Z.eqb (entryIndex subc) (lastpointer (currNode subc r)))))) 
     SEP (cursor_rep subc r pc; relation_rep (root, prel))).
    + assert(PARTIAL: ne_partial_cursor subc r \/ complete_cursor subc r).
      { fold c in H6. fold r in H6. destruct (eq_dec i0 0) as [heq|hneq].
        replace ((n, i) :: c') with subc in H by (unfold subc; now rewrite heq, sublist_same).
        right. assumption. 
        left. unfold complete_cursor in H. destruct H as [CORRECT BALANCED].
        unfold ne_partial_cursor. split.
        - unfold subc. apply complete_sublist_partial. auto.
          lia. assumption.
        - (*New proof*) subst subc. autorewrite with sublist. autorewrite with sublist in H6. rewrite Int.signed_repr in H6. lia.
          rep_lia. }
      forward_call(r,subc,pc).     (* t'3=entryIndex(cursor) *)
      { fold r. cancel. }       
      forward_call(r,subc,pc).                (* t'4 = curnode(cursor) *)
      destruct subc as [|[currnode i'] subc'] eqn:HSUBC.
      { fold c subc in H6. rewrite HSUBC in *. simpl in H6. rewrite Int.signed_repr in H6. lia. rep_lia. }
      simpl. fold c subc in H6. assert (SUBNODE: subnode currnode root).
      {
        destruct PARTIAL as [PARTIAL | PARTIAL].
        unfold ne_partial_cursor in PARTIAL. destruct PARTIAL.
        apply partial_cursor_subnode in H7. simpl in H7. auto.
        destruct PARTIAL as [PARTIAL _].
        apply complete_cursor_subnode in PARTIAL. simpl in PARTIAL. assumption. }
      assert(CURRNODE: currnode = currNode subc r). { rewrite HSUBC. simpl. auto. }
      assert (H98: -1 <= i' < Zlength (node_le currnode)). {
          clear - PARTIAL.
          destruct PARTIAL. destruct H as [? _]. simpl in H.
          destruct (nth_node i' currnode) eqn:?H; try contradiction.
          destruct currnode, entryzero; try destruct isLeaf; simpl in H0; inv H0.
          simpl.
          if_tac in H2. rep_lia.
          apply nth_node_le_some in H2. lia.
          destruct H as [? _].
          destruct currnode; simpl in H|-*.
          red in H; simpl in H.
          destruct (Znth_option i' le) eqn:?H; try contradiction.
          apply Znth_option_some in H0. lia.
       }
      forward_call(currNode subc r). (* 't'5=lastpointer t'4 *)
      { subst; apply prop_right; auto. }
      { rewrite (subnode_rep _ _ SUBNODE), CURRNODE. cancel. }
      { rewrite <- CURRNODE. apply H1. apply SUBNODE. }
      forward.                  (* t'2= (t'3==t'5) *)
      entailer!.
      { f_equal. clear H7.
        remember (lastpointer (@currNode val (@sublist (node val * Z) i0 (@Zlength (node val * Z)c) c) r)) as lastp.
        assert(LENGTH: Zlength subc' >? 0 = true).
        { rewrite HSUBC in *. destruct(subc').
          + rewrite Zlength_cons, Zlength_nil in H6. simpl in H6. rewrite Int.signed_repr in H6; rep_lia.
          + rewrite Zlength_cons. apply Z.gtb_lt. rep_lia. }
        rewrite Zlength_cons, Zsuccminusone, LENGTH. simpl.
        destruct(Z.eqb i' lastp) eqn:HEQ.
        + rewrite <- Heqlastp. (*fold lastp.*) apply Z.eqb_eq in HEQ.  subst i'.
          (*  f_equal.*) rewrite Z.eqb_refl. rewrite Int.eq_true. auto.
        + unfold Int.eq.
          unfold ne_partial_cursor in PARTIAL.
          unfold root_wf in H1.
          apply H1 in SUBNODE. apply node_wf_numKeys in SUBNODE.
          assert(XX: -1 <= lastp <= Zlength (node_le (currNode (sublist i0 (Zlength c) c) r))).
          { unfold lastpointer in lastp. destruct (currNode (sublist i0 (Zlength c) c) r).
            destruct isLeaf. (*unfold lastp.*)subst lastp. simpl.
            rep_lia. simpl.
            subst lastp. simpl.
            rep_lia. }
          clear -PARTIAL SUBNODE (* H13*)XX HEQ H98 Heqlastp. (* fold lastp.*) rewrite <- Heqlastp.
          rewrite HEQ.  if_tac; auto.
           elimtype False. (*clearbody lastp.*) clear - H HEQ H98 XX(*H13*) SUBNODE.
           forget (Zlength (node_le (currNode (sublist i0 (Zlength c) c) r))) as k.
           simpl in *. apply Z.eqb_neq in HEQ.
           destruct (zlt i' 0), (zlt lastp 0).
           * lia.
           * assert (i' = -1) by lia. subst i'.  
               rewrite (Int.unsigned_repr lastp) in H by rep_lia.            
              change (Int.max_unsigned = lastp) in H. rep_lia.
           * assert (lastp = -1) by lia. subst lastp.  
               rewrite (Int.unsigned_repr i') in H by rep_lia.            
              change (i' = Int.max_unsigned) in H. rep_lia.
           * rewrite !Int.unsigned_repr in H by rep_lia. lia.
      }
      unfold relation_rep. fold r. cancel.
      rewrite <- Vptrofs_repr_Vlong_repr by auto. 
      sep_apply (wand_frame_elim (btnode_rep (currNode (sublist i0 (Zlength c) c) r))).
      cancel.
    + forward.                  (* t'2=0 *)
      entailer!. 
      clear - H H0 H5 H6. fold c in H6. fold subc in H6.
      rewrite Int.signed_repr in H6.
      * replace (Zlength subc -1 >? 0) with false. auto. rewrite Z.gtb_ltb. symmetry. apply Zaux.Zlt_bool_false. lia. 
      * split; [ rep_lia |]. 
        assert(0 <= Zlength c - 1 < MaxTreeDepth).
        { eapply partial_complete_length; [ right| ]; eassumption. }
        unfold subc.  autorewrite with sublist. rep_lia.
    + forward_if.
      * unfold cursor_rep. unfold r. Intros anc_end1 idx_end1.
        assert_PROP (value_fits tcursor (prel,
               (Vint (Int.repr (Zlength subc - 1)),
               (rev (map (fun x : node val * Z => Vint (Int.repr (snd x))) subc) ++ idx_end1,
                rev (map getval (map fst subc)) ++ anc_end1)))) as VF by entailer!.
        apply value_fits_tcursor_props in VF. rewrite ! Zlength_app, ! Zlength_rev, ! Zlength_map in VF; destruct VF as [IL' AL'].

        forward.                (* t'15=cursor->level *)
        forward.                (* cursor->level = t'15-1 *)
        assert(i0 + 1 <= Zlength c).
        { apply andb_true_iff in H6. destruct H6. 
          unfold subc in H6. rewrite Zlength_sublist in H6; trivial. 2: rep_lia.
          apply Zgt_is_gt_bool in H6. subst c. rep_lia. }
        Exists (i0+1). entailer!.
        { clear - subc H4 H5 H6 H7. fold subc in H4. rewrite H4; clear H4. fold c in H6. fold subc in H6.
          apply andb_true_iff in H6. destruct H6 as [X1 X2].
          destruct subc as [|[subn subi] subc'] eqn:HSUBC.
          - simpl in X1. apply Z.gtb_lt in X1. lia.
          - unfold subc in HSUBC.
            apply sublist_tl in HSUBC.
            + rewrite HSUBC.
              rewrite Zlength_cons, Zsuccminusone in X1. rewrite <- HSUBC.
              destruct subc'.
              * rewrite Zlength_nil in X1. apply Z.gtb_lt in X1; lia.
              * simpl in X2 |- *. rewrite X2. auto.
            + exact (btnode val None nil true true true nullval, 0).
            + lia. }
        Exists ((getval (currNode subc r))::anc_end1).
        Exists ((Vint(Int.repr(entryIndex subc)))::idx_end1).
        cancel.
        unfold subc, r; autorewrite with sublist.
        apply derives_refl'. do 3 f_equal.
        do 2 f_equal; lia.
        f_equal.
       --
        repeat rewrite <- map_rev.
        rewrite sublist_split with (mid:=i0+1) at 1  by rep_lia. rewrite rev_app_distr.
        rewrite sublist_len_1 by rep_lia. simpl. rewrite list_append_map. rewrite <- app_assoc.
        simpl.
        replace(snd (Znth i0 c)) with (entryIndex (sublist i0 (Zlength c) c)).
        reflexivity.
        rewrite sublist_split with (mid:=i0+1) by rep_lia.
        erewrite @sublist_len_1 by rep_lia. reflexivity.
       --
        rewrite <- !map_rev.
        rewrite sublist_split with (mid:=i0+1) by rep_lia. rewrite rev_app_distr.
        rewrite sublist_len_1 by rep_lia. simpl. rewrite !list_append_map.
        rewrite <- app_assoc.
        simpl. reflexivity.
      * forward.                (* break *)
        Exists i0. clear - H4 H5 H6. fold c in H6. fold subc in H4.
        assert(SC: subc = up_at_last subc).
        { fold subc in H6. rewrite andb_false_iff in H6.
          destruct H6 as [H6 | H6].
          - rewrite Z.gtb_ltb in H6. apply Z.ltb_ge in H6.
            destruct subc; simpl; [ trivial |].
            rewrite Zlength_cons, Zsuccminusone  in H6.
            destruct subc; [ destruct p; trivial |].
            rewrite Zlength_cons in H6. specialize (Zlength_nonneg subc); lia. 
          - destruct subc as [|[subn subi] subc'].
            + simpl; trivial.
            + simpl. simpl in H6. rewrite H6. destruct subc'; auto. }

        fold subc in H4|-*. rewrite <- SC in *; clear SC. rewrite H4; clear H4. fold r.
        rewrite Zlength_sublist in H6 by rep_lia.
        entailer!. rewrite andb_false_iff in H6.
        destruct H6 as [H6 | H6]; [left|right].
        -- rewrite Z.gtb_ltb in H6. apply Z.ltb_ge in H6; lia.
        -- apply Z.eqb_neq in H6; auto.
  - unfold cursor_rep. Intros uali. Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'12=cursor->level *)
    forward.                    (* t'13=cursor->level *)
    assert(UPATLAST: up_at_last c = match c' with
            | [] => [(n, i)]
            | _ :: _ => if Z.eqb i (lastpointer n) then up_at_last c' else (n, i) :: c'
                                    end). 
   { simpl. auto. }
    assert(RANGE: 0 <= Zlength (up_at_last c) - 1 < MaxTreeDepth).
    { apply up_at_last_range. fold c in H. eapply partial_complete_length; eauto. }
    set (u := Zlength (up_at_last c)) in *.
    forward.                    (* t'14=cursor->ancidx[t'13] *)
    { subst u. entailer!. rewrite <- UPATLAST.
      rewrite app_Znth1. rewrite Znth_rev.
      rewrite Zlength_map. replace (Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
      destruct (up_at_last c).
      - simpl in RANGE. lia.
      - simpl. auto.
      - rep_lia.
      -  autorewrite with sublist. rep_lia.
      -  autorewrite with sublist. rep_lia.
    }
    rename H5 into H55.
    rename H6 into H56. 
    fold c in H, POSTCONDITION. clearbody c; clear c' UPATLAST .
    assert (H57: uali = Zlength c-u). { clear - H4 H55. subst u. rewrite H4. clear H4. list_solve. }
    subst uali. replace (Zlength c - (Zlength c - u)) with u in H56 by lia.
    assert (H57: 1 <= u <= Zlength c) by lia. clear H55.
    forward.                    (* cursor->ancestors[t'12] = t'14 +1 *)
    { subst u. entailer!.
      rewrite app_Znth1 by (autorewrite with sublist; lia).
      rewrite Znth_rev by (autorewrite with sublist; lia). rewrite Zlength_map.
      replace (Zlength _ - (Zlength _ - 1) - 1) with 0 by lia.
      destruct (up_at_last c) as [|[n' i'] up'] eqn:?Hup; [simpl in RANGE; lia | ].
      apply prop_right. simpl. destruct H.
        assert(SUBNODE: subnode n' root).
        { assert(h : partial_cursor_correct_rel c (root, prel) \/ complete_cursor_correct_rel c (root, prel)) by (right; auto).
          
          apply complete_partial_upatlast in h. rewrite Hup in h.
          destruct h as [h1 | h2]. 
          - apply partial_cursor_subnode in h1. simpl in h1. auto.
          - apply complete_cursor_subnode in h2. simpl in h2. auto. }
        assert(Zlength (node_le n') <= Fanout).
        { apply H1 in SUBNODE. auto. }
        clear -H H10 H2 Hup.
        assert(partial_cursor_correct_rel c (root, prel) \/ complete_cursor_correct_rel c (root, prel)) by (right; auto).
        apply complete_partial_upatlast in H0.
        destruct H0.
        + unfold partial_cursor_correct_rel in H0. rewrite Hup in H0.
          destruct(nth_node i' n'); try contradiction.
          destruct H0 as [_ ?]. destruct n', entryzero; try destruct isLeaf;  simpl in H0; try discriminate.
          if_tac in H0. subst i'. normalize. rep_lia.
          apply nth_node_le_some in H0. simpl in H10. 
          rewrite Int.signed_repr by rep_lia. rep_lia.
        + unfold complete_cursor_correct_rel in H0.
          destruct(getCEntry (up_at_last c)); try contradiction.
          destruct e; try contradiction.
          rewrite Hup in H0. simpl in H0.
          destruct H0 as [_ ?]. 
          apply Znth_option_some in H0. 
          rewrite Int.signed_repr by rep_lia. rep_lia. }
    deadvars!.
    pose(cincr := next_cursor (up_at_last c)).
    gather_SEP (malloc_token _ _ pc) (data_at _ _ _ pc).
    replace_SEP 0 (cursor_rep cincr r pc).
    {  subst u. unfold cursor_rep. entailer!.
       (*NEW*) apply value_fits_tcursor_props in H7. rewrite ! Zlength_app, ! Zlength_rev, ! Zlength_map in H7; destruct H7 as [IL' AL'].
               rewrite Zlength_upd_Znth in IL'.
       Exists anc_end0. Exists idx_end0. cancel.
       unfold r.
       (* rewrite <- UPATLAST. *)
       unfold cincr.
       rewrite length_next_cursor.
       rewrite upd_Znth_app1.
       2:{ split. lia. rewrite Zlength_rev, Zlength_map; lia. }
       rewrite fst_next_cursor. 
       rewrite app_Znth1 by (rewrite Zlength_rev, Zlength_map; lia).
       rewrite Znth_rev, Zlength_map by (rewrite Zlength_map; lia).
       replace(Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0 by lia.
       destruct (up_at_last c) as [|[upn upi] upc] eqn:HUP.
       { simpl in RANGE. lia. }
       simpl. apply derives_refl'. do 4 f_equal.
       rewrite upd_Znth_app2 by (autorewrite with sublist; lia).
       rewrite Zlength_rev by (autorewrite with sublist; lia).
       rewrite Zlength_map by (autorewrite with sublist; lia).
       rewrite Zlength_cons, Zsuccminusone, Z.sub_diag, upd_Znth0. normalize.
    }
    fold r.
    forward_call(r,cincr,pc).       (* t'6=currNode(cursor) *)
    { unfold r. split; auto. subst cincr.
(*
      clear - H H57 H56 VALID H2.
      destruct H56. assert (u=1) by lia. clear H0 H57; subst u.
      pose proof (upatlast_correct _ _ H).
      destruct (up_at_last c) as [|[n i] [|]]; try discriminate.
      simpl.
*)
     apply movetonext_correct; auto.  }
    assert(SUBNODE: subnode (currNode cincr r) root).
    { apply movetonext_correct in H; try easy. 
      destruct H. inv H. apply partial_cursor_subnode in H5. simpl in H5. auto.
      inv H. apply complete_cursor_subnode in H5. simpl in H5. assumption. }
    assert(SUBREP: subnode (currNode cincr r) root) by auto.
    pose(currnode:= currNode cincr r). fold currnode.
    destruct currnode eqn:HCURR.
    simpl.
    apply subnode_rep in SUBREP. rewrite SUBREP. Intros. fold currnode.
    sep_apply (unfold_btnode_rep currnode). rewrite HCURR.
    Intros ent_end.
    forward.                    (* t'11=t'6->isLeaf *)
    { intro rho; apply prop_right. destruct isLeaf; simpl; auto. }
    sep_apply (fold_btnode_rep entryzero).
    sep_apply modus_ponens_wand.
    forward_if.                 (* if t'11 *)
    + forward.                  (* return *)
      entailer!. fold r.
      assert(cincr = moveToNext c r).
      { unfold cincr. unfold moveToNext. fold r in H4.
        rewrite VALID. unfold cincr in HCURR.
        destruct(up_at_last c).
        { simpl in RANGE. lia. }
        simpl in cincr. destruct p.
        simpl in HCURR. destruct isLeaf.
        rewrite HCURR. simpl. auto.
        apply typed_true_of_bool in H5. inv H5. }
      rewrite H11. unfold relation_rep, r. 
     rewrite <- Vptrofs_repr_Vlong_repr by auto.
     cancel.
    + forward_call(r,cincr,pc).     (* t'7=currnode(cursor) *)
      { unfold relation_rep. unfold r.  cancel. }
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. }
      forward_call(r,cincr,pc). (* t'8 = entryIndex(cursor) *)
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. }
      apply movetonext_correct in H; auto.
      assert(CINCRDEF: cincr = next_cursor(up_at_last c)) by auto.
      destruct (up_at_last c) as [|[upn upi] upc] eqn:HUP.
      { simpl in RANGE. lia. } rewrite <- HUP in CINCRDEF.
      simpl in cincr. unfold cincr. simpl.
      set (incri := Z.succ upi).
      simpl. Intros.
      unfold cincr in SUBREP, SUBNODE. simpl in SUBREP, SUBNODE.
      rewrite SUBREP.
      sep_apply (unfold_btnode_rep upn).
      destruct upn eqn:HUPN. Intros ent_end0. simpl.
      assert(INCRI:  0 <= incri < Zlength (node_le upn)).
      { split.
        - clear - H99 HUP.
         forget (btnode val entryzero0 le0 isLeaf0 First0 Last0 x0) as n1.
         clear - HUP H99. subst incri.
         revert n1 upi upc HUP; induction c; intros. inv HUP.
         unfold up_at_last in HUP; fold @up_at_last in HUP.
         destruct a. inv H99. specialize (IHc H2).
         destruct c. inv HUP. lia.
         destruct (Z.eqb z (lastpointer n)). apply IHc in HUP. auto.
         inv HUP. lia.
        -
        simpl in H.
        destruct H.
        + rewrite <- HUPN in H. clear -H. destruct H. hnf in H. fold incri in H.
          destruct(nth_node incri upn) eqn:HNTH; try contradiction.
          destruct upn. destruct entryzero,isLeaf; simpl in  HNTH; try discriminate.
          simpl in *. 
          if_tac in HNTH.  rep_lia.
          destruct H. simpl in *. 
          apply nth_node_le_some in HNTH. rep_lia.
        + rewrite <- HUPN in H. clear -H. fold incri in H. inv H. unfold complete_cursor_correct_rel in H0.
          destruct(getCEntry((upn, incri) :: upc)); try contradiction.
          destruct e; try contradiction. simpl in H0. destruct H0.
          destruct upn; simpl in H0.
          apply Znth_option_some in H0; auto.
          simpl. lia.
      }
      assert(WF: subnode upn root).
      { rewrite <- HUPN in SUBNODE. auto. }
      apply H1 in WF. red in WF.
      assert(NTH: 0 <= incri < Zlength le0).
      { simpl in INCRI. rewrite HUPN in INCRI. simpl in INCRI. apply INCRI. }
      apply Znth_option_in_range in NTH. destruct NTH as [e NTHH].
      unfold cincr in currnode. simpl in currnode. unfold currnode in HCURR.
      inv HCURR.
      assert(INTERN: isLeaf = false).
      { destruct isLeaf. simpl in H5. inv H5. auto. }
      assert(INTEGRITY:  subnode (btnode val entryzero le isLeaf First Last x) root) by auto.
      unfold root_integrity in H2. simpl in H2. apply H2 in INTEGRITY.
      rewrite INTERN in INTEGRITY.
      apply integrity_nth with (e0:=e) (i0:=incri) in INTEGRITY; simpl; auto.
      destruct INTEGRITY as [k [child HE]].
      assert (H98: 0 <= incri < Fanout). {
            simpl in INCRI, WF. rep_lia.
      }
      forward.                  (* t'9=t'7 -> entries + t'8 ->ptr.child *)
      { destruct entryzero. assert(subnode child root).
        eapply sub_trans with (m:=(btnode val (Some n0) le false First Last x)).
        apply nth_subnode with (i0:=incri). simpl.
        rewrite if_false by lia.
        apply nth_entry_child with (k:=k). rewrite HE in NTHH.
        eauto. rewrite INTERN in SUBNODE. auto.
        apply subnode_rep in H3.
        pose(upn:=btnode val (Some n0)  le isLeaf First Last x).
        sep_apply (fold_btnode_rep (Some n0)). fold upn.
        sep_apply modus_ponens_wand. rewrite HE in NTHH.
        rewrite Znth_to_list' with (e:=(keychild val k child)) by auto. rewrite H3.
       entailer!.
       assert (node_integrity  (btnode val None  le isLeaf First Last x)). auto. subst. easy. }
      pose(upn:=btnode val entryzero  le isLeaf First Last x).
      sep_apply (fold_btnode_rep entryzero). fold upn.
      sep_apply modus_ponens_wand.
      unfold cursor_rep. Intros anc_end1. Intros idx_end1. unfold r.
      forward.                  (* t'10=cursor->level *)
      rewrite HE in NTHH.
      rewrite Znth_to_list' with (e:=(keychild val k child)) by auto. simpl.
      subst u.
      forward_call(r,cincr,pc,child). (* movetofirst(t'9,cursor,t'10+1) *)
      { rewrite Zlength_cons. rewrite Zsuccminusone.
        rewrite Zlength_cons, Zsuccminusone in RANGE.
        rewrite Int.signed_repr by rep_lia.
        rewrite Int.signed_repr by rep_lia.
        rep_lia. }
      { entailer!. 
        repeat rewrite Zlength_cons. repeat rewrite Zsuccminusone.
        rewrite Z.add_1_r. auto. }
      { unfold relation_rep. unfold cursor_rep. Exists anc_end1. Exists idx_end1. unfold r.
        cancel. } simpl in H. fold cincr in H.
      { repeat split.
        - destruct H. unfold ne_partial_cursor in H. destruct H as [P L].
          unfold r. auto.
          unfold cincr in H.
          exfalso. apply complete_leaf in H. rewrite INTERN in H. inv H.
        - destruct H; destruct H; auto.
        - auto.
        - unfold cincr. simpl. destruct entryzero, isLeaf; try easy.
           rewrite if_false by lia.
           apply nth_entry_child with (k:=k). eauto. assert (node_integrity (btnode val None le false First Last x)). auto. easy. 
        - auto. }
      Ltac entailer_for_return ::= idtac.
      forward.                  (* return *)
         entailer!. fold r. cancel.
         apply derives_refl'; f_equal.
         unfold moveToNext. fold r in H2.
        rewrite VALID. rewrite <- CINCRDEF.
        simpl. fold incri.
        replace (nth_node_le incri le) with (Some child)
           by (symmetry; apply (nth_entry_child _ _ k); auto).
        destruct entryzero; auto.        
        rewrite if_false by lia. auto.
        assert (node_integrity (btnode val None le false First Last x)). auto.
          easy.
Qed.

Lemma body_RL_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c'].
  inv H. inv H3. pose (c:=(n,i)::c'). fold c.
  forward_call(r,c,pc).         (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc).         (* t'2=currNode(cursor) *)
  unfold c. simpl.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). simpl.
  assert (SUBNODE: subnode n root).
  { unfold complete_cursor in H. destruct H. apply complete_cursor_subnode in H. auto. }
  unfold relation_rep. rewrite subnode_rep with (n:=n) by auto.
  rewrite unfold_btnode_rep at 1. unfold n. Intros ent_end.
  forward.                      (* t'3=t'2->numKeys *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n in H,c|-*.
  sep_apply modus_ponens_wand.
  change (get_numrec r) with (get_numrec (root,prel)).
  sep_apply (fold_relation_rep). fold r in H0,H1,H2|-*. fold c in H|-*.
  forward_if(PROP ( )
     LOCAL (temp _t'3 (Vint (Int.repr (Zlength le))); temp _t'2 pn;
     temp _t'1 (Vint(Int.repr i)); temp _cursor pc)
     SEP (relation_rep r; match (Z.eqb i (Zlength (node_le n))) with true => cursor_rep (moveToNext c r) r pc | false => cursor_rep c r pc end)).
  - forward_call(c,pc,r).       (* moveToNext(cursor) *)
    entailer!.
    destruct H.
    assert (H': 0 <= i < Zlength (node_le n)). {
       clear - H.
       subst c. hnf in H; simpl in H.
       destruct (Znth_option i le) eqn:?H; try contradiction.
       apply Znth_option_some in H0. auto.
    }
    unfold root_wf in H1. apply H1 in SUBNODE. apply node_wf_numKeys in SUBNODE. fold n  in H.
    assert(0 <= Zlength le <= Fanout).
    { simpl in SUBNODE. lia. } simpl in H.
      simpl in H3. apply (f_equal Int.unsigned) in H3. simpl in H'.
        rewrite !Int.unsigned_repr in H3 by rep_lia. subst i; simpl.
        rewrite Z.eqb_refl. auto.
  - forward.                                            (* skip *)
    destruct H. apply complete_correct_rel_index in H.
    unfold root_wf in H1. apply H1 in SUBNODE. apply node_wf_numKeys in SUBNODE.
    assert(0 <= Zlength le <= Fanout) by (clear - SUBNODE; subst n; auto).
    unfold n. simpl node_le.
    destruct (i =? Zlength le) eqn:HII.
    + exfalso. apply Z.eqb_eq in HII. subst. simpl in H2. contradiction.
    + entailer!.
  - pose (newc:=if Z.eqb i (Zlength (node_le n)) then (moveToNext c r) else c).
    forward_call(newc,pc,r).                               (* moveToNext(cursor) *)
    + unfold newc. destruct (Z.eqb i (Zlength (node_le n))); cancel.
    + split; auto. unfold newc.
      destruct (Z.eqb i (Zlength (node_le n))).
      * apply movetonext_complete. auto.
      * auto.
    + Local Ltac entailer_for_return ::= idtac.
        forward.
        entailer!. unfold newc. simpl. fold n. fold c. 
      destruct (Z.eqb i (Zlength le)); fold c; fold r; cancel.
Qed.
