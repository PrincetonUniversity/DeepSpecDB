(** * verif_findindex.v : Correctness proof of findChildIndex and findRecordIndex *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import index.

Lemma FCI_increase: forall X (le:listentry X) key i,
    idx_to_Z i <= idx_to_Z (findChildIndex' le key i).
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. omega.
  - destruct e; simpl.
    * destruct (k_ key <? k_ k). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (k_ key <? k_ k). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma FCI'_next_index {X: Type} (le: listentry X) key i:
  findChildIndex' le key (next_index i) = next_index (findChildIndex' le key i).
Proof.
  revert i.
  induction le as [|[k v x|k n] le]; simpl; try easy;
    destruct (k_ key <? k_ k); easy.
Qed.  

Lemma FRI'_next_index {X: Type} (le: listentry X) key i:
  findRecordIndex' le key (next_index i) = next_index (findRecordIndex' le key i).
Proof.
  revert i.
  induction le as [|[k v x|k n] le]; simpl; try easy;
    destruct (k_ key <=? k_ k); easy.
Qed.

Lemma FCI_inrange: forall X (n:node X) key,
    -1 <= idx_to_Z(findChildIndex n key) < Z.of_nat (numKeys n).
Proof.
  intros X n key.
  destruct n as [ptr0 le isLeaf F L x]; simpl.
  induction le. easy.
  unfold findChildIndex', numKeys_le; fold (@findChildIndex' X) (@numKeys_le X).
  destruct e as [k v x'|k n]; destruct (k_ key <? k_ k); try easy;
  unfold next_index;
  replace (findChildIndex' le key (ip 0)) with (next_index (findChildIndex' le key im)) by now rewrite <- FCI'_next_index.
  destruct (findChildIndex' le key im); unfold findChildIndex', next_index, idx_to_Z in IHle |- *.
  easy. split. omega. apply inj_lt. omega.
  destruct (findChildIndex' le key im); unfold findChildIndex', next_index, idx_to_Z in IHle |- *.
  easy. split. omega. apply inj_lt. omega.
Qed.

Lemma FRI_increase: forall X (le:listentry X) key i,
    idx_to_Z i <= idx_to_Z (findRecordIndex' le key i).
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. omega.
  - destruct e; simpl.
    * destruct (k_ key <=? k_ k). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (k_ key <=? k_ k). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma FRI_inrange: forall X (n:node X) key,
    0 <= idx_to_Z (findRecordIndex n key) <= Z.of_nat(numKeys n).
Proof.
  intros X n key.
   destruct n as [ptr0 le isLeaf F L x]; simpl.
  induction le. easy.
  unfold findRecordIndex', numKeys_le; fold (@findRecordIndex' X) (@numKeys_le X).
  destruct e as [k v x'|k n]; destruct (k_ key <=? k_ k); try easy;
  unfold next_index;
  replace (findRecordIndex' le key (ip 1)) with (next_index (findRecordIndex' le key (ip 0))) by now rewrite <- FRI'_next_index.
  destruct (findRecordIndex' le key (ip 0)); unfold findRecordIndex', next_index, idx_to_Z in IHle |- *.
  easy. split. omega. apply inj_le. omega.
  destruct (findRecordIndex' le key (ip 0)); unfold findRecordIndex', next_index, idx_to_Z in IHle |- *.
  easy. split. omega. apply inj_le. omega.
Qed.

Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  simpl in H. destruct isLeaf; try inv H.
  gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
  { rewrite unfold_btnode_rep with (n:=n). entailer!. Exists ent_end. entailer!. }

  forward_if (PROP ( )
     LOCAL (temp _t'4 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le false First Last pn)))));
     temp _i (Vint (Int.repr 0)); temp _node (getval (btnode val ptr0 le false First Last pn));
     temp _key (key_repr key))  SEP (btnode_rep n)).
  - forward.                    (* skip *)
    entailer!.
  - apply intern_le_cons in H0. destruct H0. destruct H0. rewrite H0 in H. simpl in H.
    pose (num := numKeys_le x0). fold num in H. rewrite Zpos_P_of_succ_nat in H.
    rewrite Int.signed_repr in H. omega.
    split. rep_omega. unfold node_wf in H1. rewrite H0 in H1. simpl in H1. unfold num.
    rep_omega. simpl. auto.
  - destruct le as [|e le'] eqn:HLE.
    { apply intern_le_cons in H0. destruct H0. destruct H. inv H. simpl. auto. }
    destruct e eqn:HE.
    simpl in H0.
    destruct ptr0; try inv H0.  (* keyval isn't possible in an intern node *)
    rewrite unfold_btnode_rep. unfold n. simpl. Intros ent_end0.
    forward.                    (* t'6=node->entries[0]->key *)
    gather_SEP 0 1 2 3 4 5. replace_SEP 0 (btnode_rep n).
    { rewrite unfold_btnode_rep with (n:=n). unfold n.
      entailer!. Exists ent_end0. entailer!.
      unfold le_iter_sepcon at 2 ; fold le_iter_sepcon ; fold btnode_rep.
      apply derives_refl. } deadvars!.      
      
{ forward_loop (EX i:nat, PROP((i <= numKeys n)%nat; findChildIndex' le key im = findChildIndex' (skipn_le le i) key (prev_index_nat i)) LOCAL(temp _i (Vint(Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n))
                   break:(EX i:nat, PROP(i=numKeys n; findChildIndex' le key im = prev_index_nat i) LOCAL(temp _i (Vint(Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n)).

  - Exists O.
    entailer!. omega.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6. replace_SEP 0 (btnode_rep n).
    { rewrite unfold_btnode_rep with (n:=n). unfold n. entailer!. Exists ent_end. entailer!. }
    forward_if.
    + clear ent_end. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
      assert(HRANGE: (i < numKeys_le le)%nat).
      { rewrite Zpos_P_of_succ_nat in H3.
        rewrite Int.signed_repr in H3. rewrite Int.signed_repr in H3.
        rewrite HLE. simpl. omega.
        unfold node_wf in H1. simpl in H1. rep_omega.
        unfold n in H. unfold node_wf in H1. simpl in H, H1. rep_omega. }
      assert(NTHENTRY: exists ei, nth_entry_le i le = Some ei).
      { apply nth_entry_le_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: nth_entry_le i le = Some ei) by auto.
      eapply Znth_to_list with (endle:=ent_end) in ZNTH. 
      
      forward.                  (* t'2=node->entries+i->key *)
      { entailer!. split. omega. unfold node_wf in H1. simpl in H1. simpl in HRANGE.
        rewrite Fanout_eq in H1. omega. }
      { entailer!. simpl in ZNTH. rewrite ZNTH. destruct ei; simpl; auto. }
      rewrite HLE in ZNTH. rewrite ZNTH.
      forward_if.
      * forward.                (* return i-1 *)
        { entailer!.
          unfold n in H. simpl in H. unfold node_wf in H1. simpl in H1.
          rewrite Int.signed_repr. rewrite Int.signed_repr.
          rep_omega. rep_omega. rep_omega. }
        entailer!.
        { simpl. replace (if k_ key <? k_ k then im else findChildIndex' le' key (ip 0)) with
              (findChildIndex' (cons val (keychild val k n0) le') key im) by (simpl; auto).
          rewrite H2.
          f_equal. f_equal.
          pose (le:=cons val (keychild val k n0) le').
          fold le. fold le in NTHENTRY.
          clear -NTHENTRY H4.
          assert(k_ key <? k_ (entry_key ei) = true).
          { assert(-1 < k_ key < Int.modulus) by apply key.(Int.intrange).           
            destruct ei; simpl in H4; simpl;
            apply typed_true_of_bool in H4; apply ltu_repr in H4;
            try apply Zaux.Zlt_bool_true; auto;
              assert(-1 < k_ k0 < Int.modulus) by apply k0.(Int.intrange); rep_omega. }
          apply nth_entry_skipn in NTHENTRY.
          destruct (skipn_le le i); simpl in NTHENTRY; inv NTHENTRY.
          destruct ei; simpl in H; simpl; rewrite H.
          destruct i. simpl. auto. rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. simpl. auto.
          destruct i. simpl. auto. rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. simpl. auto. }
          rewrite unfold_btnode_rep with (n:= btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn).
        Exists ent_end. cancel.
      * forward.                (* i++ *)
        { entailer!.
          unfold n in H. unfold node_wf in H1. simpl in H, H1.
          rewrite Int.signed_repr. rewrite Int.signed_repr by rep_omega. rep_omega. rep_omega. }
        Exists (S i). entailer!. split.
        { rewrite H2.
          pose (le:=cons val (keychild val k n0) le').
          fold le. fold le in NTHENTRY. clear -NTHENTRY H4.
          assert(k_ key <? k_ (entry_key ei) = false).
          { assert(-1 < k_ key < Int.modulus) by apply key.(Int.intrange).           
            destruct ei; simpl in H4; simpl;
              apply typed_false_of_bool in H4; apply ltu_false_inv in H4;
                rewrite key_unsigned_repr in H4;  rewrite key_unsigned_repr in H4;
                  apply Zaux.Zlt_bool_false; omega. }
          apply nth_entry_skipn in NTHENTRY.          
          rewrite skip_S.
          destruct (skipn_le le i); simpl in NTHENTRY; inv NTHENTRY.
          assert(findChildIndex' (cons val ei l) key (prev_index_nat i) = findChildIndex' l key (next_index (prev_index_nat i))).
          { simpl; destruct ei; simpl in H; rewrite H; simpl; auto. } rewrite H0.
          simpl.
          destruct i; simpl; auto. }
        do 2 f_equal. replace 1 with (Z.of_nat 1) by reflexivity. rewrite <- Nat2Z.inj_add.
        rewrite NPeano.Nat.add_1_r. reflexivity.
        rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end.
        cancel.
    + forward.                  (* break *)
      rewrite Zpos_P_of_succ_nat in H3.
      unfold n in H. unfold node_wf in H1. simpl in H, H1.
      rewrite Int.signed_repr in H3 by rep_omega.
      rewrite Int.signed_repr in H3 by rep_omega.
      rewrite <- Nat2Z.inj_succ in H3. apply Nat2Z.inj_ge in H3.
      assert( i = S(numKeys_le le')) by omega.
      Exists i. entailer!.
      rewrite H2. simpl.
      rewrite skipn_full. simpl. auto.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                     (* t'1=node->numKeys *)
    forward.                     (* return t'1-1 *)
    + entailer!. unfold node_wf in H1. simpl in H1.
      rewrite Zpos_P_of_succ_nat.
      rewrite Int.signed_repr by rep_omega.
      rewrite Int.signed_repr by rep_omega.
      rewrite Zsuccminusone. rep_omega.
    + entailer!.
      * do 2 f_equal.
        unfold findChildIndex. rewrite H2. simpl rep_index. simpl numKeys.
        replace 1 with (Z.of_nat 1) by reflexivity.
        rewrite <- Nat2Z.inj_sub. simpl. rewrite Nat.sub_0_r. auto. omega.
      * rewrite unfold_btnode_rep with (n:=btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn).
        Exists ent_end. cancel.  }
Qed.

Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'5=node->numKeys *)
  simpl.
  gather_SEP 0 1 2 3 4. replace_SEP 0 (btnode_rep n).
  { rewrite unfold_btnode_rep with (n:=n). unfold n. entailer!. Exists ent_end.
    entailer!. } clear ent_end.
  forward_if(PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys_le le))));
     temp _i (Vint (Int.repr 0)); temp _node pn;
     temp _key (key_repr key))  SEP (btnode_rep n)).
  { forward. entailer!. }
  { exfalso. unfold node_wf in H0. simpl in H0.
    rewrite Int.signed_repr in H1. omega. rep_omega. }
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  forward_if.
  { forward.                    (* return 0 *)
    entailer!.
    apply (f_equal Int.unsigned) in H1. rewrite Int.unsigned_repr in H1.
    rewrite Int.unsigned_repr in H1 by rep_omega.
    destruct le.
    simpl. auto.
    simpl in H1. inv H1.
    split; try omega. unfold node_wf in H0. simpl in H0.
    rep_omega.
    rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
    Exists ent_end. entailer!. }
  forward.                    (* i=0 *)
  simpl.
  gather_SEP 0 1 2 3 4.
  replace_SEP 0 (btnode_rep n).
  { rewrite unfold_btnode_rep with (n:=n).
    unfold n. entailer!. Exists ent_end. entailer!. }
  clear ent_end. deadvars!.
{ forward_loop (EX i:nat, PROP((i<=numKeys n)%nat; findRecordIndex' le key (ip O) = findRecordIndex' (skipn_le le i) key (ip i)) LOCAL (temp _i (Vint (Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key))  SEP (btnode_rep n))
               break:(EX i:nat, PROP((i=numKeys n)%nat; findRecordIndex' le key (ip O) = ip (i)) LOCAL (temp _i (Vint (Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key))  SEP (btnode_rep n)).
  - Exists O. entailer!.
    split. omega.
    rewrite skipn_0. auto.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'3=node->numKeys *)
    forward_if.
    + entailer!.
      unfold node_wf in H0. simpl in H0.
      rewrite Int.signed_repr by rep_omega.
      rewrite Int.signed_repr by rep_omega.
      rep_omega.
    + assert(HRANGE: (i < numKeys_le le)%nat).
      { rewrite Int.signed_repr in H4. rewrite Int.signed_repr in H4.
        omega. unfold n in H2. simpl in H2.
        unfold node_wf in H0. simpl in H0. rep_omega.
        unfold node_wf in H0. simpl in H0. rep_omega. }
      assert(NTHENTRY: exists ei, nth_entry_le i le = Some ei).
      { apply nth_entry_le_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: nth_entry_le i le = Some ei) by auto.
      eapply Znth_to_list with (endle:=ent_end) in ZNTH.
      forward.                  (* t'2=node->entries[i]->key *)
      { unfold node_wf in H0. simpl in H0. entailer!. }
      { entailer!. rewrite ZNTH. destruct ei; simpl; auto. }
      rewrite ZNTH.
      forward_if.
      * forward.                (* return i *)
        entailer!. unfold findRecordIndex. rewrite H3.
        f_equal. f_equal.
        destruct (skipn_le le i) eqn:HSKIP.
        { simpl. auto. }
        apply nth_entry_skipn in NTHENTRY.
        simpl in  NTHENTRY. rewrite HSKIP in NTHENTRY. inv NTHENTRY.
        assert(k_ key <=? k_ (entry_key ei) = true).
        { assert(-1 < k_ key < Int.modulus) by apply key.(Int.intrange).
          destruct ei; simpl in H5; simpl;
            apply typed_true_of_bool in H5;
            apply binop_lemmas3.negb_true in H5;
            apply ltu_repr_false in H5;
            try apply Zaux.Zle_bool_true; try omega;
              assert(-1 < k_ k < Int.modulus) by apply k.(Int.intrange);
              rep_omega. }
        simpl. destruct ei; simpl in H10; rewrite H10.
        simpl. auto. simpl. auto.
        rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
        Exists ent_end. entailer!.
      * forward.                (* i=i+1 *)
        { entailer!. unfold node_wf in H0. simpl in H0.
          rewrite Int.signed_repr by rep_omega.
          rewrite Int.signed_repr by rep_omega.
          rep_omega. }
        Exists (S i). entailer!.
        split.
        { rewrite H3. clear -NTHENTRY H5.
          assert(k_ key <=? k_ (entry_key ei) = false).
          { assert(-1 < k_ key < Int.modulus) by apply key.(Int.intrange).           
            destruct ei; simpl in H5; simpl;
              apply typed_false_of_bool in H5;
              apply negb_false_iff in H5;

              apply ltu_repr in H5;
              try apply Zaux.Zle_bool_false; try omega;
                assert(-1 < k_ k < Int.modulus) by apply k.(Int.intrange);
                rep_omega. }
          apply nth_entry_skipn in NTHENTRY.          
          rewrite skip_S.
          destruct (skipn_le le i); simpl in NTHENTRY; inv NTHENTRY.
          simpl. destruct ei; simpl; simpl in H; rewrite H; auto. }
        do 2 f_equal. replace 1 with (Z.of_nat 1) by reflexivity. rewrite <- Nat2Z.inj_add. f_equal. omega.
        rewrite unfold_btnode_rep with (n:=n). unfold n.
        Exists ent_end. entailer!.
    + forward.                  (* break *)
      Exists (numKeys_le le).
      entailer!.
      assert(i=numKeys_le le).
      { unfold n in H2. simpl in H2.
        unfold node_wf in H0. simpl in H0.
        rewrite Int.signed_repr in H4 by rep_omega.
        rewrite Int.signed_repr in H4 by rep_omega.
        rep_omega. }
      subst. split.
      * rewrite H3. rewrite skipn_full.
        simpl. auto.
      * auto.
      * rewrite unfold_btnode_rep with (n:=n).
        unfold n. Exists ent_end. entailer!.
  - Intros i. subst.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'1=node->numkeys *)
    forward.                    (* return t'1 *)
    entailer!.
    + f_equal. f_equal. unfold findRecordIndex. rewrite H3. simpl. auto.
    + rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
      Exists ent_end. entailer!. }
Qed.
