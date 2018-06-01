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
    * destruct (key.(k_) <? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (key.(k_) <? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma FCI_inrange: forall X (n:node X) key,
    -1 <= idx_to_Z(findChildIndex n key) < Z.of_nat (numKeys n).
Proof.
Admitted.

Lemma FRI_increase: forall X (le:listentry X) key i,
    idx_to_Z i <= idx_to_Z (findRecordIndex' le key i).
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. omega.
  - destruct e; simpl.
    * destruct (key.(k_) <=? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (key.(k_) <=? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma FRI_inrange: forall X (n:node X) key,
    0 <= idx_to_Z (findRecordIndex n key) <= Z.of_nat(numKeys n).
Proof.
Admitted.

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
      entailer!. Exists ent_end0. entailer!. } deadvars!.      
      
{ forward_loop (EX i:nat, PROP((i <= numKeys n)%nat; findChildIndex' le key im = findChildIndex' (skipn_le le i) key (prev_index_nat i)) LOCAL(temp _i (Vint(Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n))
                   break:(EX i:nat, PROP() LOCAL(temp _i (Vint(Int.repr (Z.of_nat i))); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n)).

  - Exists O.
    entailer!. omega.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6. replace_SEP 0 (btnode_rep n).
    { rewrite unfold_btnode_rep with (n:=n). unfold n. entailer!. Exists ent_end. entailer!. }
    forward_if.
    + forward.                  (* skip *)
      clear ent_end. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
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
        { entailer!. admit. }
        entailer!.
        { replace (if k_ key <? k_ k then im else findChildIndex' le' key (ip 0)) with
              (findChildIndex' (cons val (keychild val k n0) le') key im) by (simpl; auto).
          rewrite H2.
          f_equal. f_equal. admit. }
        rewrite unfold_btnode_rep with (n:= btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn).
        Exists ent_end. cancel.
      * forward.                (* skip *)
        forward.                (* i++ *)
        { entailer!. admit. }
        Exists (S i). entailer!. split.
        { rewrite H2. admit. }
        rewrite Zpos_P_of_succ_nat. rewrite <- Z.add_1_r. auto.
        rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end.
        cancel.
    + forward.                  (* break *)
      admit.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                     (* t'1=node->numKeys *)
    forward.                     (* return t'1-1 *)
    + entailer!. admit.
    + entailer!.
      * admit.
      * rewrite unfold_btnode_rep with (n:=btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn).
        Exists ent_end. cancel.
Admitted.    

Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  forward_if (PROP ( ) LOCAL (temp _i (Vint (Int.repr 0)); temp _node pn; temp _key (key_repr key)) SEP (btnode_rep n)).
Admitted.