(** * verif_isnodeparent.v : Correctness proof of isNodeParent *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_findindex.

Lemma body_isNodeParent: semax_body Vprog Gprog f_isNodeParent isNodeParent_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'5 = node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
{                               (* Leaf Node *)
  assert(LEAF: isLeaf = true).
  { destruct isLeaf; auto. simpl in H1. inv H1. } subst.
  forward.                       (* t'10 = node->numKeys *)
  sep_apply (fold_btnode_rep ptr0). fold n.
  forward_if.
  - forward.                    (* return. *)
    entailer!. destruct le as [|lowest le']. auto.
    simpl in H2. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0. exfalso.
    rewrite Zpos_P_of_succ_nat in H2. apply (f_equal Int.unsigned) in H2.
    autorewrite with norm in H2. omega.
  - assert(NELE: numKeys_le le <> O).
    { destruct le. simpl in H2. contradiction. simpl. omega. }
    destruct le as [|lowest le']. simpl in NELE. contradiction.
    pose (le:= cons val lowest le'). fold le.
    rewrite unfold_btnode_rep. clear ent_end. unfold n. Intros ent_end.
    forward.                    (* lowest=node->entries[0]->key *)
    { simpl le_to_list.
      rewrite app_Znth1. rewrite Znth_0_cons. destruct lowest; entailer!.
      rewrite Zlength_cons. assert(0<=Zlength (le_to_list le')) by apply Zlength_nonneg.
      omega. }
    forward.                    (* t'9=node->numKeys *)
    assert(LASTENTRY: (numKeys_le le' < numKeys_le (cons val lowest le'))%nat) by (simpl; omega).
    apply nth_entry_le_in_range in LASTENTRY.
    destruct LASTENTRY as [highest LASTENTRY].
    assert(NTHLAST: nth_entry_le (numKeys_le le') (cons val lowest le') = Some highest) by auto.
    eapply Znth_to_list with (endle:=ent_end) in LASTENTRY.
    forward.                    (* highest=node->entries[t'9-1] *)
    + rewrite Zpos_P_of_succ_nat. entailer!. rewrite Zsuccminusone.
      unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0. omega.
    + rewrite app_Znth1. rewrite Zpos_P_of_succ_nat.
      rewrite Zsuccminusone. rewrite LASTENTRY.
      destruct highest; entailer!. simpl. rewrite Zlength_cons.
      assert(0 <= Zlength(le_to_list le')) by apply Zlength_nonneg. omega.
    + entailer!. rewrite Zpos_P_of_succ_nat. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0.
      rewrite Int.signed_repr. rewrite Int.signed_repr.
      rewrite Zsuccminusone. 
      rep_omega. rep_omega. rep_omega.
    +
{ rewrite Zpos_P_of_succ_nat. rewrite Zsuccminusone. rewrite LASTENTRY.
  simpl. rewrite Znth_0_cons.
  change Vtrue with (Val.of_bool true).
  sep_apply cons_le_iter_sepcon.
  change (?A :: ?B ++ ?C) with ((A::B)++C).
  change (entry_val_rep lowest :: le_to_list le')
     with (le_to_list (cons val lowest le')).
  sep_apply (fold_btnode_rep ptr0). fold n.
  deadvars!.
  forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
            temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (key_repr key);
            temp _t'1 (Val.of_bool (orb (k_ key >=? k_ (entry_key lowest)) (First)))) (* new temp *)
     SEP (btnode_rep n)).
  - forward.                    (* t'1 = 1 *)
    entailer!.
    destruct lowest.
    + simpl. simpl in H3. unfold Int.ltu in H3.
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity.
         apply typed_true_of_bool in H3. fold k_ in H3.
      destruct(k_ key >=? k_ k) eqn:COMP.
      * simpl. auto.
      * simpl.
        rewrite Z.geb_leb in COMP. apply Z.leb_gt in COMP.
        rewrite zlt_true in H3. inv H3. auto.
    + simpl. simpl in H3. unfold Int.ltu in H3.
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity.
         apply typed_true_of_bool in H3. fold k_ in H3.
      destruct(k_ key >=? k_ k) eqn:COMP.
      * simpl. auto.
      * simpl.
        rewrite Z.geb_leb in COMP. apply Z.leb_gt in COMP.
        rewrite zlt_true in H3. inv H3. auto.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'8=node->firstleaf *)
    {  entailer!. destruct First; simpl; auto. }
    forward.                    (* t'1=(t'8==1) *)
    entailer!.
    assert(k_ key >=? k_ (entry_key lowest) = false).
    { destruct lowest; simpl in H3; simpl; unfold Int.ltu in H3;
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity;
         fold k_ in H3;
         apply typed_false_of_bool in H3;
         rewrite Z.geb_leb; apply Z.leb_gt;
         if_tac in H3; try discriminate H3; omega. }
    rewrite H11. simpl.
    destruct First; simpl; auto.
    rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end0. entailer!. 
  - forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
     temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (key_repr key);
     temp _t'1 (Val.of_bool ((k_ key >=? k_ (entry_key lowest)) || First));
     temp _t'2 (Val.of_bool (andb ( orb (k_ key >=? k_ (entry_key lowest)) (First))
                                  ( orb (k_ key <=? k_ (entry_key highest)) (Last))))) (* new temp *)
     SEP (btnode_rep n)).
+ forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
     temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (key_repr key);
     temp _t'1 (Val.of_bool ((k_ key >=? k_ (entry_key lowest)) || First));
     temp _t'2 (Val.of_bool ((k_ key <=? k_ (entry_key highest))|| Last))) (* new temp *)
     SEP (btnode_rep n)).
  * forward.                    (* t'2=1 *)
    entailer!.
    { destruct highest; simpl; simpl in H4;
         unfold Int.ltu in H4;
         rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
         apply typed_true_of_bool in H4;
         if_tac in H4; try discriminate H4; clear H4;
         rewrite Zle_imp_le_bool by (unfold k_; omega); auto. }
  * rewrite unfold_btnode_rep with (n:=n). unfold n. Intros ent_end0. 
    forward.                    (* t'6=node->Last *)
    { entailer!. destruct Last; simpl; auto. }
    forward.                    (* t'2=(t'7==1) *)
    forward.                    (* t'2=t'2 *)
    entailer!.
    {  
       destruct highest; simpl; simpl in H4;
       apply typed_false_of_bool in H4;
        unfold Int.ltu in H4;
         rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
         if_tac in H4; try discriminate H4; clear H4;
         rewrite Zaux.Zle_bool_false by (unfold k_; omega);
        destruct Last; reflexivity. }
    rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end0. entailer!.
  * entailer!. rewrite H3. simpl. auto.
+ forward.                      (* t'2=0 *)
  entailer!.
  rewrite H3. simpl. auto.
+ forward_if.
  * forward.                    (* return 1 *)
    entailer!. simpl. rewrite NTHLAST. rewrite H3. simpl. auto.
  * forward.                    (* return 0 *)
    entailer!.
    simpl. rewrite NTHLAST. rewrite H3. simpl. auto. }
} {                             (* Intern Node *)
  assert(INTERN: isLeaf = false).
  { destruct isLeaf; auto. simpl in H1. inv H1. } subst.
  sep_apply (fold_btnode_rep ptr0); fold n.
  forward_call(n,key).
  { split3. unfold n. simpl. auto. auto. auto. }
  forward_if(PROP() LOCAL(temp _t'4 (Val.of_bool (negb (isNodeParent n key))); temp _idx (Vint(Int.repr((rep_index (findChildIndex n key))))); temp _node pn; temp _key (key_repr key)) SEP (btnode_rep n)).
  - forward.                    (* t'4=1 *)
    entailer!.
    destruct (findChildIndex n key) eqn:FCI.
    simpl in FCI. simpl. rewrite FCI. auto.
    simpl in FCI. simpl. rewrite FCI in H2. simpl in H2.
    apply (f_equal Int.unsigned) in H2.
    assert(Z.of_nat n0 < Z.of_nat Fanout).
    { assert(-1 <= idx_to_Z (findChildIndex n key) < Z.of_nat (numKeys n)) by apply FCI_inrange.
      simpl in H4. rewrite FCI in H4. simpl in H4.
      unfold node_wf in H0. simpl in H0. omega. }
    rewrite Fanout_eq in H4. simpl in H4. autorewrite with norm in H2.
    rewrite H2 in H4. compute in H4. inv H4.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'6=node->numKeys *)
    forward.                    (* t'4= (idx==t'6-1) *)
    { entailer!. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0.
      rewrite Int.signed_repr. rewrite Int.signed_repr.
      rep_omega. rep_omega. rep_omega. }
    sep_apply (fold_btnode_rep ptr0); fold n.
    entailer!.
    destruct (findChildIndex' le key im) eqn:FCI'.
    { simpl in H2. contradiction. }
    simpl. rewrite FCI'.
    rewrite negb_involutive.
    destruct (S n0 =? numKeys_le le)%nat eqn:HNUM.
    + destruct (numKeys_le le).
      apply beq_nat_true in HNUM. omega.
      apply beq_nat_true in HNUM. inv HNUM.
      replace (Z.of_nat (S n1) -1) with (Z.of_nat n1).
      rewrite Int.eq_true. rewrite Nat.eqb_refl. simpl. auto.
      rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. auto.
    + apply beq_nat_false in HNUM.
      destruct(Int.eq (Int.repr (Z.of_nat n0)) (Int.repr (Z.of_nat (numKeys_le le) - 1))) eqn:HEQ.
      { unfold node_wf in H0. rewrite Fanout_eq in H0. simpl in H0.
        apply eq_sym in HEQ. apply binop_lemmas2.int_eq_true in HEQ. exfalso.
        apply (f_equal Int.unsigned) in HEQ.
        rewrite Int.unsigned_repr in HEQ. rewrite Int.unsigned_repr in HEQ.
        assert(Z.of_nat (S n0) = Z.of_nat (numKeys_le le)) by omega.
        apply Nat2Z.inj in H5. rewrite H5 in HNUM. contradiction.
        split. destruct le. simpl in FCI'. inv FCI'. simpl numKeys_le.
        rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. omega.
        rep_omega.
        split. omega.
        assert(-1 <= idx_to_Z (findChildIndex n key) < Z.of_nat (numKeys n)) by apply FCI_inrange.
        simpl in H5. rewrite FCI' in H5. simpl in H5. rep_omega. }      
      destruct (numKeys_le le).
      simpl. auto. destruct (n0 =? n1)%nat eqn:HEQ2.
      apply beq_nat_true in HEQ2. subst. contradiction. simpl. auto.      
  - forward_if.
    + forward.                  (* return 0 *)
      entailer!. simpl.
      rewrite H2. simpl. auto.
    + forward.                  (* return 1 *)
      simpl. rewrite H2. entailer!. }
Qed.
