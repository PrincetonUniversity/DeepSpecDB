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
    pose proof (numKeys_le_nonneg le').
    apply (f_equal Int.unsigned) in H2.
    autorewrite with norm in H2. omega.
  - assert(NELE:=  numKeys_le_nonneg le).
    destruct le as [|lowest le']. simpl in NELE. contradiction.
    pose (le:= cons val lowest le'). fold le.
    rewrite unfold_btnode_rep. clear ent_end. unfold n. Intros ent_end.
    forward.                    (* lowest=node->entries[0]->key *)
    { simpl le_to_list.
      rewrite app_Znth1. rewrite Znth_0_cons. destruct lowest; entailer!.
      rewrite Zlength_cons. assert(0<=Zlength (le_to_list le')) by apply Zlength_nonneg.
      omega. }
    forward.                    (* t'9=node->numKeys *)
    assert(LASTENTRY: 0 <= numKeys_le le' < numKeys_le (cons val lowest le')) 
        by (simpl; pose proof (numKeys_le_nonneg le'); omega).
    apply nth_entry_le_in_range in LASTENTRY.
    destruct LASTENTRY as [highest LASTENTRY].
    assert(NTHLAST: nth_entry_le (numKeys_le le') (cons val lowest le') = Some highest) by auto.
    eapply Znth_to_list with (endle:=ent_end) in LASTENTRY.
    forward.                    (* highest=node->entries[t'9-1] *)
    + entailer!. rewrite Zsuccminusone.
      apply node_wf_numKeys in H0. simpl in H0. pose proof (numKeys_le_nonneg le'); rep_omega.
    + rewrite app_Znth1.
      rewrite Zsuccminusone. rewrite LASTENTRY.
      destruct highest; entailer!. simpl. rewrite Zlength_cons.
      assert(0 <= Zlength(le_to_list le')) by apply Zlength_nonneg. omega.
    + entailer!. apply node_wf_numKeys in H0. simpl in H0.
      rewrite !Int.signed_repr by rep_omega. rep_omega.
    +
{ rewrite Zsuccminusone. rewrite LASTENTRY.
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
    entailer!. unfold isNodeParent.  if_tac; auto.
    simpl nth_entry_le at 1. cbv beta iota. simpl numKeys_le.
    rewrite Z.pred_succ.
    rewrite NTHLAST. rewrite H3. simpl. auto.
  * forward.                    (* return 0 *)
    entailer!. unfold isNodeParent. 
    rewrite zle_false by (simpl;  pose proof (numKeys_le_nonneg le'); omega).
    simpl nth_entry_le at 1. cbv beta iota. simpl numKeys_le.
    rewrite Z.pred_succ.
    rewrite NTHLAST. rewrite H3. simpl. auto. }
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
    assert(0 <= z < Fanout). 
    { apply FCI_inrange' in FCI. fold n in H0. apply node_wf_numKeys in H0. omega. }
    simpl in FCI. rewrite FCI in H2. simpl in H2. 
    apply (f_equal Int.unsigned) in H2. autorewrite with norm in H2. compute in H2. rep_omega.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'6=node->numKeys *)
    forward.                    (* t'4= (idx==t'6-1) *)
    { entailer!. apply node_wf_numKeys in H0. simpl in H0.
      rewrite !Int.signed_repr by rep_omega. rep_omega. }
    sep_apply (fold_btnode_rep ptr0); fold n.
    entailer!.
    destruct (findChildIndex' le key im) eqn:FCI'.
    { simpl in H2. contradiction. }
    simpl. rewrite FCI'.
    rewrite negb_involutive.
    destruct (Z.succ z =? numKeys_le le) eqn:HNUM.
    + 
      apply Z.eqb_eq in HNUM. f_equal. symmetry. rewrite <- HNUM.
      rewrite Zsuccminusone. 
      rewrite Int.eq_true. auto.
    + apply Z.eqb_neq in HNUM. f_equal. symmetry. apply Int.eq_false.
        contradict HNUM. 
        apply (f_equal Int.unsigned) in HNUM.
        change (findChildIndex n key = ip z) in FCI'.
        apply FCI_inrange' in FCI'. apply node_wf_numKeys in H0. fold n in H0.
        generalize H0; intro. unfold n in H5. simpl in H5.
        simpl in H3.
        rewrite !Int.unsigned_repr in HNUM by rep_omega.
        destruct (zeq (numKeys_le le) 0). rewrite e in *.
        change (z = Int.max_unsigned) in HNUM. rep_omega.
        rewrite !Int.unsigned_repr in HNUM by rep_omega. subst z. omega.
  - forward_if.
    + forward.                  (* return 0 *)
      entailer!. simpl.
      rewrite H2. simpl. auto.
    + forward.                  (* return 1 *)
      simpl. rewrite H2. entailer!. }
Qed.
