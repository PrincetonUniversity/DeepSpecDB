(** * verif_isnodeparent.v : Correctness proof of isNodeParent *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import btrees.relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec.

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
   autorewrite with sublist in H0,H2.
    apply (f_equal Int.unsigned) in H2.
    autorewrite with norm in H2. rep_lia.
  - assert(NELE:=  Zlength_nonneg le).
    destruct le as [|lowest le']. simpl in NELE. contradiction.
    pose (le:= lowest :: le'). fold le.
    rewrite unfold_btnode_rep. clear ent_end. unfold n. Intros ent_end.
    forward.                    (* lowest=node->entries[0]->key *)
    { simpl map.
      rewrite app_Znth1. rewrite Znth_0_cons. destruct lowest; entailer!.
      rewrite Zlength_cons. assert(0<=Zlength le') by apply Zlength_nonneg.
      list_solve. }
    forward.                    (* t'9=node->numKeys *)
    assert(LASTENTRY: 0 <= Zlength le' < Zlength (lowest :: le')) 
        by list_solve.
    apply Znth_option_in_range in LASTENTRY.
    destruct LASTENTRY as [highest LASTENTRY].
    assert(NTHLAST: Znth_option (Zlength le') (lowest :: le') = Some highest) by auto.
    apply Znth_to_list' with (endle:=ent_end) in LASTENTRY.
    autorewrite with sublist in NELE.
    assert (H99: 0 < Z.succ (Zlength le') <= Fanout).  {
        pose proof (node_wf_numKeys _ H0). simpl in H3.
        autorewrite with sublist in H3. rep_lia.
    }
    simpl node_le. autorewrite with sublist.
    forward.                    (* highest=node->entries[t'9-1] *)
    + apply prop_right; rep_lia.
    + rewrite app_Znth1 by list_solve.
      rewrite Zsuccminusone.
     rewrite app_Znth1 in LASTENTRY by list_solve.
     fold Inhabitant_entry_val_rep.
     rewrite LASTENTRY.
      destruct highest; entailer!.
    +
{ rewrite Zsuccminusone. 
  fold Inhabitant_entry_val_rep.
  rewrite LASTENTRY.
  simpl. rewrite Znth_0_cons.
  change Vtrue with (Val.of_bool true).
  sep_apply cons_le_iter_sepcon.
  change (?A :: ?B ++ ?C) with ((A::B)++C).
  change (entry_val_rep lowest :: _)
     with (map entry_val_rep (lowest :: le')).
  sep_apply (fold_btnode_rep ptr0). simpl. list_solve.
  fold n.
  deadvars!.
  forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
            temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (Vptrofs key);
            temp _t'1 (Val.of_bool (orb (Ptrofs.cmpu Cge key (entry_key lowest)) (First)))) (* new temp *)
     SEP (btnode_rep n)).
  - forward.                    (* t'1 = 1 *)
    entailer!.
    destruct lowest.
    + simpl. simpl in H3. apply typed_true_of_bool in H3.
        unfold Int64.ltu in H3.
        unfold Ptrofs.ltu. 
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity.
         rewrite H3. reflexivity.
    + simpl. simpl in H3. apply typed_true_of_bool in H3.
        unfold Int64.ltu in H3.
        unfold Ptrofs.ltu. 
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity.
         rewrite H3. reflexivity.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'8=node->firstleaf *)
    {  entailer!. destruct First; simpl; auto. }
    forward.                    (* t'1=(t'8==1) *)
    entailer!.
    assert(Ptrofs.cmpu Cge key (entry_key lowest) = false).
    { destruct lowest; simpl in H3; simpl; unfold Int.ltu, Int64.ltu in H3;
         rewrite ?int_unsigned_ptrofs_toint in H3 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H3 by reflexivity;
         apply typed_false_of_bool in H3; auto. }
    rewrite H11. simpl.
    destruct First; simpl; auto.
    rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end0. entailer!. 
  - forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
     temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (Vptrofs key);
     temp _t'1 (Val.of_bool ((Ptrofs.cmpu Cge key (entry_key lowest)) || First));
     temp _t'2 (Val.of_bool (andb ( orb (Ptrofs.cmpu Cge key (entry_key lowest)) (First))
                                  ( orb (Ptrofs.cmpu Cle key (entry_key highest)) (Last))))) (* new temp *)
     SEP (btnode_rep n)).
+ forward_if(PROP ( )
     LOCAL (temp _highest (let (x, _) := entry_val_rep highest in x);
     temp _lowest (let (x, _) := entry_val_rep lowest in x); temp _node pn; temp _key (Vptrofs key);
     temp _t'1 (Val.of_bool ((Ptrofs.cmpu Cge key (entry_key lowest)) || First));
     temp _t'2 (Val.of_bool ((Ptrofs.cmpu Cle key (entry_key highest))|| Last))) (* new temp *)
     SEP (btnode_rep n)).
  * forward.                    (* t'2=1 *)
    entailer!.
    { destruct highest; simpl; simpl in H4;
         unfold Int.ltu, Int64.ltu in H4; unfold Ptrofs.ltu;
         rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
         apply typed_true_of_bool in H4; rewrite H4; auto. }
  * rewrite unfold_btnode_rep with (n:=n). unfold n. Intros ent_end0. 
    forward.                    (* t'6=node->Last *)
    { entailer!. destruct Last; simpl; auto. }
    forward.                    (* t'2=(t'7==1) *)
    forward.                    (* t'2=t'2 *)
    entailer!.
    {  
       destruct highest; simpl; simpl in H4;
       apply typed_false_of_bool in H4;
        unfold Int.ltu, Int64.ltu in H4; unfold Ptrofs.ltu;
         rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
         rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
         rewrite H4;
        destruct Last; reflexivity. }
    rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end0. entailer!.
  * entailer!. simpl. rewrite H3. simpl. auto.
+ forward.                      (* t'2=0 *)
  entailer!. simpl.
  rewrite H3. simpl. auto.
+ forward_if.
  * forward.                    (* return 1 *)
    entailer!. unfold isNodeParent.  if_tac; auto.
    autorewrite with sublist.
    rewrite Z.pred_succ. 
    rewrite NTHLAST. simpl. rewrite H3. simpl. auto.
  * forward.                    (* return 0 *)
    entailer!. unfold isNodeParent. 
    autorewrite with sublist.
    rewrite zle_false by rep_lia.
    rewrite Z.pred_succ.
    rewrite NTHLAST.  simpl.
     rewrite H3. simpl. auto. }
} {                             (* Intern Node *)
  assert(INTERN: isLeaf = false).
  { destruct isLeaf; auto. simpl in H1. inv H1. } subst.
  sep_apply (fold_btnode_rep ptr0); fold n.
  forward_call(n,key).
  { split3. unfold n. simpl. auto. auto. auto. }
  forward_if(PROP()
                   LOCAL(temp _t'4 (Val.of_bool (negb (isNodeParent n key)));
                              temp _idx (Vint(Int.repr((findChildIndex n key)))); 
                              temp _node pn; temp _key (Vptrofs key))
                   SEP (btnode_rep n)).
  - forward.                    (* t'4=1 *)
    entailer!.
    unfold isNodeParent, n. 
    simpl findChildIndex.
    if_tac. reflexivity.
    change (findChildIndex' le key (-1)) with (findChildIndex n key) in *.
    pose proof (FCI_inrange _ n key).
    pose proof (node_wf_numKeys _ H0) . fold n in H6.
    apply (f_equal Int.unsigned) in H2. autorewrite with norm in H2. 
    change (Int.unsigned (Int.repr (-(1)))) with Int.max_unsigned in H2. 
    (*WAS:rep_lia.*)
    (*NOW:*)rewrite Int.unsigned_repr in H2. 2:{ subst n;  simpl in *. rewrite Fanout_eq in *. rep_lia. }
      simpl. rewrite negb_involutive. unfold Val.of_bool.
      remember (Z.succ (findChildIndex' le key (-1)) =? Zlength le).
      destruct b. reflexivity.
      subst n; simpl in *. symmetry in Heqb. apply Z.eqb_neq in Heqb. rep_lia.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'6=node->numKeys *)
    forward.                    (* t'4= (idx==t'6-1) *)
    { entailer!. apply node_wf_numKeys in H0. simpl in H0.
      rewrite !Int.signed_repr by rep_lia. rep_lia. }
    sep_apply (fold_btnode_rep ptr0); fold n.
    entailer!.
    clear H3 H1. f_equal.
    pose proof (FCI_inrange _ n key). simpl in H1.
    assert (findChildIndex' le key (-1) <> -1). contradict H2. f_equal. apply H2.
    clear H2.
    unfold isNodeParent; simpl. rewrite if_false by lia.
    rewrite negb_involutive.
    forget (findChildIndex' le key (-1)) as z.
    destruct (Z.succ z =? Zlength le) eqn:HNUM.
    + 
      apply Z.eqb_eq in HNUM. f_equal. symmetry. rewrite <- HNUM.
      rewrite Zsuccminusone. 
      rewrite Int.eq_true. auto.
    + apply Z.eqb_neq in HNUM. symmetry. apply Int.eq_false.
        contradict HNUM.
        apply (f_equal Int.unsigned) in HNUM.
        pose proof (node_wf_numKeys _ H0). simpl in H2.
        normalize in HNUM. subst. lia.
  - forward_if.
    + forward.                  (* return 0 *)
      entailer!. simpl.
      rewrite H2. simpl. auto.
    + forward.                  (* return 1 *)
      simpl. rewrite H2. entailer!. }
Qed.