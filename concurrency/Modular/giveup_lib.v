Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.give_up_template.
Require Import bst.puretree.
Require Import bst.dataStruct.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_pn := Tstruct _pn noattr.

Context {N: NodeRep}.

About NodeRep.

Definition node_rep  pn g g_current (r : node_info) :=
    !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2)
       /\ is_pointer_or_null r.1.1.1 /\ is_pointer_or_null r.1.1.2 ) &&
      field_at Ews (t_struct_node) [StructField _t] r.1.1.1 pn *
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
      malloc_token Ews t_struct_node pn * in_tree g g_current pn r.1.1.2 *
      node_rep_R r.1.1.1 r.1.2 r.2 g.

Definition node_lock_inv_pred g p gp node := my_half gp Tsh node * node_rep p g gp node.

Lemma node_conflict_local pn g g_in a b:
  node_rep pn g g_in a * node_rep pn g g_in b |-- FF.
Proof.
  unfold node_rep.
  iIntros "(((((((_ & H) & _) & _) & _) & _) & _) & ((((((_ & H') & _) & _) & _) & _) & _))".
  iPoseProof (field_at_conflict Ews t_struct_node (DOT _t) pn  with "[$H $H']") as "HF";
      simpl; eauto. lia.
Qed.

Lemma node_lock_inv_pred_exclusive : forall p g g_current node,
  exclusive_mpred (node_lock_inv_pred g p g_current node).
Proof.
  intros.
  unfold exclusive_mpred, node_lock_inv_pred.
  iIntros "((_ & H) & (_ & H'))".
   iPoseProof (node_conflict_local p g g_current node node with "[$H $H']") as "?"; done.
Qed.
Global Hint Resolve node_lock_inv_pred_exclusive : core.

Definition ghost_ref (g : own.gname) r1 :=
  ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) r1 g.

Lemma ghost_snapshot_intree g (s : gmap gname (val * val)) (pn : val) (lock: val) (g_in: gname):
    ghost_ref g s * (!! (s !! g_in = Some(pn, lock)) && seplog.emp)
                      |-- (in_tree g g_in pn lock * ghost_ref g s).
Proof.
  unfold ghost_ref, ghost_master1, in_tree.
  iIntros "(H & (%Hx & _))".
  rewrite snap_master_join; auto.
  iFrame "H".
  iPureIntro.
  by eapply map_singleton_subseteq_l in Hx.
Qed.

Lemma node_exist_in_tree g (s : gmap gname (val * val)) (pn : val) (lock: val) (g_in:gname):
    in_tree g g_in pn lock * ghost_ref g s |-- !! ( s !! g_in = Some(pn, lock)).
Proof.
 unfold ghost_ref, in_tree.
 rewrite -> snap_master_join1.
 iIntros "(% & H)".
 iPureIntro.
 by apply map_singleton_subseteq_l.
Qed.

Definition ltree p (lock : val) R:=
  EX lsh, !!(field_compatible t_struct_node nil p /\ readable_share lsh) &&
  (field_at lsh t_struct_node [StructField _lock] lock p * inv_for_lock lock R).

(* Record tuple of (g, g_in, pn, lock, info)
In the future, we might replace info with only range,
Note that in each node we have a pointer that points to the node info
For e.g, with bst that has {int k, void *v, node_t * left, * right }
We have two cases (1) node info is NULL, then the pointer that points to nullval
(2) is (k, v, left, right)
Updated: no need to have g in the record. 
 *)

(* rename g, g_in, ... *)
Record mpredList := {
    g_inL : gname; pnL : val; lockL: val;
    NodeL: (@G (prod_PCM (discrete_PCM (val * val * range))
                  (exclusive_PCM (option (key * val * list val)))))
}.

Definition extract_lst_pn (m: mpredList) : list val :=
  match m.(NodeL).2 with
  | Some (Some (_, _, lst)) => lst
  | _ => []
  end.

Definition pn_unique (pn : val) (lst : list mpredList) : Prop :=
  fold_right (fun r acc => ( pn <> pnL r) /\ acc) true lst.

Definition ghost_tree_rep (I : list mpredList) (g: gname): mpred :=
  iter_sepcon (fun (p: mpredList) => 
                 !!((pn_unique p.(pnL) I)  /\ incl (extract_lst_pn p) (map pnL I)  )
                 && public_half p.(g_inL) p.(NodeL) *
                 ltree p.(pnL) p.(lockL) (node_lock_inv_pred g p.(pnL) p.(g_inL) p.(NodeL))) I.

(* Global ghost *)
Definition find_ghost_set (I : list mpredList): gmap gname (val * val) :=
  let add_to_map (gmap_acc : gmap gname (val * val)) (mp : mpredList) :=
    let cur_gname := g_inL mp in
    match gmap_acc !! cur_gname with
    | Some _ => gmap_acc (* Already added to the map *)
    | None => <[ cur_gname := (pnL mp, lockL mp) ]> gmap_acc
    end
  in
  List.fold_left add_to_map I ∅.

(* return the first element of g_in of the list *)
Definition extract_g_and_g_in (lst : list mpredList) : option (gname) :=
  match lst with
  | [] => None  (* Empty list *)
  | hd :: _ => Some (hd.(g_inL))
  end.

Lemma test: forall (p : mpredList), True.
Proof.
  intros.
  Check p.(NodeL).1.1.1. (* pointer *)
  Check p.(NodeL).1.1.2. (* lock *)
  Check p.(NodeL).1.2.   (* range *)
  Check (p.(NodeL).2).
Abort.

Definition extract_key_value (m: mpredList) : option (key * val) :=
  match m.(NodeL).2 with
  | Some (Some (key, value, _)) => Some (key, value)
  | _ => None
  end.

Definition tree_to_gmap (I : list mpredList): gmap key val :=
  let add_to_map (gmap_acc : gmap key val) (mp : mpredList) :=
    match extract_key_value mp with
    | Some (cur_key, cur_value) =>
      match gmap_acc !! cur_key with
      | Some _ => gmap_acc (* Already added to the map *)
      | None => <[ cur_key := cur_value ]> gmap_acc
      end
    | None => gmap_acc (* No (key, value) pair, just return the current map *)
    end
  in
  List.fold_left add_to_map I ∅.

(* CSS *)
(* old name is tree_rep*)
(* we need to have g_root that represents for the root node of BST, or the head of linked list *)
(* therefore, (extract_g_and_g_in I = Some (g, g_root)) ensures that the first element of the list,
in which (g, g_in) should be (g, g_root) with the keep-track purpose. *)
Definition CSS (g g_root : gname) (m: gmap key val): mpred :=
  EX I, !!(extract_g_and_g_in I = Some (g_root)) && !! (tree_to_gmap I = m) &&
          ghost_tree_rep I g * ghost_ref g (find_ghost_set I).

Lemma find_ghost (I : list mpredList) (pn lock_in : val) (g g_in: gname):
  find_ghost_set I !! g_in = Some (pn, lock_in) ->
  exists nodeI , In ({| g_inL := g_in; pnL := pn; lockL := lock_in;
                        NodeL := nodeI |}) I.
Proof.
  intros.
  unfold find_ghost_set in H.
  set (S := empty) in H.
  assert ((∃ (nodeI: G), In {| g_inL := g_in; pnL := pn;
                                     lockL := lock_in; NodeL := nodeI |} I) \/
            S !! g_in = Some(pn, lock_in)).
  {
    clearbody S.
    generalize dependent S.
    induction I as [| mp I']; intros S; simpl in *.
    - by right.
    - destruct (S !! g_inL mp) eqn: Heq; intros.
      + specialize ((IHI' _) H).
        destruct IHI' as [(NodeI & H1) | H2].
        left; auto.
        exists NodeI. by right. by right.
      + specialize ((IHI' _ ) H).
        destruct IHI' as [(NodeI & H1) | H2].
        left. exists NodeI. by right. 
        destruct (g_inL mp =? g_in)%nat eqn: Hg.
        * rewrite Nat.eqb_eq in Hg.
          subst g_in.
          pose proof Heq as HNone.
          apply insert_union_singleton_r with (x:= (pnL mp, lockL mp)) in Heq.
          rewrite Heq lookup_union_r in H2; auto. 
          rewrite lookup_singleton in H2.
          inversion H2; subst.
          left. exists (NodeL mp).
          left. by destruct mp.
        * rewrite Nat.eqb_neq in Hg.
          pose proof Heq as HNone.
          apply insert_union_singleton_r with (x:= (pnL mp, lockL mp)) in Heq.
          rewrite Heq lookup_union_l in H2; auto.
          by apply lookup_singleton_None.
  }
  destruct H0 as [(NodeI & H1) | H2].
  - eexists; eauto.
  - by replace S with (∅ : gmap gname (val * val)) in H2.
Qed.

#[global] Instance Inhabitant_mpredList :
  Inhabitant mpredList := {
    default := {| g_inL := 0%nat; pnL := Vnullptr; lockL := Vnullptr;
                  NodeL := ((Vnullptr, Vnullptr, (Neg_Infinity, Pos_Infinity)), None) |}}.

Lemma find_ghost_1 (I : list mpredList) (pn lock_in : val) (g_in: gname) nodeI :
  In ({| g_inL := g_in; pnL := pn; lockL := lock_in; NodeL := nodeI |}) I ->
  pn_unique pn I ->
  find_ghost_set I !! g_in = Some (pn, lock_in).
Proof.
  intros.
  unfold pn_unique in H0.
  unfold find_ghost_set.
  set (S := empty).
  generalize dependent S.
  induction I; intros S; simpl.
  - inversion H.
  - simpl in H0.
    inversion H; destruct H0.
    + by rewrite H1 in H0. 
    + specialize ((IHI H1) H2).
      apply IHI.
Qed.

Lemma ghost_update_step_1 I pn pn' g g_in g_in' (lock_in lock_in': val) node nodeI:
  !!(In ({| g_inL := g_in'; pnL := pn'; lockL := lock_in'; NodeL := nodeI |}) I) &&
    in_tree g g_in pn lock_in * node_lock_inv_pred g pn g_in node *
    (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)) |--
    node_lock_inv_pred g pn g_in node *
    (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)) * in_tree g g_in' pn' lock_in'.
Proof.
  iIntros "(((%H1 & H1) & H2) & (H3 & H4))".
  iPoseProof (node_exist_in_tree with "[$H1 $H4]") as "%".
  unfold ghost_tree_rep at 1.
  pose proof H1 as H1'.
  apply (find_ghost _ _ _ g _) in H.
  destruct H as (node' & H).
  eapply (In_Znth_iff I) in H1'.
  destruct H1' as [i [H' H1']].
  erewrite -> (iter_sepcon_Znth  _ _ i); eauto.
  erewrite H1'.
  simpl.
  iDestruct "H3" as "(((%H31 & K31) & H32) & H33)".
  unfold ltree.
  iDestruct "H32" as (lsh) "(%K1 & (K2 & K3))".
  (* need to prove (find_ghost_set I) !! g_in' = Some(pn', lock')*)
  assert((find_ghost_set I) !! g_in' = Some(pn', lock_in')).
  { eapply(find_ghost_1 I pn' lock_in' g_in' nodeI); auto.
    by destruct H31.
  }
  iPoseProof (ghost_snapshot_intree with "[$H4]") as "(K41 & K42)". done.
  unfold node_lock_inv_pred.
  iFrame "H2 K41 K42".
  unfold ghost_tree_rep.
  erewrite (iter_sepcon_Znth (λ p : mpredList,
                  !! (pn_unique (pnL p) I ∧ incl (extract_lst_pn p) (map pnL I))  &&
                    public_half (g_inL p) (NodeL p) *
                    ltree (pnL p) (lockL p) (node_lock_inv_pred g (pnL p) (g_inL p) (NodeL p))) I i); auto.
  iFrame.
  iSplitL "K31".
  rewrite H1'.
  by iFrame.
  iExists _.
  rewrite H1'.
  by iFrame.
Qed.

Definition extract_node_pn (node: node_info) : list val :=
  match node.2 with
  | Some (Some (_, _, lst)) => lst
  | _ => []
  end.

Lemma In_list_node I (pn : val) mp (node: node_info):
  NodeL mp = node -> incl (extract_lst_pn mp) (map pnL I) ->
  pn ∈ extract_node_pn node ->
  exists (g: gname) (lk : val) (node : G), In {| g_inL := g; pnL := pn; lockL := lk; NodeL := node |} I.
Proof.
  intros H HIncl HIng.
  unfold extract_node_pn in HIng.
  unfold extract_lst_pn in HIncl.
  rewrite H in HIncl.
  destruct (node.2) eqn: Heq; last first.
  by apply elem_of_nil in HIng.
  - rewrite Heq in HIng, HIncl.
    destruct o. destruct g. destruct p.
    assert (In pn (map pnL I)).
    {
      apply elem_of_list_In in HIng.
      apply elem_of_list_In.
      assert(incl [pn] (map pnL I)).
      {
        unfold incl in HIncl.
        specialize ((HIncl pn) HIng).
        apply (incl_cons_iff pn [] (map pnL I)).
        split; auto. by apply incl_nil.
      }
      apply incl_cons_iff in H0.
      apply elem_of_list_In. auto.
    }
    apply in_map_iff in H0.
    destruct H0 as (lmp & K1 & K2); subst.
    exists (g_inL lmp), (lockL lmp), (NodeL lmp).
    destruct lmp. simpl. auto.
    (* contradiction *)
    by apply elem_of_nil in HIng.
Qed.

(* Consider a is In in Iris proof *)
Lemma ghost_update_step g g_in g_root (pn pnext: val) (lk : val) (M: gmap key val) (a :node_info):
  !!(pnext ∈ extract_node_pn a) && in_tree g g_in pn lk *
    node_lock_inv_pred g pn g_in a * CSS g g_root M |--
  EX g1 lk1, node_lock_inv_pred g pn g_in a * CSS g g_root M * in_tree g g1 pnext lk1.
Proof.
  unfold CSS.
  iIntros "(((%H & H1) & H2) & H3)".
  iDestruct "H3" as (I) "(((%H3 & %H4) & H3) & H4)".
  iPoseProof (node_exist_in_tree with "[$H1 $H4]") as "%".
  apply (find_ghost _ _ _ g _) in H0.
  destruct H0 as (node & H0).
  pose proof H0 as H0'.
  eapply (In_Znth_iff I) in H0.
  destruct H0 as [i [H0 H01]].
  unfold ghost_tree_rep at 1.
  erewrite -> (iter_sepcon_Znth  _ _ i); eauto.
  erewrite H01.
  simpl. 
  iDestruct "H3" as "((((%H21 & %H22) & H23) & H24) & H25)".
  iDestruct "H2" as "(K2 & K3)".
  iPoseProof (public_agree with "[$H23 $K2]") as "%H2".
  subst a.
  simpl.
  pose proof (In_list_node I pnext {|
                     g_inL := g_in; pnL := pnext; lockL := lk; NodeL := node
                           |} node).
  assert (node = node); auto. 
  simpl in H1.
  specialize (H1 H2 H22 H).
  destruct H1 as (g_in1 & lk1 & node1 & H1).
  iAssert(ghost_tree_rep I g) with "[H23 H24 H25]" as "H3".
  {
    unfold ghost_tree_rep.
    erewrite (iter_sepcon_Znth (λ p : mpredList,
      !! (pn_unique (pnL p) I ∧ incl (extract_lst_pn p) (map pnL I))
      && public_half (g_inL p) (NodeL p) *
       ltree (pnL p) (lockL p) (node_lock_inv_pred g (pnL p) (g_inL p) (NodeL p))) I i) ; auto.
    iFrame.
    rewrite H01.
    simpl.
    iFrame.
    iPureIntro. done.
  }
  Check ghost_update_step_1.
  iPoseProof(ghost_update_step_1 I pn pnext g g_in g_in1 lk lk1 node node1 with "[H1 K2 K3 H4 H3]") as "H".
  {
    iFrame "H1". iFrame.
    iPureIntro.
    done.
  }
  iDestruct "H" as "((H1 & (H2 & H3)) & H4)".
  iExists g_in1, lk1.
  iFrame "H1 H4".
  iExists I.
  by iFrame "H2 H3".
Qed.

Lemma in_tree_inv1 I pn g g_in (lock_in : val) (lk : val):
  in_tree g g_in pn lock_in * (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)) |--
 (EX a : node_info,
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) *
  (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) -*
   (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)))) &&
     (EX R, ltree pn lock_in R * (ltree pn lock_in R -* (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)))).
Proof.
  iIntros "(H1 & (H2 & H3))".
  iPoseProof (node_exist_in_tree with "[$H1 $H3]") as "%".
  unfold ghost_tree_rep at 1.
  apply (find_ghost _ _ _ g _) in H.
  destruct H as (node & H).
  eapply (In_Znth_iff I) in H.
  destruct H as [i [H H1]].
  erewrite -> (iter_sepcon_Znth  _ _ i); eauto.
  erewrite H1.
  simpl.
  iDestruct "H2" as "((H22 & H23) & H32)".
  unfold ltree at 1.
  iDestruct "H23" as (lsh) "(%H2 & (H23 & H24))".
  iSplit.
  - iExists _.
    iFrame "H24".
    iIntros "H2".
    iFrame.
    unfold ghost_tree_rep.
    erewrite (iter_sepcon_Znth _ I i); auto.
    iFrame.
    erewrite H1.
    unfold ltree. iFrame "H22".
    iExists _.
    iFrame. done.
  - unfold ltree at 2.
    iExists _.
    iSplitL "H23 H24".
    + iExists _. by iFrame.
    + iIntros "H2". iFrame.
      unfold ghost_tree_rep.
      erewrite (iter_sepcon_Znth (λ p : mpredList,
                      !! (pn_unique (pnL p) I ∧ incl (extract_lst_pn p) (map pnL I))
                      && public_half (g_inL p) (NodeL p) *
       ltree (pnL p) (lockL p) (node_lock_inv_pred g (pnL p) (g_inL p) (NodeL p))) I i) ; auto.
      iFrame "H32".
      erewrite H1.
      iFrame "H2 H22".
Qed.

Lemma in_tree_inv g g_in g_root (pn : val) (lock_in : val) (M: gmap key val):
    in_tree g g_in pn lock_in * CSS g g_root M |--
      (EX a, (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)
         -* CSS g g_root M))) &&
      (EX R, (ltree pn lock_in R) * (ltree pn lock_in R -* CSS g g_root M)).
Proof.
  unfold CSS.
  iIntros "[H1 H2]".
  iDestruct "H2" as (I) "((%H3 & H4) & H5)".
  iPoseProof (in_tree_inv1 I pn g g_in with "[H1 H4 H5]") as "H"; auto.
  + iFrame "H4". iFrame "H1 H5".
  + iSplit.
    * iDestruct "H" as "(H & _)".
      iDestruct "H" as (r) "(H1 & H2)".
      iExists r. iFrame.
      iIntros "H".
      iSpecialize ("H2" with "H").
      iDestruct "H2" as "(H1 & H2)".
      iExists I; iFrame; done.
    * iDestruct "H" as "(_ & H)".
      iDestruct "H" as (r) "(H1 & H2)".
      iExists r. iFrame.
      iIntros "H".
      iSpecialize ("H2" with "H").
      iDestruct "H2" as "(H1 & H2)".
      iExists I; iFrame; done.
Qed.

Lemma inv_lock g pn g_in (lock_in : val) a b c:
  node_lock_inv_pred g pn g_in a * inv_for_lock lock_in (node_lock_inv_pred g pn g_in b) |--
  node_lock_inv_pred g pn g_in a * inv_for_lock lock_in (node_lock_inv_pred g pn g_in c).
Proof.
  iIntros "(H1 & H2)".
  unfold inv_for_lock.
  iDestruct "H2" as (b0) "(H2 & H3)".
  destruct b0.
  - iFrame. iExists _. iFrame.
  - iExFalso.
    unfold node_lock_inv_pred.
    iDestruct "H1" as "(_ & Hn1)".
    iDestruct "H3" as "(_ & Hn2)".
    unfold node_rep.
    iPoseProof (node_conflict_local pn g g_in a b  with "[$Hn1 $Hn2]") as "HF"; auto.
Qed.

Lemma in_tree_inv1' I pn g g_in (lock_in lk : val) a:
  in_tree g g_in pn lock_in * node_lock_inv_pred g pn g_in a *
  (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)) |--
  node_lock_inv_pred g pn g_in a *
   (inv_for_lock lock_in (node_lock_inv_pred g pn g_in  a)) *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) -*
         (ghost_tree_rep I g * ghost_ref g (find_ghost_set I))).
Proof.
  iIntros "((H1 & H2) & (H3 & H4))".
  iPoseProof (node_exist_in_tree with "[$H1 $H4]") as "%".
  unfold ghost_tree_rep at 1.
  apply (find_ghost _ _ _ g _) in H.
  destruct H as (node & H).
  eapply (In_Znth_iff I) in H.
  destruct H as [i [H H1]].
  erewrite -> (iter_sepcon_Znth  _ _ i); eauto.
  erewrite H1.
  simpl.
  iDestruct "H3" as "(((%H31 & H32) & H33) & H34)".
  iDestruct "H2" as "(H21 & H22)".
  unfold ltree.
  iDestruct "H33" as (lsh) "(%K31 & (K32 & K33))".
  iPoseProof (public_agree with "[$H21 $H32]") as "%H2".
  iPoseProof (inv_lock with "[H21 H22 K33]") as "(H21 & K33)". iFrame.
  iFrame.
  iIntros "H".
  unfold ghost_tree_rep.
  erewrite (iter_sepcon_Znth (λ p : mpredList,
                 !! (pn_unique (pnL p) I ∧ incl (extract_lst_pn p) (map pnL I))
                 && public_half (g_inL p) (NodeL p) *
       ltree (pnL p) (lockL p) (node_lock_inv_pred g (pnL p) (g_inL p) (NodeL p))) I i); auto.
  iFrame.
  subst.
  erewrite H1. simpl.
  iFrame "H32".
  iSplit. done.
  unfold ltree.
  iExists _. iFrame. done.
Qed.

Lemma in_tree_inv' g g_in g_root (pn : val) (lock_in : val) (M: gmap key val) a:
  in_tree g g_in pn lock_in * node_lock_inv_pred g pn g_in a *
    CSS g g_root M |--
      (node_lock_inv_pred g pn g_in a *
         (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a))) *
           (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) -* (CSS g g_root M)).
Proof.
  unfold CSS.
  iIntros "[[H1 H2] H3]".
  iDestruct "H3" as (I) "(H31 & H32)".
  iDestruct "H31" as "[%H H31]".
  iPoseProof ((in_tree_inv1' I) with "[H1 H2 H31 H32]") as "((H1 & H31) & H32)"; auto.
  iFrame "H1 H2 H31 H32".
  iFrame "H1 H31".
  iIntros "H".
  iSpecialize ("H32" with "H").
  iDestruct "H32" as "(H31 & H32)".
  iExists I. iFrame. done.
Qed.

Lemma lock_join lsh1 lsh2 pn lock_in :
  (!!(readable_share lsh1) && @field_at CompSpecs lsh1 t_struct_node (DOT _lock) lock_in pn) *
  (!!(readable_share lsh2) && @field_at CompSpecs lsh2 t_struct_node (DOT _lock) lock_in pn) |--
  EX (lsh : share), !!(readable_share lsh) &&
    @field_at CompSpecs lsh t_struct_node (DOT _lock) lock_in pn.
Proof.
  intros.
  normalize.
  sep_apply field_at_share_joins.
  normalize.
  destruct H1 as (lsh & H1).
  rewrite (field_at_share_join lsh1 lsh2 lsh); auto.
  Exists lsh.
  entailer !.
  apply (@join_readable1 lsh1 lsh2 lsh); auto.
Qed.

Lemma share_divided lsh pn (lock_in : val):
  !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_node (DOT _lock) lock_in pn |--
  (EX lsh, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_node (DOT _lock) lock_in pn) *
  (EX lsh, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_node (DOT _lock) lock_in pn).
Proof.
  iIntros "(% & H1)".
  assert(sepalg.join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) lsh).
  apply slice.cleave_join.
  iPoseProof(field_at_share_join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) with "[H1]")
    as "(H11 & H12)"; auto; auto.
  pose proof H as H'.
  apply cleave_readable1 in H.
  apply cleave_readable2 in H'.
  iSplitL "H11";
  iExists _; by iFrame.
Qed.

Lemma lock_alloc (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (g g_root g_in: gname) p lk:
  atomic_shift (λ M, CSS g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk |--
  (|={⊤}=> atomic_shift (λ M, CSS g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk *
         (EX lsh: share, !! readable_share lsh && field_at lsh t_struct_node (DOT _lock) lk p)).
Proof.
  iIntros "(AU & #H)".
  iMod "AU" as (m) "[Hm HClose]".
  iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
  iDestruct "InvLock" as "(_ & InvLock)".
  iDestruct "InvLock" as (R) "[H1 H2]".
  unfold ltree.
  iDestruct "H1" as (lsh) "(%H12 & (H12 & H13))".
  destruct H12.
  iPoseProof (share_divided with "[$H12]") as "H1"; auto.
  iDestruct "H1" as "(H1 & H1')".
  iDestruct "H1" as (lsh1) "(% & H1)".
  iDestruct "H1'" as (lsh2) "(% & H1')".
  iAssert (EX lsh: Share.t, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_node (DOT _lock) lk p) with "[H1]" as "H3". iExists _; by iFrame.
  iAssert (EX lsh: Share.t, !!(readable_share lsh) && @field_at CompSpecs lsh t_struct_node (DOT _lock) lk p) with "[H1']" as "H3'". iExists _; by iFrame.
  iFrame. iFrame "H".
  iAssert (EX lsh : share,
          !! (field_compatible t_struct_node [] p ∧ readable_share lsh) &&
          (@field_at CompSpecs lsh t_struct_node (DOT _lock) lk p *
           inv_for_lock lk R))  with "[H3 H13]" as "H1".
      { iDestruct "H3" as (lsh') "(% & H3)". iExists _; iFrame. done. }
      iSpecialize ("H2" with "H1").
      by iSpecialize ("HClose" with "H2").
Qed.

Lemma push_lock_back (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) (g g_root g_in: gname) p lk lsh
  (Hrs: readable_share lsh):
  atomic_shift (λ M, CSS g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk *
  field_at lsh t_struct_node (DOT _lock) lk p |--
  (|={⊤}=> atomic_shift (λ M, CSS g g_root M) ⊤ ∅ b Q * in_tree g g_in p lk ).
Proof.
  iIntros "((AU & #H) & Hf)".
  iMod "AU" as (m) "[Hm HClose]".
  iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
  iDestruct "InvLock" as "(_ & InvLock)".
  iDestruct "InvLock" as (R) "[H1 H2]".
  iDestruct "H1" as (lsh1) "(% & (Hf' & HInv))".
  destruct H as (Hf & Hrs1).
  iAssert(EX lsh0 : share, !! (field_compatible t_struct_node [] p ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lk p * inv_for_lock lk R))
              with "[Hf Hf' HInv ]" as "H1".
  {
    iPoseProof (lock_join with "[$Hf $Hf']") as "H1"; try iSplit; auto.
    iDestruct "H1" as (Lsh) "(% & Hf)".
    iExists _. by iFrame.
  }
  unfold ltree.
  iSpecialize ("H2" with "H1").
  iDestruct "HClose" as "(HClose & _)".
  iSpecialize ("HClose" with "H2").
  iMod "HClose". by iFrame "H".
Qed.