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

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; !!( key_in_range x (((pt.2.2.2).2).1).2 = true ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.1) ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.2) /\
                         is_pointer_or_null ((((pt.2.2.2).2).1).1).2
                       /\ (if Val.eq (enums pt.1) (enums NN) then
                            pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                          else ((((pt.2.2.2).2).1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp; 
        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b;
        in_tree g pt.2.2.2.1 pt.2.1 ((((pt.2.2.2).2).1).1).2;
       node_lock_inv_pred g pt.2.1 pt.2.2.2.1 (pt.2.2.2).2



  )| (CSS g g_root M).

Check enums _.
(* t_struct_node represents for the generic-struct rather specific-data-structure *)
(* Spec of inrange function *)
Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, p: val, min: Z, max : Z, sh: share, gv: globals
  PRE [ tptr t_struct_node, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
          PARAMS (p; Vint (Int.repr x)) GLOBALS (gv)
          SEP (
              field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p)
  POST [ tint ]
  EX (succ: bool),
         PROP (match succ with
               | true => (and (Z.lt min x) (Z.lt x max))
               | false => (or (Z.le x min) (Z.le max x))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (
             field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p).

Lemma node_rep_saturate_local r p g g_current:
  node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof. unfold node_rep; entailer !. Qed.
Global Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer t g g_current p: node_rep p g g_current t |-- valid_pointer p.
Proof.
  unfold node_rep.
  Intros.
  iIntros "(((((H & ?) & ?) & ?) & ?) & ?)".
  iPoseProof (field_at_valid_ptr0 with "H") as "H"; try auto; simpl; try lia.
  iVST. entailer !.
Qed.
Global Hint Resolve node_rep_valid_pointer : valid_pointer.


(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r : node_info, g: gname, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP ((* data_at sh (t_struct_tree_t) (p, n) b *)
            node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_node) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_node) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_node) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p).

(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inRange inRange_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP ()
              LOCAL (temp _t'1 (if andb (min <? x) (x <? max)
                                then Val.of_bool true
                                else Val.of_bool false);
                     temp _t'2 (vint min); gvars gv; temp _p p; temp _x (vint x))
     SEP (field_at sh t_struct_node (DOT _min) (vint min) p;
     field_at sh t_struct_node (DOT _max) (vint max) p)).
  - repeat forward. entailer !.
     destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      apply Z.le_ge in H8.
      destruct (zlt x max); [try easy | auto].
  - forward.
    destruct (Z.ltb_spec min x); try rep_lia.
    entailer !.
  - forward_if; forward.
    + assert (((min <? x) && (x <? max))%bool = true) as Hx.
      { destruct((min <? x) && (x <? max))%bool; easy. }
      Exists true. entailer !.
    + assert (((min <? x) && (x <? max))%bool = false) as Hy.
      { destruct ((min <? x) && (x <? max))%bool; easy. }
      Exists false. entailer !.
Qed.


(* traverse invariants *)
Definition traverse_inv (b: val) (n pnN': val) (sh: share)
                        (x : Z) (v: val) (g_root: gname) (lock: val) gv
                        (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (pnN p: val) (gN_in: gname) (lockN_in: val),
            PROP ()
            LOCAL (temp _p pnN'; temp _flag (vint 2); temp _pn__2 b; temp _x (vint x);
                   (* temp _value v; *) gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 in_tree g gN_in pnN lockN_in; in_tree g g_root pnN' lock;
                 !!(is_pointer_or_null lockN_in) && seplog.emp; AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred g p g_in r *
  (!!(key_in_range x r.1.2 = true /\ r.2 = Some None /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  (* node_lock_inv_pred_1 g p g_in r x * *) (* modify it later*)
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; findnext_spec; 
                             inRange_spec; traverse_spec ]).
(*
Axiom node_rep_R_saturate_local: forall t p g_children g,
  node_rep_R p t g_children g |-- !! is_pointer_or_null p.
Global Hint Resolve node_rep_R_saturate_local: saturate_local.
*)

Axiom node_rep_R_valid_pointer: forall t tp g_children g,
  node_rep_R tp t g_children g |-- valid_pointer tp.

Global Hint Resolve node_rep_R_valid_pointer : valid_pointer.

(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
  forward.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  (* New pt: bool * (val * (share * (gname * node_info))) *)
  forward_loop (traverse_inv b n n Ews x v g_root lock gv inv_names g AS)
    break: (*consider to remove gsh *)
    (EX (flag: enum) (q : val) (gsh: share) (g_in: gname) (r: node_info),
     PROP() LOCAL(temp _flag (enums flag))
     SEP((match flag with
            | F => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NF => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NN => ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 = nullval) && seplog.emp)) end) *
                       Q (flag, (q, (gsh, (g_in, r)))) * mem_mgr gv)).
  - unfold traverse_inv.
    Exists n p g_root lock. sep_apply in_tree_duplicate. entailer !. 
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn p1 g_in lock_in.
    gather_SEP AS (in_tree g g_in pn lock_in).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in) *
                          (EX lsh, !!(readable_share lsh) &&
                                     field_at lsh t_struct_node (DOT _lock) lock_in pn)).
    { go_lower. apply lock_alloc. }
    Intros lsh.
    forward.
    forward.
    sep_apply in_tree_duplicate.
    (* acquire(pn->n->lock); *)
    forward_call acquire_inv_atomic (lock_in,
        AS  * (EX R, node_lock_inv_pred g pn g_in R)  ).
    {
      iIntros "[[[[[[HITlkin HITlkin1] HAS] H4] H5] HITlkin2] H7]".
      iCombine "HITlkin HAS" as "HITlkin".
      iCombine "HITlkin HITlkin1 H4 H5 HITlkin2 H7" as "HITAS".
      iVST.
      apply sepcon_derives; [| cancel_frame].
      unfold atomic_shift. iIntros "AU". iAuIntro; unfold atomic_acc; simpl.
      iDestruct "AU" as "[#HITlkin AU]".
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      iPoseProof (in_tree_inv g g_in g_root with "[$HITlkin $Hm]") as "InvLock".
      iDestruct "InvLock" as "(InvLock & _)".
      iDestruct "InvLock" as (r) "[H1 H2]".
      iExists _. iFrame.
      iSplit; iFrame.
      iIntros "H1".
      iSpecialize ("H2" with "H1").
      iFrame "HITlkin".
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2"); auto.
      iIntros (m') "((H1 & H1') & _)".
      iSpecialize ("H2" with "H1").
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2").
      iMod ("HClose").
      iFrame "HClose". by iExists _.
    }
    Intros r.
    forward.
    forward.
    unfold node_lock_inv_pred, node_rep.
    Intros.
    forward.
    (* inrange function *)
    forward_call(x, pn, (number2Z r.1.2.1), (number2Z r.1.2.2), Ews, gv).
    Intros succ1.
    assert_PROP(is_pointer_or_null r.1.1.1). entailer !.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if.
      (* prove r.1.1.2 = lock_in *)
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
           !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct H12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NN, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NN, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      (*proving it satisfies with the post condition of traverse *)
      Intros y.
      forward.
      Exists NN pn Ews g_in r.
      unfold traverse_inv_1.
      unfold node_lock_inv_pred, node_rep.
      entailer !.
      by iIntros "_".
      forward.
      assert_PROP(field_compatible t_struct_pn (DOT _n) b). entailer !.
      (* findNext *)
      forward_call(x, pn, (field_address t_struct_pn [StructField _n] b),
                   pn, r, g, Ews, gv).
      {
        unfold_data_at (data_at Ews t_struct_pn _ b).
        cancel.
      }
      {
        Intros succ.
        (* assert_PROP(r.1.1.1 <> nullval) by entailer !. *)
        destruct succ.1.1; last first.
        Intros. 
        * (* NN => succ.1.2 = succ.2  *)
          (* not found and find the next point *)
          forward.
          forward_if.
          easy. (* contradiction *)
          forward_if.
          easy. (* contradiction *)
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          forward.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower.
            apply push_lock_back; auto.  }
          (* make in_tree of next node : in_tree g succ.2 pnext lknext *)
          Intros.
          gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
          viewshift_SEP 0 (EX g_in1 lock1, AS * (node_lock_inv_pred g pn g_in r ) *
                                           (in_tree g g_in1 succ.2 lock1)).
          {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iMod "AU" as (m) "[Hm HClose]".
            Check ghost_update_step.
            iPoseProof (ghost_update_step g g_in g_root pn succ.1.2 lock_in m r
                         with "[$H $Hm $HNode $H2 $H3 $H4 $H5 $H6]") as (g_in1 lock1) "((Inv & H1) & H2)".
            { rewrite <- Hlk. iFrame "H". done. }
            iExists g_in1, lock1.
            iSpecialize ("HClose" with "H1").
            rewrite H11.
            by iFrame "Inv H2".
          }
          (*Now we have in_tree g succ.2 pnext lknext *)
          Intros gnext lknext.
          Search is_pointer_or_null.
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((HAS & H1) & H2) & H3) & H4) & H5) & H6) & H7)".
            iCombine "HAS H1 H3 H2 H4 H5 H6 H7" as "Hnode_inv_pred".
            iVST.
            rewrite <- H11.
            rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            unfold atomic_shift;
              iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
            iMod "AU" as (m) "[Hm HClose]".
            iModIntro.
            iExists tt.
            iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
            { rewrite Hlk. iFrame "H1 H2". }
            iDestruct "HI1" as "(HI1' & HI1)".
            rewrite Hlk.
            iFrame "HI1' HI1".
            iSplit.
            {
              iIntros "(Hnode_Iinv & InvLock)".
              iSpecialize ("HI2" with "InvLock").
              iDestruct "HClose" as "[HClose _]".
              iFrame "Hnode_Iinv".
              iSpecialize ("HClose" with "HI2").
              iFrame.
            }
            iIntros (_) "(H & _)".
            iSpecialize ("HI2" with "H").
            iDestruct "HClose" as "[HClose _]". 
            by iSpecialize ("HClose" with "HI2").
         }
         (* proving |--  traverse_inv *)
         unfold traverse_inv.
         Exists succ.1.2 pn gnext lknext.
         entailer !. admit.
         unfold_data_at (data_at Ews t_struct_pn _ b).
         cancel.
       * (* NF case *)
         forward.
         forward_if.
         forward.
         easy.
         forward_if.
         gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
         assert_PROP (r.1.1.2 = lock_in) as Hlk.
         { sep_apply in_tree_equiv; entailer !. }
         Intros.
         rewrite Hlk.
         (* push back lock into invariant *)
         gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
         viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
         {
           go_lower.
           iIntros "((AU & #H) & H1)".
           iMod "AU" as (m) "[Hm HClose]".
           iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
           iDestruct "InvLock" as "(_ & InvLock)".
           iDestruct "InvLock" as (R) "[H1' H2']".
           unfold ltree.
           iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
           iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NF, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NF, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      Exists  (NF, (succ.1.2 , (Ews, (g_in, r)))).
      simpl.
      unfold node_lock_inv_pred, node_rep.
      simpl.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      by iIntros "_".
      (* contradiction *)
      easy.
    * forward.
      forward_if.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (F, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (F, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      Exists  (F, (succ.1.2 , (Ews, (g_in, r)))).
      simpl.
      unfold node_lock_inv_pred, node_rep.
      simpl.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      by iIntros "_".
      (* contradiction *)
      easy.
    }
    easy.
  + forward_if.
    easy.
    forward.
    forward.
    gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
    assert_PROP (r.1.1.2 = lock_in) as Hlk.
    { sep_apply in_tree_equiv; entailer !. }
    rewrite Hlk.
    Intros.
      (* push back lock into invariant *)
    gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
    { go_lower; apply push_lock_back; auto. }
    Intros.
    gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
    viewshift_SEP 0 (AS * (node_lock_inv_pred g pn g_in r )).
    {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iFrame.
            rewrite <- Hlk. iFrame "H". done.
    }
    forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
    {
        lock_props.
        iIntros "(((((HAS & H1) & H2) & H3) & H4) & H5)".
        iCombine "HAS H1 H2 H3 H4 H5" as "Hnode_inv_pred".
        iVST.
        rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iExists tt.
        iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
        { rewrite Hlk. iFrame "H1 H2". }
          iDestruct "HI1" as "(HI1' & HI1)".
          rewrite Hlk.
          iFrame "HI1' HI1".
          iSplit.
          {
            iIntros "(Hnode_Iinv & InvLock)".
            iSpecialize ("HI2" with "InvLock").
            iDestruct "HClose" as "[HClose _]".
            iFrame "Hnode_Iinv".
            iSpecialize ("HClose" with "HI2").
              iFrame.
          }
          iIntros (_) "(H & _)".
          iSpecialize ("HI2" with "H").
          iDestruct "HClose" as "[HClose _]". 
          by iSpecialize ("HClose" with "HI2").
     }
     (* proving |--  traverse_inv *)
       forward.
       unfold traverse_inv.
       Exists n pn g_root lock.
       sep_apply (in_tree_duplicate g g_root n).
       entailer !.
   
       
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       + simpl.
         autorewrite with norm.
         forward.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl. entailer !. 
       + forward.
         Exists (false, (pn, (gsh, (g_in, r)))).
         simpl.
         unfold node_lock_inv_pred_1, node_rep_1 at 1, tree_rep_R_1 at 1.
         Intros g1 g2 v1 p1 p2 l1 l2.
         rewrite H7.
         entailer !.
         exists v1, g1, g2; auto.
         unfold node_lock_inv_pred, node_rep, tree_rep_R.
         rewrite -> if_false; auto.
         simpl.
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
