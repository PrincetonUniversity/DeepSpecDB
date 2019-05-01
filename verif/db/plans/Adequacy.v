(************************************************************************************)
(**                                                                                 *)
(**                             The SQLEngines Library                              *)
(**                                                                                 *)
(**            LRI, CNRS & Université Paris-Sud, Université Paris-Saclay            *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                  Chantal Keller                                                 *)
(**                  Eunice-Raquel Martins                                          *)
(**                                                                                 *)
(************************************************************************************)

Require Import List NArith.
Require Import ListFacts ListPermut Utils Signatures.
Require Import OrderedSet FiniteSet FiniteBag HighLevelSpec.

Set Implicit Arguments.

Section Filter_is_a_filter_op.
  Require Import Filter.

  Hypothesis A : Type.
  Hypothesis OA : Oeset.Rcd A.
  Hypothesis C : Cursor.Rcd OA.
  Hypothesis theta : A -> bool.
  Hypothesis theta_eq : forall x1 x2, Oeset.compare OA x1 x2 = Eq -> theta x1 = theta x2.

  Lemma mk_filter_is_a_filter_op : 
    let F := (Filter.build _ theta_eq C) in
    is_a_filter_op OA (Cursor.materialize C) (Cursor.materialize F) theta (Filter.mk_filter F).
Proof.
intros F c t.
unfold Filter.mk_filter.
assert (Hc := Cursor.materialize_collection C c).
assert (Hf := Cursor.materialize_collection F c).
simpl in Hf; unfold Filter.collection in Hf.
apply eq_trans with (Oeset.nb_occ OA t (filter theta (Cursor.collection c))).
- apply permut_nb_occ; apply permut_refl_alt; assumption.
- rewrite Oeset.nb_occ_filter; [ | intros; apply theta_eq; assumption].
  case (theta t).
  + rewrite N.mul_1_r.
    apply sym_eq; apply permut_nb_occ; apply permut_refl_alt; assumption.
  + rewrite N.mul_0_r; apply refl_equal.
Qed.

End Filter_is_a_filter_op.

Section NestedLoop_is_a_join_op.
  Require Import NestedLoop.

  Hypotheses o1 o2 o : Type.
  Hypothesis O1 : Oeset.Rcd o1.
  Hypothesis O2 : Oeset.Rcd o2.
  Hypothesis O : Oeset.Rcd o.
  
  Hypothesis build_ : o1 -> o2 -> o.
  Hypothesis build_eq_1  : 
    forall x1 x1' x2, 
      Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
  Hypothesis build_eq_2  : 
    forall x1 x2 x2', 
      Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.
  
  Hypothesis C1 : Cursor.Rcd O1.
  Hypothesis C2 : Cursor.Rcd O2.
  
  Hypothesis A : Type.
  Hypothesis OA : Oset.Rcd A.
  Hypothesis FA : Fset.Rcd OA.
  
  Hypothesis sort1 : Cursor.cursor C1 -> Fset.set FA.
  Hypothesis sort2 : Cursor.cursor C2 -> Fset.set FA.
  Hypothesis sup1 : o1 -> Fset.set FA.
  Hypothesis sup2 : o2 -> Fset.set FA.
  Hypothesis sup : o -> Fset.set FA.
  Hypothesis proj1 : o -> o1.
  Hypothesis proj2 : o -> o2.
  Hypothesis sa1 sa2: Fset.set FA.
  Hypothesis sup_eq : forall t1 t2, Oeset.compare O t1 t2 = Eq -> sup t1 =S= sup t2.
  Hypothesis sup_build : forall t1 t2, sup (build_ t1 t2) =S= (sup1 t1 unionS sup2 t2).
  Hypothesis sup_proj1 : forall t, sup1 (proj1 t) =S= sa1.
  Hypothesis sup_proj2 : forall t, sup2 (proj2 t) =S= sa2.
  Hypothesis build_proj : 
    forall t, sup t =S= (sa1 unionS sa2) -> Oeset.compare O t (build_ (proj1 t) (proj2 t)) = Eq.
  Hypothesis build_eq :
    forall t1 u1 t2 u2, Oeset.compare O1 t1 u1 = Eq -> Oeset.compare O2 t2 u2 = Eq ->
                        Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq.
  Hypothesis build_split_eq_1 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O1 t1 u1 = Eq.
  Hypothesis build_split_eq_2 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sa1 -> sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sa2 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O2 t2 u2 = Eq.
                                                        
  Notation NL := (NestedLoop.build O build_ build_eq_1 build_eq_2 C1 C2).  
  
  Lemma NL_is_a_join_op : 
    is_a_join_op O1 O2 O (Cursor.materialize C1) (Cursor.materialize C2) (Cursor.materialize NL) 
                  FA sup1 sup2 sup proj1 proj2 sa1 sa2
                 (fun c1 c2 => NestedLoop.mk_cursor C1 C2 nil c1 c2).
Proof.
  unfold is_a_join_op.
  intros c1 c2 H1 H2; split.
  - intros t Ht.
    assert (Kt : Oeset.mem_bool 
                   O t (flat_map (fun a : o1 => map (build_ a) (Cursor.collection c2)) 
                                 (Cursor.collection c1)) = true).
    {
      rewrite <- Oeset.nb_occ_diff_0_pos in Ht.
      generalize (Oeset.nb_occ_mem _ _ _ Ht); clear Ht; intro Ht.
      rewrite <- Ht; apply sym_eq.
      apply Oeset.mem_bool_eq_2.
      apply Cursor.materialize_collection.
    }
    rewrite Oeset.mem_bool_true_iff in Kt.
    destruct Kt as [t' [Kt Ht']].
    rewrite in_flat_map in Ht'.
    destruct Ht' as [x1 [Hx1 Ht']].
    rewrite in_map_iff in Ht'.
    destruct Ht' as [x2 [Ht' Hx2]]; subst t'.
    rewrite (Fset.equal_eq_1 _ _ _ _ (sup_eq _ _ Kt)).
    rewrite (Fset.equal_eq_1 _ _ _ _ (sup_build _ _)).
    apply Fset.union_eq.
    + apply H1.
      assert (Kx1 : Oeset.mem_bool O1 x1 (Cursor.collection c1) = true).
      {
        rewrite Oeset.mem_bool_true_iff; exists x1; split; [apply Oeset.compare_eq_refl | assumption].
      }
      rewrite <- Oeset.nb_occ_diff_0_pos.
      apply Oeset.mem_nb_occ.
      rewrite <- Kx1; apply Oeset.mem_bool_eq_2.
      apply Cursor.materialize_collection.
    + apply H2.
      rewrite <- Oeset.nb_occ_diff_0_pos.
      apply Oeset.mem_nb_occ.
      assert (Kx2 : Oeset.mem_bool O2 x2 (Cursor.collection c2) = true).
      {
        rewrite Oeset.mem_bool_true_iff; exists x2; split; [apply Oeset.compare_eq_refl | assumption].
      }
      rewrite <- Kx2; apply Oeset.mem_bool_eq_2.
      apply Cursor.materialize_collection.
  - intros t Ht.
    assert (Kt : Oeset.nb_occ 
                   O t
                   (Cursor.materialize 
                      NL 
                      {| NestedLoop.visited := nil; NestedLoop.outer := c1; NestedLoop.inner := c2 |}) =
                 Oeset.nb_occ O t (flat_map (fun a : o1 => map (build_ a) (Cursor.collection c2)) 
                                 (Cursor.collection c1))).
    {
      apply Oeset.nb_occ_eq_2.
      apply Cursor.materialize_collection.
    }
    rewrite Kt.
    apply trans_eq with
        (Oeset.nb_occ 
           O (build_ (proj1 t) (proj2 t))  
           (flat_map (fun a : o1 => map (build_ a) (Cursor.collection c2)) (Cursor.collection c1))).
    + apply Oeset.nb_occ_eq_1.
      apply build_proj; assumption.
    + apply trans_eq with
          (Oeset.nb_occ O1 (proj1 t) (Cursor.collection c1) *
           Oeset.nb_occ O2 (proj2 t) (Cursor.collection c2)).
      * assert (Sx1 := sup_proj1 t); set (x1 := proj1 t) in *; clearbody x1.
        assert (Sx2 := sup_proj2 t); set (x2 := proj2 t) in *; clearbody x2.
        assert (Hl1 : forall y1, In y1 (Cursor.collection c1) -> sup1 y1 =S= sa1).
        {
          intros y1 Hy1.
          apply H1.
          assert (Ky1 : Oeset.mem_bool O1 y1 (Cursor.collection c1) = true).
          {
            rewrite Oeset.mem_bool_true_iff; exists y1; split; [ | assumption].
            apply Oeset.compare_eq_refl.
          }
          rewrite <- Oeset.nb_occ_diff_0_pos.
          apply Oeset.mem_nb_occ; rewrite <- Ky1; apply Oeset.mem_bool_eq_2.
          apply Cursor.materialize_collection.
        }
        assert (Hl2 : forall y2, In y2 (Cursor.collection c2) -> sup2 y2 =S= sa2).
        {
          intros y2 Hy2.
          apply H2.
          assert (Ky2 : Oeset.mem_bool O2 y2 (Cursor.collection c2) = true).
          {
            rewrite Oeset.mem_bool_true_iff; exists y2; split; [ | assumption].
            apply Oeset.compare_eq_refl.
          }
          rewrite <- Oeset.nb_occ_diff_0_pos.
          apply Oeset.mem_nb_occ; rewrite <- Ky2; apply Oeset.mem_bool_eq_2.
          apply Cursor.materialize_collection.
        }
        set (l1 := (Cursor.collection c1)) in *; clearbody l1.
        set (l2 := (Cursor.collection c2)) in *; clearbody l2.
        clear Kt; revert l2 Hl2; induction l1 as [ | a1 l1]; intros l2 Hl2; simpl; trivial.
        rewrite Oeset.nb_occ_app, IHl1; [ | intros; apply Hl1; right; assumption | assumption].
        {
          case_eq (Oeset.compare O1 x1 a1); intro Hx1.
          - rewrite Nmult_plus_distr_r, N.mul_1_l; apply f_equal2; [ | apply refl_equal].
            induction l2 as [ | a2 l2]; [apply refl_equal | ].
            simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
            apply f_equal2; [ | apply refl_equal].
            case_eq (Oeset.compare O2 x2 a2); intro Hx2.
            + rewrite (build_eq _ _ _ _ Hx1 Hx2); trivial.
            + case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
              assert (Abs : Oeset.compare O2 x2 a2 = Eq).
              {
                apply (build_split_eq_2 _ _ _ _ Hx).
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                  rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl1 _ (or_introl _ (refl_equal _)))).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                  rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                  apply Fset.equal_refl.
              }
              rewrite Abs in Hx2; discriminate Hx2.
            + case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
              assert (Abs : Oeset.compare O2 x2 a2 = Eq).
              {
                apply (build_split_eq_2 _ _ _ _ Hx).
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                  rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl1 _ (or_introl _ (refl_equal _)))).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                  apply Fset.equal_refl.
                - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                  rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                  apply Fset.equal_refl.
              }
              rewrite Abs in Hx2; discriminate Hx2.
          - rewrite Nmult_plus_distr_r; apply f_equal2; [ | apply refl_equal].
            rewrite N.mul_0_l.
            induction l2 as [ | a2 l2]; [apply refl_equal | ].
            simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
            case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
            assert (Abs : Oeset.compare O1 x1 a1 = Eq).
            {
              apply (build_split_eq_1 _ _ _ _ Hx).
              - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl1 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
            }
            rewrite Abs in Hx1; discriminate Hx1.
          - rewrite Nmult_plus_distr_r; apply f_equal2; [ | apply refl_equal].
            rewrite N.mul_0_l.
            induction l2 as [ | a2 l2]; [apply refl_equal | ].
            simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
            case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
            assert (Abs : Oeset.compare O1 x1 a1 = Eq).
            {
              apply (build_split_eq_1 _ _ _ _ Hx).
              - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl1 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
            }
            rewrite Abs in Hx1; discriminate Hx1.
        }  
      * {
          apply f_equal2; apply sym_eq; apply Oeset.nb_occ_eq_2.
          - apply Cursor.materialize_collection.
          - apply Cursor.materialize_collection.
        }
Qed.
  
End NestedLoop_is_a_join_op.

Section BlockNestedLoop_is_a_join_op.
  Require Import BlockNestedLoop.

  Hypotheses o1 o2 o : Type.
  Hypothesis O1 : Oeset.Rcd o1.
  Hypothesis O2 : Oeset.Rcd o2.
  Hypothesis O : Oeset.Rcd o.
  
  Hypothesis build_ : o1 -> o2 -> o.
  Hypothesis build_eq_1  : 
    forall x1 x1' x2, 
      Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
  Hypothesis build_eq_2  : 
    forall x1 x2 x2', 
      Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.
  
  Definition OL1 := mk_oelists O1.
  Definition OL2 := mk_oelists O2.
  Definition OL := mk_oelists O.

  Hypothesis C1 : Cursor.Rcd OL1.
  Hypothesis C2 : Cursor.Rcd OL2.
  
  Hypothesis A : Type.
  Hypothesis OA : Oset.Rcd A.
  Hypothesis FA : Fset.Rcd OA.
  
  Hypothesis sort1 : Cursor.cursor C1 -> Fset.set FA.
  Hypothesis sort2 : Cursor.cursor C2 -> Fset.set FA.
  Hypothesis sup1 : o1 -> Fset.set FA.
  Hypothesis sup2 : o2 -> Fset.set FA.
  Hypothesis sup : o -> Fset.set FA.
  Hypothesis proj1 : o -> o1.
  Hypothesis proj2 : o -> o2.
  Hypothesis sa1 sa2: Fset.set FA.
  Hypothesis sup_eq : forall t1 t2, Oeset.compare O t1 t2 = Eq -> sup t1 =S= sup t2.
  Hypothesis sup_build : forall t1 t2, sup (build_ t1 t2) =S= (sup1 t1 unionS sup2 t2).
  Hypothesis sup_proj1 : forall t, sup1 (proj1 t) =S= sa1.
  Hypothesis sup_proj2 : forall t, sup2 (proj2 t) =S= sa2.
  Hypothesis build_proj : 
    forall t, sup t =S= (sa1 unionS sa2) -> Oeset.compare O t (build_ (proj1 t) (proj2 t)) = Eq.
  Hypothesis build_eq :
    forall t1 u1 t2 u2, Oeset.compare O1 t1 u1 = Eq -> Oeset.compare O2 t2 u2 = Eq ->
                        Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq.
  Hypothesis build_split_eq_1 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O1 t1 u1 = Eq.
  Hypothesis build_split_eq_2 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sa1 -> sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sa2 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O2 t2 u2 = Eq.
                                                        
  Notation BNL := (BlockNestedLoop.build O build_ build_eq_1 build_eq_2 C1 C2).  
                            
  Lemma BNL_is_a_join_op : 
    is_a_join_op O1 O2 O (fun c1 => flat_map (fun x => x) (Cursor.materialize C1 c1)) 
                 (fun c2 => flat_map (fun x => x) (Cursor.materialize C2 c2)) 
                 (fun c => flat_map (fun x => x) (Cursor.materialize BNL c)) 
                 _ sup1 sup2 sup proj1 proj2 sa1 sa2
                 (fun c1 c2 => NestedLoop.mk_cursor C1 C2 nil c1 c2).
Proof.
  unfold is_a_join_op.
  intros c1 c2 H1 H2; split.
  - intros t Ht.
    assert (Kt : Oeset.mem_bool 
                   O t (flat_map 
                          (fun x : list o => x)
                          (@Cursor.collection _ _ BNL (NestedLoop.mk_cursor C1 C2 nil c1 c2))) = true).
    {
      rewrite <- Oeset.nb_occ_diff_0_pos in Ht.
      generalize (Oeset.nb_occ_mem _ _ _ Ht); clear Ht; intro Ht.
      rewrite <- Ht; apply sym_eq.
      apply Oeset.mem_bool_eq_2; apply comparelA_comparelA_eq.
      apply (@Cursor.materialize_collection _ _ BNL (NestedLoop.mk_cursor C1 C2 nil c1 c2)).
    }
    simpl in Kt; unfold NestedLoop.collection in Kt; simpl in Kt.
    assert (Aux := mem_permut_mem_strong 
                     O t (permut_flat_map build_ (Cursor.collection c1) (Cursor.collection c2))).
    unfold cartesian_product in Aux; unfold BlockNestedLoop.OL1, BlockNestedLoop.OL2 in Kt; 
      unfold OL1, OL2 in Aux; simpl in Aux, Kt.
    rewrite <- Aux in Kt; clear Aux.
    rewrite Oeset.mem_bool_true_iff in Kt.
    destruct Kt as [t' [Kt Ht']]; rewrite (Fset.equal_eq_1 _ _ _ _ (sup_eq _ _ Kt)).
    rewrite in_flat_map in Ht'.
    destruct Ht' as [x1 [Hx1 Ht']].
    simpl in Hx1; unfold NestedLoop.collection in Hx1. 
    rewrite in_flat_map in Hx1.
    destruct Hx1 as [l1 [Hl1 Hx1]]; simpl in Hl1.
    rewrite in_map_iff in Ht'; destruct Ht' as [x2 [Ht' Hx2]].
    rewrite in_flat_map in Hx2; destruct Hx2 as [l2 [Hl2 Hx2]]; subst t'.
    rewrite (Fset.equal_eq_1 _ _ _ _ (sup_build _ _)); apply Fset.union_eq.
    + apply H1.
      rewrite <- Oeset.nb_occ_diff_0_pos.
      apply Oeset.mem_nb_occ.
      rewrite (Oeset.mem_bool_eq_2 _ x1 _ (flat_map (fun x => x) (Cursor.collection c1))).
      * rewrite Oeset.mem_bool_true_iff; exists x1; split; [apply Oeset.compare_eq_refl | ].
        rewrite in_flat_map; exists l1; split; trivial.
      * apply comparelA_comparelA_eq.
        assert (Aux := Cursor.materialize_collection C1 c1); simpl in Aux; apply Aux.
    + apply H2.
      rewrite <- Oeset.nb_occ_diff_0_pos.
      apply Oeset.mem_nb_occ.
      rewrite (Oeset.mem_bool_eq_2 _ x2 _ (flat_map (fun x => x) (Cursor.collection c2))).
      * rewrite Oeset.mem_bool_true_iff; exists x2; split; [apply Oeset.compare_eq_refl | ].
        rewrite in_flat_map; exists l2; split; trivial.
      * apply comparelA_comparelA_eq.
        assert (Aux := Cursor.materialize_collection C2 c2); simpl in Aux; apply Aux.
  - intros t Ht.
    assert (Kt :  Oeset.nb_occ 
                    O t
                    (flat_map 
                       (fun x : list o => x)
                       (Cursor.materialize 
                          BNL {| NestedLoop.visited := nil; 
                                 NestedLoop.outer := c1; 
                                 NestedLoop.inner := c2 |})) =
                  Oeset.nb_occ 
                    O t
                    (flat_map 
                       (fun x : list o => x)
                       (@Cursor.collection 
                          _ _ BNL {| NestedLoop.visited := nil; 
                                 NestedLoop.outer := c1; 
                                 NestedLoop.inner := c2 |}))).
    {
      apply Oeset.nb_occ_eq_2.
      apply comparelA_comparelA_eq.
      assert (Aux := @Cursor.materialize_collection _ _ BNL (NestedLoop.mk_cursor C1 C2 nil c1 c2)).
      simpl in Aux; unfold Cursor.collection; simpl; apply Aux.
    }
    rewrite Kt.
    apply trans_eq with
        (Oeset.nb_occ 
           O (build_ (proj1 t) (proj2 t))  
           (flat_map (fun x : list o => x)
       (@Cursor.collection _ _ BNL 
                           {| NestedLoop.visited := nil; NestedLoop.outer := c1; NestedLoop.inner := c2 |}))).
    + apply Oeset.nb_occ_eq_1.
      apply build_proj; assumption.
    + apply trans_eq with
          (Oeset.nb_occ O1 (proj1 t) (flat_map (fun x => x) (Cursor.collection c1)) *
           Oeset.nb_occ O2 (proj2 t) (flat_map (fun x => x) (Cursor.collection c2))).
      * assert (Sx1 := sup_proj1 t); set (x1 := proj1 t) in *; clearbody x1.
        assert (Sx2 := sup_proj2 t); set (x2 := proj2 t) in *; clearbody x2.
        assert (Hl1 : forall y1, In y1 (flat_map (fun x => x) (Cursor.collection c1)) -> sup1 y1 =S= sa1).
        {
          intros y1 Hy1.
          apply H1.
          assert (Ky1 : Oeset.mem_bool O1 y1 (flat_map (fun x => x) (Cursor.collection c1)) = true).
          {
            rewrite Oeset.mem_bool_true_iff; exists y1; split; [ | assumption].
            apply Oeset.compare_eq_refl.
          }
          rewrite <- Oeset.nb_occ_diff_0_pos.
          apply Oeset.mem_nb_occ; rewrite <- Ky1; apply Oeset.mem_bool_eq_2.
          apply comparelA_comparelA_eq.
          assert (Aux := Cursor.materialize_collection C1 c1); unfold OL1 in Aux; simpl in Aux.
          apply Aux.
        }
        assert (Hl2 : forall y2, In y2 (flat_map (fun x => x) (Cursor.collection c2)) -> sup2 y2 =S= sa2).
        {
          intros y2 Hy2.
          apply H2.
          assert (Ky2 : Oeset.mem_bool O2 y2 (flat_map (fun x => x) (Cursor.collection c2)) = true).
          {
            rewrite Oeset.mem_bool_true_iff; exists y2; split; [ | assumption].
            apply Oeset.compare_eq_refl.
          }
          rewrite <- Oeset.nb_occ_diff_0_pos.
          apply Oeset.mem_nb_occ; rewrite <- Ky2; apply Oeset.mem_bool_eq_2.
          apply comparelA_comparelA_eq.
          assert (Aux := Cursor.materialize_collection C2 c2); unfold OL2 in Aux; simpl in Aux.
          apply Aux.
        }
        clear Kt; simpl; unfold NestedLoop.collection in *; simpl.
        unfold BlockNestedLoop.OL1, BlockNestedLoop.OL2, OL1, OL2 in *; simpl.
        set (l1 := (@Cursor.collection (list o1) (@mk_oelists o1 O1) C1 c1)) in *; 
          clearbody l1.
        set (l2 := (@Cursor.collection (list o2) (@mk_oelists o2 O2) C2 c2)) in *;
          clearbody l2.
        revert l2 Hl2; induction l1 as [ | a1 l1]; intros l2 Hl2; simpl; trivial.
        {
          rewrite flat_map_app, 2 Oeset.nb_occ_app, IHl1.
          - rewrite Nmult_plus_distr_r; apply f_equal2; [ | apply refl_equal]. 
            simpl in Hl1.
            assert (Ha1 : forall y1, In y1 a1 -> sup1 y1 =S= sa1).
            {
              intros y1 Hy1; apply Hl1; apply in_or_app; left; assumption.
            }
            clear l1 IHl1 Hl1.
            induction l2 as [ | a2 l2]; simpl; [rewrite N.mul_0_r; apply refl_equal | ].
            rewrite 2 Oeset.nb_occ_app, Nmult_plus_distr_l, IHl2.
            + apply f_equal2; [ | apply refl_equal].
              assert (Ha2 : forall y2, In y2 a2 -> sup2 y2 =S= sa2).
              {
                intros y2 Hy2; apply Hl2; simpl; apply in_or_app; left; assumption.
              }
              clear l2 Hl2 IHl2.
              revert a2 Ha2.
              induction a1 as [ | a1 l1]; intros l2 Hl2; simpl; trivial.
              rewrite Oeset.nb_occ_app, IHl1, Nmult_plus_distr_r.
              * apply f_equal2; [ | apply refl_equal].
                {
                  case_eq (Oeset.compare O1 x1 a1); intro Hx1.
                  - rewrite N.mul_1_l.
                    induction l2 as [ | a2 l2]; [apply refl_equal | ].
                    simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
                    apply f_equal2; [ | apply refl_equal].
                    case_eq (Oeset.compare O2 x2 a2); intro Hx2.
                    + rewrite (build_eq _ _ _ _ Hx1 Hx2); trivial.
                    + case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
                      assert (Abs : Oeset.compare O2 x2 a2 = Eq).
                      {
                        apply (build_split_eq_2 _ _ _ _ Hx).
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                          rewrite <- (Fset.equal_eq_1 _ _ _ _ (Ha1 _ (or_introl _ (refl_equal _)))).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                          rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                          apply Fset.equal_refl.
                      }
                      rewrite Abs in Hx2; discriminate Hx2.
                    + case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
                      assert (Abs : Oeset.compare O2 x2 a2 = Eq).
                      {
                        apply (build_split_eq_2 _ _ _ _ Hx).
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                          rewrite <- (Fset.equal_eq_1 _ _ _ _ (Ha1 _ (or_introl _ (refl_equal _)))).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                          apply Fset.equal_refl.
                        - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                          rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                          apply Fset.equal_refl.
                      }
                      rewrite Abs in Hx2; discriminate Hx2.
                  - rewrite N.mul_0_l.
                    induction l2 as [ | a2 l2]; [apply refl_equal | ].
                    simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
                    case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
                    assert (Abs : Oeset.compare O1 x1 a1 = Eq).
                    {
                      apply (build_split_eq_1 _ _ _ _ Hx).
                      - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                        rewrite <- (Fset.equal_eq_1 _ _ _ _ (Ha1 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
                      - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                        rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
                    }
                    rewrite Abs in Hx1; discriminate Hx1.
                  - rewrite N.mul_0_l.
                    induction l2 as [ | a2 l2]; [apply refl_equal | ].
                    simpl; rewrite IHl2; [ | intros; apply Hl2; right; trivial].
                    case_eq (Oeset.compare O (build_ x1 x2) (build_ a1 a2)); intro Hx; trivial.
                    assert (Abs : Oeset.compare O1 x1 a1 = Eq).
                    {
                      apply (build_split_eq_1 _ _ _ _ Hx).
                      - rewrite (Fset.equal_eq_1 _ _ _ _ Sx1).
                        rewrite <- (Fset.equal_eq_1 _ _ _ _ (Ha1 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
                      - rewrite (Fset.equal_eq_1 _ _ _ _ Sx2).
                        rewrite <- (Fset.equal_eq_1 _ _ _ _ (Hl2 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
            }
            rewrite Abs in Hx1; discriminate Hx1.
        }  
      * intros; apply Ha1; right; assumption.
      * assumption.
    + intros y2 Hy2; apply Hl2.
      simpl; apply in_or_app; right; assumption.
  - intros y1 Hy1; apply Hl1.
    simpl; apply in_or_app; right; assumption.
  - assumption. 
  }
  * {
      apply f_equal2; apply sym_eq; apply Oeset.nb_occ_eq_2.
      - apply comparelA_comparelA_eq.
        assert (Aux := @Cursor.materialize_collection _ _ C1 c1).
        simpl in Aux; unfold Cursor.collection; simpl; apply Aux.
      - apply comparelA_comparelA_eq.
        assert (Aux := @Cursor.materialize_collection _ _ C2 c2).
        simpl in Aux; unfold Cursor.collection; simpl; apply Aux.
    }
Qed.
  
End BlockNestedLoop_is_a_join_op.

Section ThetaNestedLoop_is_a_filter_join_op.
Require Import ThetaNestedLoop.
  Hypotheses o1 o2 o : Type.
  Hypothesis O1 : Oeset.Rcd o1.
  Hypothesis O2 : Oeset.Rcd o2.
  Hypothesis O : Oeset.Rcd o.
  
  Hypothesis build_ : o1 -> o2 -> o.
  Hypothesis build_eq_1  : 
    forall x1 x1' x2, 
      Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
  Hypothesis build_eq_2  : 
    forall x1 x2 x2', 
      Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.
  Hypothesis theta : o -> bool.
  Hypothesis theta_eq : forall x y, Oeset.compare O x y = Eq -> theta x = theta y.

  Hypothesis C1 : Cursor.Rcd O1.
  Hypothesis C2 : Cursor.Rcd O2.
  
  Hypothesis A : Type.
  Hypothesis OA : Oset.Rcd A.
  Hypothesis FA : Fset.Rcd OA.
  
  Hypothesis sort1 : Cursor.cursor C1 -> Fset.set FA.
  Hypothesis sort2 : Cursor.cursor C2 -> Fset.set FA.
  Hypothesis sup1 : o1 -> Fset.set FA.
  Hypothesis sup2 : o2 -> Fset.set FA.
  Hypothesis sup : o -> Fset.set FA.
  Hypothesis proj1_ : o -> o1.
  Hypothesis proj2_ : o -> o2.
  Hypothesis sa1 sa2: Fset.set FA.
  Hypothesis sup_eq : forall t1 t2, Oeset.compare O t1 t2 = Eq -> sup t1 =S= sup t2.
  Hypothesis sup_build : forall t1 t2, sup (build_ t1 t2) =S= (sup1 t1 unionS sup2 t2).
  Hypothesis sup_proj1 : forall t, sup1 (proj1_ t) =S= sa1.
  Hypothesis sup_proj2 : forall t, sup2 (proj2_ t) =S= sa2.
  Hypothesis build_proj : 
    forall t, sup t =S= (sa1 unionS sa2) -> Oeset.compare O t (build_ (proj1_ t) (proj2_ t)) = Eq.
  Hypothesis build_eq :
    forall t1 u1 t2 u2, Oeset.compare O1 t1 u1 = Eq -> Oeset.compare O2 t2 u2 = Eq ->
                        Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq.
  Hypothesis build_split_eq_1 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O1 t1 u1 = Eq.
  Hypothesis build_split_eq_2 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sa1 -> sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sa2 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O2 t2 u2 = Eq.
  
  Notation TNL := (ThetaNestedLoop.build O build_ build_eq_1 build_eq_2 _ theta_eq C1 C2).

  Lemma TNL_is_a_filter_join_op : 
    is_a_filter_join_op 
      O1 O2 O (Cursor.materialize C1) (Cursor.materialize C2) (Cursor.materialize TNL) 
      _ sup1 sup2 sup proj1_ proj2_ theta sa1 sa2
      (fun c1 c2 => NestedLoop.mk_cursor C1 C2 nil c1 c2).
    Proof.
      intros c1 c2  H1 H2.
      assert (HJ := NL_is_a_join_op 
                     O _ build_eq_1 build_eq_2 C1 C2 FA  
                     _ _ _ _ _ sa1 sa2 sup_eq sup_build sup_proj1 sup_proj2 
                     build_proj build_eq build_split_eq_1 build_split_eq_2 _ _ H1 H2).
      assert (HF := mk_filter_is_a_filter_op 
                      (NestedLoop.build O build_ build_eq_1 build_eq_2 C1 C2) 
                      _ theta_eq (NestedLoop.mk_cursor C1 C2 nil c1 c2)).
      split.
      - intros t Ht.
        apply ((proj1 HJ) t).
        assert (Kt := HF t); simpl in Kt.
        unfold ThetaNestedLoop.build in Ht; unfold Filter.mk_filter in Kt.
        rewrite Kt in Ht.
        destruct (theta t).
        + rewrite N.mul_1_r in Ht; apply Ht.
        + rewrite N.mul_0_r in Ht; discriminate Ht.
      - intros t Ht.
        assert (Kt := HF t); simpl in Kt.
        unfold ThetaNestedLoop.build; unfold Filter.mk_filter in Kt.
        rewrite Kt, (proj2 HJ t Ht).
        apply refl_equal.
    Qed.

End ThetaNestedLoop_is_a_filter_join_op.


(* Any index scan is a filter *)

Section IndexScan_is_a_filter_op.

Variable o1 o2 : Type.
Variable O1 : Oeset.Rcd o1.
Variable O2 : Oeset.Rcd o2.

Variable IS : Index.Rcd O1 O2.

Lemma IS_is_a_filter_op :
    forall (x1 : o1),
    is_a_filter_op O1 (Index.c1 IS)
    (Cursor.materialize (Index.C1 IS))
    (fun x => Index.P IS (Index.proj IS x1) (Index.proj IS x))
    (fun c => Index.i IS c (Index.proj IS x1)).
Proof.
intros x1 c x; simpl.
rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _)).
rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Index.i_collection IS _ _)).
rewrite Oeset.nb_occ_filter.
- case_eq (Index.P IS (Index.proj IS x1) (Index.proj IS x)); intro Hx;
    [ | rewrite N.mul_0_r; apply refl_equal].
  rewrite N.mul_1_r.
  apply refl_equal.
- intros y1 y2 _ H.
  apply (Index.P_eq_2 IS); apply (Index.proj_eq IS); assumption.
Qed.

End IndexScan_is_a_filter_op.


Section IndexJoin_is_a_filter_join_op.

Require Import IndexJoin.

Variable o1 o2 op o : Type.
Hypothesis O1 : Oeset.Rcd o1.
Hypothesis O2 : Oeset.Rcd o2.
Hypothesis OP : Oeset.Rcd op.
Hypothesis O : Oeset.Rcd o.

Hypothesis projS1 : o1 -> op.
Hypothesis projS1_eq : 
  forall x1 x2, Oeset.compare O1 x1 x2 = Eq -> Oeset.compare OP (projS1 x1) (projS1 x2) = Eq.

Hypothesis S1 : Cursor.Rcd O1.
Hypothesis S2 : Index.Rcd O2 OP.
Hypothesis build_ : o1 -> o2 -> o.
Hypothesis build_eq_1  : 
  forall x1 x1' x2, 
    Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
Hypothesis build_eq_2  : 
  forall x1 x2 x2', 
    Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.


  Hypothesis A : Type.
  Hypothesis OA : Oset.Rcd A.
  Hypothesis FA : Fset.Rcd OA.
  
  Hypothesis sort1 : Cursor.cursor S1 -> Fset.set FA.
  Hypothesis sort2 : (Index.containers S2) -> Fset.set FA.
  Hypothesis sup1 : o1 -> Fset.set FA.
  Hypothesis sup2 : o2 -> Fset.set FA.
  Hypothesis sup : o -> Fset.set FA.
  Hypothesis proj1_ : o -> o1.
  Hypothesis proj2_ : o -> o2.
  Hypothesis sa1 sa2: Fset.set FA.
  Hypothesis sup_eq : forall t1 t2, Oeset.compare O t1 t2 = Eq -> sup t1 =S= sup t2.
  Hypothesis sup_build : forall t1 t2, sup (build_ t1 t2) =S= (sup1 t1 unionS sup2 t2).
  Hypothesis sup_proj1 : forall t, sup1 (proj1_ t) =S= sa1.
  Hypothesis sup_proj2 : forall t, sup2 (proj2_ t) =S= sa2.
  Hypothesis build_proj : 
    forall t, sup t =S= (sa1 unionS sa2) -> Oeset.compare O t (build_ (proj1_ t) (proj2_ t)) = Eq.
  Hypothesis build_eq :
    forall t1 u1 t2 u2, Oeset.compare O1 t1 u1 = Eq -> Oeset.compare O2 t2 u2 = Eq ->
                        Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq.
  Hypothesis build_split_eq_1 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O1 t1 u1 = Eq.
  Hypothesis build_split_eq_2 : forall t1 u1 t2 u2,
      Oeset.compare O (build_ t1 t2) (build_ u1 u2) = Eq ->
      sup1 t1 =S= sa1 -> sup1 t1 =S= sup1 u1 -> sup2 t2 =S= sa2 -> sup2 t2 =S= sup2 u2 ->
      Oeset.compare O2 t2 u2 = Eq.

  Notation IJ := 
    (IndexJoin.build _ _ _ _ O1 O2 OP O projS1 projS1_eq S1 S2 build_ build_eq_1 build_eq_2).

Lemma IndexJoin_is_a_filter_join_op :
  is_a_filter_join_op O1 O2 O
      (Cursor.materialize S1) (Index.c1 S2) 
      (Cursor.materialize IJ) 
      _ sup1 sup2 sup proj1_ proj2_ 
      (fun x => Index.P S2 (projS1 (proj1_ x)) (Index.proj S2 (proj2_ x)))
      sa1 sa2
      (fun c1 c2 => IndexJoin.mk_cursor 
                      _ _ _ _ O1 O2 OP S1 S2 nil 
                      c1 (Cursor.empty_cursor _) c2).
    Proof.
      intros c1 c2 H1 H2.
      assert (K1 : forall t1, In t1 (Cursor.collection c1) -> sup1 t1 =S= sa1).
      {
        intros t1 Ht1; apply H1.
        rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _)).
        rewrite <- Oeset.nb_occ_diff_0_pos; apply Oeset.mem_nb_occ.
        apply Oeset.in_mem_bool; assumption.
      }
      assert (K2 : forall t2, In t2 (Index.c1 S2 c2) -> sup2 t2 =S= sa2).
      {
        intros t2 Ht2; apply H2.
        rewrite <- Oeset.nb_occ_diff_0_pos; apply Oeset.mem_nb_occ.
        apply Oeset.in_mem_bool; assumption.
      }
      split.
      - intros t Ht.
        rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _)) in Ht.
        simpl in Ht; unfold IndexJoin.collection in Ht; simpl in Ht.
        rewrite IndexJoin.cross2_no_fold in Ht.
        rewrite <- Oeset.nb_occ_diff_0_pos in Ht.
        assert (Kt := Oeset.nb_occ_mem _ _ _ Ht).
        rewrite Oeset.mem_bool_true_iff in Kt; destruct Kt as [t' [Kt Ht']].
        rewrite  (Fset.equal_eq_1 _ _ _ _ (sup_eq _ _ Kt)).
        rewrite in_flat_map in Ht'.
        destruct Ht' as [t1 [Ht1 Ht']].
        rewrite in_map_iff in Ht'.
        destruct Ht' as [[b _t'] [_H Ht']].
        simpl in _H; subst _t'. rewrite filter_In in Ht'. destruct Ht' as [Ht' Hb]; subst b.
        rewrite in_map_iff in Ht'. destruct Ht' as [t2 [Ht' Kt']].
        injection Ht'; clear Ht'; intros Hb Ht'; subst t'.
        rewrite (Fset.equal_eq_1 _ _ _ _ (sup_build _ _)).
        apply Fset.union_eq; [apply K1 | apply K2]; trivial.
      - intros t Ht.
        rewrite 2 (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _)); simpl.
        unfold IndexJoin.collection; simpl.
        rewrite IndexJoin.cross2_no_fold.
        unfold IndexJoin.S2P, IndexJoin.projS2.
        assert (Kt : Oeset.compare O t (build_ (proj1_ t) (proj2_ t)) = Eq).
        {
          apply build_proj; assumption.
        }
        set (l1 := (Cursor.collection c1)) in *; clearbody l1.
        set (l2 := Index.c1 S2 c2) in *; clearbody l2; clear H2.
        revert l2 K2; induction l1 as [ | t1 l1]; intros l2 K2; simpl; trivial.
        rewrite Oeset.nb_occ_app, IHl1; trivial; [ | intros; apply K1; right]; trivial.
        assert (Kt1 := K1 _ (or_introl _ (refl_equal _))).
        assert (K1' : forall t1, In t1 l1 -> sup1 t1 =S= sa1).
        {
          intros; apply K1; right; assumption.
        }
        rewrite !Nmult_plus_distr_r; apply f_equal2; [ | apply refl_equal].
        clear l1 K1 K1' IHl1; induction l2 as [ | t2 l2]; simpl;
          [rewrite N.mul_0_r, N.mul_0_l; trivial | ].
        case_eq (Index.P S2 (projS1 t1) (Index.proj S2 t2)); intro H; simpl; rewrite IHl2.
        + case_eq (Oeset.compare O t (build_ t1 t2)); intro Jt.
          * rewrite (Oeset.compare_eq_1 _ _ _ _ Kt) in Jt.
            {
              rewrite (build_split_eq_1 _ _ _ _ Jt), (build_split_eq_2 _ _ _ _ Jt).
              - replace (Index.P S2 (projS1 (proj1_ t)) (Index.proj S2 (proj2_ t))) with true.
                + rewrite 2 Nmult_1_l, 2 Nmult_1_r; apply refl_equal.
                + rewrite <- H.
                  apply trans_eq with (Index.P S2 (projS1 t1) (Index.proj S2 (proj2_ t))).
                  * apply sym_eq; apply Index.P_eq_2; apply Index.proj_eq. 
                    {
                      apply (build_split_eq_2 _ _ _ _ Jt (sup_proj1 _)).
                      - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj1 _)), 
                          (Fset.equal_eq_2 _ _ _ _ Kt1).
                        apply Fset.equal_refl.
                      - apply sup_proj2.
                      - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj2 _)).
                        rewrite (Fset.equal_eq_2 _ _ _ _ (K2 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
                    }
                  * apply sym_eq; apply Index.P_eq_1; apply projS1_eq.
                    {
                      apply (build_split_eq_1 _ _ _ _ Jt).
                      - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj1 _)), 
                        (Fset.equal_eq_2 _ _ _ _ Kt1). 
                        apply Fset.equal_refl.
                      - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj2 _)).
                        rewrite (Fset.equal_eq_2 _ _ _ _ (K2 _ (or_introl _ (refl_equal _)))).
                        apply Fset.equal_refl.
                    } 
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj1 _)); apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj1 _)), 
                  (Fset.equal_eq_2 _ _ _ _ Kt1).
                apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj2 _)).
                  apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj2 _)).
                rewrite (Fset.equal_eq_2 _ _ _ _ (K2 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj1 _)), 
                  (Fset.equal_eq_2 _ _ _ _ Kt1).
                apply Fset.equal_refl.
              - rewrite (Fset.equal_eq_1 _ _ _ _ (sup_proj2 _)).
                rewrite (Fset.equal_eq_2 _ _ _ _ (K2 _ (or_introl _ (refl_equal _)))).
                apply Fset.equal_refl.
            }
          * rewrite N.add_0_l.
            {
              case_eq (Oeset.compare O1 (proj1_ t) t1); intro Jt1.
              - case_eq (Oeset.compare O2 (proj2_ t) t2); intro Jt2.
                + rewrite (Oeset.compare_eq_2 _ _ _ _ (build_eq _ _ _ _ Jt1 Jt2)) in Kt.
                  rewrite Kt in Jt; discriminate Jt.
                + rewrite N.add_0_l, Nmult_1_l; apply refl_equal.
                +  rewrite N.add_0_l, Nmult_1_l; apply refl_equal.
              - rewrite 2 N.mul_0_l; apply refl_equal.
              - rewrite 2 N.mul_0_l; apply refl_equal.
            }
          * rewrite N.add_0_l.
            {
              case_eq (Oeset.compare O1 (proj1_ t) t1); intro Jt1.
              - case_eq (Oeset.compare O2 (proj2_ t) t2); intro Jt2.
                + rewrite (Oeset.compare_eq_2 _ _ _ _ (build_eq _ _ _ _ Jt1 Jt2)) in Kt.
                  rewrite Kt in Jt; discriminate Jt.
                + rewrite N.add_0_l, Nmult_1_l; apply refl_equal.
                +  rewrite N.add_0_l, Nmult_1_l; apply refl_equal.
              - rewrite 2 N.mul_0_l; apply refl_equal.
              - rewrite 2 N.mul_0_l; apply refl_equal.
            }
        + intros; apply K2; right; assumption.
        + case_eq (Oeset.compare O1 (proj1_ t) t1); intro Jt1.
          * 
            {
              case_eq (Oeset.compare O2 (proj2_ t) t2); intro Jt2.
              - assert (Hb : Index.P S2 (projS1 (proj1_ t)) (Index.proj S2 (proj2_ t)) = false).
                {
                  rewrite <- H.
                  apply trans_eq with (Index.P S2 (projS1 t1) (Index.proj S2 (proj2_ t))).
                  - apply Index.P_eq_1; apply projS1_eq; assumption.
                  - apply Index.P_eq_2; apply Index.proj_eq; assumption.
                }
                rewrite Hb, 2 N.mul_0_r; apply refl_equal.
              - rewrite N.add_0_l; trivial.
              - rewrite N.add_0_l; trivial.
            }
          * rewrite 2 N.mul_0_l; apply refl_equal.
          * rewrite 2 N.mul_0_l; apply refl_equal.
        + intros; apply K2; right; assumption.
Qed.

End IndexJoin_is_a_filter_join_op.


(* Group is grouping *)

Require Import Group.

Section Group_is_a_grouping_op.

  Variable elt : Type.
  Variable Elt : Oeset.Rcd elt.
  Variable C : Cursor.Rcd Elt.

  Variable key : Type.
  Variable Key : Oeset.Rcd key.

  Variable proj : elt -> key.
  Variable theta : list elt -> bool.
  Variable build : list elt -> elt.

  Hypothesis proj_eq : forall e1 e2,
      Oeset.compare Elt e1 e2 = Eq ->
      Oeset.compare Key (proj e1) (proj e2) = Eq.
  Hypothesis build_eq : forall l1 l2,
    comparelA (Oeset.compare Elt) l1 l2 = Eq ->
    Oeset.compare Elt (build l1) (build l2) = Eq.
  Hypothesis theta_eq : forall l1 l2,
    comparelA (Oeset.compare Elt) l1 l2 = Eq -> theta l1 = theta l2.

Notation assoc := (OrderedSet.group Key proj).

  Lemma Group_is_a_grouping_op :
    is_a_grouping_op 
      Elt
      (Cursor.materialize (SeqScan.SeqScan.build Elt))
      (fun proj c => List.map snd (List.fold_left (fun acc e => assoc e acc) (Cursor.materialize C c) nil))
      proj
      theta
      build
      (group C Key proj theta build).
  Proof.
    intros q t.
    assert (Hg := Cursor.materialize_collection (SeqScan.SeqScan.build Elt) (group C Key proj theta build q)).
    assert (Hq := Cursor.materialize_collection C q).
    rewrite (Oeset.nb_occ_eq_2 _ t _ _ Hg).
    rewrite (Oeset.nb_occ_eq_2 _ t _ _ (group_collection _ _ _ _ _ proj_eq build_eq theta_eq _)).
    apply permut_nb_occ, permut_refl_alt.
    apply (comparelA_map_eq_2 (OL Elt) _ _ _ _ build_eq).
    apply (comparelA_eq_filter _ _ _ _).
    - intros a1 a2 _; apply theta_eq.
    - apply (comparelA_map_eq_2 (OKL Elt Key)).
      + intros [k1 l1] [k2 l2]; simpl.
        now case (Oeset.compare Key k1 k2); try discriminate.
      + apply (comparelA_fold_left_eq (mk_oelists (OKL Elt Key)) Elt).
        * now intros; apply assoc_eq.
        * now apply (Oeset.compare_eq_sym (OL Elt)).
  Qed.

End Group_is_a_grouping_op.
