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
Require Import BasicFacts ListFacts 
        ListSort ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection
        Signatures SeqScan Filter NestedLoop BlockNestedLoop ThetaNestedLoop IndexJoin Group
        HighLevelSpec Adequacy
        Partition FlatData SqlCommon SqlAlgebra.

Set Implicit Arguments.

Section Sec.
Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

Hypothesis predicate : Type.
Hypothesis symb : Type.
Hypothesis aggregate : Type.
Hypothesis OPredicate : Oset.Rcd predicate.
Hypothesis OSymb : Oset.Rcd symb.
Hypothesis OAggregate : Oset.Rcd aggregate.
Hypothesis interp_predicate : predicate -> list (Tuple.value T) -> bool.
Hypothesis interp_symb : symb -> list (Tuple.value T) -> Tuple.value T.
Hypothesis interp_aggregate : aggregate -> list (Tuple.value T) -> Tuple.value T.
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Import Tuple.

Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Notation env_t := (env_t (T := T) (OSymb := OSymb) (OAggregate := OAggregate)).
Notation projection_ := 
  (projection (OSymb := OSymb) (OAggregate := OAggregate) interp_symb interp_aggregate).
Notation interp_funterm_ := 
  (interp_funterm_ (OSymb := OSymb) (OAggregate := OAggregate) interp_symb).
Notation interp_aggterm_ :=
  (interp_aggterm_ (OSymb := OSymb) (OAggregate := OAggregate) interp_symb interp_aggregate).
Notation eval_query := 
  (eval_query (OSymb := OSymb) (OAggregate := OAggregate) 
                  interp_predicate interp_symb interp_aggregate basesort instance).
Notation eval_formula := 
  (eval_formula (OSymb := OSymb) (OAggregate := OAggregate) 
                  interp_predicate interp_symb interp_aggregate basesort instance).
Notation eval_f_eq := 
  (eval_f_eq (OSymb := OSymb) (OAggregate := OAggregate) 
                  interp_predicate interp_symb interp_aggregate basesort instance).
Notation "b '=R=' l" := 
  (forall t, Febag.nb_occ BTupleT t b = Oeset.nb_occ (OTuple T) t l) (at level 70, no associativity).

Lemma sup_eq : forall t1 t2 : tuple T, t1 =t= t2 -> support T t1 =S= support T t2.
Proof.
  intros t1 t2 Ht; rewrite tuple_eq in Ht; apply (proj1 Ht).
Qed.

Lemma sup_build : 
 forall t1 t2 : tuple T, support T (join_tuple T t1 t2) =S= (support T t1 unionS support T t2).
Proof.
intros t1 t2; unfold join_tuple; apply (support_mk_tuple _ _ _).
Qed.

Lemma sup_proj12 : 
 forall s (t : tuple T), support T (mk_tuple T s (dot T t)) =S= s.
Proof.
intros s t; apply support_mk_tuple.
Qed.

Lemma build_proj : 
  forall s1 s2 (t : tuple T),
    support T t =S= (s1 unionS s2) ->
    t =t= join_tuple T (mk_tuple T s1 (dot T t)) (mk_tuple T s2 (dot T t)).
Proof.
  intros s1 s2 t Ht; rewrite (split_tuple T s1 s2); repeat split.
  + apply Oeset.compare_eq_refl.
  + apply Oeset.compare_eq_refl.
  + assumption.
  + apply support_mk_tuple.
  + apply support_mk_tuple.
  + rewrite join_compatible_tuple_alt.
    intros a Ha1 Ha2; rewrite 2 dot_mk_tuple; trivial.
    * rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ha2; apply Ha2.
    * rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ha1; apply Ha1.
Qed.

Lemma build_eq :
  forall t1 u1 t2 u2 : tuple T,
    t1 =t= u1 -> t2 =t= u2 -> join_tuple T t1 t2 =t= join_tuple T u1 u2.
Proof.
  - do 6 intro; apply join_tuple_eq; assumption.
Qed.

Lemma build_split_eq_1 : 
  forall t1 u1 t2 u2 : tuple T,
    join_tuple T t1 t2 =t= join_tuple T u1 u2 ->
    support T t1 =S= support T u1 -> support T t2 =S= support T u2 -> t1 =t= u1.
Proof.
- intros t1 u1 t2 u2 H Hs1 Hs2.
  rewrite tuple_eq; split; [assumption | ].
  intros a.
  case_eq (a inS? support T t1); 
      intro Ha; [ | unfold dot; rewrite <- (Fset.mem_eq_2 _ _ _ Hs1), Ha; trivial].
  rewrite tuple_eq in H.
  apply trans_eq with (dot T (join_tuple T t1 t2) a).
  + unfold join_tuple; rewrite dot_mk_tuple, Ha; trivial.
    rewrite Fset.mem_union, Ha; trivial.
  + rewrite (proj2 H); unfold join_tuple; rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ Hs1), Ha; trivial.
    rewrite Fset.mem_union, <- (Fset.mem_eq_2 _ _ _ Hs1), Ha; trivial.
Qed.

Lemma build_split_eq_2 : 
  forall s1 s2, (s1 interS s2 =S= (emptysetS)) ->
  forall (t1 u1 t2 u2 : tuple T),
    join_tuple T t1 t2 =t= join_tuple T u1 u2 ->
    support T t1 =S= s1 ->
    support T t1 =S= support T u1 ->
    support T t2 =S= s2 -> support T t2 =S= support T u2 -> t2 =t= u2.
Proof.
- intros s1 s2 Sq t1 u1 t2 u2 H Ht1 Hs1 Ht2 Hs2.
  rewrite tuple_eq; split; [assumption | ].
  intros a.
  case_eq (a inS? support T t2); 
      intro Ha; [ | unfold dot; rewrite <- (Fset.mem_eq_2 _ _ _ Hs2), Ha; trivial].
  assert (Ka : a inS? support T t1 = false).
  {
    case_eq (a inS? support T t1); [ | intros; apply refl_equal].
    intro Ka.
    assert (Abs : a inS (Fset.empty (A T))).
    {
      rewrite <- (Fset.mem_eq_2 _ _ _ Sq), Fset.mem_inter.
      rewrite <- (Fset.mem_eq_2 _ _ _ Ht1), Ka, <- (Fset.mem_eq_2 _ _ _ Ht2), Ha.
      apply refl_equal.
    }
    rewrite Fset.empty_spec in Abs; discriminate Abs.
  }
  rewrite tuple_eq in H.
  apply trans_eq with (dot T (join_tuple T t1 t2) a).
  + unfold join_tuple; rewrite dot_mk_tuple, Ka; trivial.
    rewrite Fset.mem_union, Ha, Bool.orb_true_r; trivial.
  + rewrite (proj2 H); unfold join_tuple; rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ Hs1), Ka; trivial.
    rewrite Fset.mem_union, <- (Fset.mem_eq_2 _ _ _ Hs2), Ha, Bool.orb_true_r; trivial.
Qed.

Lemma mk_filter_implements_Q_Sigma : 
  forall C env f q, 
    let F := Filter.build _ (eval_f_eq env f) C in
    forall c, 
      eval_query env q =R= Cursor.materialize C c -> 
      eval_query env (Q_Sigma f q) =R= Cursor.materialize F (Filter.mk_filter F c). 
Proof.
intros C env f q eval_f F c Hc.
apply Q_Sigma_is_computable_by_any_filter_op with (Cursor.materialize C); trivial.
- apply mk_filter_is_a_filter_op.
Qed.

Lemma IS_implements_Q_Sigma :
  forall (IS : Index.Rcd  (OTuple T) (oeset_of_oset (mk_olists (OVal T)))),
    (forall lv1 lv2, Index.P IS lv1 lv2 = Oset.eq_bool (mk_olists (OVal T)) lv1 lv2) -> 
    forall la lval env f q ,
    (forall t, eval_formula (env_t env t) f = 
               Oset.eq_bool (mk_olists (OVal T)) (map (dot T t) la) lval) ->
    (forall t, Index.proj IS t = map (dot T t) la) ->
    forall c, 
      eval_query env q =R= Index.c1 IS c ->
      eval_query env (Q_Sigma f q) =R= Cursor.materialize _ (Index.i IS c lval).
Proof.
intros IS HP la lval env f q Hf Hi c Hq t.
rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _ )).
rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Index.i_collection IS c lval)).
rewrite eval_query_unfold, Febag.nb_occ_filter; [ | intros; apply eval_f_eq; trivial].
rewrite Hf, <- Hi, Hq, Oeset.nb_occ_filter, HP.
- rewrite Oset.eq_bool_sym.
  case (Oset.eq_bool (mk_olists (OVal T)) lval (Index.proj IS t)).
  + rewrite N.mul_1_r; trivial.
  + rewrite N.mul_0_r; trivial.
- intros x1 x2 _ Hx; rewrite tuple_eq in Hx; rewrite 2 Hi.
  apply f_equal; rewrite <- map_eq.
  intros; rewrite (proj2 Hx); trivial.
Qed.

Lemma NL_implements_Q_Join :
  forall C1 C2 env q1 q2, (sort basesort q1 interS sort basesort q2) =S= (emptysetS) ->
    (forall t, t inBE eval_query env q1 -> support T t =S= sort basesort q1) ->
    (forall t, t inBE eval_query env q2 -> support T t =S= sort basesort q2) ->
    let NL := NestedLoop.build (OTuple T) (join_tuple T) (join_tuple_eq_1 T) (join_tuple_eq_2 T) C1 C2 in 
    forall c1 c2, 
      eval_query env q1 =R= Cursor.materialize C1 c1 -> 
      eval_query env q2 =R= Cursor.materialize C2 c2 -> 
      eval_query env (Q_Join q1 q2) =R= 
      Cursor.materialize NL (NestedLoop.mk_cursor C1 C2 nil c1 c2).
Proof.
intros C1 C2 env q1 q2 Sq Hq1 Hq2 NL c1 c2 Hc1 Hc2.
apply Q_Join_is_computable_by_any_join_op with (Cursor.materialize C1) (Cursor.materialize C2); trivial.
apply NL_is_a_join_op.
- apply sup_eq.
- apply sup_build. 
- apply sup_proj12. 
- apply sup_proj12. 
- apply build_proj. 
- apply build_eq.
- apply build_split_eq_1. 
- apply build_split_eq_2; trivial.
Qed.

Lemma BNL_implements_Q_Join :
  forall C1 C2 env q1 q2, (sort basesort q1 interS sort basesort q2) =S= (emptysetS) ->
    (forall t, t inBE eval_query env q1 -> support T t =S= sort basesort q1) ->
    (forall t, t inBE eval_query env q2 -> support T t =S= sort basesort q2) ->
    let BNL := BlockNestedLoop.build 
                 (OTuple T) (join_tuple T) (join_tuple_eq_1 T) (join_tuple_eq_2 T) C1 C2 in 
    forall c1 c2, 
      eval_query env q1 =R=  flat_map (fun x => x) (Cursor.materialize C1 c1) -> 
      eval_query env q2 =R= flat_map (fun x => x) (Cursor.materialize C2 c2) -> 
      eval_query env (Q_Join q1 q2) =R= 
      flat_map (fun x => x) (Cursor.materialize BNL (NestedLoop.mk_cursor C1 C2 nil c1 c2)).
Proof.
intros C1 C2 env q1 q2 Sq Hq1 Hq2 BNL c1 c2 Hc1 Hc2.
apply (Q_Join_is_computable_by_any_join_op 
         (OSymb := OSymb) (OAggregate := OAggregate)
         interp_predicate interp_symb interp_aggregate basesort instance
         (bagA1 := Cursor.cursor C1) (bagA2 := Cursor.cursor C2) (bagA := Cursor.cursor BNL)
         (elementsA1 := fun c => flat_map (fun x => x) (Cursor.materialize C1 c))
         (elementsA2 := fun c => flat_map (fun x => x) (Cursor.materialize C2 c))
         (elementsA := fun c => flat_map (fun x => x) (Cursor.materialize BNL c))); trivial.
apply (BNL_is_a_join_op (O1 := OTuple T) (O2 := OTuple T) (OTuple T) (join_tuple T)).
- apply sup_eq.
- apply sup_build. 
- apply sup_proj12. 
- apply sup_proj12. 
- apply build_proj. 
- apply build_eq.
- apply build_split_eq_1. 
- apply build_split_eq_2; trivial.
Qed.

Lemma TNL_implements_Q_Sigma_Join :
  forall C1 C2 env f q1 q2, (sort basesort q1 interS sort basesort q2) =S= (emptysetS) ->
    (forall t, t inBE eval_query env q1 -> support T t =S= sort basesort q1) ->
    (forall t, t inBE eval_query env q2 -> support T t =S= sort basesort q2) ->
    let TNL := ThetaNestedLoop.build 
                 (OTuple T) (join_tuple T) (join_tuple_eq_1 T) (join_tuple_eq_2 T) 
                 _ (eval_f_eq env f) C1 C2 in 
    forall c1 c2, 
      eval_query env q1 =R= Cursor.materialize C1 c1 -> 
      eval_query env q2 =R= Cursor.materialize C2 c2 -> 
      eval_query env (Q_Sigma f (Q_Join q1 q2)) =R= 
      Cursor.materialize TNL (NestedLoop.mk_cursor C1 C2 nil c1 c2).
Proof.
intros C1 C2 env f q1 q2 Sq Hq1 Hq2 NL c1 c2 H1 H2.
apply (Q_Sigma_Join_is_computable_by_any_filter_join_op 
         (OSymb := OSymb) (OAggregate := OAggregate)
         interp_predicate interp_symb interp_aggregate basesort instance
         (bagA1 := Cursor.cursor C1) (bagA2 := Cursor.cursor C2) (bagA := Cursor.cursor NL)
         (elementsA1 := Cursor.materialize C1)
         (elementsA2 := Cursor.materialize C2)
         (elementsA := Cursor.materialize NL) env f q1 q2); trivial.
apply TNL_is_a_filter_join_op.
- apply sup_eq.
- apply sup_build. 
- apply sup_proj12. 
- apply sup_proj12. 
- apply build_proj. 
- apply build_eq.
- apply build_split_eq_1. 
- apply build_split_eq_2; trivial.
Qed.

Lemma mk_tuple_eq_2_alt : 
  forall s (x1 x2 : tuple T), x1 =t= x2 -> mk_tuple T s (dot T x1) =t= mk_tuple T s (dot T x2).
Proof.
intros s x1 x2 Hx; apply mk_tuple_eq_2.
intros a _; rewrite tuple_eq in Hx; apply (proj2 Hx).
Qed.

Lemma IJ_implements_Q_Sigma_Join :
  forall C1 S2 env f q1 q2, (sort basesort q1 interS sort basesort q2) =S= (emptysetS) ->
    (forall t, t inBE eval_query env q1 -> support T t =S= sort basesort q1) ->
    (forall t, t inBE eval_query env q2 -> support T t =S= sort basesort q2) ->
    let IJ := (IndexJoin.build _ _ _ _ (OTuple T) (OTuple T) (OTuple T)
                 (OTuple T) 
                 (fun t => mk_tuple T (sort basesort q1) (dot T t)) (mk_tuple_eq_2_alt _)
                 C1 S2 (join_tuple T) (join_tuple_eq_1 T) (join_tuple_eq_2 T)) in 

    forall c1 c2, 
      eval_query env q1 =R= Cursor.materialize C1 c1 -> 
      eval_query env q2 =R= Index.c1 S2 c2 -> 

      let f_index := 
          (fun x : tuple T =>
             Index.P 
               S2 
               (mk_tuple T (sort basesort q1) (dot T (mk_tuple T (sort basesort q1) (dot T x))))
               (Index.proj S2 (mk_tuple T (sort basesort q2) (dot T x)))) in
      (forall t t1 t2, 
          t1 inBE eval_query env q1 -> t2 inBE eval_query env q2 ->
          t =t= join_tuple T t1 t2 ->
          eval_formula (env_t env t) f = f_index t) ->

      eval_query env (Q_Sigma f (Q_Join q1 q2)) =R= 
      Cursor.materialize IJ
        (IndexJoin.mk_cursor 
           _ _ _ _ (OTuple T) (OTuple T) (OTuple T) C1 S2 nil c1 (Cursor.empty_cursor _) c2).
Proof.
intros C1 S2 env f q1 q2 Sq Hq1 Hq2 IJ c1 c2 H1 H2 f_index Hf t.
assert (H1' : forall t1 : tuple T,
           (BinNat.N.lt 0 (Oeset.nb_occ (OTuple T) t1 (Cursor.materialize C1 c1))) -> 
           support T t1 =S= sort basesort q1).
{
  intros t1 Ht1; apply Hq1; apply Febag.nb_occ_mem; rewrite H1, Oeset.nb_occ_diff_0_pos; trivial.
}
assert (H2' : forall t2 : tuple T,
           BinNat.N.lt 0 (Oeset.nb_occ (OTuple T) t2 (Index.c1 S2 c2)) ->
           support T t2 =S= sort basesort q2).
{
  intros t2 Ht2; apply Hq2; apply Febag.nb_occ_mem; rewrite H2, Oeset.nb_occ_diff_0_pos; trivial.
}
assert (H' := IndexJoin_is_a_filter_join_op 
                (O1 := OTuple T) (OTuple T) (O2 := OTuple T) (OP := OTuple T) 
                _ (mk_tuple_eq_2_alt (sort basesort q1)) 
                C1 S2 (join_tuple T) (join_tuple_eq_1 T) (join_tuple_eq_2 T) (A T) 
                (support T) (support T) (support T)
                (fun t => mk_tuple T (sort basesort q1) (dot T t))
                (fun t => mk_tuple T (sort basesort q2) (dot T t)) 
                (sort basesort q1) (sort basesort q2)
                sup_eq sup_build (sup_proj12 (sort basesort q1)) (sup_proj12 (sort basesort q2))
                (build_proj _ _) build_eq build_split_eq_1 (build_split_eq_2 _ _ Sq) c1 c2
                H1' H2').
assert (H1'' : 
          (forall t1 : tuple T,
              BinNat.N.lt 
                0
                (Oeset.nb_occ (OTuple T) t1
                              ((fun q : query T relname predicate OSymb OAggregate =>
                                  Febag.elements BTupleT (eval_query env q)) q1)) -> 
              support T t1 =S= sort basesort q1)).
{
  intros t1 Ht1; apply Hq1; apply Febag.nb_occ_mem; rewrite Febag.nb_occ_elements.
  rewrite Oeset.nb_occ_diff_0_pos; trivial.
}
assert (H2'' : (forall t2 : tuple T,
         BinNat.N.lt 0
           (Oeset.nb_occ (OTuple T) t2
              ((fun q : query T relname predicate OSymb OAggregate =>
                Febag.elements BTupleT (eval_query env q)) q2)) -> 
         support T t2 =S= sort basesort q2)).
{
  intros t2 Ht2; apply Hq2; apply Febag.nb_occ_mem; rewrite Febag.nb_occ_elements.
  rewrite Oeset.nb_occ_diff_0_pos; trivial.
}
assert (H'' := Q_Join_is_a_join_op (OSymb := OSymb) (OAggregate := OAggregate) 
                                    interp_predicate interp_symb interp_aggregate 
                                    basesort instance env
                                    (sort basesort q1) (sort basesort q2) q1 q2 
                                    H1'' H2'').
destruct H' as [K1' K2']; destruct H'' as [K1'' K2''].
case_eq (support T t =S?= (sort basesort q1 unionS sort basesort q2)); intro Ht.
- unfold IJ; rewrite (K2' _ Ht), eval_query_unfold, Febag.nb_occ_filter;
    [ | intros; apply eval_f_eq; trivial].
  rewrite Febag.nb_occ_elements, (K2'' _ Ht), <- H1, <- H2, <- 2 Febag.nb_occ_elements.
  case_eq (Febag.nb_occ BTupleT (mk_tuple T (sort basesort q1) (dot T t)) (eval_query env q1));
    [intro H0; rewrite 2 N.mul_0_l; trivial | ].
  intros p1 Hp1.
  case_eq (Febag.nb_occ BTupleT (mk_tuple T (sort basesort q2) (dot T t)) (eval_query env q2));
    [intro H0; rewrite 2 N.mul_0_l; trivial | ].
  intros p2 Hp2.
  rewrite (Hf t (mk_tuple T (sort basesort q1) (dot T t)) 
              (mk_tuple T (sort basesort q2) (dot T t))).
  + apply refl_equal.
  + apply Febag.nb_occ_mem; rewrite Hp1; discriminate.
  + apply Febag.nb_occ_mem; rewrite Hp2; discriminate.
  + apply build_proj; assumption.
- apply trans_eq with 0.
  + case_eq (Febag.nb_occ BTupleT t (eval_query env (Q_Sigma f (Q_Join q1 q2))));
      [intros; trivial | ].
    intros p Hp; rewrite K1'' in Ht; [discriminate Ht | ].
    rewrite eval_query_unfold, Febag.nb_occ_filter in Hp; [ | intros; apply eval_f_eq; trivial].
    destruct (eval_formula (env_t env t) f).
    * rewrite N.mul_1_r, Febag.nb_occ_elements in Hp; rewrite Hp; apply refl_equal.
    * rewrite N.mul_0_r in Hp; discriminate Hp.
  + case_eq (Oeset.nb_occ (OTuple T) t
    (Cursor.materialize IJ
       {|
       IndexJoin.visited := nil;
       IndexJoin.outer := c1;
       IndexJoin.inner := Cursor.empty_cursor (Index.C1 S2);
       IndexJoin.containers2 := c2 |})); [intros; trivial | ].
    intros p Hp; rewrite K1' in Ht; [discriminate Ht | ].
    unfold IJ in Hp; rewrite Hp; apply refl_equal.
Qed.

Lemma group_crit_eq :
  forall env g,
    let group_crit t := map (interp_funterm_ (env_t env t)) g in
    forall e1 e2 : tuple T,
      e1 =t= e2 ->
      Oeset.compare (oeset_of_oset (mk_olists (OVal T))) (group_crit e1) (group_crit e2) = Eq.
Proof.
  intros env g group_crit x1 x2 Hx.  
  unfold group_crit; simpl.
  apply comparelA_eq_refl_alt.
  - intros; apply Oset.compare_eq_refl.
  - rewrite <- map_eq; intros; apply interp_funterm_eq.
    constructor 2; simpl; [ | apply equiv_env_refl].
    simpl; repeat split; 
      [ | rewrite compare_list_t; simpl; rewrite Hx; trivial].
    rewrite tuple_eq in Hx; apply (proj1 Hx).
Qed.

Lemma projection_g_eq :
  forall env g s,
    let eval_s := fun l => projection_ (env_g env (Group_By g) l) (Select_List s) in
    forall l1 l2 : listT,
      comparelA (Oeset.compare (OTuple T)) l1 l2 = Eq -> eval_s l1 =t= eval_s l2.
Proof.
  intros env g s eval_s l1 l2 Hl; apply projection_eq.
  constructor 2; [ | apply equiv_env_refl].
  assert (H1 : l1 =PE= l2).
  {
    apply permut_refl_alt; assumption.
  }
  assert (H2 := extract_from_groups _ H1).
  repeat split; trivial.
  destruct (quicksort (OTuple T) l1) as [ | t1]; 
    destruct (quicksort (OTuple T) l2) as [ | t2]; try discriminate H2.
  - apply Fset.equal_refl.
  - simpl in H2.
    case_eq (Oeset.compare (OTuple T) t1 t2); intro Ht; rewrite Ht in H2; try discriminate H2.
    rewrite tuple_eq in Ht; apply (proj1 Ht).
Qed.

Lemma eval_formula_g_eq :
  forall env g f, 
    let eval_f := fun l => eval_formula (env_g env (Group_By g) l) f in
    forall l1 l2 : listT,
       comparelA (Oeset.compare (OTuple T)) l1 l2 = Eq -> eval_f l1 = eval_f l2.
Proof.
  intros env g f eval_f l1 l2 Hl; apply eval_formula_eq.
  constructor 2; [ | apply equiv_env_refl].
  assert (H1 : l1 =PE= l2).
  {
    apply permut_refl_alt; assumption.
  }
  assert (H2 := extract_from_groups _ H1).
  repeat split; trivial.
  destruct (quicksort (OTuple T) l1) as [ | t1]; 
    destruct (quicksort (OTuple T) l2) as [ | t2]; try discriminate H2.
  - apply Fset.equal_refl.
  - simpl in H2.
    case_eq (Oeset.compare (OTuple T) t1 t2); intro Ht; rewrite Ht in H2; try discriminate H2.
    rewrite tuple_eq in Ht; apply (proj1 Ht).
Qed.

Lemma Group_implements_Q_Gamma :
  forall (C : Cursor.Rcd (OTuple T)) env g f s q,
    let group_crit := fun t => map (interp_funterm_ (env_t env t)) g in
    let eval_s := fun l => projection_ (env_g env (Group_By g) l) (Select_List s) in
    let eval_f := fun l => eval_formula (env_g env (Group_By g) l) f in
    forall c,
      eval_query env q =R= Cursor.materialize _ c ->
      eval_query env (Q_Gamma g f s q) =R= 
      (SeqScan.collection (group C (oeset_of_oset (mk_olists (OVal T)))  
                                 group_crit eval_f eval_s c)).
Proof.
intros C env g f s q group_crit eval_s eval_f c Hc t.
assert (H := Group_is_a_grouping_op 
               C (oeset_of_oset (mk_olists (OVal T))) group_crit eval_f eval_s 
                (group_crit_eq _ _) (projection_g_eq _ _ _) (eval_formula_g_eq _ _ _) c t).
rewrite (Oeset.nb_occ_eq_2 _ _ _ _ (Cursor.materialize_collection _ _)) in H.
simpl in H; simpl; rewrite H; clear H.
rewrite Febag.nb_occ_elements, Q_Gamma_is_a_grouping_op.
unfold eval_s; apply (Oeset.nb_occ_map_eq_2_3 (OLTuple T)).
- intros l1 l2 Hl; apply projection_eq.
  constructor 2; [ | apply equiv_env_refl].
  simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption.
- intro l; unfold eval_f; rewrite 2 Oeset.nb_occ_filter.
  + apply if_eq; trivial.
    intros _; apply permut_nb_occ.
    set (_group_crit := map (fun x t => (interp_funterm_ (env_t env t) x)) g) in *.
    assert (Hgc : forall e : tuple T -> value T,
               In e _group_crit -> forall t1 t2 : tuple T, t1 =t= t2 -> e t1 = e t2).
    {
      intros e He; unfold _group_crit in He; rewrite in_map_iff in He.
      destruct He as [x [He Hx]]; subst e.
      intros t1 t2 Ht; apply interp_funterm_eq.
      constructor 2; [ | apply equiv_env_refl].
      split; [rewrite tuple_eq in Ht; apply (proj1 Ht) | ].
      split; [apply refl_equal | ].
      rewrite compare_list_t; simpl; rewrite Ht; apply refl_equal.
    }
    apply permut_trans with
        (map snd 
             (map (fun x : list (value T) * listT => let (k, lk) := x in (k, rev lk))
                  (rebuild_keys (FVal T) 
                                (Febag.elements BTupleT (eval_query env q)) _group_crit))).
    * unfold rebuild_keys; rewrite 2 map_map.
      set (x := partition_list_expr 
                  (FVal T) (Febag.elements BTupleT (eval_query env q)) _group_crit).
      clearbody x.
      induction x as [ | x1 x]; [apply _permut_refl; intros a Ha; contradiction Ha | ].
      simpl map; rewrite <- (permut_cons (OLTuple T)); [apply IHx | ].
      apply extract_from_groups.
      destruct x1; [apply permut_refl | ].
      apply _permut_rev; intros; apply Oeset.compare_eq_refl.
    * {
        apply _permut_map with 
            (fun x1 x2 => 
               Oeset.compare (mk_oepairs (oeset_of_oset (mk_olists (OVal T))) (OLA (OTuple T))) 
                       x1 x2 = Eq).
        - intros [k1 lk1] [k2 lk2] _ _; simpl.
          destruct (comparelA (Oset.compare (OVal T)) k1 k2); try discriminate.
          exact (fun h => h).
        - rewrite (partition_list_expr_fold_inv (OTuple T)).
          + assert (Aux2 :
                      fold_left
                        (fun (acc : list (list (value T) * listT)) (e : tuple T) =>
                           OrderedSet.group (oeset_of_oset (mk_olists (OVal T))) group_crit e acc)
                        (Cursor.materialize _ c) nil =
                      fold_left
                        (fun (acc : list (list (value T) * listT)) (t : tuple T) =>
                           OrderedSet.group 
                             (oeset_of_oset (mk_olists (OVal T)))
                             (fun u : tuple T => map (fun e => e u) _group_crit) t acc)
                        (Cursor.materialize _ c) nil).
            {
              apply fold_left_eq; trivial.
              intros a b H; apply OrderedSet.group_eq_0.
              intro u; unfold group_crit, _group_crit; rewrite map_map, <- map_eq.
              intros; trivial.
            }
            rewrite Aux2; clear Aux2.
            rewrite <- 2 flg_unfold; apply flg_permut.
            * apply Hgc.
            * apply permut_refl.
            * constructor 1.
            * constructor 1.
            * refine (permut_trans _ _ (_permut_rev _ _ _)); 
                [ | intros; apply Oeset.compare_eq_refl].
              apply permut_sym.
              refine (permut_trans _ _ (_permut_rev _ _ _)); 
                [ | intros; apply Oeset.compare_eq_refl].
              {
                apply permut_trans with (Febag.elements _ (eval_query env q)).
                - apply nb_occ_permut; intro x.
                  rewrite <- Hc, Febag.nb_occ_elements; apply refl_equal.
                - generalize (proj1 (partition_list_expr_invariant 
                            (OTuple T) (FVal T) 
                            _ (Febag.elements BTupleT (eval_query env q)) Hgc (refl_equal _))).
                  apply _permut_incl.
                  intros; subst; apply Oeset.compare_eq_refl.
              }
          + apply Hgc.
      }
  + intros l1 l2 _ Hl; apply eval_formula_eq.
    constructor 2; [ | apply equiv_env_refl].
    simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption.
  + intros l1 l2 _ Hl; apply eval_formula_eq.
    constructor 2; [ | apply equiv_env_refl].
    simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption.
Qed.

End Sec.
