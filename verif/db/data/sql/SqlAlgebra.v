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
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import Bool List Arith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet 
        FiniteSet FiniteBag FiniteCollection Formula Partition DExpressions Data FlatData Tree SqlCommon.

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

Arguments Select_Star {T} {symb} {aggregate} {OSymb} {OAggregate}.
Arguments Group_Fine {T} {symb} {aggregate} {OSymb} {OAggregate}.

Import Tuple.

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Notation funterm := (funterm (E T OSymb OAggregate)).
Notation aggterm := (aggterm (E T OSymb OAggregate)).
Notation select := (select T OSymb OAggregate).

Inductive query : Type := 
  | Q_Empty_Tuple : query
  | Q_Table : relname -> query
  | Q_Set : set_op -> query -> query -> query
  | Q_Join : query -> query -> query
  | Q_Pi : list select -> query -> query
  | Q_Sigma : formula -> query -> query
  | Q_Gamma : list funterm -> formula -> list select -> query -> query

with formula : Type :=
  | Q_Conj : Formula.and_or -> formula -> formula -> formula
  | Q_Not : formula -> formula
  | Q_Atom : q_atom -> formula

with q_atom : Type :=
  | Q_True
  | Q_Pred : predicate -> list aggterm -> q_atom
  | Q_Quant : Formula.quantifier -> predicate -> list aggterm -> query -> q_atom
  | Q_In : list select -> query -> q_atom
  | Q_Exists : query -> q_atom.


Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.

Fixpoint sort (q : query) : setA :=
  match q with
    | Q_Empty_Tuple => Fset.empty _
    | Q_Table t => basesort t
    | Q_Set _ q1 _ => sort q1
    | Q_Join q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi l _ 
    | Q_Gamma _ _ l _ =>
      Fset.mk_set _ (map (fun x => match x with Select_As _ a => a end) l)
  end.

Lemma sort_unfold :
  forall q, sort q =
  match q with
    | Q_Empty_Tuple => Fset.empty _
    | Q_Table t => basesort t
    | Q_Set _ q1 _ => sort q1
    | Q_Join q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi l _ 
    | Q_Gamma _ _ l _ =>
      Fset.mk_set _ (map (fun x => match x with Select_As _ a => a end) l)
  end.
Proof.
intro q; case q; intros; apply refl_equal.
Qed.

Notation env_t := (env_t (T := T) (OSymb := OSymb) (OAggregate := OAggregate)).
Notation env_g := (env_g (T := T) (OSymb := OSymb) (OAggregate := OAggregate)).
Notation projection_ := (projection (OSymb := OSymb) (OAggregate := OAggregate) interp_symb interp_aggregate).
Notation interp_funterm_ := (interp_funterm_ (OSymb := OSymb) (OAggregate := OAggregate) interp_symb).
Notation interp_aggterm_ := 
  (interp_aggterm_ (OSymb := OSymb) (OAggregate := OAggregate) interp_symb interp_aggregate).
Notation make_groups_ := (fun env b => make_groups (T := T) (OSymb := OSymb) (OAggregate := OAggregate) interp_symb env (Febag.elements (Fecol.CBag (CTuple T)) b)).
Notation natural_join_bag b1 b2 := 
  (Febag.mk_bag (Fecol.CBag (CTuple T)) (Data.natural_join_list 
     _ _ (build_data T) 
     (Febag.elements (Fecol.CBag (CTuple T)) b1) (Febag.elements(Fecol.CBag (CTuple T)) b2))).
Notation N_product_bag ll := (Data.N_product_bag _ _ (build_data T) (Fecol.CBag (CTuple T)) ll).

Fixpoint eval_query env q {struct q} : bagT :=
  match q with
  | Q_Empty_Tuple => Febag.singleton _ (empty_tuple T)
  | Q_Table r => instance r
  | Q_Set o q1 q2 =>
    if sort q1 =S?= sort q2 
    then Febag.interp_set_op _ o (eval_query env q1) (eval_query env q2)
    else Febag.empty _
  | Q_Join q1 q2 => natural_join_bag (eval_query env q1) (eval_query env q2)
  | Q_Pi s q => 
    Febag.map _  _ (fun t => projection_ (env_t env t) (Select_List s) base.nullval) (eval_query env q) 
  | Q_Sigma f q => Febag.filter _ (fun t => eval_formula (env_t env t) f) (eval_query env q)
  | Q_Gamma lf f s q => 
    Febag.mk_bag 
      _ (map (fun l => projection_ (env_g env (Group_By lf) l) (Select_List s) base.nullval)
             (filter (fun l => eval_formula (env_g env (Group_By lf) l) f)
                     (make_groups_ env (eval_query env q) (Group_By lf))))
  end

with eval_formula env f :=
  match f with
    | Q_Conj Formula.And_F f1 f2 => (eval_formula env f1) && (eval_formula env f2)
    | Q_Conj Formula.Or_F f1 f2 => (eval_formula env f1) || (eval_formula env f2)
    | Q_Not f => negb (eval_formula env f)
    | Q_Atom a => eval_q_atom env a
  end

with eval_q_atom env atm :=
  match atm with
  | Q_True => true
  | Q_Pred p l => interp_predicate p (map (interp_aggterm_ env) l)
  | Q_Quant qtf p l sq =>
      let lt := map (interp_aggterm_ env) l in
      Formula.interp_quant qtf
        (fun x : tuple T =>
         let la := {{{support T x}}} in
         interp_predicate p (lt ++ map (dot T x) la))
        (Febag.elements (Fecol.CBag (CTuple T)) (eval_query env sq))
  | Q_In s q => projection_ env (Select_List s) base.nullval inBE? eval_query env q
  | Q_Exists q => negb (Febag.is_empty (Fecol.CBag (CTuple T)) (eval_query env q))
  end.

Lemma eval_query_unfold :
  forall env q, eval_query env q =
  match q with
  | Q_Empty_Tuple => Febag.singleton _ (empty_tuple T)
  | Q_Table r => instance r
  | Q_Set o q1 q2 =>
    if sort q1 =S?= sort q2 
    then Febag.interp_set_op _ o (eval_query env q1) (eval_query env q2)
    else Febag.empty _
  | Q_Join q1 q2 => natural_join_bag (eval_query env q1) (eval_query env q2)
  | Q_Pi s q => 
    Febag.map _  _ (fun t => projection_ (env_t env t) (Select_List s) base.nullval) (eval_query env q) 
  | Q_Sigma f q => Febag.filter _ (fun t => eval_formula (env_t env t) f) (eval_query env q)
  | Q_Gamma lf f s q => 
    Febag.mk_bag 
      _ (map (fun l => projection_ (env_g env (Group_By lf) l) (Select_List s) base.nullval)
             (filter (fun l => eval_formula (env_g env (Group_By lf) l) f)
                     (make_groups_ env (eval_query env q) (Group_By lf))))
  end.
Proof.
intros env q; case q; intros; apply refl_equal.
Qed.

Lemma eval_formula_unfold :
  forall env f, eval_formula env f =
  match f with
    | Q_Conj Formula.And_F f1 f2 => (eval_formula env f1) && (eval_formula env f2)
    | Q_Conj Formula.Or_F f1 f2 => (eval_formula env f1) || (eval_formula env f2)
    | Q_Not f => negb (eval_formula env f)
    | Q_Atom a => eval_q_atom env a
  end.
Proof.
intros env f; case f; intros; apply refl_equal.
Qed.

Lemma eval_q_atom_unfold :
  forall env atm, eval_q_atom env atm =
  match atm with
  | Q_True => true
  | Q_Pred p l => interp_predicate p (map (interp_aggterm_ env) l)
  | Q_Quant qtf p l sq =>
      let lt := map (interp_aggterm_ env) l in
      Formula.interp_quant qtf
        (fun x : tuple T =>
         let la := {{{support T x}}} in
         interp_predicate p (lt ++ map (dot T x) la))
        (Febag.elements (Fecol.CBag (CTuple T)) (eval_query env sq))
  | Q_In s q => projection_ env (Select_List s) base.nullval inBE? eval_query env q
  | Q_Exists q => negb (Febag.is_empty (Fecol.CBag (CTuple T)) (eval_query env q))
  end.
Proof.
intros env atm; case atm; intros; apply refl_equal.
Qed.

Fixpoint N_Q_Join l :=
  match l with
    | nil => Q_Empty_Tuple
    | q :: nil => q
    | q1 :: l => Q_Join q1 (N_Q_Join l)
  end.

Lemma N_Q_Join_unfold :
  forall l, N_Q_Join l =
  match l with
    | nil => Q_Empty_Tuple
    | q :: nil => q
    | q1 :: l => Q_Join q1 (N_Q_Join l)
  end.
Proof.
intros [ | x1 [ | x2 l]]; apply refl_equal.
Qed.

Lemma sort_N_Q_Join :
  forall l, sort (N_Q_Join l) =S= Fset.Union _ (map sort l).
Proof.
intro l; induction l as [ | x1 [ | x2 l]].
- apply Fset.equal_refl.
- simpl; rewrite Fset.equal_spec; intro a.
  rewrite Fset.mem_union, Fset.empty_spec, Bool.orb_false_r.
  apply refl_equal.
- rewrite map_unfold, Fset.Union_unfold, N_Q_Join_unfold, sort_unfold.
  apply Fset.union_eq_2; apply IHl.
Qed.

(** * Syntactic comparison of queries *)

Section Compare.

Inductive All : Type :=
  | All_relname : relname  -> All 
  | All_attribute : attribute T -> All
  | All_predicate : predicate -> All
  | All_funterm : funterm -> All
  | All_aggterm : aggterm -> All.

Definition tree_of_attribute (a : attribute T) : tree All := Leaf (All_attribute a).

Definition tree_of_select s : tree All :=
  match s with
    | Select_As e a => Node 0 (Leaf (All_aggterm e) :: tree_of_attribute a :: nil)
  end.
         
Definition tree_of_select_item s : tree All := Node 2 (map tree_of_select s).

Fixpoint tree_of_query (q : query) : tree All :=
  match q with
(*    | Q_Empty sa => Node 3 (map tree_of_attribute sa) *)
    | Q_Empty_Tuple => Node 4 nil 
    | Q_Table r => Node 5 (Leaf (All_relname r) :: nil)
    | Q_Set o q1 q2 => 
      Node 
        (match o with 
           | Union => 6 
           | Inter => 7 
           | Diff => 8 
           | UnionMax => 9 end)
        (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Join q1 q2 => Node 10 (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Pi s q => Node 11 (tree_of_select_item s :: tree_of_query q :: nil)
    | Q_Sigma f q => Node 12 (tree_of_formula f ::  tree_of_query q :: nil)
    | Q_Gamma lf f s q => 
      Node 13 (tree_of_formula f  
               :: tree_of_select_item s 
               :: tree_of_query q 
               :: (map (fun x => Leaf (All_funterm x)) lf))
  end

with tree_of_formula f :=
  match f with
    | Q_Conj a f1 f2 => 
        Node (match a with Formula.And_F => 14 | Or_F => 15 end) 
             (tree_of_formula f1 :: tree_of_formula f2 :: nil)
    | Q_Not f => Node 16 (tree_of_formula f :: nil)
    | Q_Atom a => tree_of_q_atom a
  end

with tree_of_q_atom a :=
  match a with
    | Q_True => Node 17 nil
    | Q_Pred p l => Node 18 (Leaf (All_predicate p) :: map (fun x => Leaf (All_aggterm x)) l)
    | Q_Quant qtf p l q => 
      Node 
        (match qtf with 
           | Formula.Forall_F => 19
           | Exists_F => 20
         end) 
        (Leaf (All_predicate p) 
              :: tree_of_query q 
              :: (map (fun x => Leaf (All_aggterm x)) l))
    | Q_In s q => Node 21 ( tree_of_query q :: map tree_of_select s)
    | Q_Exists q => Node 22 (tree_of_query q :: nil)
  end.

Lemma tree_of_select_item_unfold :
  forall s, tree_of_select_item s = Node 2 (map tree_of_select s).
Proof.
intros; apply refl_equal.
Qed.

Lemma tree_of_query_unfold :
  forall q, tree_of_query q =
  match q with
(*    | Q_Empty sa => Node 3 (map tree_of_attribute sa) *)
    | Q_Empty_Tuple => Node 4 nil 
    | Q_Table r => Node 5 (Leaf (All_relname r) :: nil)
    | Q_Set o q1 q2 => 
      Node 
        (match o with 
           | Union => 6 
           | Inter => 7 
           | Diff => 8 
           | UnionMax => 9 end)
        (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Join q1 q2 => Node 10 (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Pi s q => Node 11 (tree_of_select_item s :: tree_of_query q :: nil)
    | Q_Sigma f q => Node 12 (tree_of_formula f ::  tree_of_query q :: nil)
    | Q_Gamma lf f s q => 
      Node 13 (tree_of_formula f  
               :: tree_of_select_item s 
               :: tree_of_query q 
               :: (map (fun x => Leaf (All_funterm x)) lf))
  end.
Proof.
intro q; case q; intros; apply refl_equal.
Qed.

Lemma tree_of_formula_unfold :
  forall f, tree_of_formula f =
  match f with
    | Q_Conj a f1 f2 => 
        Node (match a with Formula.And_F => 14 | Or_F => 15 end) 
             (tree_of_formula f1 :: tree_of_formula f2 :: nil)
    | Q_Not f => Node 16 (tree_of_formula f :: nil)
    | Q_Atom a => tree_of_q_atom a
  end.
Proof.
intro f; case f; intros; apply refl_equal.
Qed.

Lemma tree_of_q_atom_unfold :
  forall a, tree_of_q_atom a =
  match a with
    | Q_True => Node 17 nil
    | Q_Pred p l => Node 18 (Leaf (All_predicate p) :: map (fun x => Leaf (All_aggterm x)) l)
    | Q_Quant qtf p l q => 
      Node 
        (match qtf with 
           | Formula.Forall_F => 19
           | Exists_F => 20
         end) 
        (Leaf (All_predicate p) 
              :: tree_of_query q 
              :: (map (fun x => Leaf (All_aggterm x)) l))
    | Q_In s q => Node 21 ( tree_of_query q :: map tree_of_select s)
    | Q_Exists q => Node 22 (tree_of_query q :: nil)
  end.
Proof.
intro a; case a; intros; apply refl_equal.
Qed.

Open Scope N_scope.

Definition N_of_All (a : All) : N :=
  match a with
  | All_relname _ => 0
  | All_attribute _ => 1
  | All_predicate _ => 2 
  | All_funterm _ => 3
  | All_aggterm _ => 4
  end.

Close Scope N_scope.

Definition all_compare a1 a2 :=
   match Ncompare (N_of_All a1) (N_of_All a2) with
   | Lt => Lt
   | Gt => Gt
   | Eq =>
       match a1, a2 with
       | All_relname r1, All_relname r2 => Oset.compare ORN r1 r2
       | All_attribute a1, All_attribute a2 => Oset.compare (OAtt T) a1 a2
       | All_predicate p1, All_predicate p2 => Oset.compare OPredicate p1 p2
       | All_funterm f1, All_funterm f2 => Oset.compare (OFun (E T OSymb OAggregate)) f1 f2
       | All_aggterm a1, All_aggterm a2 => Oset.compare (OAgg (E T OSymb OAggregate)) a1 a2
       | _, _ => Eq
       end
   end.

Definition OAll : Oset.Rcd All.
split with all_compare; unfold all_compare.
(* 1/3 *)
- intros a1 a2.
  case a1; clear a1;
  (intro x1; case a2; clear a2; intro x2; simpl; try discriminate);
  try oset_compare_tac.
  + generalize (funterm_compare_eq_bool_ok x1 x2).
    case (funterm_compare x1 x2).
    * apply f_equal.
    * intros H K; apply H.
      injection K; exact (fun h => h).
    * intros H K; apply H.
      injection K; exact (fun h => h).
  + generalize (aggterm_compare_eq_bool_ok x1 x2).
    case (aggterm_compare x1 x2).
    * apply f_equal.
    * intros H K; apply H.
      injection K; exact (fun h => h).
    * intros H K; apply H.
      injection K; exact (fun h => h).
- intros a1 a2 a3.
  case a1; clear a1;
  (intro x1; case a2; clear a2; try discriminate; 
   (intro x2; case a3; clear a3; intro x3; simpl; 
    try (discriminate || intros; apply refl_equal)));
  try oset_compare_tac.
  + apply (Oset.compare_lt_trans (OFun (E T OSymb OAggregate))).
  + apply (Oset.compare_lt_trans (OAgg (E T OSymb OAggregate))).
- (* 1/1 *)
  intros a1 a2.
  case a1; clear a1; 
  (intro x1; case a2; clear a2; intro x2; simpl;
   try (discriminate || intros; apply refl_equal));
  try oset_compare_tac.
  + apply (Oset.compare_lt_gt (OFun (E T OSymb OAggregate))).
  + apply (Oset.compare_lt_gt (OAgg (E T OSymb OAggregate))).
Defined.

End Compare.

Notation equiv_env_slice := (equiv_env_slice (T := T) (OSymb := OSymb) (OAggregate := OAggregate)).
Notation equiv_env := (equiv_env (T := T) (OSymb := OSymb) (OAggregate := OAggregate)).

Ltac env_tac :=
  match goal with
    | |- equiv_env ?e ?e => apply equiv_abstract_env_refl

(* env_g *)
    | Hx : ?x1 =t= ?x2 
      |- equiv_env (env_g ?e Group_Fine (?x1 :: nil)) 
                   (env_g ?e Group_Fine (?x2 :: nil)) =>
      constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; [ | apply compare_list_t; simpl; rewrite Hx; apply refl_equal];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

    | Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env (env_g ?e ?g ?x1) (env_g ?e ?g ?x2) =>
      unfold SqlCommon.env_g; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption

    | He : equiv_env ?e1 ?e2
      |- equiv_env (env_g ?e1 ?g ?x) (env_g ?e2 ?g ?x) =>
      unfold SqlCommon.env_g; constructor 2; [ | apply He];
      simpl; repeat split; trivial;
      [apply Fset.equal_refl | 
       rewrite compare_list_t; apply Oeset.compare_eq_refl]

    | He : equiv_env ?e1 ?e2, 
      Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env (env_g ?e1 ?g ?x1) (env_g ?e2 ?g ?x2) =>
      unfold SqlCommon.env_g; constructor 2; [ | apply He];
      simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption

(* env_t *)
    | Hx : ?x1 =t= ?x2 
      |- equiv_env (env_t ?env ?x1) (env_t ?env ?x2) =>
      unfold SqlCommon.env_t; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; [ | apply compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx) 

    | He : equiv_env ?e1 ?e2 
      |- equiv_env (env_t ?e1 ?x) (env_t ?e2 ?x) =>
      unfold SqlCommon.env_t; constructor 2; [ | assumption];
      simpl; repeat split; [ | apply permut_refl];
      apply Fset.equal_refl

    | He : equiv_env ?env1 ?env2, Hx : ?x1 =t= ?x2 
      |- equiv_env (env_t ?env1 ?x1) (env_t ?env2 ?x2) =>
      unfold SqlCommon.env_t; constructor 2; [ | assumption];
      simpl; repeat split; [ | apply compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

(* env_t, env_g *)
    | |- equiv_env (env_t ?e ?x) (env_g ?e Group_Fine  (?x :: nil)) =>
      unfold SqlCommon.env_t, SqlCommon.env_g; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; [ | apply permut_refl]; 
      apply Fset.equal_refl

    | Hx : ?x1 =t= ?x2
      |- equiv_env (env_t ?e ?x1) (env_g ?e Group_Fine (?x2 :: nil)) =>
      unfold SqlCommon.env_t, SqlCommon.env_g; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; [ | rewrite compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

    | He : equiv_env ?e1 ?e2, Hx : ?x1 =t= ?x2
      |- equiv_env (env_t ?e1 ?x1) (env_g ?e2 Group_Fine (?x2 :: nil)) =>
      unfold SqlCommon.env_t, SqlCommon.env_g; constructor 2; [ | apply He];
      simpl; repeat split; [ | rewrite compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

(* env *)
    | He : equiv_env ?e1 ?e2
      |- equiv_env ((?sa1, ?g, ?x) :: ?e1) ((?sa1, ?g, ?x) :: ?e2) =>
      constructor 2; [ | assumption];
      simpl; repeat split; trivial;
      [apply Fset.equal_refl | 
       rewrite compare_list_t; apply Oeset.compare_eq_refl]

    |  Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env ((?sa1, ?g, ?x1) :: ?e1) ((?sa1, ?g, ?x2) :: ?e1) =>
       constructor 2; [ | apply equiv_env_refl];
       simpl; repeat split; [apply Fset.equal_refl | rewrite compare_list_t; assumption] 

    |  Hx : Oeset.compare (OTuple T) ?x1 ?x2 = Eq
      |- equiv_env ((?sa, ?g, ?x1 :: nil) :: ?e) ((?sa, ?g, ?x2 :: ?nil) :: ?e) =>
       constructor 2; [ | apply equiv_env_refl];
       simpl; repeat split; 
       [apply Fset.equal_refl | rewrite compare_list_t; simpl; rewrite Hx; trivial]

    | He : equiv_env ?e1 ?e2,
           Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env ((?sa1, ?g, ?x1) :: ?e1) ((?sa1, ?g, ?x2) :: ?e2) =>
      constructor 2; [ | apply He];
      simpl; repeat split; 
      [apply Fset.equal_refl | rewrite compare_list_t; assumption]

    | He : equiv_env ?e1 ?e2,
           Hx : Oeset.compare (OTuple T) ?x1 ?x2 = Eq
      |- equiv_env ((?sa, ?g, ?x1 :: nil) :: ?e1) ((?sa, ?g, ?x2 :: ?nil) :: ?e2) =>
      constructor 2; [ | apply He]; 
      simpl; repeat split; 
      [apply Fset.equal_refl 
      | rewrite compare_list_t; simpl; rewrite Hx; trivial]
            
    | He : equiv_env ?e1 ?e2,
           Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env ((?sa, ?g, ?x1) :: ?e1) (((?sa unionS (emptysetS)), ?g, ?x2) :: ?e2) => 
      constructor 2; [ | apply He];
      simpl; repeat split; 
      [ rewrite Fset.equal_spec; intro a;
        rewrite Fset.mem_union, Fset.empty_spec, Bool.orb_false_r; apply refl_equal
      | apply compare_list_t; trivial]

    | _ => fail
  end.

Lemma eval_query_eq_etc :
  forall n,
    (forall q, 
       tree_size (tree_of_query q) <= n -> 
       forall env1 env2, equiv_env env1 env2 ->
                         eval_query env1 q =BE= eval_query env2 q) /\
        
    (forall f, 
       tree_size (tree_of_formula f) <= n ->
       forall env1 env2, equiv_env env1 env2 ->
                         eval_formula env1 f = eval_formula env2 f).
Proof.
intro n; induction n as [ | n]; repeat split.
- intros q Hn; destruct q; inversion Hn.
- intros f Hn; destruct f; inversion Hn.
  destruct q; inversion Hn.
- intros q Hn env1 env2 He; destruct q as [(*sa |*) | r | o q1 q2 | q1 q2 | s q | f q | g f s q];
  rewrite Febag.nb_occ_equal; intro t.
(*  + apply refl_equal. *)
  + apply refl_equal. 
  + apply refl_equal.
  + rewrite 2 (eval_query_unfold _ (Q_Set _ _ _)).
    assert (IH1 : eval_query env1 q1 =BE= eval_query env2 q1).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 : eval_query env1 q2 =BE= eval_query env2 q2).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    case (sort q1 =S?= sort q2); [ | apply refl_equal].
    destruct o; simpl.
    * rewrite 2 Febag.nb_occ_union, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_union_max, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_inter, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_diff, IH1, IH2; apply refl_equal.
  + rewrite 2 (eval_query_unfold _ (Q_Join _ _)).
    assert (IH1 : eval_query env1 q1 =BE= eval_query env2 q1).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 : eval_query env1 q2 =BE= eval_query env2 q2).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    rewrite 2 Febag.nb_occ_mk_bag; unfold Data.natural_join_list.
    rewrite 2 Data.nb_occ_theta_join_list; simpl Data.projection; simpl Data.combine; simpl Data.compatible.
    apply f_equal; apply _permut_size with (fun x y => x =t= y).
    * intros a1 a2 Ha1 Ha2 Ha.
      do 2 (rewrite (Oeset.compare_eq_2 _ _ _ _ (mk_tuple_id T _ _ _ (Fset.equal_refl _ _))),
              Oeset.compare_eq_refl, Nat.mul_1_l).
      {
        apply _permut_size with (fun x y => x =t= y).
        - intros b1 b2 Hb1 Hb2 Hb.
          rewrite <- (join_compatible_tuple_eq _ _ _ _ _ Ha Hb).
          rewrite <- (Oeset.compare_eq_1 _ _ _ _ (join_tuple_eq _ base.nullval base.nullval _ _ _ _ Ha Hb)).
          apply refl_equal.
        - apply permut_refl_alt; apply Febag.elements_spec1; rewrite Febag.nb_occ_equal.
          apply IH2.
      }
    * apply permut_refl_alt; apply Febag.elements_spec1; rewrite Febag.nb_occ_equal.
      apply IH1.
  + rewrite 2 (eval_query_unfold _ (Q_Pi _ _)).
    assert (IH : eval_query env1 q =BE= eval_query env2 q).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
    * intros x1 x2 Hx; apply projection_eq; env_tac.
    * intro x; apply permut_nb_occ.
      apply permut_refl_alt; apply Febag.elements_spec1; apply IH.
  + rewrite 2 (eval_query_unfold _ (Q_Sigma _ _)).
    assert (IHq : eval_query env1 q =BE= eval_query env2 q).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    assert (IHf : forall env1 env2, equiv_env env1 env2 -> 
                                    eval_formula env1 f = eval_formula env2 f).
    {
      apply (proj2 IHn).
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    rewrite 2 Febag.nb_occ_filter.
    * {
        apply f_equal2.
        - rewrite Febag.nb_occ_equal in IHq; apply IHq.
        - apply if_eq; [ | intros; apply refl_equal | intros; apply refl_equal].
          apply IHf; env_tac.
      }
    * intros u1 u2 _ Hu; apply IHf; env_tac.
    * intros u1 u2 _ Hu; apply IHf; env_tac.
  + rewrite 2 (eval_query_unfold _ (Q_Gamma _ _ _ _)).
    rewrite 2 Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3 (OLTuple T)).
    * intros l1 l2 Hl; apply projection_eq; env_tac.
    * {
        intro l; rewrite 2 Oeset.nb_occ_filter.
        - apply if_eq.
          + apply (proj2 IHn).
            * rewrite tree_of_query_unfold in Hn; simpl in Hn.
              refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
              apply le_plus_l.
            * env_tac.
          + intro Hl; unfold make_groups.
            apply permut_nb_occ; apply permut_refl_alt; apply partition_list_expr_eq_alt.
            * clear Hn Hl.
              induction g as [ | x1 g]; [constructor 1 | constructor 2; [ | apply IHg]].
              intros y1 y2 Hy; apply interp_funterm_eq; env_tac.
            * apply permut_refl_alt; apply Febag.elements_spec1.
              apply (proj1 IHn); [ | assumption].
              rewrite tree_of_query_unfold in Hn; simpl in Hn.
              refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
              refine (le_trans _ _ _ _ (le_plus_r _ _)).
              apply le_S.
              refine (le_trans _ _ _ _ (le_plus_r _ _)).
              apply le_plus_l.
          + intros; apply refl_equal.
        - intros x1 x2 _ Hx; apply (proj2 IHn).
          + rewrite tree_of_query_unfold in Hn; simpl in Hn.
            refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
          + env_tac.
        - intros x1 x2 _ Hx; apply (proj2 IHn).
          + rewrite tree_of_query_unfold in Hn; simpl in Hn.
            refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
          + env_tac.
      }
- intros f Hn env1 env2 He.
  destruct f as [a f1 f2 | f | [ | p l | qtf p l q | s q | q]].
  + assert (IHf1 : forall env1 env2, equiv_env env1 env2 -> 
                                    eval_formula env1 f1 = eval_formula env2 f1).
    {
      apply (proj2 IHn).
      rewrite tree_of_formula_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IHf2 : forall env1 env2, equiv_env env1 env2 -> 
                                    eval_formula env1 f2 = eval_formula env2 f2).
    {
      apply (proj2 IHn).
      rewrite tree_of_formula_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite 2 (eval_formula_unfold _ (Q_Conj _ _ _)).
    destruct a; (apply f_equal2; [apply IHf1 | apply IHf2]; assumption).
  + rewrite 2 (eval_formula_unfold _ (Q_Not _)); apply f_equal.
    apply (proj2 IHn); [ | assumption].
    rewrite tree_of_formula_unfold in Hn; simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_plus_l.
  + apply refl_equal.
  + rewrite 2 (eval_formula_unfold _ (Q_Atom _)), 2 eval_q_atom_unfold.
    apply f_equal; rewrite <- map_eq.
    intros; apply interp_aggterm_eq; assumption.
  + rewrite 2 (eval_formula_unfold _ (Q_Atom _)), 2 eval_q_atom_unfold.
    apply (Formula.interp_quant_eq (OTuple T)).
    * intro a; rewrite <- 2 Febag.mem_unfold.
      apply Febag.mem_eq_2.
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_formula_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S; apply le_plus_l.
    * intros x1 x2 Hx1 Hx; apply f_equal.
      {
        apply f_equal2.
        - rewrite <- map_eq.
          intros a Ha; apply interp_aggterm_eq; assumption.
        - rewrite tuple_eq in Hx.
          rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)), <- map_eq.
          intros; apply (proj2 Hx).
      }
  + rewrite 2 (eval_formula_unfold _ (Q_Atom _)), 2 eval_q_atom_unfold.
    apply Febag.mem_eq.
    * apply (proj1 IHn); [ | assumption].
      rewrite tree_of_formula_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * apply projection_eq; assumption.
  + rewrite 2 (eval_formula_unfold _ (Q_Atom _)), 2 eval_q_atom_unfold.
    apply f_equal.
    rewrite 2 Febag.is_empty_spec.
    apply Febag.equal_eq_1.
    apply (proj1 IHn); [ | assumption].
    rewrite tree_of_formula_unfold in Hn; simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_plus_l.
Qed.

Lemma eval_query_eq :
  forall q env1 env2, equiv_env env1 env2 -> eval_query env1 q =BE= eval_query env2 q.
Proof.
intros q env1 env2 He.
apply (proj1 (eval_query_eq_etc _) _ (le_n _) _ _ He).
Qed.

Lemma eval_formula_eq :    
  forall f env1 env2, equiv_env env1 env2 -> eval_formula env1 f = eval_formula env2 f.
Proof.
intros f env1 env2 He.
apply (proj2 (eval_query_eq_etc _) _ (le_n _) _ _ He).
Qed.


Require Import HighLevelSpec.
Notation "b '=R=' l" := 
  (forall t, Febag.nb_occ BTupleT t b = Oeset.nb_occ (OTuple T) t l) (at level 70, no associativity).

Lemma Q_Sigma_is_a_filter_op : 
  forall env f, 
    is_a_filter_op 
      (OTuple T) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (fun t => eval_formula (env_t env t) f)
      (fun q => Q_Sigma f q).
Proof.
intros env f q t.
rewrite <- 2 Febag.nb_occ_elements, eval_query_unfold, Febag.nb_occ_filter.
- apply refl_equal.
- intros; apply eval_formula_eq; env_tac.
Qed.

Lemma Q_Sigma_is_computable_by_any_filter_op :
  forall (bagA bagA' : Type) 
         (elementsA : bagA -> list (tuple T)) (elementsA' : bagA' -> list (tuple T))
         flt env f q, 
    let eval_f := fun t => eval_formula (env_t env t) f in
    is_a_filter_op (OTuple T) elementsA elementsA' eval_f flt ->
    forall q', eval_query env q =R= elementsA q' ->
      eval_query env (Q_Sigma f q) =R= elementsA' (flt q').
Proof.
intros bagA bagA' elementsA elementsA' flt env f q eval_f HH cursor_q Hq' t.
unfold is_a_filter_op in HH.
rewrite eval_query_unfold, Febag.nb_occ_filter, Hq', HH.
- unfold eval_f; apply refl_equal.
- intros u1 u2 _ Hu; apply eval_formula_eq; env_tac.
Qed.

Lemma Q_Pi_is_a_map_op :
  forall env s, 
    let eval_s t := projection_ (env_t env t) (Select_List s) base.nullval in
    let Q_Pi_s q := Q_Pi s q in
    is_a_map_op 
      (OTuple T) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      eval_s Q_Pi_s.
Proof.
intros env s eval_s Q_Pi_s.
unfold Q_Pi_s, eval_s.
intros q t.
rewrite <- Febag.nb_occ_elements, eval_query_unfold.
unfold Febag.map; rewrite Febag.nb_occ_mk_bag. apply refl_equal.
Qed.

Lemma Q_Join_is_a_join_op : 
  forall env s1 s2, 
    let Q_Join q1 q2 := Q_Join q1 q2 in
    is_a_join_op
      (OTuple T) (OTuple T) (OTuple T) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (fun q => Febag.elements BTupleT (eval_query env q)) 
      (A T) 
      (support T) 
      (support T) 
      (support T) 
      (fun t => mk_tuple T s1 (dot T t) base.nullval) 
      (fun t => mk_tuple T s2 (dot T t) base.nullval) s1 s2 Q_Join.
Proof.
intros env s1 s2 Q_Join.
rewrite is_a_join_op_is_a_join_op_alt.
unfold is_a_join_op_alt, Q_Join; intros q1 q2 Hq1 Hq2.
rewrite eval_query_unfold; intro t.
rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag.
rewrite (Data.nb_occ_natural_join_list _ _ (build_data T)
           (Febag.elements BTupleT (eval_query env q1)) 
           (Febag.elements BTupleT (eval_query env q2)) s1 s2).
- apply refl_equal.
- intros t1 Ht1; simpl.
  apply Hq1.
  rewrite <- Oeset.nb_occ_diff_0_pos.
  apply Oeset.mem_nb_occ.
  rewrite <- Febag.mem_unfold; apply Febag.in_elements_mem; assumption.
- intros t12 Ht2; simpl.
  apply Hq2.
  rewrite <- Oeset.nb_occ_diff_0_pos.
  apply Oeset.mem_nb_occ.
  rewrite <- Febag.mem_unfold; apply Febag.in_elements_mem; assumption.
Qed.

Lemma Q_Join_is_computable_by_any_join_op :
  forall (bagA1 bagA2 bagA : Type) 
         (elementsA1 : bagA1 -> list (tuple T)) 
         (elementsA2 : bagA2 -> list (tuple T)) 
         (elementsA : bagA -> list (tuple T)) 
         j env q1 q2,
    is_a_join_op 
      (OTuple T) (OTuple T) (OTuple T) 
      elementsA1 elementsA2 elementsA _ 
      (support T) 
      (support T) 
      (support T) 
      (fun t => mk_tuple T (sort q1) (dot T t) base.nullval) 
      (fun t => mk_tuple T (sort q2) (dot T t) base.nullval) (sort q1) (sort q2) j ->
    let eval_q1 := eval_query env q1 in
    let eval_q2 := eval_query env q2 in
    (forall t1, t1 inBE eval_q1 -> support T t1 =S= sort q1) ->
    (forall t2, t2 inBE eval_q2 -> support T t2 =S= sort q2) ->
    forall q1', eval_query env q1 =R= elementsA1 q1' ->
    forall q2', eval_query env q2 =R= elementsA2 q2' -> 
    eval_query env (Q_Join q1 q2) =R= elementsA (j q1' q2').
Proof.
intros bagA1 bagA2 bagA elementsA1 elementsA2 elementsA 
       j env q1 q2 H eval_q1 eval_q2 H1 H2 q1' Hq1 q2' Hq2.
rewrite is_a_join_op_is_a_join_op_alt in H.
unfold is_a_join_op_alt in H.
rewrite eval_query_unfold; intro t.
rewrite Febag.nb_occ_mk_bag.
rewrite (Data.nb_occ_natural_join_list _ _ (build_data T)
           (Febag.elements BTupleT (eval_query env q1)) 
           (Febag.elements BTupleT (eval_query env q2)) (sort q1) (sort q2)).
- rewrite <- 2 Febag.nb_occ_elements, Hq1, Hq2, H.
  + apply refl_equal.
  + intros t1 Ht1; apply H1.
    apply Febag.nb_occ_mem; rewrite Hq1.
    rewrite Oeset.nb_occ_diff_0_pos; assumption.
  + intros t2 Ht2; apply H2; apply Febag.nb_occ_mem; rewrite Hq2.
    rewrite Oeset.nb_occ_diff_0_pos; assumption.
- intros t1 Ht1; apply H1; apply Febag.in_elements_mem; assumption.
- intros t2 Ht2; apply H2; apply Febag.in_elements_mem; assumption.
Qed.
 
Lemma Q_Sigma_Join_is_computable_by_any_filter_join_op :
  forall (bagA1 bagA2 bagA : Type) 
         (elementsA1 : bagA1 -> list (tuple T)) 
         (elementsA2 : bagA2 -> list (tuple T)) 
         (elementsA : bagA -> list (tuple T)) 
         j env f q1 q2,

    let eval_f := fun t => eval_formula (env_t env t) f in
    is_a_filter_join_op 
      (OTuple T) (OTuple T) (OTuple T) 
      elementsA1 elementsA2 elementsA _ 
      (support T) 
      (support T) 
      (support T) 
      (fun t => mk_tuple T (sort q1) (dot T t) base.nullval) 
      (fun t => mk_tuple T (sort q2) (dot T t) base.nullval) eval_f (sort q1) (sort q2) j ->
    let eval_q1 := eval_query env q1 in
    let eval_q2 := eval_query env q2 in
    (forall t1, t1 inBE eval_q1 -> support T t1 =S= sort q1) ->
    (forall t2, t2 inBE eval_q2 -> support T t2 =S= sort q2) ->
    forall q1', eval_query env q1 =R= elementsA1 q1' ->
    forall q2', eval_query env q2 =R= elementsA2 q2' -> 
    eval_query env (Q_Sigma f (Q_Join q1 q2)) =R= elementsA (j q1' q2').
Proof.
intros bagA1 bagA2 bagA elementsA1 elementsA2 elementsA 
       j env f q1 q2 eval_f H eval_q1 eval_q2 H1 H2 q1' Hq1 q2' Hq2.
unfold is_a_filter_join_op in H.
assert (H' :  (forall t : tuple T,
       0 < Oeset.nb_occ (OTuple T) t (elementsA (j q1' q2')) ->
       support T t =S= (sort q1 unionS sort q2)) /\
      (forall t : tuple T,
       support T t =S= (sort q1 unionS sort q2) ->
       Oeset.nb_occ (OTuple T) t (elementsA (j q1' q2')) =
       Oeset.nb_occ (OTuple T) (mk_tuple T (sort q1) (dot T t) base.nullval) (elementsA1 q1') *
       Oeset.nb_occ (OTuple T) (mk_tuple T (sort q2) (dot T t) base.nullval) (elementsA2 q2') *
       (if eval_f t then 1 else 0))).
{
  apply H.
  - intros t Ht; apply H1.
    apply Febag.nb_occ_mem; rewrite Hq1.
    rewrite Oeset.nb_occ_diff_0_pos; assumption.
  - intros t Ht; apply H2.
    apply Febag.nb_occ_mem; rewrite Hq2.
    rewrite Oeset.nb_occ_diff_0_pos; assumption.
}
rewrite eval_query_unfold; intro t.
rewrite Febag.nb_occ_filter; [ | intros; apply eval_formula_eq; env_tac].
case_eq (support T t =S?= (sort q1 unionS sort q2)); intro Ht.
- rewrite (proj2 H' _ Ht), eval_query_unfold.
  rewrite Febag.nb_occ_mk_bag.
  rewrite (Data.nb_occ_natural_join_list _ _ (build_data T)
             (Febag.elements BTupleT (eval_query env q1)) 
             (Febag.elements BTupleT (eval_query env q2)) (sort q1) (sort q2)).
  + simpl Data.projection; simpl Data.support; simpl Data.att; simpl Data.OAtt; simpl Data.FAtt.
    rewrite Ht, N.mul_1_r. 
    apply f_equal2; [ | apply refl_equal].
    rewrite <- 2 Febag.nb_occ_elements, Hq1, Hq2; apply refl_equal.
  + intros t1 Ht1; apply H1.
    rewrite Febag.mem_unfold; apply Oeset.in_mem_bool; apply Ht1.
  + intros t2 Ht2; apply H2.
    rewrite Febag.mem_unfold; apply Oeset.in_mem_bool; apply Ht2.
- assert (Kt : Oeset.nb_occ (OTuple T) t (elementsA (j q1' q2')) = 0).
  {
    case_eq (Oeset.nb_occ (OTuple T) t (elementsA (j q1' q2'))); [trivial | ].
    intros p Hp; rewrite (proj1 H') in Ht; [discriminate Ht | ].
    rewrite Hp; unfold N.lt; apply refl_equal.
  }
  rewrite Kt.
  case_eq (Febag.nb_occ BTupleT t (eval_query env (Q_Join q1 q2))).
  + intros; rewrite N.mul_0_l; trivial.
  + intros p Hp.
    assert (Jt : t inBE (eval_query env (Q_Join q1 q2))).
    {
     rewrite Febag.mem_unfold.
     apply Oeset.nb_occ_mem; rewrite <- Febag.nb_occ_elements, Hp.
     discriminate.
    }
    rewrite eval_query_unfold, Data.natural_join_list_unfold in Jt.
    rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Jt.
    destruct Jt as [t' [Jt Ht']]; rewrite Data.theta_join_list_unfold in Ht'.
    rewrite in_flat_map in Ht'.
    destruct Ht' as [t1 [Ht1 Ht']]; unfold Data.d_join_list in Ht'.
    rewrite in_map_iff in Ht'.
    destruct Ht' as [t2 [Ht' Ht2]].
    rewrite filter_In in Ht2.
    destruct Ht2 as [Ht2 H12].
    rewrite tuple_eq in Jt; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Jt)) in Ht.
    subst t'; unfold join_tuple in Ht; simpl in Ht; unfold join_tuple in Ht.
    rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _ _)) in Ht.
    assert (Abs : (support T t1 unionS support T t2) =S= (sort q1 unionS sort q2)).
    {
      apply Fset.union_eq.
      - apply H1; apply Febag.in_elements_mem; assumption.
      - apply H2; apply Febag.in_elements_mem; assumption.
    }
    rewrite Abs in Ht; discriminate Ht.
Qed.

Lemma Q_Gamma_is_a_grouping_op :
  forall env g f s ,
    let eval_s l := projection_ (env_g env (Group_By g) l) (Select_List s) base.nullval in
    let eval_f l := eval_formula (env_g env (Group_By g) l) f in
    let mk_grp g q :=
        partition_list_expr 
          (FVal T) (Febag.elements _ (eval_query env q))
          (map (fun f t => SqlCommon.interp_funterm_ interp_symb (SqlCommon.env_t env t) f) g) in
    let Q_Gamma g f s q := eval_query env (Q_Gamma g f s q) in
    is_a_grouping_op 
      (OTuple T) 
      (Febag.elements BTupleT) mk_grp g eval_f eval_s (Q_Gamma g f s).
Proof.
intros env g f s eval_s eval_f mk_grp Q_Gamma q t.
unfold Q_Gamma; rewrite eval_query_unfold, <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag.
unfold eval_s, eval_f, mk_grp, make_groups.
apply refl_equal.
Qed.

Lemma Q_Gamma_is_computable_by_any_group_op :
  forall (bagA bagA': Type) 
         (elementsA : bagA -> list (tuple T)) 
         (elementsA' : bagA' -> list (tuple T)) 
         grp env g f s q,
    let eval_f l := eval_formula (env_g env (Group_By g) l) f in
    let eval_s l := projection_ (env_g env (Group_By g) l) (Select_List s) base.nullval in
    let mk_grp g l := make_groups interp_symb env (elementsA l) (Group_By g) in
    is_a_grouping_op (OTuple T) elementsA' mk_grp g eval_f eval_s grp ->
    forall q', eval_query env q =R= elementsA q' ->
               eval_query env (Q_Gamma g f s q) =R= elementsA' (grp q').
Proof.
intros bagA bagA' elementsA elementsA' grp env g f s q eval_f eval_s mk_grp H q' Hq t.
rewrite eval_query_unfold, H, Febag.nb_occ_mk_bag.
unfold eval_s, eval_f, mk_grp.
apply (Oeset.nb_occ_map_eq_2_3 (OLTuple T)).
- intros l1 l2 Hl; apply projection_eq; env_tac.
- intro l; rewrite 2 Oeset.nb_occ_filter.
  + apply if_eq; trivial.
    intros _.
    apply permut_nb_occ; apply permut_refl_alt; apply partition_list_expr_eq_alt.
    * clear eval_f eval_s mk_grp H.
      induction g as [ | fe g]; simpl; [constructor 1 | constructor 2; [ | apply IHg]].
      intros x y _H.
      apply interp_funterm_eq; env_tac.
    * apply nb_occ_permut; intro x.
      rewrite <- Hq, Febag.nb_occ_elements; apply refl_equal.
  + intros; apply eval_formula_eq; env_tac.
  + intros; apply eval_formula_eq; env_tac.
Qed.

Lemma eval_f_eq :
  forall env f, 
    let eval_f := fun t => eval_formula (env_t env t) f in
    forall t1 t2, t1 =t= t2 -> eval_f t1 = eval_f t2.
Proof.
intros env f eval_f t1 t2 Ht; unfold eval_f.
apply eval_formula_eq; env_tac.
Qed.

End Sec.
