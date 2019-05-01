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
        FiniteSet FiniteBag FiniteCollection.

Module Expression.

Record Rcd (attribute value : Type) (OAtt : Oset.Rcd attribute) (A : Fset.Rcd OAtt) (OVal : Oset.Rcd value) : Type :=
  mk_R
    {
      symb : Type;
      aggregate : Type;
      OSymb : Oset.Rcd symb;
      OAggregate : Oset.Rcd aggregate;
      default_value : attribute -> value
    }.

End Expression.

Section Sec.
Hypotheses attribute value : Type.
Hypothesis OAtt : Oset.Rcd attribute.
Hypothesis A : Fset.Rcd OAtt.
Hypothesis OVal : Oset.Rcd value.


Hypothesis E : Expression.Rcd A OVal.

Notation symb := (Expression.symb E).
Notation aggregate := (Expression.aggregate E).
Notation OSymb := (Expression.OSymb E).
Notation OAggregate := (Expression.OAggregate E).
Notation default_value := (Expression.default_value E).

Inductive symbol : Type :=
  | Constant : value -> symbol
  | Dot : attribute -> symbol
  | Symbol : symb -> symbol.

Definition symbol_compare (f1 f2 : symbol) : comparison :=
  match f1, f2 with
    | Constant c1, Constant c2 => Oset.compare OVal c1 c2
    | Constant _, _ => Lt
    | Dot _, Constant _ => Gt
    | Dot a1, Dot a2 => Oset.compare OAtt a1 a2
    | Dot _, Symbol _ => Lt
    | Symbol _, Constant _ => Gt
    | Symbol _, Dot _ => Gt
    | Symbol f1, Symbol f2 => Oset.compare OSymb f1 f2
  end.

Lemma symbol_compare_eq_bool_ok :
 forall a1 a2,
   match symbol_compare a1 a2 with
     | Eq => a1 = a2
     | Lt => a1 <> a2
     | Gt => a1 <> a2
   end.
Proof.
intros a1 a2; 
  destruct a1 as [c1 | a1 | f1]; 
  destruct a2 as [c2 | a2 | f2]; simpl; try (oset_compare_tac || discriminate).
Qed.

Definition OSymbol : Oset.Rcd symbol.
split with symbol_compare.
- apply symbol_compare_eq_bool_ok.
- intros [c1 | a1 | f1] [c2 | a2 | f2] [c3 | a3 | f3];
  simpl; trivial; try discriminate; try apply Oset.compare_lt_trans.
- intros [c1 | a1 | f1] [c2 | a2 | f2];
  simpl; trivial; try discriminate; try apply Oset.compare_lt_gt.
Defined.

Inductive funterm : Type :=
| F_Constant : value -> funterm
| F_Dot : attribute -> funterm
| F_Expr : symb -> list funterm -> funterm.

Inductive aggterm : Type := 
| A_Expr : funterm -> aggterm
| A_agg : aggregate -> funterm -> aggterm
| A_fun : symb -> list aggterm -> aggterm.

Fixpoint size_funterm (t : funterm) : nat :=
  match t with
    | F_Constant _
    | F_Dot _ => 1%nat
    | F_Expr _ l => S (list_size size_funterm l)
  end.

Fixpoint funterm_compare (f1 f2 : funterm) : comparison :=
  match f1, f2 with
    | F_Constant c1, F_Constant c2 => Oset.compare OVal c1 c2
    | F_Constant _, _ => Lt
    | F_Dot _, F_Constant _ => Gt
    | F_Dot a1, F_Dot a2 => Oset.compare OAtt a1 a2
    | F_Dot _, F_Expr _ _ => Lt
    | F_Expr _ _, F_Constant _ => Gt
    | F_Expr _ _, F_Dot _ => Gt
    | F_Expr f1 l1, F_Expr f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA funterm_compare) (f1, l1) (f2, l2)
  end.

Lemma funterm_compare_eq_bool_ok :
 forall a1 a2,
   match funterm_compare a1 a2 with
     | Eq => a1 = a2
     | Lt => a1 <> a2
     | Gt => a1 <> a2
   end.
Proof.
intro a1; set (n1 := size_funterm a1).
assert (Hn1 := le_n n1).
unfold n1 at 1 in Hn1; clearbody n1.
revert a1 Hn1; induction n1 as [ | n1].
- intros a1 Hn1; destruct a1; inversion Hn1.
- intros a1 Hn1 a2; 
  destruct a1 as [c1 | a1 | f1 l1]; 
  destruct a2 as [c2 | a2 | f2 l2]; simpl; try (oset_compare_tac || discriminate).
  generalize (Oset.eq_bool_ok OSymb f1 f2).
  case (Oset.compare OSymb f1 f2).
  + intro; subst f2.
    assert (IH : match comparelA funterm_compare l1 l2 with
                   | Eq => l1 = l2
                   | Lt => l1 <> l2
                   | Gt => l1 <> l2
                 end).
    {
      apply comparelA_eq_bool_ok.
      intros a1 a2 Ha1 Ha2; apply IHn1.
      simpl in Hn1.
      refine (Le.le_trans _ _ _ (in_list_size _ _ _ Ha1) (le_S_n _ _ Hn1)).
    } 
    {
      revert IH; case (comparelA funterm_compare l1 l2).
      - apply f_equal.
      - intros Hl Kl.
        apply Hl; injection Kl; exact (fun h => h).
      - intros Hl Kl.
        apply Hl; injection Kl; exact (fun h => h).
    }
  + intros Hf Kf; apply Hf.
    injection Kf; exact (fun _ h => h).
  + intros Hf Kf; apply Hf.
    injection Kf; exact (fun _ h => h).
Qed.

Definition OFun : Oset.Rcd funterm.
split with funterm_compare.
- apply funterm_compare_eq_bool_ok.
- intro a1; set (n1 := size_funterm a1).
  assert (Hn1 := le_n n1).
  unfold n1 at 1 in Hn1; clearbody n1.
  revert a1 Hn1; 
    induction n1 as [ | n1];
    [intros a1 Hn1; destruct a1; inversion Hn1 | ].
  intros [c1 | a1 | f1 l1] Hn1 [c2 | a2 | f2 l2] [c3 | a3 | f3 l3];
  simpl; trivial; try discriminate; try oset_compare_tac.
  case_eq (Oset.compare OSymb f1 f2); intro Hf; try discriminate.
  + generalize (Oset.eq_bool_ok OSymb f1 f2); rewrite Hf.
    intro; subst f2; clear Hf.
    case_eq (Oset.compare OSymb f1 f3); intro Hf; trivial.
    apply comparelA_lt_trans.
    * intros a1 a2 a3 _ _ _ H.
      generalize (funterm_compare_eq_bool_ok a1 a2); rewrite H.
      intro; subst a2; exact (fun h => h).
    * intros a1 a2 a3 _ _ _ H.
      generalize (funterm_compare_eq_bool_ok a1 a2); rewrite H.
      intro; subst a2; exact (fun h => h).
    * intros a1 a2 a3 _ _ _ H K.
      generalize (funterm_compare_eq_bool_ok a2 a3); rewrite K.
      intro; subst a3; assumption.
    * intros a1 a2 a3 Ha1 _ _; apply IHn1.
      simpl in Hn1.
      refine (Le.le_trans _ _ _ (in_list_size _ _ _ Ha1) (le_S_n _ _ Hn1)).
  + intros _; case_eq (Oset.compare OSymb f2 f3); intro Kf; try discriminate.
    * generalize (Oset.eq_bool_ok OSymb f2 f3); rewrite Kf.
      intro; subst f3; clear Kf.
      rewrite Hf; trivial.
    * intros _; rewrite (Oset.compare_lt_trans _ _ _ _ Hf Kf).
      trivial.
- intro a1; set (n1 := size_funterm a1).
  assert (Hn1 := le_n n1).
  unfold n1 at 1 in Hn1; clearbody n1.
  revert a1 Hn1; 
    induction n1 as [ | n1];
    [intros a1 Hn1; destruct a1; inversion Hn1 | ].
  intros [c1 | a1 | f1 l1] Hn1 [c2 | a2 | f2 l2];
  simpl; trivial; try discriminate; try apply Oset.compare_lt_gt.
  rewrite (Oset.compare_lt_gt OSymb f2 f1).
  case_eq (Oset.compare OSymb f1 f2); intro Hf; simpl; trivial.
  apply comparelA_lt_gt.
  intros a1 a2 Ha1 _; apply IHn1.
  simpl in Hn1.
  refine (Le.le_trans _ _ _ (in_list_size _ _ _ Ha1) (le_S_n _ _ Hn1)).
Defined.

Definition FFun := Fset.build OFun.

Fixpoint size_aggterm (t : aggterm) : nat :=
  match t with
    | A_Expr f 
    | A_agg _ f => S (size_funterm f)
    | A_fun _ l => S (list_size size_aggterm l)
  end.

Fixpoint aggterm_compare (a1 a2 : aggterm) : comparison :=
  match a1, a2 with
    | A_Expr f1, A_Expr f2 => Oset.compare OFun f1 f2
    | A_Expr _, _ => Lt
    | A_agg _ _, A_Expr _ => Gt
    | A_agg a1 f1, A_agg a2 f2 =>
      compareAB (Oset.compare OAggregate) (Oset.compare OFun)
                (a1, f1) (a2, f2)
    | A_agg _ _, A_fun _ _ => Lt
    | A_fun _ _, A_Expr _ => Gt
    | A_fun _ _, A_agg _ _ => Gt
    | A_fun f1 l1, A_fun f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA aggterm_compare) (f1, l1) (f2, l2)
  end.

Lemma aggterm_compare_eq_bool_ok :
 forall a1 a2,
   match aggterm_compare a1 a2 with
     | Eq => a1 = a2
     | Lt => a1 <> a2
     | Gt => a1 <> a2
   end.
Proof.
intro a1; set (n1 := size_aggterm a1).
assert (Hn1 := le_n n1).
unfold n1 at 1 in Hn1; clearbody n1.
revert a1 Hn1; induction n1 as [ | n1].
- intros a1 Hn1; destruct a1; inversion Hn1.
- intros a1 Hn1 a2; 
  destruct a1 as [c1 | a1 f1 | f1 l1]; 
  destruct a2 as [c2 | a2 f2 | f2 l2]; try discriminate.
  + generalize (Oset.eq_bool_ok OFun c1 c2). 
    unfold aggterm_compare.
    case (Oset.compare OFun c1 c2).
    * apply f_equal.
    * intros Hc Kc.
      apply Hc; injection Kc; exact (fun h => h).
    * intros Hc Kc.
      apply Hc; injection Kc; exact (fun h => h).
  + unfold aggterm_compare.
    generalize (Oset.eq_bool_ok OAggregate a1 a2). 
    unfold compareAB.
    case (Oset.compare OAggregate a1 a2).
    * intro; subst a2.
      generalize (Oset.eq_bool_ok OFun f1 f2). 
      {
        case (Oset.compare OFun f1 f2).
        - apply f_equal. 
        - intros Hc Kc.
          apply Hc; injection Kc; exact (fun h => h).
        - intros Hc Kc.
          apply Hc; injection Kc; exact (fun h => h).
      }
    * intros Hc Kc.
      apply Hc; injection Kc; exact (fun _ h => h).
    * intros Hc Kc.
      apply Hc; injection Kc; exact (fun _ h => h).
  + simpl.
    generalize (Oset.eq_bool_ok OSymb f1 f2).
    case (Oset.compare OSymb f1 f2). 
    * intro; subst f2.
      assert (IH : match comparelA aggterm_compare l1 l2 with
                     | Eq => l1 = l2
                     | Lt => l1 <> l2
                     | Gt => l1 <> l2
                   end).
      {
        apply comparelA_eq_bool_ok.
        intros a1 a2 Ha1 Ha2; apply IHn1.
        simpl in Hn1.
        refine (Le.le_trans _ _ _ (in_list_size _ _ _ Ha1) (le_S_n _ _ Hn1)).
      } 
      {
        revert IH; case (comparelA aggterm_compare l1 l2).
        - apply f_equal.
        - intros Hl Kl.
            apply Hl; injection Kl; exact (fun h => h).
        - intros Hl Kl.
          apply Hl; injection Kl; exact (fun h => h).
      }
    * intros Hf Kf; apply Hf.
      injection Kf; exact (fun _ h => h).
    * intros Hf Kf; apply Hf.
      injection Kf; exact (fun _ h => h).
Qed.

Definition OAgg : Oset.Rcd aggterm.
split with aggterm_compare.
- apply aggterm_compare_eq_bool_ok.
- intro a1; set (n1 := size_aggterm a1).
  assert (Hn1 := le_n n1).
  unfold n1 at 1 in Hn1; clearbody n1.
  revert a1 Hn1; 
    induction n1 as [ | n1];
    [intros a1 Hn1; destruct a1; inversion Hn1 | ].
  intros [c1 | a1 f1 | f1 l1] Hn1 [c2 | a2 f2| f2 l2] [c3 | a3 f3 | f3 l3];
  simpl; trivial; try discriminate; try apply Oset.compare_lt_trans.
  + apply (Oset.compare_lt_trans OFun c1 c2 c3).
  + case_eq (Oset.compare OAggregate a1 a2); intro Ha; try discriminate.
    * generalize (Oset.eq_bool_ok OAggregate a1 a2); rewrite Ha.
      intro; subst a2; clear Ha.
      simpl; intro Hf. 
      case_eq (Oset.compare OAggregate a1 a3); intro Ha; trivial; try discriminate.
      revert Hf; apply (Oset.compare_lt_trans OFun f1 f2 f3).
    * {
        intros _; 
        case_eq (Oset.compare OAggregate a2 a3); intro Ka; trivial; try discriminate.
        - rewrite (Oset.compare_lt_eq_trans _ _ _ _ Ha Ka); trivial.
        - rewrite (Oset.compare_lt_trans _ _ _ _ Ha Ka); trivial.
      } 
  + case_eq (Oset.compare OSymb f1 f2); intro Hf.
    * generalize (Oset.eq_bool_ok OSymb f1 f2); 
      rewrite Hf; clear Hf; intro; subst f2.
      case_eq (Oset.compare OSymb f1 f3); intro Kf; trivial.
      {
        apply comparelA_lt_trans.
        - do 6 intro; intro Ha.
          generalize (aggterm_compare_eq_bool_ok a1 a2).
          rewrite Ha; intro; subst a2.
          exact (fun h => h).
        - do 6 intro; intro Ha.
          generalize (aggterm_compare_eq_bool_ok a1 a2).
          rewrite Ha; intro; subst a2.
          exact (fun h => h).
        - do 6 intro; intros Ha Ka.
          generalize (aggterm_compare_eq_bool_ok a2 a3).
          rewrite Ka; intro; subst a3.
          assumption.
        - do 6 intro; apply IHn1.
          simpl in Hn1.
          refine (Le.le_trans _ _ _ (in_list_size _ _ _ H) (le_S_n _ _ Hn1)).
      }
    * {
        intros _;
        case_eq (Oset.compare OSymb f2 f3); intro Kf.
        - generalize (Oset.eq_bool_ok OSymb f2 f3); 
          rewrite Kf; clear Kf; intro; subst f3.
          rewrite Hf; trivial.
        - intros _; rewrite (Oset.compare_lt_trans OSymb _ _ _ Hf Kf).
          trivial.
        - intro Abs; discriminate Abs.
      } 
    * intro Abs; discriminate Abs.
- intro a1; set (n1 := size_aggterm a1).
  assert (Hn1 := le_n n1).
  unfold n1 at 1 in Hn1; clearbody n1.
  revert a1 Hn1; 
    induction n1 as [ | n1];
    [intros a1 Hn1; destruct a1; inversion Hn1 | ].
  intros [c1 | a1 f1 | f1 l1] Hn1 [c2 | a2 f2 | f2 l2];
  simpl; trivial; try discriminate; try apply Oset.compare_lt_gt. 
 + apply (Oset.compare_lt_gt OFun c1 c2).
 + rewrite (Oset.compare_lt_gt OAggregate a2 a1).
   destruct (Oset.compare OAggregate a1 a2); trivial.
   apply (Oset.compare_lt_gt OFun f1 f2).
 + rewrite (Oset.compare_lt_gt OSymb f2 f1).
   destruct (Oset.compare OSymb f1 f2); trivial.
   simpl CompOpp.
   apply comparelA_lt_gt.
   intros a1 a2 Ha1 Ha2; apply IHn1.
   simpl in Hn1.
   refine (Le.le_trans _ _ _ (in_list_size _ _ _ Ha1) (le_S_n _ _ Hn1)).
Defined.

Definition FAgg := Fset.build OAgg.

Fixpoint att_of_funterm (e : funterm) :=
  match e with
    | F_Constant _ => emptysetS
    | F_Dot a => Fset.singleton A a
    | F_Expr _ l => Fset.Union A (List.map att_of_funterm l)
  end.

Fixpoint att_of_aggterm (ag : aggterm) :=
  match ag with
    | A_Expr e 
    | A_agg _ e => att_of_funterm e
    | A_fun _ l => Fset.Union A (List.map att_of_aggterm l)
  end.

Lemma att_of_funterm_unfold :
  forall e, att_of_funterm e =
  match e with
    | F_Constant _ => emptysetS
    | F_Dot a => Fset.singleton A a
    | F_Expr _ l => Fset.Union A (List.map att_of_funterm l)
  end.
Proof.
intros e; case e; intros; apply refl_equal.
Qed.

Lemma att_of_aggterm_unfold :
  forall ag, att_of_aggterm ag =
             match ag with
               | A_Expr e 
               | A_agg _ e => att_of_funterm e
               | A_fun _ l => Fset.Union A (List.map att_of_aggterm l)
             end.
Proof.
intro ag; case ag; intros; apply refl_equal.
Qed.

Hypothesis interp_symb : symb -> list value -> value.
Hypothesis interp_aggregate : aggregate -> list value -> value.

(* Evaluation in an environment :-( *)

(*
Fixpoint interp_dot (B : Type) (env : list (Fset.set A * B * listT)) (a : attribute T) :=
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l1) :: env => 
      match quicksort (OTuple T) l1 with
        | nil => interp_dot env a
        | t1 :: _ => if a inS? support T t1 
                     then dot T t1 a
                     else interp_dot env a
      end
  end.
   
Lemma interp_dot_unfold :
  forall (B : Type) env a, interp_dot (B := B) env a =
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l1) :: env => 
      match quicksort (OTuple T) l1 with
        | nil => interp_dot env a
        | t1 :: _ => if a inS? support T t1 
                     then dot T t1 a
                     else interp_dot env a
      end
  end.
Proof.
intros B env a; destruct env; intros; trivial.
Qed.

Definition groups_of_env_slice (s : (setA * group_by * (list (tuple T)))) :=
  match s with
    | (_, Group_By g, _) => g
    | (sa, Group_Fine, _) => List.map (fun a => F_Dot _ _ a) ({{{sa}}})
  end.

*)
Hypothesis SEnv : Type.
Notation Env := (list SEnv).

Hypothesis interp_dot_env_slice : SEnv -> attribute -> option value. 
Hypothesis attributes_of_env_slice : SEnv -> Fset.set A.
Hypothesis groups_of_env_slice : SEnv -> list funterm.
Hypothesis unfold_env_slice : SEnv -> list SEnv.

Fixpoint interp_dot env (a : attribute) :=
  match env with
    | nil => default_value a
    | slc :: env => match interp_dot_env_slice slc a with
                      | Some v => v
                      | None => interp_dot env a
                    end
  end.
      
Lemma interp_dot_unfold :
  forall env a, interp_dot env a =
  match env with
    | nil => default_value a
    | slc :: env => match interp_dot_env_slice slc a with
                      | Some v => v
                      | None => interp_dot env a
                    end
  end.
Proof.
intros env a; case env; intros; apply refl_equal.
Qed.

Fixpoint interp_funterm env t := 
  match t with
    | F_Constant c => c
    | F_Dot a => interp_dot env a
    | F_Expr f l => interp_symb f (List.map (fun x => interp_funterm env x) l)
  end.

Lemma interp_funterm_unfold :
  forall env t, interp_funterm env t =
  match t with
    | F_Constant c => c
    | F_Dot a => interp_dot env a
    | F_Expr f l => interp_symb f (List.map (fun x => interp_funterm env x) l)
  end.
Proof.
intros env t; case t; intros; apply refl_equal.
Qed.

Fixpoint built_upon_fun g f :=
  match f with
    | F_Constant _ => true
    | F_Dot _ => Oset.mem_bool OFun f g
    | F_Expr s l => Oset.mem_bool OFun f g || forallb (built_upon_fun g) l
  end.

Definition is_a_grouping_env (sa : Fset.set A) env f :=
  built_upon_fun  (map (fun a => F_Dot a) ({{{sa}}}) ++ flat_map groups_of_env_slice env) f.

Fixpoint find_smallest_grouping_env (env : Env) f := 
  match env with
    | nil => if built_upon_fun nil f 
             then Some nil
             else None
    | slc1 :: env' => 
      match find_smallest_grouping_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_grouping_env (attributes_of_env_slice slc1) env' f
          then Some env
          else None
      end
  end.
  
Lemma find_smallest_grouping_env_unfold :
  forall env f, find_smallest_grouping_env env f =
  match env with
    | nil => if built_upon_fun nil f 
             then Some nil
             else None
    | slc1 :: env' => 
      match find_smallest_grouping_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_grouping_env (attributes_of_env_slice slc1) env' f
          then Some env
          else None
      end
  end.
Proof.
intros env f; case env; intros; apply refl_equal.
Qed.

Fixpoint interp_aggterm (env : Env) (ag : aggterm) := 
  match ag with
  | A_Expr ft => interp_funterm env ft
  | A_agg ag ft => 
    let env' := 
        if Fset.is_empty A (att_of_funterm ft)
        then Some env 
        else find_smallest_grouping_env env ft in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun f lag => interp_symb f (List.map (fun x => interp_aggterm env x) lag)
  end.

Lemma interp_aggterm_unfold :
  forall env ag, interp_aggterm env ag =
  match ag with
  | A_Expr ft => interp_funterm env ft
  | A_agg ag ft => 
    let env' := 
        if Fset.is_empty A (att_of_funterm ft)
        then Some env 
        else find_smallest_grouping_env env ft in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun f lag => interp_symb f (List.map (fun x => interp_aggterm env x) lag)
  end.
Proof.
intros env ag; case ag; intros; apply refl_equal.
Qed.

Hypothesis equiv_env_slice : SEnv -> SEnv -> Prop.

Hypothesis equiv_env_slice_refl : forall slc, equiv_env_slice slc slc.

Hypothesis equiv_env_slice_sym : 
  forall slc1 slc2, equiv_env_slice slc1 slc2 <-> equiv_env_slice slc2 slc1.

Hypothesis attributes_of_env_slice_eq :
  forall slc1 slc2, 
    equiv_env_slice slc1 slc2 -> attributes_of_env_slice slc1 =S= attributes_of_env_slice slc2.

Hypothesis unfold_env_slice_eq : 
  forall slc1 slc2, equiv_env_slice slc1 slc2 -> 
                    Forall2 equiv_env_slice (unfold_env_slice slc1) (unfold_env_slice slc2).

Hypothesis groups_of_env_slice_eq :
  forall slc1 slc2, equiv_env_slice slc1 slc2 -> 
                    forall f, In f (groups_of_env_slice slc1) <-> In f (groups_of_env_slice slc2).

Hypothesis interp_dot_env_slice_eq :
  forall a e1 e2, equiv_env_slice e1 e2 -> interp_dot_env_slice e1 a = interp_dot_env_slice e2 a.

Definition equiv_env e1 e2 := Forall2 equiv_env_slice e1 e2.

Lemma equiv_env_refl : forall e, equiv_env e e.
Proof.
intro e; unfold equiv_env; induction e as [ | slc1 e]; simpl; trivial.
constructor 2; [apply equiv_env_slice_refl | apply IHe].
Qed.

Lemma equiv_env_sym :
  forall e1 e2, equiv_env e1 e2 <-> equiv_env e2 e1.
Proof.
assert (H : forall e1 e2, equiv_env e1 e2 -> equiv_env e2 e1).
{
  intro e1; induction e1 as [ | s1 e1]; intros [ | s2 e2].
  - exact (fun h => h).
  - intro H; inversion H.
  - intro H; inversion H.
  - intro H; simpl in H.
    inversion H; subst.
    constructor 2.
    + rewrite equiv_env_slice_sym; assumption.
    + apply IHe1; assumption.
}
intros e1 e2; split; apply H.
Qed.

Lemma interp_dot_eq :
  forall a e1 e2, equiv_env e1 e2 -> interp_dot e1 a = interp_dot e2 a.
Proof.
Proof.
intros a e1; induction e1 as [ | slc1 e1]; intros [ | slc2 e2] H.
- apply refl_equal.
- inversion H.
- inversion H.
- simpl in H; inversion H; subst.
  simpl; rewrite <- (interp_dot_env_slice_eq _ H3).
  case (interp_dot_env_slice slc1 a); [intro; apply refl_equal | ].
  apply IHe1; assumption.
Qed.

Lemma interp_funterm_eq :
  forall f e1 e2, equiv_env e1 e2 -> interp_funterm e1 f = interp_funterm e2 f.
Proof.
intro f.
set (n := size_funterm f).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert f Hn.
induction n as [ | n];
  intros f Hn e1 e2 He. 
- destruct f; inversion Hn.
- destruct f as [c | a | f l].
  + apply refl_equal.
  + simpl; apply interp_dot_eq; trivial.
  + simpl; apply f_equal.
    rewrite <- map_eq.
    intros a Ha.
    apply IHn; [ | assumption].
    simpl in Hn.
    refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; apply Ha.
Qed.

Lemma built_upon_fun_incl :
  forall f g1 g2, (forall x, In x g1 -> In x g2) -> 
                  built_upon_fun g1 f = true -> built_upon_fun g2 f = true.
Proof.
intro f; set (m := size_funterm f); assert (Hm := le_n m); unfold m at 1 in Hm.
clearbody m; revert f Hm; induction m as [ | m].
- intros e Hm; destruct e; inversion Hm.
- intros e Hm g1 g2 Hg Hf; destruct e as [c | b | f1 l]; simpl; trivial.
  + rewrite Oset.mem_bool_true_iff; apply Hg.
    simpl in Hf; rewrite Oset.mem_bool_true_iff in Hf; trivial.
  + simpl in Hf; rewrite Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
    * rewrite Bool.orb_true_iff; left.
      rewrite Oset.mem_bool_true_iff; apply Hg.
      rewrite Oset.mem_bool_true_iff in Hf; trivial.
    * rewrite Bool.orb_true_iff; right.
      rewrite forallb_forall; intros x Hx.
      {
        apply IHm with g1; trivial.
        - simpl in Hm; refine (le_trans _ _ _ _ (le_S_n _ _ Hm)).
          apply in_list_size; trivial.
        - rewrite forallb_forall in Hf; apply Hf; trivial.
      }
Qed.

Lemma is_a_grouping_env_eq :
  forall e sa1 env1 sa2 env2, sa1 =S= sa2 -> equiv_env env1 env2 ->
                              is_a_grouping_env sa1 env1 e = is_a_grouping_env sa2 env2 e.
Proof.
assert (H : forall env1 env2 slc1, 
              equiv_env env1 env2 -> In slc1 env1 -> 
              exists slc2, In slc2 env2 /\ equiv_env_slice slc1 slc2).
{
  intro env1; induction env1 as [ | s1 e1]; intros [ | s2 e2] slc1 He Hs.
  - contradiction Hs.
  - inversion He.
  - inversion He.
  - simpl in He; inversion He; subst.
    simpl in Hs; destruct Hs as [Hs | Hs].
    + subst slc1; exists s2; split; [left | ]; trivial.
    + destruct (IHe1 _ _ H4 Hs) as [slc2 [K1 K2]].
      exists slc2; split; [right | ]; trivial.
}
intros e sa1 env1 sa2 env2 Hsa Henv.
unfold is_a_grouping_env; rewrite eq_bool_iff; split; 
apply built_upon_fun_incl; intros f Hf;
(destruct (in_app_or _ _ _ Hf) as [Kf | Kf]; apply in_or_app; [left | right]).
- rewrite <- (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [slc1 [H1 H2]].
  destruct (H _ _ _ Henv H1) as [slc2 [H3 H4]].
  rewrite in_flat_map; exists slc2; split; [assumption | ].
  rewrite <- (groups_of_env_slice_eq H4); assumption.
- rewrite (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [slc1 [H1 H2]].
  rewrite equiv_env_sym in Henv.
  destruct (H _ _ _ Henv H1) as [slc2 [H3 H4]].
  rewrite in_flat_map; exists slc2; split; [assumption | ].
  rewrite <- (groups_of_env_slice_eq H4); assumption.
Qed.

Lemma find_smallest_grouping_env_eq :
  forall e env1 env2, 
    equiv_env env1 env2 -> 
    match (find_smallest_grouping_env env1 e), (find_smallest_grouping_env env2 e) with
      | None, None => True
      | Some e1, Some e2 => equiv_env e1 e2
      | _, _ => False
    end.
Proof.
intros e env1; induction env1 as [ | slc1 env1]; intros [ | slc2 env2] He.
- simpl; case (built_upon_fun nil e); trivial.
- inversion He.
- inversion He.
- inversion He; subst.
  assert (IH := IHenv1 _ H4).
  simpl.
  destruct (find_smallest_grouping_env env1 e) as [l1 | ];
    destruct (find_smallest_grouping_env env2 e) as [l2 | ]; try contradiction IH.
  + assumption.
  + assert (H1 := attributes_of_env_slice_eq H2).
    rewrite <- (is_a_grouping_env_eq e _ _ H1 H4).
    case (is_a_grouping_env (attributes_of_env_slice slc1) env1 e).
    * constructor 2; trivial.
    * trivial.
Qed.
    
Lemma interp_aggterm_eq :
  forall e env1 env2, equiv_env env1 env2 -> interp_aggterm env1 e = interp_aggterm env2 e.
Proof.
intro a.
set (n := size_aggterm a).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert a Hn.
induction n as [ | n]; intros a Hn env1 env2 He.
- destruct a; inversion Hn.
- destruct a as [f | a f | f l]; simpl.
  + apply interp_funterm_eq; trivial.
  + apply f_equal.
    case (Fset.is_empty A (att_of_funterm f)).
    * destruct env1 as [ | slc1 e1]; destruct env2 as [ | slc2 e2];
      try inversion He; [apply refl_equal | ].
      subst.
      rewrite 2 map_map.
      assert (H' := unfold_env_slice_eq H2).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      {
        revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'.
        - apply refl_equal.
        - inversion H'.
        - inversion H'.
        - inversion H' as [ | _t1 _t2 _l1 _l2 Ht Hl K3 K4]; subst.
          simpl map; apply f_equal2.
          + apply interp_funterm_eq; constructor 2; trivial.
          + apply IHl1; trivial.
      }
    * assert (H := find_smallest_grouping_env_eq f He).
      destruct (find_smallest_grouping_env env1 f) as [[ | slc1 e1] | ];
        destruct (find_smallest_grouping_env env2 f) as [[ | slc2 e2] | ];
        try inversion H; trivial.
      subst; rewrite 2 map_map.
      simpl in H.
      assert (H' := unfold_env_slice_eq H3).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'; 
      try (inversion H'; fail); trivial.
      {
        inversion H'; subst.
        simpl map; apply f_equal2.
        - apply interp_funterm_eq; constructor 2; trivial.
        - apply IHl1; trivial.
      }
  + apply f_equal; rewrite <- map_eq.
    intros a Ha; apply IHn; trivial.
    simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
Qed.

End Sec.
