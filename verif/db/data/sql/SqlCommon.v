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

Require Import List.
Require Import OrderedSet FiniteSet FiniteBag FiniteCollection ListSort ListPermut 
        Partition DExpressions FlatData.

Set Implicit Arguments.

Section Sec.

Hypothesis T : Tuple.Rcd.

Import Tuple.

Hypothesis symb : Type.
Hypothesis aggregate : Type.

Hypothesis OSymb : Oset.Rcd symb.
Hypothesis OAggregate : Oset.Rcd aggregate.

Definition E : Expression.Rcd (A T) (OVal T).
split with symb aggregate.
- exact OSymb.
- exact OAggregate.
- exact (fun a => default_value T (type_of_attribute T a)).
Defined.

Inductive group_by : Type :=
  | Group_By : list (funterm E) -> group_by
  | Group_Fine.

(** * SQL_COQ Syntax *)
Inductive select : Type := 
  | Select_As : aggterm E -> attribute T -> select.

Inductive select_item : Type :=
  | Select_Star 
  | Select_List : list select -> select_item.

Definition env_type := (list (Fset.set (A T) * group_by * list (tuple T))).

Definition env_t (env : env_type) t := 
  (support T t, Group_Fine, t :: nil) :: env. 

Definition env_g (env : env_type) g s := 
  (match quicksort (OTuple T) s with 
     | nil => Fset.empty _ 
     | t :: _ => support T t 
   end, g, s) :: env.


Lemma extract_from_groups :
  forall (x1 x2 : list (tuple T)), 
    x1 =PE= x2 -> 
    comparelA (Oeset.compare (OTuple T)) (quicksort (OTuple T) x1) (quicksort (OTuple T) x2) = Eq.
Proof.
intros x1 x2 Hx.
apply (sort_is_unique (OA := OTuple T)).
- apply quick_sorted.
- apply quick_sorted.
- apply permut_trans with x1.
  + apply permut_sym; apply (quick_permut (OTuple T)).
  + apply permut_trans with x2; [assumption | ].
    apply (quick_permut (OTuple T)).
Qed.

Lemma env_slice_eq_1 :
  forall x1 x2, Oeset.compare (OLTuple T) x1 x2 = Eq ->
   match quicksort (OTuple T) x1 with
   | nil => emptysetS
   | t0 :: _ => support T t0
   end =S=
   match quicksort (OTuple T) x2 with
   | nil => emptysetS
   | t0 :: _ => support T t0
   end.
Proof.
intros l1 l2 Hl.
rewrite <- (compare_list_t (OTuple T)) in Hl.
assert (H1 := extract_from_groups Hl).
set (q1 := quicksort (OTuple T) l1) in *.
set (q2 := quicksort (OTuple T) l2) in *.
clearbody q1 q2; revert q2 H1.
induction q1 as [ | x1 q1]; intros [ | x2 q2] H1; try discriminate H1.
- simpl; apply Fset.equal_refl.
- simpl in H1.
  case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in H1; try discriminate H1.
  rewrite tuple_eq in Hx; apply (proj1 Hx).
Qed.


Definition interp_dot_env_slice (l : listT) (a : attribute T) :=
  match quicksort (OTuple T) l with
    | nil => None
    | t :: _ => if a inS? support T t 
                 then Some (dot T t a)
                 else None
  end.

Lemma interp_dot_env_slice_unfold :
  forall l a, interp_dot_env_slice l a =
  match quicksort (OTuple T) l with
    | nil => None
    | t1 :: _ => if a inS? support T t1 
                 then Some (dot T t1 a)
                 else None
  end.
Proof.
intros l a; unfold interp_dot_env_slice; apply refl_equal.
Qed.

Definition equiv_abstract_env_slice (e1 e2 : (Fset.set (A T) * group_by)) := 
  match e1, e2 with
    | (sa1, g1), (sa2, g2) => 
      sa1 =S= sa2 /\ g1 = g2 
  end.

Definition equiv_abstract_env := DExpressions.equiv_env equiv_abstract_env_slice.

Lemma equiv_t_env_slice_refl :
  forall e1, equiv_abstract_env_slice e1 e1.
Proof.
intros [sa g1]; simpl; repeat split.
apply Fset.equal_refl.
Qed.

Lemma equiv_abstract_env_refl : forall e, equiv_abstract_env e e.
Proof.
apply DExpressions.equiv_env_refl.
apply equiv_t_env_slice_refl.
Qed.

Definition equiv_env_slice (e1 e2 : (Fset.set (A T) * group_by * (list (tuple T)))) := 
  match e1, e2 with
    | (sa1, g1, x1), (sa2, g2, x2) => 
      sa1 =S= sa2 /\ g1 = g2 /\ x1 =PE= x2
  end.

Lemma equiv_env_slice_refl :
  forall e1, equiv_env_slice e1 e1.
Proof.
intros [[sa g1] l1]; simpl; repeat split.
- apply Fset.equal_refl.
- apply permut_refl.
Qed.

Lemma equiv_env_slice_sym :
  forall e1 e2, equiv_env_slice e1 e2 <-> equiv_env_slice e2 e1.
Proof.
intros [[sa1 g1] l1] [[sa2 g2] l2]; split; intros [H1 [H2 H3]]; simpl; repeat split.
- rewrite Fset.equal_spec in H1; rewrite Fset.equal_spec; intro; rewrite H1; trivial.
- subst; trivial.
- apply permut_sym; assumption.
- rewrite Fset.equal_spec in H1; rewrite Fset.equal_spec; intro; rewrite H1; trivial.
- subst; trivial.
- apply permut_sym; assumption.
Qed.

Definition equiv_env := equiv_env equiv_env_slice.

Lemma equiv_env_refl : forall env, equiv_env env env.
Proof.
apply equiv_env_refl.
apply equiv_env_slice_refl.
Qed.


Hypothesis interp_symb : symb -> list (value T) -> (value T).
Hypothesis interp_aggregate : aggregate -> list (value T) -> (value T).

Definition interp_funterm_ := 
  (interp_funterm 
     (E := E) interp_symb
     (fun (x : (Fset.set (A T) * group_by * _)) a => 
        match x with (_, _, l) => interp_dot_env_slice l a end)).

Definition interp_aggterm_ := 
  interp_aggterm (E := E) interp_symb interp_aggregate
     (fun (x : (Fset.set (A T) * group_by * _)) a => 
        match x with 
          | (_,_,l) => interp_dot_env_slice l a 
        end)
     (fun x => match x with (sa, _, _) => sa end)
     (fun x => match x with 
              | (sa, Group_Fine, _) => map (fun a => F_Dot E a) (Fset.elements _ sa) 
              | (_, Group_By g,_) => g 
            end)
     (fun x => match x with 
              | (sa, g, l) =>
                List.map (fun t => (sa, g, t :: nil)) (quicksort (OTuple T) l)
            end).


(** * Building a flat tuple from a tuple or a group of tuples by applying a select part *)
Definition projection (env : list (setA * group_by * listT)) (las : select_item) (p: Values.val) :=
  match las with
    | Select_Star => 
      match env with
        | nil => default_tuple T (Fset.empty _) p
        | (sa, gby, l) :: _ =>
          match l with
            | t :: nil => t
            | g =>
              match quicksort (OTuple T) g with
                | t :: _ => t
                | nil => default_tuple T (Fset.empty _) p
              end
          end
      end
    | Select_List las =>
      let la' :=
          List.map 
            (fun x => match x with Select_As e a => (a, e) end) 
            las in
       mk_tuple T 
          (Fset.mk_set (A T) (List.map (@fst _ _) la'))
                  (fun a => 
                     match Oset.find (OAtt T) a la' with 
                         | Some e => interp_aggterm_ env e
                         | None => dot T (default_tuple T (Fset.empty _) base.nullval) a
                     end) p
  end.

(** * Partitioning a set of tuples into homogeneous lists w.r.t to a set of fun_term expressions *)

Definition make_groups env (s : list (tuple T)) gby := 
  match gby with
    | Group_By g =>
      partition_list_expr 
        (A := tuple T) (value := value T) (FVal T) s 
        (map (fun f => fun t => interp_funterm_ (env_t env t) f) g)
    | Group_Fine => List.map (fun x => x :: nil) s  
  end.

Lemma interp_dot_env_slice_eq :
  forall a l1 l2, l1 =PE= l2 -> interp_dot_env_slice l1 a = interp_dot_env_slice l2 a.
Proof.
  intros a l1 l2 H; unfold interp_dot_env_slice.
  assert (H1 := extract_from_groups H).
  set (q1 := quicksort (OTuple T) l1) in *.
  set (q2 := quicksort (OTuple T) l2) in *.
  clearbody q1 q2; revert q2 H1.
  induction q1 as [ | x1 q1]; intros [ | x2 q2] H1; try discriminate H1.
  + simpl; trivial.
  + simpl in H1.
    case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in H1; try discriminate H1.
    rewrite tuple_eq in Hx; rewrite <- (Fset.mem_eq_2 _ _ _ (proj1 Hx)).
    case_eq (a inS? support T x1); intro Ha; [ | apply refl_equal].
    rewrite <- (proj2 Hx); apply refl_equal.
Qed.

Lemma interp_funterm_eq :
  forall f env1 env2, equiv_env env1 env2 -> 
                      interp_funterm_ env1 f = interp_funterm_ env2 f.
Proof.
intros f e1 e2 H.
apply (interp_funterm_eq (E := E)) with equiv_env_slice.
- intros a [[sa1 g1] l1] [[sa2 g2] l2] K; simpl in K.
  apply interp_dot_env_slice_eq; apply (proj2 K).
- apply H.
Qed.

Lemma interp_aggterm_eq :
  forall e env1 env2, equiv_env env1 env2 -> interp_aggterm_ env1 e = interp_aggterm_ env2 e.
Proof.
intros e env1 env2.
apply interp_aggterm_eq.
- apply equiv_env_slice_sym.
- intros [[sa1 g1] l1] [[sa2 g2] l2] H; simpl in H; apply (proj1 H).
- intros [[sa1 g1] l1] [[sa2 g2] l2] H; simpl in H.
  assert (H1 := extract_from_groups (proj2 (proj2 H))).
  set (q1 := quicksort (OTuple T) l1) in *.
  set (q2 := quicksort (OTuple T) l2) in *.
  clearbody q1 q2; revert q2 H1.
  induction q1 as [ | x1 q1]; intros [ | x2 q2] H1; try discriminate H1.
  + simpl; trivial.
  + simpl in H1.
    case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in H1; try discriminate H1.
    simpl; constructor 2; [ | apply IHq1; assumption].
    simpl; split; [apply (proj1 H) | ].
    simpl; split; [apply (proj1 (proj2 H)) | ].
    apply permut_refl_alt; simpl; rewrite Hx; trivial.
- intros [[sa1 g1] l1] [[sa2 g2] l2] H f; simpl in H.
  destruct H as [H1 [H2 H3]].
  subst g2; destruct g1 as [g1 | ]; [split; exact (fun h => h) | ].
  rewrite <- (Fset.elements_spec1 _ _ _ H1); split; exact (fun h => h).
- intros a [[sa1 g1] l1] [[sa2 g2] l2] H; simpl in H; destruct H as [H1 [H2 H3]].
  apply interp_dot_env_slice_eq; assumption.
Qed.

Lemma projection_eq :
  forall s env1 p1 env2 p2, equiv_env env1 env2 -> projection env1 s p1 =t= projection env2 s p2.
Proof.
intros s env1 p1 env2 p2 He; unfold projection.
destruct s as [ | s].
- destruct env1 as [ | [[sa1 gb1] x1] env1]; destruct env2 as [ | [[sa2 gb2] x2] env2];
  try inversion He.
  + apply mk_tuple_eq_1, Fset.equal_refl.
  + subst.
    simpl in H2; destruct H2 as [Hsa [Hg Hx]].
    assert (Kx := extract_from_groups Hx).
    assert (L := _permut_length Hx).
    destruct x1 as [ | u1 x1]; destruct x2 as [ | u2 x2]; try discriminate L.
    * destruct quicksort. apply mk_tuple_eq_1, Fset.equal_refl. apply Oeset.compare_eq_refl.
    * {
        destruct x1 as [ | t1 x1]; destruct x2 as [ | t2 x2]; try discriminate L.
        - simpl in Kx.
          case_eq (Oeset.compare (OTuple T) u1 u2); 
            intro Hu; rewrite Hu in Kx; try discriminate Kx; trivial.
        - destruct (quicksort (OTuple T) (u1 :: t1 :: x1)) as [ | s1 l1]; 
          destruct (quicksort (OTuple T) (u2 :: t2 :: x2)) as [ | s2 l2]; try discriminate Kx.
          + apply mk_tuple_eq_1, Fset.equal_refl.
          + simpl in Kx.
            destruct (Oeset.compare (OTuple T) s1 s2); try discriminate Kx; trivial.
      }
- apply mk_tuple_eq_2.
  intros a Ha.
  case_eq (Oset.find 
               (OAtt T) a
               (map (fun x : select => match x with
                                         | Select_As e a0 => (a0, e)
                                       end) s));
    [intros e _He | intros _; apply refl_equal].
  apply interp_aggterm_eq; trivial.
Qed.

End Sec.
