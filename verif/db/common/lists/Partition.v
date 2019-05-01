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

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet FiniteSet.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.

Hypothesis value : Type.
Hypothesis OVal : Oset.Rcd value.
Hypothesis FVal : Fset.Rcd OVal.

Notation "t1 '=t=' t2" := (Oeset.compare OA t1 t2 = Eq) (at level 70, no associativity).
Notation "s1 '=P=' s2" := (_permut (@eq A) s1 s2) (at level 70, no associativity).
Notation "s1 '=PE=' s2" := 
  (_permut (fun x y => Oeset.compare OA x y = Eq) s1 s2) (at level 70, no associativity).


Definition OLA : Oeset.Rcd (list A).
split with (fun l1 l2 => 
              Oeset.compare (mk_oelists OA) (quicksort OA l1) 
                                        (quicksort OA l2)).
- do 3 intro; apply Oeset.compare_eq_trans.
- do 3 intro; apply Oeset.compare_eq_lt_trans.
- do 3 intro; apply Oeset.compare_lt_eq_trans.
- do 3 intro; apply Oeset.compare_lt_trans.
- do 2 intro; apply Oeset.compare_lt_gt.
Defined.

Lemma compare_list_t :
  forall l1 l2, l1 =PE= l2 <-> Oeset.compare OLA l1 l2 = Eq.
Proof.
intros l1 l2.
assert (Hl1 := quick_sorted OA l1).
assert (Hl2 := quick_sorted OA l2).
assert (Kl1 := quick_permut OA l1).
assert (Kl2 := quick_permut OA l2).
split; intro H.
- simpl.
  set (q1 := quicksort OA l1) in *; clearbody q1.
  set (q2 := quicksort OA l2) in *; clearbody q2.
  assert (Hq : q1 =PE= q2).
  {
    refine (permut_trans OA _ Kl2).
    refine (permut_trans OA _ H).
    apply (permut_sym OA); apply Kl1.
  }
  clear l1 l2 Kl1 Kl2 H.
  apply (sort_is_unique (OA := OA) Hl1 Hl2 Hq).
-  refine (permut_trans OA Kl1 _).
   apply (permut_trans OA) with (quicksort OA l2).
   + apply permut_refl_alt; apply H.
   + apply (permut_sym OA); apply Kl2.
Qed.

(* [partition_value e lv ls] recursively splits each set of [ls] wrt to the values [v] in [lv]. *)

Fixpoint partition_value e (lv : list value) (ls : list (list A)) : list (list A) :=
  match lv with
    | nil => ls
    | v1 :: lv =>
      let ls' := partition_value e lv ls in
      match ls' with
        | nil => nil
        | s :: ls'' =>
          let (hv1, h') := 
              List.partition 
                (fun t => 
                   Oset.eq_bool OVal (e t) v1) s in
          h' :: hv1 :: ls''
      end
  end.

(* [partition_expr e1 s] splits the set [s] into a list of sets according to the evaluation of [e1]. *)
Definition partition_expr fe1 (s : list A) : list (list A) :=
  let values_of_e1 := 
      Fset.elements _ (Fset.mk_set FVal (List.map fe1 s)) in
  match partition_value fe1 values_of_e1 (s :: nil) with
    | nil :: ls => ls
    | _ => nil
  end.

(* [partition s l] splits the set [s] into a list a sets such that the evalution of all expressions in the list [l] are constants over each subset :
\[
\forall si ej t1 t2, si \in (partition s l) -> ej \in l, t1 \in si -> t2 \in si -> eval_expression_tuple t1 ej = eval_expression_tuple t2 ej /\

\forall si1 si2 t1 t2, si1 \in (partition s l) -> si2 \in (partition s l) -> si1 <> si2 -> t1 \in si1 -> t2 \in si2 -> 
exists ej, ej \in l /\ eval_expression_tuple t1 ej <> eval_expression_tuple t2 ej.
\]
*)
Fixpoint partition_list_expr (s : list A) lf  : list (list A) :=
  match lf, s with
    | nil, nil => nil
    | nil, (_ :: _) => s :: nil
    | e1 :: l, _ => 
      let pl := partition_list_expr s l in
      flat_map (partition_expr e1) pl
  end.

(* [partition_expr e1 s] splits the set [s] into a list of sets according to the evaluation of [e1]. *)
Definition partition_expr2 e1 (s : list A) : list (list A) :=
  let values_of_e1 := 
      Fset.elements _ (Fset.mk_set FVal (List.map e1 s)) in
  partition_value e1 values_of_e1 (s :: nil).

Fixpoint partition_list_expr2 (s : list A) lf : list (list A) :=
  match lf with
    | nil => s :: nil
    | e1 :: l => 
      let pl := partition_list_expr2 s l in
      flat_map (partition_expr2 e1) pl
  end.

Lemma partition_value_unfold :
  forall e lv ls,
    partition_value e lv ls =
  match lv with
    | nil => ls
    | v1 :: lv =>
      let ls' := partition_value e lv ls in
      match ls' with
        | nil => nil
        | s :: ls'' =>
          let (hv1, h') := 
              List.partition 
                (fun t => 
                   Oset.eq_bool OVal (e t) v1) s in
          h' :: hv1 :: ls''
      end
  end.
Proof.
  intros e lv ls; case lv; intros; apply refl_equal.
Qed.

Lemma partition_value_nil :
  forall lv e ls, partition_value e lv ls = nil <-> ls = nil.
Proof.
intro lv; induction lv as [ | v1 lv]; intros e ls; simpl.
- split; exact (fun h => h).
- case_eq (partition_value e lv ls).
  + intro H; split.
    * intros _; rewrite IHlv in H; apply H.
    * exact (fun _ => refl_equal _).
  + intros s1 ls' H.
    case (List.partition (fun t => Oset.eq_bool OVal (e t) v1) s1).
    intros s s'; split.
    * intro Abs; discriminate Abs.
    * intro Abs.
      rewrite <- (IHlv e ls) in Abs.
      rewrite H in Abs; discriminate Abs.
Qed.

Lemma partition_value_eq :
  forall e1 e2 lv s1 s2, (forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) ->
    s1 =PE= s2 ->
    exists lls, partition_value e1 lv (s1 :: nil) = List.map (@fst _ _) lls /\
                partition_value e2 lv (s2 :: nil) = List.map (@snd _ _) lls /\
                forall p1 p2, List.In (p1, p2) lls -> p1 =PE= p2.
Proof.
intros e1 e2 lv; 
induction lv as [ | v1 lv];
intros s1 s2 He Hs.
- exists ((s1, s2) :: nil); repeat split.
  intros p1 p2 Hp; simpl in Hp; destruct Hp as [Hp | Hp]; [ | contradiction Hp].       
  injection Hp; clear Hp; do 2 intro; subst; assumption.
- destruct (IHlv _ _ He Hs) as [lls [H1 [H2 H]]].
  set (lls1 := partition_value e1 (v1 :: lv) (s1 :: nil)) in *.
  set (lls2 := partition_value e2 (v1 :: lv) (s2 :: nil)) in *.
  assert (Hlls1 := refl_equal lls1); unfold lls1 at 2 in Hlls1; clearbody lls1.
  assert (Hlls2 := refl_equal lls2); unfold lls2 at 2 in Hlls2; clearbody lls2.
  rewrite partition_value_unfold in Hlls1, Hlls2.
  rewrite H1 in Hlls1.
  rewrite H2 in Hlls2.
  set (f1 := (fun t => Oset.eq_bool OVal (e1 t) v1)) in *.
  set (f2 := (fun t => Oset.eq_bool OVal (e2 t) v1)) in *.
  assert (Hf : forall x y, x =t= y -> f1 x = f2 y).
  {
    intros x y Hxy; unfold f1.
    rewrite (He _ _ Hxy); apply refl_equal.
  }
  destruct lls as [ | [p1 p2] lls].
  + simpl in Hlls1, Hlls2.
    subst lls1 lls2.
    exists nil; repeat split; trivial.
  + rewrite map_unfold in Hlls1, Hlls2.
    assert (Hp := H _ _ (or_introl _ (refl_equal _))).
    simpl in Hlls1, Hlls2.
    case_eq (List.partition f1 p1).
    intros p1' p1'' Hp1; rewrite Hp1 in Hlls1.
    case_eq (List.partition f2 p2).
    intros p2' p2'' Hp2; rewrite Hp2 in Hlls2.
    exists ((p1'', p2'') :: (p1', p2') :: lls); repeat split; trivial.
    intros p p' K.
    simpl in K; destruct K as [K | [K | K]].
    * injection K; clear K; do 2 intro; subst p p'.
      apply (proj2 (partition_permut OA f1 f2 (l := p1) (fun x y _ => Hf x y) Hp1 Hp2 Hp)).
    * injection K; clear K; do 2 intro; subst p p'.
      apply (proj1 (partition_permut OA f1 f2 (l := p1) (fun x y _ => Hf x y) Hp1 Hp2 Hp)).
    * apply H; right; assumption.
Qed.

Lemma partition_value_invariant :
  forall e lv s lls, (forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    partition_value e lv (s :: nil) = lls ->
    s =P= flat_map (fun x => x) lls /\
    (match lls with
      | nil => False
      | s0 :: lls =>
        (forall t, In t s0 -> List.In (e t) lv -> False) /\
        (forall s1 s2, List.In s1 lls -> List.In s2 lls ->
                       s1 = s2 \/ 
                       (forall t, Oeset.mem_bool OA t s1 = true -> 
                                  Oeset.mem_bool OA t s2 = true -> False)) /\ 
        (forall s1 s2, List.In s1 lls -> List.In s2 lls ->
                       forall t1 t2, In t1 s1 -> In t2 s2 -> e t1 = e t2 -> s1 = s2) /\
        (forall si, List.In si lls ->
                    exists vi, (List.In vi lv /\ forall t, In t si -> e t = vi)) 
    end).
Proof.
intros e lv;
induction lv as [ | v1 lv];
intros s lls He H.
- simpl in H; subst lls.
  repeat split.
  + simpl; rewrite <- app_nil_end; apply _permut_refl; intros; apply refl_equal.
  + intros t _ Abs; contradiction Abs.
  + intros s1 s2 Abs; contradiction Abs.
  + intros s1 s2 Abs; contradiction Abs.
  + intros si Abs; contradiction Abs.
- simpl in H.
  case_eq (partition_value e lv (s :: nil)).
  + intro Hs; rewrite Hs in H.
    assert (IH := IHlv _ _ He Hs).
    simpl in IH.
    apply False_rec; apply (proj2 IH).
  + intros s1 ls Hs; rewrite Hs in H.
    set (f1 := fun t => Oset.eq_bool OVal (e t) v1) in *.
    case_eq (List.partition f1 s1).
    intros p1 p2 Hp; rewrite Hp in H.
    subst lls.
    assert (IH := IHlv _ _ He Hs).
    destruct IH as [IH1 [IH2 [IH3 [IH4 IH5]]]].
    assert (H1 : s =P= flat_map (fun x : list A => x) (p2 :: p1 :: ls)).
    {
      rewrite flat_map_unfold in IH1; rewrite 2 flat_map_unfold.
      refine (_permut_trans _ IH1 _); [intros; subst; trivial | ].
      rewrite ass_app.
      apply (_permut_app2 (equivalence_eq _)).
      refine (_permut_trans _ (partition_spec3_strong _ _ Hp) _); [intros; subst; trivial | ].
      apply _permut_swapp; apply _permut_refl; intros; apply refl_equal.
    }
    split; [apply H1 | ].
    assert (H2 : forall t : A, In t p2 -> In (e t) (v1 :: lv) -> False).
    {
      intros t Ht Kt.
      {
        assert (Kp2 := partition_spec2 f1 s1).
        rewrite Hp in Kp2; simpl in Kp2; rewrite Kp2, filter_In in Ht.
        simpl in Kt; destruct Kt as [Kt | Kt].
        - unfold f1 in Ht; rewrite <- Kt, negb_true_iff, <- not_true_iff_false in Ht.
          apply (proj2 Ht); rewrite Oset.eq_bool_true_iff; apply refl_equal.
        - apply (IH2 t); [ | assumption].
          apply (proj1 Ht).
      }
    }
    split; [apply H2 | ].
    assert (H3 : forall s0 s2 : list A,
                   In s0 (p1 :: ls) ->
                   In s2 (p1 :: ls) ->
                   s0 = s2 \/
                   (forall t : A,
                      Oeset.mem_bool OA t s0 = true ->
                      Oeset.mem_bool OA t s2 = true -> False)).
    {
      intros s2 s3 Hs2 Hs3.
      simpl in Hs2; simpl in Hs3.
      {
        destruct Hs2 as [Hs2 | Hs2]; destruct Hs3 as [Hs3 | Hs3].
        - left; subst s2 s3; apply refl_equal.
        - subst s2; right; intros t Ht Kt.
          replace p1 with (fst (p1, p2)) in Ht; [ | apply refl_equal].
          rewrite <- Hp, partition_spec1, Oeset.mem_bool_filter in Ht;
            [ | intros x1 x2 _ Hx; unfold f1; rewrite (He _ _ Hx); trivial].
          rewrite Bool.andb_true_iff, Oeset.mem_bool_true_iff in Ht.
          destruct Ht as [Hf1 [t1 [Ht Ht1]]].
          apply (IH2 t1 Ht1).
          assert (IHs3 := IH5 _ Hs3).
          destruct IHs3 as [v3 [Ks3 Js3]].
          rewrite Oeset.mem_bool_true_iff in Kt.
          destruct Kt as [t3 [Kt Ht3]].
          rewrite <- (He _ _ Ht), (He _ _ Kt).
          rewrite Js3; assumption.
        - subst s3; right; intros t Kt Ht.
          replace p1 with (fst (p1, p2)) in Ht; [ | apply refl_equal].
          rewrite <- Hp, partition_spec1, Oeset.mem_bool_filter in Ht;
            [ | intros x1 x2 _ Hx; unfold f1; rewrite (He _ _ Hx); trivial].
          rewrite Bool.andb_true_iff, Oeset.mem_bool_true_iff in Ht.
          destruct Ht as [Hf1 [t1 [Ht Ht1]]].
          apply (IH2 t1 Ht1).
          assert (IHs3 := IH5 _ Hs2).
          destruct IHs3 as [v3 [Ks3 Js3]].
          rewrite Oeset.mem_bool_true_iff in Kt.
          destruct Kt as [t3 [Kt Ht3]].
          rewrite <- (He _ _ Ht), (He _ _ Kt).
          rewrite Js3; assumption.
        - apply IH3; assumption.
      }
    }
    split; [apply H3 | ].
    assert (H4 : forall s0 s2 : list A,
                   In s0 (p1 :: ls) ->
                   In s2 (p1 :: ls) ->
                   forall t1 t2 : A,
                     In t1 s0 ->
                     In t2 s2 -> e t1 = e t2 -> s0 = s2).
    {
      intros s2 s3 Hs2 Hs3.
      simpl in Hs2; simpl in Hs3.
      {
        destruct Hs2 as [Hs2 | Hs2]; destruct Hs3 as [Hs3 | Hs3].
        - intros; subst s2 s3; apply refl_equal.
        - subst s2; intros t1 t2 Ht1 Ht2 H.
          apply False_rec.
          apply (IH2 t1).
          + replace p1 with (fst (p1, p2)) in Ht1; [ | apply refl_equal].
            rewrite <- Hp, partition_spec1, filter_In in Ht1; apply (proj1 Ht1).
          + rewrite H.
            assert (IHs3 := IH5 _ Hs3).
            destruct IHs3 as [v3 [Ks3 Js3]].
            rewrite (Js3 t2 Ht2); assumption.
        - subst s3; intros t1 t2 Ht1 Ht2 H.
          apply False_rec.
          apply (IH2 t2).
          + replace p1 with (fst (p1, p2)) in Ht2; [ | apply refl_equal].
            rewrite <- Hp, partition_spec1, filter_In in Ht2; apply (proj1 Ht2).
          + assert (IHs2 := IH5 _ Hs2).
            destruct IHs2 as [v2 [Ks2 Js2]].
            rewrite <- H, (Js2 t1 Ht1); assumption.
        - apply IH4; assumption.
      }
    } 
    split; [apply H4 | ].
    assert (H5 : forall si : list A,
                   In si (p1 :: ls) ->
                   exists vi : value,
                     In vi (v1 :: lv) /\
                     (forall t : A, In t si -> e t = vi)).
    {
      intros si Hsi; simpl in Hsi.
      {
        destruct Hsi as [Hsi | Hsi].
        - subst si.
          exists v1; split; [left; apply refl_equal | ].
          intros t Ht.
          replace p1 with (fst (p1, p2)) in Ht; [ | apply refl_equal].
          rewrite <- Hp, partition_spec1, filter_In in Ht.
          unfold f1 in Ht; rewrite Oset.eq_bool_true_iff in Ht; apply (proj2 Ht).
        - destruct (IH5 _ Hsi) as [vi [Hvi Ht]].
          exists vi; split; [right | ]; assumption.
      }
    }
    apply H5.
Qed.

Lemma partition_value_invariant2 :
  forall e lv s lls, (forall t1 t2, t1 =t= t2 -> e t1 = e t2) -> 
    Sorted.Sorted (fun x y => Oset.compare OVal x y = Lt) lv ->
    partition_value e lv (s :: nil) = lls ->
    match lls with
      | nil => False
      | s0 :: lls => 
        (forall si,
          List.In si lls -> 
          exists vi, List.In vi lv /\
                     si = filter (fun t => Oset.eq_bool OVal (e t) vi) s) /\
        (s0 = 
         filter (fun t => 
                   forallb 
                     (fun vi => negb (Oset.eq_bool OVal (e t) vi)) lv) s) /\
        (forall lls1 lls2 lls3 s1 s2, 
           lls = lls1 ++ s1 :: lls2 ++ s2 :: lls3 -> s1 = s2 -> s1 = nil)
    end.
Proof.
intros e lv s lls He _Hlv. 
assert (Hlv : Sorted.StronglySorted (fun x y => Oset.compare OVal x y = Lt) lv).
{
  apply Sorted.Sorted_StronglySorted; [ | assumption].
  intros v1 v2 v3; apply Oset.compare_lt_trans.
}
clear _Hlv; revert s lls Hlv;
induction lv as [ | v lv];
intros s lls Hlv H.
- simpl in H; subst lls; split.
  + intros si Hsi; contradiction Hsi.
  + split; [ | intros lls1 lls2 lls3 s1 s2 H; destruct lls1; discriminate H].
    simpl; rewrite filter_true; [ | intros]; trivial.
- rewrite partition_value_unfold in H.
  case_eq (partition_value e lv (s :: nil)).
  + assert (K := partition_value_invariant e lv s He (refl_equal _)).
    intro Hp; rewrite Hp in K.
    destruct K as [_ K]; contradiction K.
  + intros s0 lp Hp; rewrite Hp in H.
    cbv iota beta zeta in H.
    case_eq (List.partition (fun t => Oset.eq_bool OVal (e t) v) s0).
    intros p1 p2 Hs0.
    rewrite Hs0 in H.
    subst lls.
    assert (_Hlv := Hlv);
    inversion _Hlv; clear _Hlv; subst.
    assert (IH := IHlv s _ H1 (refl_equal _)).
    rewrite Hp in IH; destruct IH as [IH1 [IH2 IH3]].
    split; [ | split].
    * {
        intros si Hsi; simpl in Hsi; destruct Hsi as [Hsi | Hsi].
        - subst p1.
          exists v; split; [left; apply refl_equal | ].
          assert (Ks0 := partition_spec1 
                           (fun t : A => Oset.eq_bool OVal (e t) v) s0).
          rewrite Hs0 in Ks0; simpl fst in Ks0; rewrite Ks0, IH2, filter_filter.
          apply filter_eq.
          intros x Hx.
          case_eq (Oset.eq_bool OVal (e x) v); [ | intros _; apply refl_equal].
          intro Kx; rewrite Oset.eq_bool_true_iff in Kx.
          rewrite Bool.andb_true_l; rewrite forallb_forall.
          intros vi Hvi.
          rewrite Kx; rewrite negb_true_iff, <- not_true_iff_false, Oset.eq_bool_true_iff.
          intro Hv; subst vi; rewrite Forall_forall in H2.
          generalize (H2 v Hvi); rewrite Oset.compare_eq_refl; discriminate.
        - destruct (IH1 si Hsi) as [vi [Hvi Ksi]].
          exists vi; split; [right | ]; assumption.
      }
    * assert (Ks0 := partition_spec2 (fun t => Oset.eq_bool OVal (e t) v) s0).
      rewrite Hs0 in Ks0; simpl snd in Ks0; rewrite Ks0, IH2, filter_filter.
      apply filter_eq.
      intros x Hx; rewrite (forallb_unfold _ (_ :: _)); apply refl_equal.
    * intros lls1 lls2 lls3 s1 s2 Hlls.
      {
        destruct lls1 as [ | _p1 lls1];
        [ | injection Hlls; intros Klls _; apply (IH3 _ _ _ _ _ Klls)].
        injection Hlls; clear Hlls; intros Hlls _Hp1 Hp1; subst s1.
        assert (Ks0 := partition_spec1 (fun t => Oset.eq_bool OVal (e t) v) s0).
      rewrite Hs0 in Ks0; simpl fst in Ks0.
      assert (Hs2 : In s2 lp).
      {
        rewrite Hlls; apply in_or_app; right; left; apply refl_equal.
      }
      destruct (IH1 s2 Hs2) as [v2 [Hv2 Ks2]].
      case_eq p1; [intros; apply refl_equal | ].
      intros t1 k1 Kp1; apply False_rec.
      assert (Ht1 : In t1 p1); [rewrite Kp1; left; apply refl_equal | ].
      assert (_Ht1 := Ht1); rewrite Ks0, filter_In in _Ht1; destruct _Ht1 as [_ Kt1].
      rewrite Oset.eq_bool_true_iff in Kt1.
      rewrite Hp1, Ks2, filter_In in Ht1.
      destruct Ht1 as [_ Ht1]; rewrite Oset.eq_bool_true_iff in Ht1.
      rewrite Kt1 in Ht1; subst v2.
      rewrite Forall_forall in H2.
      generalize (H2 _ Hv2); rewrite Oset.compare_eq_refl; discriminate.
      } 
Qed.      

Lemma partition_expr_partition_expr2 :
  forall e s, (forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    partition_expr e s = 
    List.filter (fun x => match x with nil => false | _ :: _ => true end) (partition_expr2 e s).
Proof.
intros e s He.
unfold partition_expr2, partition_expr.
set (lv := ({{{Fset.mk_set FVal (map e s)}}})) in *.
case_eq (partition_value e lv (s :: nil)).
- intro; apply refl_equal.
- intros s1 ls Hs.
    assert (Hlv : Sorted.Sorted (fun x y : value => Oset.compare OVal x y = Lt) lv).
    {
      subst lv; apply Fset.elements_spec3.
    }
    destruct (partition_value_invariant2 _ _ He Hlv Hs) as [H1 [H2 H3]].
    assert (Hs1 : s1 = nil).
    {
      destruct s1 as [ | t1 s1]; [apply refl_equal | ].
      apply False_rec.
      assert (Ht1 : In t1 (t1 :: s1)); [left; apply refl_equal | ].
      rewrite H2, filter_In, forallb_forall in Ht1.
      destruct Ht1 as [Ht1 Kt1].
      assert (Jt1 : In (e t1) lv).      
      {
        subst lv; rewrite <- (Oset.mem_bool_true_iff OVal), <- Fset.mem_elements.
        rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
        exists t1; split; trivial.
      }
      generalize (Kt1 _ Jt1); rewrite negb_true_iff, <- not_true_iff_false, Oset.eq_bool_true_iff.
      intro H; apply False_rec; apply H; apply refl_equal.
    }
    clear H2 H3; rewrite Hs1, filter_unfold.
    assert (K1 : forall si, In si ls -> si <> nil).
    {
      intros si Hsi.
      destruct (H1 _ Hsi) as [vi [Hvi Ksi]].
      assert (Ki : exists ti, e ti = vi /\ In ti s).
      {
        unfold lv in Hvi.
        rewrite <- (Oset.mem_bool_true_iff OVal), <- Fset.mem_elements in Hvi.
        rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Hvi.
        apply Hvi.
      }
      destruct Ki as [ti [Ki Hti]].
      assert (Kti : In ti si).
      {
        rewrite Ksi, filter_In; split; [assumption | ].
        rewrite Oset.eq_bool_true_iff; apply Ki.
      }
      destruct si; [contradiction Kti | discriminate].
    }
    clear Hs Hlv H1 Hs1.
    induction ls as [ | s2 ls]; [apply refl_equal | simpl].
    assert (Ks2 := K1 s2 (or_introl _ (refl_equal _))).
    destruct s2; [apply False_rec; apply Ks2; apply refl_equal | ].
    apply f_equal; apply IHls.
    intros; apply K1; right; assumption.
Qed.

Lemma partition_expr2_eq :
  forall e1 e2 s1 s2, (forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) -> s1 =PE= s2 ->
  exists lls, partition_expr2 e1 s1 = map (@fst _ _) lls /\
             partition_expr2 e2 s2 = map (@snd _ _) lls /\
             forall p1 p2, List.In (p1, p2) lls -> p1 =PE= p2.
Proof.
intros e1 e2 s1 s2 He Hs.
unfold partition_expr2.
assert (Aux : {{{Fset.mk_set FVal (map e1 s1)}}} =
               {{{Fset.mk_set FVal (map e2 s2)}}}).
{
  apply Fset.elements_spec1.
  rewrite Fset.equal_spec; intro v.
  rewrite eq_bool_iff, 2 Fset.mem_mk_set, 2 Oset.mem_bool_true_iff.
  split; intro H; rewrite in_map_iff in H; destruct H as [t [Hv Ht]]; rewrite in_map_iff.
  - assert (Kt : Oeset.mem_bool OA t s2 = true).
    {
      rewrite <- (mem_permut_mem OA t Hs), Oeset.mem_bool_true_iff.
      exists t; split; [apply Oeset.compare_eq_refl | apply Ht].
    }
    rewrite Oeset.mem_bool_true_iff in Kt.
    destruct Kt as [t' [Kt Ht']].
    exists t'; split; [ | assumption].
    rewrite <- Hv; apply sym_eq; apply He; assumption.
  - assert (Kt : Oeset.mem_bool OA t s1 = true).
    {
      rewrite (mem_permut_mem OA t Hs), Oeset.mem_bool_true_iff.
      exists t; split; [apply Oeset.compare_eq_refl | apply Ht].
    }
    rewrite Oeset.mem_bool_true_iff in Kt.
    destruct Kt as [t' [Kt Ht']].
    exists t'; split; [ | assumption].
    rewrite <- Hv; apply He; apply Oeset.compare_eq_sym; assumption.
}
rewrite Aux; apply partition_value_eq; assumption.
Qed.

Lemma partition_expr_eq :
  forall e1 e2 s1 s2, (forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) -> s1 =PE= s2 ->
  exists lls, partition_expr e1 s1 = map (@fst _ _) lls /\
             partition_expr e2 s2 = map (@snd _ _) lls /\
             forall p1 p2, List.In (p1, p2) lls -> p1 =PE= p2.
Proof.
intros e1 e2 s1 s2 He H.
rewrite 2 partition_expr_partition_expr2; 
  [ | intros t1 t2 Ht; rewrite <- (He _ _ Ht); apply sym_eq; apply He; apply Oeset.compare_eq_refl
    | intros t1 t2 Ht; rewrite (He _ _ Ht); apply sym_eq; apply He; apply Oeset.compare_eq_refl].
destruct (partition_expr2_eq e1 e2 He H) as [lls [H1 [H2 Hll]]].
exists (List.filter (fun ss => match ss with (nil, _) => false | _ => true end) lls); repeat split.
- rewrite H1; clear s1 s2 H H1 H2.
  induction lls as [ | [s1 s2] lls]; simpl; [apply refl_equal | ].
  destruct s1 as [ | t1 s1]; simpl.
  + apply IHlls; intros; apply Hll; right; assumption.
  + apply f_equal; apply IHlls; intros; apply Hll; right; assumption.
- rewrite H2; clear s1 s2 H H1 H2.
  induction lls as [ | [s1 s2] lls]; simpl; [apply refl_equal | ].
  assert (Hs := Hll _ _ (or_introl _ (refl_equal _))).
  destruct s1 as [ | t1 s1].
  + destruct s2; [ | inversion Hs].
    apply IHlls; intros; apply Hll; right; assumption.
  + destruct s2 as [ | t2 s2]; [assert (Ks := permut_sym OA Hs); inversion Ks | ].
    simpl; apply f_equal.
    apply IHlls; intros; apply Hll; right; assumption.
- intros p1 p2 Hp; rewrite filter_In in Hp.
  apply Hll; apply (proj1 Hp).
Qed.
  
Lemma in_partition_expr_not_empty :
  forall e s ls, (forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
                 partition_expr e s = ls -> forall s1, List.In s1 ls -> s1 <> nil.
Proof.
intros e s He ls H s1 Hs1.
rewrite partition_expr_partition_expr2 in H; trivial.
rewrite <- H, filter_In in Hs1.
destruct Hs1 as [_ Hs1].
destruct s1; [discriminate Hs1 | discriminate].
Qed.

Lemma partition_expr_invariant :
  forall e s ls, (forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    partition_expr e s = ls ->
    s =P= flat_map (fun x => x) ls /\
    (forall s1 s2, List.In s1 ls -> List.In s2 ls -> 
                   s1 = s2 \/ 
                   (forall t, Oeset.mem_bool OA t s1 = true ->
                              Oeset.mem_bool OA t s2 = true -> False)) /\
    (forall s1, List.In s1 ls -> forall t1 t2, In t1 s1 -> In t2 s1 -> e t1 = e t2) /\
    (forall s1 s2, List.In s1 ls -> List.In s2 ls ->
     forall t1 t2, In t1 s1 -> In t2 s2 -> e t1 = e t2 -> s1 = s2) /\
    all_diff ls.
Proof.
intros e s ls He H.
unfold partition_expr in H.
set (lv := {{{Fset.mk_set FVal (map e s)}}}) in *.
assert (Hlv := refl_equal lv).
unfold lv at 2 in Hlv; clearbody lv.
destruct (partition_value_invariant e lv s He (refl_equal _)) as [H1 H2].
case_eq (partition_value e lv (s :: nil)); [intro P; rewrite P in H2; contradiction H2 | ].
intros p1 lp P; rewrite P in H, H1, H2.
destruct H2 as [H2 [H3 [H4 H5]]].
assert (Hp1 : p1 = nil).
{
  destruct p1 as [ | t1 p1]; [apply refl_equal | ].
  apply False_rec; apply (H2 t1 (or_introl _ (refl_equal _))).
  rewrite Hlv.
  rewrite <- (Oset.mem_bool_true_iff OVal).
  rewrite <- Fset.mem_elements, Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  exists t1; split; [apply refl_equal | ].
  rewrite (in_permut_in H1), in_flat_map; exists (t1 :: p1); split; left; trivial.
} 
subst p1; subst lp.
repeat split; trivial.
- intros s1 Hs1.
  destruct (H5 s1 Hs1) as [v1 [Hv1 Kv1]].
  intros t1 t2 Ht1 Ht2.
  rewrite (Kv1 _ Ht1), (Kv1 _ Ht2); apply refl_equal.
- assert (Klv : Sorted.Sorted (fun x y : value => Oset.compare OVal x y = Lt) lv).
  {
    subst lv; apply Fset.elements_spec3.
  }
  assert (I := partition_value_invariant2 e s He Klv (refl_equal _)); rewrite P in I.
  destruct I as [I1 [I2 I3]].
  apply all_diff_equiv2.
  intros l1 l2 l3 a1 a2 Hl Ha.
  assert (IH3 := I3 _ _ _ _ _ Hl Ha).
  assert (Aux := in_partition_expr_not_empty e s (ls := ls) He).
  unfold partition_expr in Aux; rewrite <- Hlv, P in Aux.
  apply (Aux (refl_equal _) a1).
  + rewrite Hl; apply in_or_app; right; left; trivial.
  + assumption.
Qed.

Lemma partition_list_expr_partition_list_expr2 :
  forall le s, (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
               partition_list_expr s le = 
               List.filter (fun x => match x with nil => false | _ => true end) 
                           (partition_list_expr2 s le).
Proof.
intro le; induction le as [ | e1 le]; intros s Hle; simpl.
- destruct s; trivial.
- rewrite IHle.
  set (ls := partition_list_expr2 s le) in *; clearbody ls.
  assert (He1 := Hle _ (or_introl _ (refl_equal _))).
  clear le Hle IHle.
  induction ls as [ | s1 ls]; simpl; [apply refl_equal | ].
  rewrite filter_app.
  rewrite <- IHls.
  destruct s1 as [ | t1 s1].
  + unfold partition_expr2; simpl.
    rewrite Fset.elements_empty; simpl; apply refl_equal.
  + simpl; apply f_equal2; [ | apply refl_equal].
    apply partition_expr_partition_expr2; assumption.
  + do 2 intro; apply Hle; right; assumption.
Qed.

Lemma partition_list_expr_empty :
  forall le s, (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
               (s = nil <-> partition_list_expr s le = nil).
Proof.
intros le;
induction le as [ | e1 le]; intros s Hle; split.
- intro Hs; subst s; trivial.
- intro Hs; simpl in Hs.
  destruct s; [apply refl_equal | discriminate Hs].
- intro Hs; rewrite IHle in Hs.
  + simpl; rewrite Hs; apply refl_equal.
  + do 2 intro; apply Hle; right; assumption.
- intro Hs; simpl in Hs.
  case_eq (partition_list_expr s le); [rewrite IHle; [exact (fun h => h) | ] | ].
  + do 2 intro; apply Hle; right; assumption.
  + intros s1 ls H; rewrite H in Hs.
    simpl in Hs.
    assert (Hs1 : s1 <> nil).
    {
      rewrite partition_list_expr_partition_list_expr2 in H.
      - assert (Aux : List.In s1 (s1 :: ls)); [left; apply refl_equal | ].
        rewrite <- H in Aux.
        rewrite filter_In in Aux.
        destruct Aux as [_ Aux].
        destruct s1; discriminate.
      - do 2 intro; apply Hle; right; assumption.
    }
  case_eq (partition_expr e1 s1); 
    [ | intros ss1 ls1 Ks1; rewrite Ks1 in Hs; discriminate Hs].
  intro Ks1.
  assert (Js1 := proj1 (partition_expr_invariant _ _ (Hle _ (or_introl _ (refl_equal _))) Ks1)); 
    simpl in Js1.
  apply False_rec; apply Hs1.
  inversion Js1; [trivial | subst].
  destruct l1; discriminate.
Qed.

Lemma partition_list_expr2_eq :
  forall le1 le2 s1 s2, Forall2 (fun e1 e2 => forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) le1 le2 ->
    s1 =PE= s2 ->
    exists lls, partition_list_expr2 s1 le1 = List.map (@fst _ _) lls /\
           partition_list_expr2 s2 le2 = List.map (@snd _ _) lls /\
                forall p1 p2, List.In (p1, p2) lls -> p1 =PE= p2.
Proof.
intro le1; 
induction le1 as [ | e1 le1];
intros [ | e2 le2] s1 s2 Hle Hs.
- exists ((s1, s2) :: nil); repeat split; trivial.
  intros p1 p2 Hp; simpl in Hp; destruct Hp as [ | Hp]; [ | contradiction Hp].
  injection H; clear H; do 2 intro; subst; assumption.
- inversion Hle.
- inversion Hle.
- simpl.
  inversion Hle; subst.
  destruct (IHle1 _ _ _ H4 Hs) as [lls [_H1 [_H2 _H]]].
  rewrite _H1, _H2; clear le1 le2 _H1 _H2 IHle1 Hle H4.
  induction lls as [ | [p1 p2] lls].
  + exists nil; repeat split; trivial.
  + simpl.
    destruct (IHlls (fun p1 p2 h => _H _ _ (or_intror h)))
      as [ll [_H1 [_H2 Hll]]].
    destruct (partition_expr2_eq e1 e2 H2 (_H _ _ (or_introl _ (refl_equal _)))) 
      as [ll1 [K1 [K2 Kll1]]].
    exists (ll1 ++ ll); repeat split.
    * rewrite map_app; apply f_equal2; assumption.
    * rewrite map_app; apply f_equal2; assumption.
    * intros u1 u2 Hu;
      destruct (in_app_or _ _ _ Hu) as [Ku | Ku];
      [apply Kll1 | apply Hll]; assumption.
Qed.

Lemma partition_list_expr_eq :
  forall le1 le2 s1 s2, Forall2 (fun e1 e2 => forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) le1 le2 ->
    s1 =PE= s2 ->
    exists lls, partition_list_expr s1 le1 = List.map (@fst _ _) lls /\
                partition_list_expr s2 le2 = List.map (@snd _ _) lls /\
                forall p1 p2, List.In (p1, p2) lls -> p1 =PE= p2.
Proof.
intros le1 le2 s1 s2 Hle Hs.
rewrite 2 partition_list_expr_partition_list_expr2.
- destruct (partition_list_expr2_eq Hle Hs) as [lls [H1 [H2 H]]].
  exists (List.filter (fun ss => match ss with (nil, _) => false | _ => true end) lls); repeat split.
  + rewrite H1; clear s1 s2 H1 H2 Hs.
    induction lls as [ | [s1 s2] lls]; simpl; [apply refl_equal | ].
    destruct s1; simpl.
    * apply IHlls; intros; apply H; right; assumption.
    * apply f_equal; apply IHlls; intros; apply H; right; assumption.
  + rewrite H2; clear s1 s2 H1 H2 Hs.
    induction lls as [ | [s1 s2] lls]; simpl; [apply refl_equal | ].
    assert (Aux : match s2 with nil => false | _ => true end = 
                  match s1 with nil => false | _ => true end).
    {
      assert (H3 := H _ _ (or_introl _ (refl_equal _))).
      destruct s1; destruct s2; trivial.
      - inversion H3.
      - inversion H3; subst.
        destruct l1; discriminate.
    }
    rewrite Aux.
    destruct s1; simpl.
    * apply IHlls; intros; apply H; right; assumption.
    * apply f_equal; apply IHlls; intros; apply H; right; assumption.
  + intros p1 p2 Hp; rewrite filter_In in Hp.
    apply H; apply (proj1 Hp).
- revert le1 Hle; induction le2 as [ | e2 le2]; intros [ | e1 le1] Hle.
  + intros e He; contradiction He.
  + inversion Hle.
  + inversion Hle.
  + inversion Hle; subst.
    intros e He; simpl in He; destruct He as [He | He].
    * subst e.
      intros t1 t2 Ht.
      rewrite <- (H2 _ _ Ht); apply sym_eq; apply H2; apply Oeset.compare_eq_refl.
    * apply (IHle2 _ H4 _ He).
- revert le1 Hle; induction le2 as [ | e2 le2]; intros [ | e1 le1] Hle.
  + intros e He; contradiction He.
  + inversion Hle.
  + inversion Hle.
  + inversion Hle; subst.
    intros e He; simpl in He; destruct He as [He | He].
    * subst e.
      intros t1 t2 Ht.
      rewrite (H2 _ _ Ht); apply sym_eq; apply H2; apply Oeset.compare_eq_refl.
    * apply (IHle2 _ H4 _ He).
Qed.

Lemma partition_list_expr_eq_alt :
  forall le1 le2 s1 s2, Forall2 (fun e1 e2 => forall t1 t2, t1 =t= t2 -> e1 t1 = e2 t2) le1 le2 ->
    s1 =PE= s2 -> 
    comparelA (Oeset.compare OLA) 
              (partition_list_expr s1 le1) (partition_list_expr s2 le2) = Eq.
Proof.
intros le1 le2 s1 s2 Hle H.
destruct (partition_list_expr_eq Hle H) as [lls [H1 [H2 H3]]].
rewrite H1, H2; clear le1 le2 s1 s2 H H1 H2 Hle.
induction lls as [ | [p1 p2] lls]; [apply refl_equal | ].
assert (H := H3 _ _ (or_introl _ (refl_equal _))).
rewrite compare_list_t in H.
simpl; simpl in H, IHlls; rewrite H; apply IHlls.
intros; apply H3; right; assumption.
Qed.

Lemma partition_list_expr_invariant :
  forall le s ls, (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    partition_list_expr s le = ls ->
    s =P= flat_map (fun x => x) ls /\
    (s = nil \/ forall s1, List.In s1 ls -> s1 <> nil) /\
    (forall s1 s2, List.In s1 ls -> List.In s2 ls -> 
                   s1 = s2 \/ (forall t, Oeset.mem_bool OA t s1 = true -> 
                                         Oeset.mem_bool OA t s2 = true -> False)) /\
    (forall e s1, List.In e le -> List.In s1 ls -> 
                  forall t1 t2, In t1 s1 -> In t2 s1 -> e t1 = e t2) /\
    (forall s1 s2, List.In s1 ls -> List.In s2 ls ->
     forall t1 t2, In t1 s1 -> In t2 s2 ->
        (forall e, List.In e le -> e t1 = e t2) -> s1 = s2) /\
    all_diff ls.
Proof.
intro le;
induction le as [ | e1 le];
intros s ls Hle H.
- simpl in H; subst ls; repeat split.
  + destruct s; [apply Pnil | ].
    simpl; rewrite <- app_nil_end.
    apply _permut_refl; intros; apply refl_equal.
  + destruct s as [ | t1 s]; [left; apply refl_equal | right; simpl].
    intros s1 [Hs1 | Hs1]; [subst; discriminate | contradiction Hs1].
  + intros s1 s2 Hs1 Hs2.
    destruct s as [ | t1 s]; [contradiction Hs1 | ].
    simpl in Hs1; destruct Hs1 as [Hs1 | Hs1]; [subst s1 | contradiction Hs1].
    simpl in Hs2; destruct Hs2 as [Hs2 | Hs2]; [subst s2 | contradiction Hs2].
    left; apply refl_equal.
  + intros e s1 Abs; contradiction Abs.
  + intros s1 s2 Hs1 Hs2 _ _ _ _ _.
    destruct s as [ | t1 s]; [contradiction Hs1 | ].
    simpl in Hs1; destruct Hs1 as [Hs1 | Hs1]; [subst s1 | contradiction Hs1].
    simpl in Hs2; destruct Hs2 as [Hs2 | Hs2]; [subst s2 | contradiction Hs2].
    apply refl_equal.
  + destruct s; simpl; trivial.
- simpl in H.
  destruct (IHle s _ (fun e h => Hle e (or_intror _ h)) (refl_equal _)) as 
      [IH1 [IH2 [IH3 [IH4 [IH5 IH6]]]]]; clear IHle.
  set (ps := partition_list_expr s le) in *.
  assert (Hps := refl_equal ps); unfold ps at 2 in Hps; clearbody ps.
  repeat split.
  + rewrite <- H.
    refine (_permut_trans _ IH1 _); [intros; subst; apply refl_equal | ].
    clear H IH1 IH2 IH3 IH4 IH5 IH6 Hps; induction ps as [ | p1 ps]; [apply Pnil | ].
    rewrite 2 flat_map_unfold, flat_map_app; apply _permut_app; [ | apply IHps].
    apply (proj1 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
  + destruct s as [ | t s]; [left; apply refl_equal | right].
    destruct IH2 as [IH2 | IH2]; [discriminate IH2 | ].
    intros s1 Hs1; rewrite <- H in Hs1.
    rewrite in_flat_map in Hs1.
    destruct Hs1 as [ss1 [Hss1 Hs1]].
    assert (IH := IH2 _ Hss1); clear IH2.
    apply (in_partition_expr_not_empty e1 ss1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _) Hs1).
  + intros s1 s2 Hs1 Hs2.
    rewrite <- H in Hs1, Hs2.
    rewrite in_flat_map in Hs1, Hs2.
    destruct Hs1 as [ps1 [Hps1 Hs1]].
    destruct Hs2 as [ps2 [Hps2 Hs2]].
    destruct (IH3 _ _ Hps1 Hps2) as [Js | Js].
    * subst ps2.
      apply (proj1 (proj2 (partition_expr_invariant e1 ps1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))));
        assumption.
    * right.
      intros t Ht Kt.
      {
        apply (Js t).
        - assert (Js1 := proj1 (partition_expr_invariant e1 ps1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
          rewrite Oeset.mem_bool_true_iff in Ht.
          destruct Ht as [t1 [Ht Ht1]].
          rewrite Oeset.mem_bool_true_iff; exists t1; split; [assumption | ].
          rewrite (in_permut_in Js1), in_flat_map; exists s1; split; trivial.
        - assert (Js2 := proj1 (partition_expr_invariant e1 ps2 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
          rewrite Oeset.mem_bool_true_iff in Kt.
          destruct Kt as [t1 [Kt Kt1]].
          rewrite Oeset.mem_bool_true_iff; exists t1; split; [assumption | ].
          rewrite (in_permut_in Js2), in_flat_map; exists s2; split; trivial.
      }
  + intros e s1 He Hs1 t1 t2 Ht1 Ht2; simpl in He.
    destruct He as [He | He].
    * subst e.
      rewrite <- H, in_flat_map in Hs1.
      destruct Hs1 as [p1 [Hp1 Kp1]].
      apply (proj1 (proj2 (proj2 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _)))) _ Kp1);
        assumption.
    * rewrite <- H, in_flat_map in Hs1.
      destruct Hs1 as [p1 [Hp1 Hs1]].
      assert (Jp1 := proj1 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
      apply (IH4 e p1 He Hp1);
        rewrite (in_permut_in Jp1), in_flat_map; exists s1; split; trivial.
  + intros s1 s2 Hs1 Hs2 t1 t2 Ht1 Ht2 K.
    rewrite <- H, in_flat_map in Hs1, Hs2.
    destruct Hs1 as [p1 [Hp1 Hs1]].
    destruct Hs2 as [p2 [Hp2 Hs2]].
    assert (IH : p1 = p2).
    {
      assert (Kp1 := proj1 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
      assert (Kp2 := proj1 (partition_expr_invariant e1 p2 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
      apply IH5 with t1 t2; trivial.
      - rewrite (in_permut_in Kp1), in_flat_map; exists s1; split; trivial.
      - rewrite (in_permut_in Kp2), in_flat_map; exists s2; split; trivial.
      - do 2 intro; apply K; right; assumption.
    }
    subst p2.
    apply (proj2 (proj2 (proj2 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))))) with t1 t2;
    trivial.
    apply K; left; apply refl_equal.
  + rewrite <- H.
    clear ls H IH1 IH2.
    clear IH3 IH4 IH4 Hps.
    induction ps as [ | p1 ps]; simpl; [trivial | ].
    rewrite <- all_diff_app_iff; split; [ | split].
    * apply (proj2 (proj2 (proj2 (proj2 (partition_expr_invariant e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _)))))).
    * apply IHps; [do 4 intro; apply IH5; right; assumption | ].
      apply (all_diff_tl _ _ IH6).
    * intros a Ha Ka.
      rewrite in_flat_map in Ka.
      destruct Ka as [s2 [Hs2 Ka]].
      assert (Ja : a <> nil).
      {
        apply (in_partition_expr_not_empty e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _) Ha).
      }
      destruct a as [ | t1 a]; [apply Ja; apply refl_equal | ].
      assert (Abs : s2 = p1).
      {
        apply IH5 with t1 t1.
        - right; assumption.
        - left; apply refl_equal.
        - assert (I1 := proj1 (partition_expr_invariant 
                                 e1 s2 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
          rewrite (in_permut_in I1), in_flat_map.
          exists (t1 :: a); split; [assumption | ].
          left; apply refl_equal.
        - assert (I1 := proj1 (partition_expr_invariant 
                                 e1 p1 (Hle e1 (or_introl _ (refl_equal _))) (refl_equal _))).
          rewrite (in_permut_in I1), in_flat_map.
          exists (t1 :: a); split; [assumption | ].
          left; apply refl_equal.
        - intros; apply refl_equal.
      }
      simpl in IH6.
      destruct ps as [ | p2 ps]; [contradiction Hs2 | ].
      apply (proj1 IH6 s2 Hs2 (sym_eq Abs)).
Qed.

Lemma in_partition_list_expr :
  forall le s p, (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    In p (partition_list_expr s le) -> forall t, List.In t p -> List.In t s.
Proof.
intros le s p Hle Hp t Ht.
assert (H := proj1 (partition_list_expr_invariant le s Hle (refl_equal _))).
rewrite (in_permut_in H), in_flat_map.
exists p; split; trivial.
Qed.

Lemma in_partition_list_expr_diff_nil :
  forall le s,
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall p, In p (partition_list_expr s le) -> s <> nil.
Proof.
  intros le s Hle p Hp.
  destruct s; [ | discriminate].
  assert (_Hp := Hp).
  rewrite partition_list_expr_partition_list_expr2 in _Hp; [ | assumption].
  rewrite filter_In in _Hp; destruct _Hp as [_ _Hp].
  destruct p; [discriminate _Hp | ].
  destruct (partition_list_expr_invariant le nil Hle (refl_equal _)) 
    as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  assert (Abs : In a nil).
  {
    rewrite in_permut_in; [ | apply H1].
    rewrite in_flat_map; eexists; split; [apply Hp | ].
    left; apply refl_equal.
  }
  contradiction Abs.
Qed.

Lemma in_partition_list_expr_filter_1 :
  forall le (t1 : A) p1, 
    (forall e, In e le -> forall t2, In t2 (t1 :: p1) -> e t1 = e t2) ->
       t1 :: p1 = filter (fun t => Oset.eq_bool (mk_olists OVal) (map (fun e => e t) le) 
                                               (map (fun e => e t1) le)) (t1 :: p1).
Proof.
intros le t1 p1 Hp.
set (p := t1 :: p1) in *; clearbody p; clear p1.
induction p as [ | x1 p]; [apply refl_equal | ].
simpl.
assert (Aux : Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e x1) le)
                           (map (fun e : A -> value => e t1) le) = true).
{
  rewrite Oset.eq_bool_true_iff; rewrite <- map_eq.
  intros; apply sym_eq; apply Hp; [ | left]; trivial.
}
rewrite Aux, <- IHp; trivial.
intros; apply Hp; [ | right]; trivial.
Qed.

Lemma in_partition_list_expr_filter_2 :
  forall le t1 p lp,
 (forall s1 s2 : list A,
   In s1 ((t1 :: p) :: lp) ->
   In s2 ((t1 :: p) :: lp) ->
   forall t2 t3 : A,
   In t2 s1 -> In t3 s2 -> (forall e : A -> value, In e le -> e t2 = e t3) -> s1 = s2) ->
  all_diff ((t1 :: p) :: lp) ->
  filter
    (fun t : A =>
     Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
       (map (fun e : A -> value => e t1) le)) (flat_map (fun x : list A => x) lp) = nil.
Proof.
intros le t1 p lp H5 H6.
case_eq (filter
    (fun t : A =>
     Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
                  (map (fun e : A -> value => e t1) le)) (flat_map (fun x : list A => x) lp));
  [intros; trivial | ].
intros t2 l2 H2.
assert (Ht2 : In t2 (t2 :: l2)).
{
  left; apply refl_equal.
}
rewrite <- H2, filter_In in Ht2.
destruct Ht2 as [Ht2 Kt2].
rewrite in_flat_map in Ht2.
destruct Ht2 as [p2 [Ht2 Hp2]].
assert (H : (t1 :: p) <> p2).
{
  simpl in H6; destruct lp; [contradiction Ht2 | ].
  destruct H6 as [H6 _].
  apply H6; assumption.
}
assert (H' : (t1 :: p) = p2).
{
  apply H5 with t1 t2.
  - left; apply refl_equal.
  - right; assumption.
  - left; trivial.
  - assumption.
  - rewrite map_eq.
    rewrite Oset.eq_bool_true_iff in Kt2.
    rewrite Kt2; destruct le; trivial.
}
apply False_rec; apply H; apply H'.
Qed.

Lemma in_partition_list_expr_filter_3 :
  forall le t1 p p1 lp,
  In (t1 :: p) lp ->
  (forall s1 s2 : list A,
   In s1 (p1 :: lp) ->
   In s2 (p1 :: lp) ->
   forall t2 t3 : A,
   In t2 s1 -> In t3 s2 -> (forall e : A -> value, In e le -> e t2 = e t3) -> s1 = s2) ->
  all_diff (p1 :: lp) ->
  filter
    (fun t : A =>
     Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
       (map (fun e : A -> value => e t1) le)) p1 = nil.
Proof.
intros le t1 p p1 lp Hp H5 H6.
case_eq (filter
           (fun t : A =>
              Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
                                 (map (fun e : A -> value => e t1) le)) p1); 
  [intros; trivial | ].
intros t2 l2 H2.
assert (Ht2 : In t2 (t2 :: l2)).
{
  left; apply refl_equal.
}
rewrite <- H2, filter_In in Ht2.
destruct Ht2 as [Ht2 Kt2].
assert (H : p1 <> (t1 :: p)).
{
  simpl in H6.
  destruct lp; [contradiction Hp | ].
  destruct H6 as [H6 _].
  apply H6; assumption.
}
assert (H' : p1 = t1 :: p).
{
  apply H5 with t2 t1.
  - left; apply refl_equal.
  - right; assumption.
  - assumption.
  - left; trivial.
  - rewrite map_eq.
    rewrite Oset.eq_bool_true_iff in Kt2.
    rewrite Kt2; trivial.
}
apply False_rec; apply H; apply H'.
Qed.

Lemma partition_list_expr_eq_permut :
  forall le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall p1 p2, In p1 (partition_list_expr s le) -> In p2 (partition_list_expr s le) ->
                  p1 = p2 <-> _permut (@eq _) p1 p2.
Proof.
intros le s Hle p1 p2 Hp1 Hp2; split; intro Hp.
- subst p2; apply _permut_refl; intros; apply refl_equal.
- destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct H2 as [H2 | H2].
  + subst s; apply False_rec.
    apply (in_partition_list_expr_diff_nil _ Hle _ Hp1); apply refl_equal.
  + destruct p1 as [ | x1 p1]; [apply False_rec; apply (H2 nil); trivial | ].
    destruct p2 as [ | x2 p2]; [apply False_rec; apply (H2 nil); trivial | ].
    destruct (H3 _ _ Hp1 Hp2) as [H | H]; [assumption | ].
    apply False_rec; apply (H x1).
    * rewrite Oeset.mem_bool_unfold; simpl; rewrite Oeset.compare_eq_refl; trivial.
    * rewrite Oeset.mem_bool_true_iff; exists x1; split; [apply Oeset.compare_eq_refl | ].
      rewrite in_permut_in; [ | apply _permut_sym; [intros; subst; trivial | apply Hp]].
      left; apply refl_equal.
Qed.

Lemma partition_list_expr_eq_equiv :
  forall le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall p1 p2, In p1 (partition_list_expr s le) -> In p2 (partition_list_expr s le) ->
                  p1 = p2 <-> Oeset.compare (mk_oelists OA) p1 p2 = Eq.
Proof.
intros le s Hle p1 p2 Hp1 Hp2; split; intro Hp.
- subst p2; apply Oeset.compare_eq_refl.
- destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  destruct H2 as [H2 | H2].
  + subst s; apply False_rec.
    apply (in_partition_list_expr_diff_nil _ Hle _ Hp1); apply refl_equal.
  + destruct p1 as [ | x1 p1]; [apply False_rec; apply (H2 nil); trivial | ].
    destruct p2 as [ | x2 p2]; [apply False_rec; apply (H2 nil); trivial | ].
    destruct (H3 _ _ Hp1 Hp2) as [H | H]; [assumption | ].
    apply False_rec; apply (H x1).
    * rewrite Oeset.mem_bool_unfold; simpl; rewrite Oeset.compare_eq_refl; trivial.
    * rewrite <- (Oeset.mem_bool_eq_2 _ _ _ _ Hp); simpl; unfold Oeset.eq_bool.
      rewrite Oeset.compare_eq_refl; trivial.
Qed.

Lemma in_partition_list_expr_filter :
  forall le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall t1 p, 
      (In (t1 :: p) (partition_list_expr s le) <-> 
       t1 :: p = filter (fun t => Oset.eq_bool (mk_olists OVal) (map (fun e => e t) le) 
                                               (map (fun e => e t1) le))
                        (flat_map (fun x => x) (partition_list_expr s le))).
Proof.
intros le s Hle t1 p.
destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
set (lp := (partition_list_expr s le)) in *; clearbody lp; clear s H1 H2 H3.
split; intro Hp.
- induction lp as [ | p1 lp]; [contradiction Hp | ].
  simpl in Hp; destruct Hp as [Hp | Hp].
  + rewrite flat_map_unfold, filter_app, Hp.
    rewrite <- in_partition_list_expr_filter_1;
      [ | intros e He t2; apply H4; [ | left | left]; trivial].
    subst p1; rewrite (in_partition_list_expr_filter_2 le H5 H6), <- app_nil_end.
    apply refl_equal.
  + rewrite flat_map_unfold, filter_app, (in_partition_list_expr_filter_3 le t1 p Hp H5 H6).
    apply IHlp.
    * do 4 intro; apply H4; [ | right]; assumption. 
    * do 4 intro; apply H5; right; assumption. 
    * apply (all_diff_tl _ _ H6).
    * assumption.
- induction lp as [ | p1 lp]; [discriminate Hp | ].
  destruct p1 as [ | x1 p1].
  + right; apply IHlp.
    * do 4 intro; apply H4; [ | right]; trivial.
    * do 4 intro; apply H5; right; trivial.
    * apply (all_diff_tl _ _ H6).
    * apply Hp.
  + case_eq (Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e x1) le)
           (map (fun e : A -> value => e t1) le)); intro H.
    * left; rewrite Hp.
      rewrite Oset.eq_bool_true_iff in H; rewrite <- H.
      rewrite flat_map_unfold, filter_app.
      rewrite (in_partition_list_expr_filter_2 le H5 H6), <- app_nil_end.
      apply in_partition_list_expr_filter_1.
      do 3 intro; apply H4; [ | left | left]; trivial.
    * {
        right; apply IHlp.
        - do 4 intro; apply H4; [ | right]; trivial.
        - do 4 intro; apply H5; right; trivial.
        - apply (all_diff_tl _ _ H6).
        - rewrite Hp, flat_map_unfold, filter_app.
          replace (filter
                     (fun t : A =>
                        Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
                                     (map (fun e : A -> value => e t1) le)) (x1 :: p1)) with 
              (@nil A); [apply refl_equal | ].
          apply sym_eq.
          apply filter_false.
          intros x Hx; rewrite <- H; apply f_equal2; [ | apply refl_equal].
          rewrite <- map_eq; intros e He; apply H4 with (x1 :: p1); trivial.
          + left; apply refl_equal.
          + left; apply refl_equal.
      }
Qed.

Lemma partition_filter_1 :
  forall le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall p, In p (partition_list_expr s le) -> 
               match p with
               | nil => False
               | t1 :: _ => 
                 _permut (@eq _) p 
                   (filter (fun t => Oset.eq_bool (mk_olists OVal) (map (fun e => e t) le) 
                                                    (map (fun e => e t1) le)) s)
               end.
Proof.
intros le s Hle p Hp.
destruct p as [ | t1 p]; 
    [rewrite partition_list_expr_partition_list_expr2, filter_In in Hp; trivial; 
     destruct Hp as [_ Hp]; discriminate Hp | ].
rewrite (in_partition_list_expr_filter _ _ Hle) in Hp.
rewrite Hp; apply permut_filter.
+ intros; subst; trivial.
+ destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  apply _permut_sym; [ | apply H1].
  intros; subst; trivial.
Qed.

Lemma partition_filter_2 :
  forall le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall t1 p, 
      t1 :: p =  filter (fun t => Oset.eq_bool (mk_olists OVal) (map (fun e => e t) le) 
                                         (map (fun e => e t1) le)) s ->
      exists p1, In p1 (partition_list_expr s le) /\ _permut (@eq _) (t1 :: p) p1.
Proof.
intros le s Hle t1 p Hp.
assert (H : t1 :: p =P=
            filter
              (fun t : A =>
                 Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
                              (map (fun e : A -> value => e t1) le))
              (flat_map (fun x : list A => x) (partition_list_expr s le))).
{
 rewrite Hp; apply permut_filter.
 + intros; subst; trivial.
 + destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
   apply H1.
}
exists (filter
         (fun t : A =>
          Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
            (map (fun e : A -> value => e t1) le)) 
         (flat_map (fun x : list A => x) (partition_list_expr s le))); split; [ | assumption].
case_eq (filter
        (fun t : A =>
         Oset.eq_bool (mk_olists OVal) (map (fun e : A -> value => e t) le)
           (map (fun e : A -> value => e t1) le))
        (flat_map (fun x : list A => x) (partition_list_expr s le))).
- intro K; rewrite K in H; inversion H; subst.
  destruct l1; discriminate.
- intros x1 p1 K.
  rewrite in_partition_list_expr_filter.
  + rewrite <- K; apply filter_eq.
    intros x Hx; apply f_equal.
    assert (Hx1 : In x1 (x1 :: p1)); [left; apply refl_equal | ].
    rewrite <- K, filter_In, Oset.eq_bool_true_iff in Hx1.
    apply sym_eq; apply (proj2 Hx1).
  + assumption.
Qed.

Definition rebuild_keys s le :=
  map (fun g => match g with 
                        | nil => (nil, nil)
                        | t1 :: _ => (map (fun e => e t1) le, g) 
                end) (partition_list_expr s le).

Lemma all_diff_fst_rebuild_keys :
  forall s (le : list (A -> value)),
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    all_diff (map fst (rebuild_keys s le)).
Proof.
intros s le Hle; unfold rebuild_keys.
destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
destruct s as [ | t s'].
- assert (H := in_partition_list_expr_diff_nil (s := nil) _ Hle). 
  destruct (partition_list_expr nil le) as [ | t s'].
  + simpl; trivial.
  + apply False_rec; apply (H t); [left | ]; trivial.
- destruct H2 as [H2 | H2]; [discriminate H2 | ].
  set (s := t :: s') in *; clearbody s; clear t s'.
  set (lp := partition_list_expr s le) in *; clearbody lp; clear s H1.
  induction lp as [ | p1 lp]; [trivial | ].
  assert (H2' : forall s1, In s1 lp -> s1 <> nil).
  {
    intros; apply H2; right; trivial.
  }
  assert (H3' : forall s1 s2 : list A,
             In s1 lp ->
             In s2 lp ->
             s1 = s2 \/
             (forall t : A, Oeset.mem_bool OA t s1 = true -> 
                            Oeset.mem_bool OA t s2 = true -> False)).
  {
    do 4 intro; apply H3; right; trivial.
  }
  assert (H4' : forall (e : A -> value) (s1 : list A),
             In e le -> In s1 lp -> forall t1 t2 : A, In t1 s1 -> In t2 s1 -> e t1 = e t2).
  {
    do 4 intro; apply H4; [ | right]; trivial.
  }
  assert (H5' : forall s1 s2 : list A,
        In s1 lp ->
        In s2 lp ->
        forall t1 t2 : A,
          In t1 s1 -> In t2 s2 -> (forall e : A -> value, In e le -> e t1 = e t2) -> s1 = s2).
  {
    do 4 intro; apply H5; right; trivial.
  }
  assert (H6' := all_diff_tl _ _ H6).
  simpl.
  assert (IH := IHlp H2' H3' H4' H5' H6').
  case_eq (map fst
            (map
               (fun g : list A =>
                match g with
                | nil => (nil, nil)
                | t1 :: _ => (map (fun e : A -> value => e t1) le, g)
                end) lp)); [intros; trivial | ].
  intros k1 lk Hlk.
  split; [ | rewrite <- Hlk; apply IH].
  intros k Hk.
  destruct p1 as [ | t1 p1]; [apply False_rec; apply (H2 nil); [left | ]; trivial | ].
  simpl.
  rewrite map_map in Hlk; rewrite <- Hlk, in_map_iff in Hk.
  destruct Hk as [p2 [Hk Hp2]]; rewrite <- Hk.
  destruct p2 as [ | t2 p2]; [apply False_rec; apply (H2 nil); [right | ]; trivial | ].
  simpl.
  intro Abs; rewrite <- map_eq in Abs.
  assert (Aux : t1 :: p1 = t2 :: p2).
  {
    apply H5 with t1 t2.
    - left; trivial.
    - right; trivial.
    - left; trivial.
    - left; trivial.
    - assumption.
  }
  {
    simpl in H6.
    destruct lp; [contradiction Hp2 | ].
    destruct H6 as [H6 _].
    apply (H6 (t2 :: p2)).
    + assumption.
    + assumption.
  } 
Qed.

Fixpoint flg le acc l :=
  match l with
  | nil => acc
  | t :: l => group (oeset_of_oset (mk_olists OVal))   
                          (fun u => map (fun e : A -> value => e u) le) t  
                          (flg le acc l)
  end.

Lemma flg_app :
  forall le l1 l2 acc,
    flg le acc (l1 ++ l2) = flg le (flg le acc l2) l1.
Proof.
intros le l1; induction l1 as [ | a1 l1]; intros l2 acc; simpl; [apply refl_equal | ].
rewrite IHl1; apply refl_equal.
Qed.

Lemma flg_unfold :
  forall le l acc,
    flg le acc (rev l) = 
    fold_left 
      (fun acc t => 
         group 
           (oeset_of_oset (mk_olists OVal)) 
           (fun u => map (fun e : A -> value => e u) le) t acc) l acc.
Proof.
intros le l; set (n := length l).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert l Hn; induction n as [ | n]; intros l Hn acc.
- destruct l; [ | inversion Hn].
  simpl; trivial.
- destruct l as [ | t1 l]; [simpl; trivial | ].
  simpl in Hn; generalize (le_S_n _ _ Hn); clear Hn; intro Hn.
  simpl; rewrite <- IHn; [ | trivial].
  clear n IHn Hn.
  set (l1 := rev l); clearbody l1.
  revert acc; induction l1 as [ | x1 l1]; intro acc; simpl; [apply refl_equal | ].
  apply f_equal; apply IHl1.
Qed.

Lemma eq_bool_eq_iff :
  forall x1 x2, Oeset.eq_bool (oeset_of_oset (mk_olists OVal)) x1 x2 = true <-> x1 = x2.
Proof.
intros x1 x2; split; intro H.
- unfold oeset_of_oset, Oeset.eq_bool, Oeset.compare in H.
  rewrite compare_eq_true, Oset.compare_eq_iff in H; apply H.
- subst x2; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; trivial.
Qed.

Lemma compare_eq_eq_iff :
  forall x1 x2, Oeset.compare (oeset_of_oset (mk_olists OVal)) x1 x2 = Eq <-> x1 = x2.
Proof.
intros x1 x2; split; intro H.
- unfold oeset_of_oset, Oeset.compare in H.
  rewrite Oset.compare_eq_iff in H; apply H.
- subst x2; rewrite Oeset.compare_eq_refl; trivial.
Qed.

Lemma mem_bool_in_iff :
  forall x l, Oeset.mem_bool (oeset_of_oset (mk_olists OVal)) x l = true <-> In x l.
Proof.
intros x l; split; intro H.
- rewrite Oeset.mem_bool_true_iff in H.
  destruct H as [x' [Hx H]].
  unfold oeset_of_oset, Oeset.compare in Hx.
  rewrite Oset.compare_eq_iff in Hx; subst x'; trivial.
- apply Oeset.in_mem_bool; assumption.
Qed.

Lemma keys_flg :
  forall le l acc, 
  forall k, In k (map fst (flg le acc l)) <-> 
            (In k (map fst acc) \/ In k (map (fun u => map (fun e : A -> value => e u) le) l)).
Proof.
intros le l; induction l as [ | t l]; intros acc k; split; intro Hk.
- left; apply Hk.
- simpl in Hk; simpl.
  destruct Hk as [Hk | Hk]; [apply Hk | contradiction Hk].
- simpl in Hk.
  rewrite keys_of_group in Hk.
  case_eq (Oeset.mem_bool (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e t) le)
          (map fst (flg le acc l)));
    intro H; rewrite H in Hk.
  + rewrite IHl in Hk; destruct Hk as [H1 | H1]; [left; assumption | ].
    right; simpl; right; assumption.
  + destruct (in_app_or _ _ _ Hk) as [HHk | HHk].
    * rewrite IHl in HHk; destruct HHk as [H1 | H1]; [left; assumption | ].
      right; simpl; right; assumption.
    * simpl in HHk; destruct HHk as [HHk | HHk]; [ | contradiction HHk].
      right; simpl; left; trivial.
- simpl in Hk; simpl.
  rewrite keys_of_group.
  case_eq (Oeset.mem_bool (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e t) le)
           (map fst (flg le acc l))); intro Ht.
  + rewrite IHl.
    destruct Hk as [Hk | [Hk | Hk]].
    * left; assumption.
    * subst k; rewrite mem_bool_in_iff, IHl in Ht.
      assumption.
    * right; assumption.
  + apply in_or_app; rewrite IHl.
    destruct Hk as [Hk | [Hk | Hk]].
    * left; left; assumption.
    * right; left; assumption.
    * left; right; assumption.
Qed.

Lemma all_diff_keys_flg :
  forall le s acc, all_diff (map fst acc) -> all_diff (map fst (flg le acc s)).
Proof.
intros le s; induction s as [ | x1 s]; intros acc Ha; [assumption | ].
simpl.
rewrite (Oset.all_diff_bool_ok (mk_olists OVal)).
apply (all_diff_keys_of_group (oeset_of_oset (mk_olists OVal))).
assert (IH := IHs _ Ha).
rewrite (Oset.all_diff_bool_ok (mk_olists OVal)) in IH.
apply IH.
Qed.

Lemma partition_list_expr_fold_inv :
  forall le s,
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    map (fun x => match x with
                  | (k, lk) => (k, rev lk)
                  end) (rebuild_keys s le) = 
        (fold_left 
           (fun acc t => 
              group 
                (oeset_of_oset (mk_olists OVal)) 
                (fun t => map (fun e : A -> value => e t) le) t acc) 
           (flat_map (fun x => x) (partition_list_expr s le)) nil).
Proof.
intros le s Hle.
rewrite <- flg_unfold.
unfold rebuild_keys.
destruct (partition_list_expr_invariant _ s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
assert (H := in_partition_list_expr_diff_nil (s := s) _ Hle). 
destruct s as [ | t1 _s].
- set (lp := partition_list_expr nil le) in *; clearbody lp.
  destruct lp as [ | p1 lp].
  + simpl; trivial.
  + apply False_rec; apply (H p1); [left | ]; trivial.
- clear H.
  destruct H2 as [H2 | H2]; [discriminate H2 | ].
  set (s := t1 :: _s) in *; clearbody s; clear t1 _s.
  set (lp := partition_list_expr s le) in *; clearbody lp.
  clear s H1; rewrite <- (rev_involutive lp) at 1.
  rewrite map_rev, flat_map_rev.
  set (rlp := rev lp).
  assert (H2' : forall s1, In s1 rlp -> s1 <> nil).
    {
      intros; apply H2; rewrite In_rev; assumption.
    }
    assert (H3' : forall s1 s2 : list A,
               In s1 rlp ->
               In s2 rlp ->
               s1 = s2 \/
               (forall t : A, Oeset.mem_bool OA t s1 = true -> 
                              Oeset.mem_bool OA t s2 = true -> False)).
    {
      do 4 intro; apply H3; rewrite In_rev; trivial.
    }
    assert (H4' : forall (e : A -> value) (s1 : list A),
               In e le -> In s1 rlp -> forall t1 t2 : A, In t1 s1 -> In t2 s1 -> e t1 = e t2).
    {
      do 4 intro; apply H4; [ | rewrite In_rev]; trivial.
    }
    assert (H5' : forall s1 s2 : list A,
               In s1 rlp ->
               In s2 rlp ->
               forall t1 t2 : A,
                 In t1 s1 -> In t2 s2 -> 
                 (forall e : A -> value, In e le -> e t1 = e t2) -> s1 = s2).
    {
      do 4 intro; apply H5; rewrite In_rev; trivial.
    }
    assert (H6' : all_diff rlp).
    {
      unfold rlp.
      apply all_diff_rev; assumption.
    }
    clearbody rlp; clear lp H2 H3 H4 H5 H6.
    rewrite map_rev, map_map.
    induction rlp as [ | [ | u1 p1] lp]; 
      [trivial | apply False_rec; apply (H2' nil); [left | ]; trivial | ].
    rewrite flat_map_unfold, flg_app.
    simpl rev; rewrite IHlp.
    set (flg_lp := flg le nil (flat_map (fun a : list A => rev a) lp)).
    assert (K1 : forall x, 
               In x (u1 :: p1) -> 
               Oeset.mem_bool (oeset_of_oset (mk_olists OVal))
                               (map (fun e : A -> value => e x) le) (map fst flg_lp) = false).
    {
      intros x Hx.
      rewrite <- not_true_iff_false, Oeset.mem_bool_true_iff.
      intros [v [Hv1 Hv2]].
      unfold flg_lp in Hv2.
      rewrite keys_flg in Hv2; destruct Hv2 as [Hv3 | Hv3]; [contradiction Hv3 | ].
      rewrite in_map_iff in Hv3.
      destruct Hv3 as [t1 [Hv3 Hv4]]; subst v.
      rewrite in_flat_map in Hv4.
      destruct Hv4 as [p [Hp Hv4]].
      assert (Kv5 : (map (fun e : A -> value => e x) le) =
                        (map (fun e : A -> value => e t1) le)).
      {
        rewrite <- (Oset.eq_bool_true_iff (mk_olists OVal)).
        revert Hv1; unfold Oset.eq_bool; simpl; intro Hv1; rewrite Hv1; trivial.
      }
      rewrite <- map_eq in Kv5.
      assert (Abs : u1 :: p1 = p).
      {
        apply H5' with x t1.
        - left; apply refl_equal.
        - right; assumption.
        - assumption.
        - rewrite In_rev; assumption.
        - assumption.
      }
      rewrite all_diff_unfold in H6'.
      apply (proj1 H6' _ Hp Abs).
    }
    assert (K1' : forall x, 
               In x (rev p1) ->
               Oeset.mem_bool (oeset_of_oset (mk_olists OVal)) 
                              (map (fun e : A -> value => e x) le)
                              (map fst flg_lp) = false).
    {
      intros x Hx; apply K1; right; rewrite In_rev; assumption.
    }
    assert (Hu1 := K1 u1 (or_introl _ (refl_equal _))).
    clear K1.
    assert (K2 : forall x, In x (rev p1) -> 
                           map (fun e : A -> value => e x) le = 
                           map (fun e : A -> value => e u1) le).
    {
      intros x Hx.        
      rewrite <- map_eq; intros e He.
      apply (H4' e (u1 :: p1) He).
      - left; apply refl_equal.
      - right; rewrite In_rev; assumption.
      - left; apply refl_equal.
    }
    set (rp1 := rev p1) in *.
    clearbody flg_lp rp1.
    induction rp1 as [ | x1 l1]; simpl.
  + clear IHlp K1' K2.
    induction flg_lp as [ | [k1 lk1] ls]; [apply refl_equal | ].
    case_eq (Oeset.compare 
                  (oeset_of_oset (mk_olists OVal)) k1 (map (fun e : A -> value => e u1) le));
         intro K3.
    * rewrite (map_unfold _ (_ :: _)) in Hu1.
      simpl fst in Hu1; rewrite Oeset.mem_bool_unfold, Oeset.compare_lt_gt, K3 in Hu1.
      discriminate Hu1.
    * simpl; simpl in K3; rewrite K3, IHls; trivial.
      rewrite (map_unfold _ (_ :: _)), Oeset.mem_bool_unfold, Bool.orb_false_iff in Hu1.
      apply (proj2 Hu1).
    * simpl; simpl in K3; rewrite K3, IHls; trivial.
      rewrite (map_unfold _ (_ :: _)), Oeset.mem_bool_unfold, Bool.orb_false_iff in Hu1.
      apply (proj2 Hu1).
  + rewrite <- IHl1, group_app.
    * rewrite (K2 x1 (or_introl _ (refl_equal _))), Hu1.
      apply f_equal.
      rewrite group_unfold, (K2 x1 (or_introl _ (refl_equal _))), Oeset.compare_eq_refl.
      trivial.
    * intros; apply K1'; right; trivial.
    * intros; apply K2; right; trivial.
  + intros; apply H2'; right; trivial.
  + do 4 intro; apply H3'; right; trivial.
  + do 4 intro; apply H4'; [ | right]; trivial.
  + do 4 intro; apply H5'; right; trivial.
  + rewrite all_diff_unfold in H6'.
    apply (proj2 H6').
Qed.
      
Lemma nb_occ_partition_list_expr :
  forall p le s, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    (Oeset.nb_occ (mk_oelists OA) p (partition_list_expr s le) <= 1)%N.
Proof.
intros p le s Hle.
destruct (partition_list_expr_invariant le s Hle (refl_equal _)) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
assert (H := partition_list_expr_eq_equiv le s Hle).
set (lp := partition_list_expr s le) in *; clearbody lp.
clear H1 H2 H3 H4 H5.
induction lp as [ | p1 lp]; [discriminate | ].
rewrite Oeset.nb_occ_unfold.
case_eq (Oeset.compare (mk_oelists OA) p p1); intro Hp.
- case_eq (Oeset.nb_occ (mk_oelists OA) p lp).
  + intro Kp; discriminate.
  + intros q Hq.
    assert (Kp : Oeset.mem_bool (mk_oelists OA) p lp = true).
    {
      apply Oeset.nb_occ_mem; rewrite Hq; discriminate.
    }
    rewrite (Oeset.mem_bool_eq_1 _ _ _ _ Hp), Oeset.mem_bool_true_iff in Kp.
    destruct Kp as [p2 [Kp Hp2]].
    rewrite <- H in Kp; [ | left | right]; trivial.
    simpl in H6.
    destruct lp; [contradiction Hp2 | ].
    apply False_rec; apply (proj1 H6 p2 Hp2 Kp).
- apply IHlp.
  + simpl in H6; destruct lp; [trivial | ].
    apply (proj2 H6).
  + do 4 intro; apply H; right; trivial.
- apply IHlp.
  + simpl in H6; destruct lp; [trivial | ].
    apply (proj2 H6).
  + do 4 intro; apply H; right; trivial.
Qed.

Definition equiv_groups lk1 lk2 :=
  _permut 
    (fun x1 x2 => Oeset.compare (mk_oepairs (oeset_of_oset (mk_olists OVal)) OLA) x1 x2 = Eq) 
    lk1 lk2.

Lemma equiv_groups_equiv_keys :
  forall lg1 lg2, equiv_groups lg1 lg2 ->
                  _permut (fun x1 x2 => Oeset.compare (oeset_of_oset (mk_olists OVal)) x1 x2 = Eq)
                          (map fst lg1) (map fst lg2).
Proof.
intros lg1 lg2; apply _permut_map.
intros [k1 lk1] [k2 lk2] _ _; simpl.
case (comparelA (Oset.compare OVal) k1 k2); trivial.
Qed.

Lemma group_eq_2 :
  forall le a acc1 acc2,
    equiv_groups acc1 acc2 ->
    all_diff (map fst acc1) ->
    all_diff (map fst acc2) ->
    equiv_groups
      (group (oeset_of_oset (mk_olists OVal))
                   (fun u : A => map (fun e : A -> value => e u) le) a acc1)
      (group (oeset_of_oset (mk_olists OVal))
                   (fun u : A => map (fun e : A -> value => e u) le) a acc2).
Proof.
intros le a acc1s acc2s H' H1' H2'.
rewrite (Oset.all_diff_bool_ok (mk_olists OVal)) in H1', H2'.
rewrite (insert_in_groups 
                (oeset_of_oset (mk_olists OVal))
                (fun u => map (fun e : A -> value => e u) le) a acc1s H1').
rewrite (insert_in_groups 
                (oeset_of_oset (mk_olists OVal))
                (fun u => map (fun e : A -> value => e u) le) a acc2s H2').
assert (H := equiv_groups_equiv_keys H').
rewrite <- (mem_permut_mem _ _ H).
case_eq (Oeset.mem_bool (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e a) le)
        (map fst acc1s)); intro Ha.
- revert H'; apply _permut_map.
  intros [k1 lk1] [k2 lk2] H1 H2; simpl.
  case_eq (comparelA (Oset.compare OVal) k1 k2); intros Hk Hlk; try discriminate Hk.
  unfold Oeset.eq_bool; simpl.
  assert (K : comparelA (Oset.compare OVal) (map (fun e : A -> value => e a) le) k2 =
              comparelA (Oset.compare OVal) (map (fun e : A -> value => e a) le) k1).
  {
    case_eq (comparelA (Oset.compare OVal) (map (fun e : A -> value => e a) le) k1); intro K1.
    - refine (comparelA_eq_trans _ _ _ _ _ K1 Hk).
      do 6 intro; apply Oset.compare_eq_trans.
    - refine (comparelA_lt_le_trans _ _ _ _ _ _ K1 Hk).
      + do 6 intro; apply Oset.compare_eq_trans.
      + do 6 intro; apply Oset.compare_lt_eq_trans.
    - refine (comparelA_gt_eq_trans _ _ _ _ _ _ _ _ _ K1 Hk).
      + do 6 intro; apply Oset.compare_eq_trans.
      + do 6 intro; apply Oset.compare_eq_lt_trans.
      + do 4 intro; apply Oset.compare_lt_gt.
      + do 4 intro; apply Oset.compare_lt_gt.
      + do 4 intro; apply Oset.compare_lt_gt.
  } 
  rewrite K.
  case_eq (comparelA (Oset.compare OVal) (map (fun e : A -> value => e a) le) k1); intro Hk1;
    simpl; rewrite Hk.
  + assert (Hq1 := quick_sorted OA (a :: lk1)).
    assert (Hq2 := quick_sorted OA (a :: lk2)).
    apply (sort_is_unique Hq1 Hq2).
    apply permut_trans with (a :: lk1).
    * apply permut_sym; apply quick_permut.
    * {
        apply permut_trans with (a :: lk2).
        - apply permut_cons; [apply Oeset.compare_eq_refl | ].
          apply permut_trans with (quicksort OA lk1).
          + apply quick_permut.
          + apply permut_trans with (quicksort OA lk2); [ | apply permut_sym; apply quick_permut].
            apply permut_refl_alt; apply Hlk.
        - apply quick_permut.
      }
  + assumption.
  + assumption.
  + discriminate Hlk.
  + discriminate Hlk.
- apply _permut_app; [apply H' | ].
  apply permut_cons; [ | apply Pnil].
  apply Oeset.compare_eq_refl.
Qed.

Lemma flg_eq_2 :
  forall le,     
    forall s acc1 acc2, equiv_groups acc1 acc2 -> 
                        all_diff (map fst acc1) -> all_diff (map fst acc2) ->
                        equiv_groups (flg le acc1 s) (flg le acc2 s).
Proof.
intros le s; induction s as [ | a s]; intros acc1 acc2 H H1 H2; [apply H | ].
simpl.
assert (H' := IHs _ _ H H1 H2).
apply group_eq_2.
- assumption.
- apply (all_diff_keys_flg); assumption.
- apply (all_diff_keys_flg); assumption.
Qed.

Lemma proj_eq :
  forall le,
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    (forall b1 b2 : A,
         b1 =t= b2 ->
         Oeset.compare (oeset_of_oset (mk_olists OVal))
           ((fun u : A => map (fun e : A -> value => e u) le) b1)
           ((fun u : A => map (fun e : A -> value => e u) le) b2) = Eq).
Proof.
intros le Hle x1 x2 Hx.
induction le as [ | e1 le]; [trivial | ].
simpl; rewrite (Hle e1) with x1 x2, Oset.compare_eq_refl.
- apply IHle.
  do 2 intro; apply Hle; right; assumption.
- left; apply refl_equal.
- assumption.
Qed.

Lemma flg_eq_3 :
  forall le,
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall s1 s2 acc, comparelA (fun x y => Oeset.compare OA x y) s1 s2 = Eq ->
  all_diff (map fst acc) -> equiv_groups (flg le acc s1) (flg le acc s2).
Proof.
intros le Hle s1; induction s1 as [ | a1 s1]; intros [ | a2 s2] acc Hs Hacc.
- apply permut_refl.
- discriminate Hs.
- discriminate Hs.
- rewrite comparelA_unfold in Hs.
  case_eq (Oeset.compare OA a1 a2); intro Ha; rewrite Ha in Hs; try discriminate Hs.
  replace (a1 :: s1) with ((a1 :: nil) ++ s1); [ | trivial].
  replace (a2 :: s2) with ((a2 :: nil) ++ s2); [ | trivial].
  rewrite 2 flg_app.
  apply permut_trans with (flg le (flg le acc s2) (a1 :: nil)).
  + apply flg_eq_2.
    * apply IHs1; trivial.
    * apply all_diff_keys_flg; trivial.
    * apply all_diff_keys_flg; trivial.
  + set (acc2 := flg le acc s2).
    apply permut_refl_alt; simpl.
    assert (Aux := group_eq_1 
                     (oeset_of_oset (mk_olists OVal))   
                     (fun u => map (fun e : A -> value => e u) le) OA (proj_eq _ Hle) _ _ acc2 Ha).
    simpl in Aux; simpl.
    set (lg1 := (group (oeset_of_oset (mk_olists OVal))
             (fun u : A => map (fun e : A -> value => e u) le) a1 acc2)) in *.
    set (lg2 := (group (oeset_of_oset (mk_olists OVal)) 
                  (fun u : A => map (fun e : A -> value => e u) le) a2 acc2)) in *.
    clearbody lg1 lg2.
    revert lg2 Aux; induction lg1 as [ | [k1 lk1] lg1]; intros [ | [k2 lk2] lg2] H;
      try discriminate H; trivial.
    simpl in H; simpl.
    case_eq (comparelA (Oset.compare OVal) k1 k2); intro Hk; rewrite Hk in H; try discriminate H.
    case_eq (comparelA (Oeset.compare OA) lk1 lk2); intro Hlk; rewrite Hlk in H;
      try discriminate H.
    rewrite (IHlg1 _ H).
    assert (Hq1 := quick_sorted OA lk1).
    assert (Hq2 := quick_sorted OA lk2).
    assert (Hq := sort_is_unique Hq1 Hq2).
    simpl in Hq; rewrite Hq; trivial.
    apply permut_trans with lk1; [apply permut_sym; apply quick_permut | ].
    apply permut_trans with lk2; [ | apply quick_permut].
    apply permut_refl_alt; apply Hlk.
Qed.    

Lemma group_switch :
  forall le lg a1 a2 , 
      equiv_groups (group (oeset_of_oset (mk_olists OVal))   
                          (fun u => map (fun e : A -> value => e u) le) a1
                          (group (oeset_of_oset (mk_olists OVal))   
                                       (fun u => map (fun e : A -> value => e u) le) a2 lg))
                   (group (oeset_of_oset (mk_olists OVal))   
                          (fun u => map (fun e : A -> value => e u) le) a2
                          (group (oeset_of_oset (mk_olists OVal))   
                                       (fun u => map (fun e : A -> value => e u) le) a1 lg)).
Proof.
intros le lg a1 a2.
case_eq (Oeset.mem_bool 
           (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e a1) le) (map fst lg));
        intro Ha1.
- destruct (insert_in_one_group 
              (oeset_of_oset (mk_olists OVal)) 
              (fun u => map (fun e : A -> value => e u) le) a1 lg Ha1)
  as [lg1 [lg2 [k [lk [Hlg [Hlg1 [Hk H]]]]]]].
  rewrite H.
  case_eq (Oeset.mem_bool 
           (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e a2) le) (map fst lg));
        intro Ha2.
  + destruct (insert_in_one_group
              (oeset_of_oset (mk_olists OVal)) 
              (fun u => map (fun e : A -> value => e u) le) a2 lg Ha2)
  as [lg1' [lg2' [k' [lk' [Hlg' [Hlg1' [Hk' H']]]]]]].
  rewrite H'.
  rewrite Hlg in Hlg'.
  destruct (split_list_2 _ _ _ _ _ _ Hlg') as [[H1 | H1] | H1].
  * destruct H1 as [ll [H1 H2]].
    rewrite H1, H2; rewrite <- ass_app; simpl.
    apply permut_trans with (lg1' ++ (k', a2 :: lk') :: ll ++ (k, a1 :: lk) :: lg2).
    {
      rewrite app_comm_cons, ass_app, insert_in_one_group_alt, <- ass_app, app_comm_cons.
      - apply permut_refl.
      - rewrite <- Hlg1, H1, 2 map_app; simpl.
        apply refl_equal.
      - assumption.
    }
    {
      rewrite insert_in_one_group_alt.
      - apply permut_refl.
      - assumption.
      - assumption.
    }
  * destruct H1 as [ll [H1 H2]]; rewrite H1, H2.
    apply permut_trans with (lg1 ++ (k, a1 :: lk) :: ll ++ (k', a2 :: lk') :: lg2').
    {
      rewrite <- ass_app, <- app_comm_cons, insert_in_one_group_alt.
      - apply permut_refl.
      - assumption.
      - assumption.
    }
    {
      rewrite 2 app_comm_cons, 2 ass_app, insert_in_one_group_alt.
      - apply permut_refl.
      - rewrite <- Hlg1', H1, 2 map_app; simpl.
        apply refl_equal.
      - assumption.
    }
  * destruct H1 as [H1 [H2 H3]]; injection H1; clear H1; do 2 intro; subst k' lk' lg1' lg2'.
    apply permut_trans with (lg1 ++ (k, a1 :: a2 :: lk) :: lg2).
    {
      rewrite insert_in_one_group_alt.
      - apply permut_refl.
      - assumption.
      - assumption.
    }
    {
      rewrite insert_in_one_group_alt.
      - apply permut_refl_alt.
        apply comparelA_eq_app.
        + apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl.
        + rewrite comparelA_unfold, comparelA_eq_refl; [ | intros; apply Oeset.compare_eq_refl].
          unfold mk_oepairs, Oeset.compare.
          unfold oeset_of_oset.
          rewrite compareAB_unfold, Oset.compare_eq_refl.
          assert (Aux := sort_is_unique (quick_sorted OA (a1 :: a2 :: lk)) 
                                        (quick_sorted OA (a2 :: a1 :: lk))); simpl; simpl in Aux.
          rewrite Aux; [trivial | ].
          refine (permut_trans _ _ (quick_permut _ _)).
          apply permut_sym; refine (permut_trans _ _ (quick_permut _ _)).
          apply (Pcons (R := fun x1 x2 => Oeset.compare OA x1 x2 = Eq) a2 a2 (l := a1 :: lk)
                       (a1 :: nil) lk (Oeset.compare_eq_refl _ _)).
          apply permut_refl.
      - assumption.
      - assumption.
    }
  + rewrite (insert_in_groups_weak (oeset_of_oset (mk_olists OVal))
                                    (fun u : A => map (fun e : A -> value => e u) le) a2 lg Ha2).
    rewrite group_app, Ha1, H.
    rewrite (insert_in_groups_weak (oeset_of_oset (mk_olists OVal))
                                    (fun u : A => map (fun e : A -> value => e u) le) a2).
    * apply permut_refl.
    * rewrite <- Ha2, Hlg, 2 map_app; simpl; apply refl_equal.
- rewrite (insert_in_groups_weak (oeset_of_oset (mk_olists OVal))
                                    (fun u : A => map (fun e : A -> value => e u) le) a1 lg Ha1).
  case_eq (Oeset.mem_bool 
           (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e a2) le) (map fst lg));
        intro Ha2.
  + destruct (insert_in_one_group
              (oeset_of_oset (mk_olists OVal)) 
              (fun u => map (fun e : A -> value => e u) le) a2 lg Ha2)
  as [lg1' [lg2' [k' [lk' [Hlg' [Hlg1' [Hk' H']]]]]]].
  rewrite H'.
  rewrite (insert_in_groups_weak (oeset_of_oset (mk_olists OVal))
                                    (fun u : A => map (fun e : A -> value => e u) le) a1).
    * rewrite group_app, Ha2, H'.
      apply permut_refl.
    * rewrite <- Ha1, Hlg', 2 map_app; apply refl_equal.
  + rewrite (insert_in_groups_weak 
               (oeset_of_oset (mk_olists OVal))
               (fun u : A => map (fun e : A -> value => e u) le) a2 lg Ha2).
    rewrite 2 group_app, Ha1, Ha2.
    apply permut_app1.
    rewrite 4 group_unfold, Oeset.compare_lt_gt.
    case_eq (Oeset.compare (oeset_of_oset (mk_olists OVal)) (map (fun e : A -> value => e a1) le)
           (map (fun e : A -> value => e a2) le)); intro Ha;
      simpl CompOpp; cbv beta iota zeta.
    * unfold oeset_of_oset, Oeset.compare in Ha.
      rewrite Oset.compare_eq_iff in Ha; rewrite <- Ha.
      apply permut_refl_alt; rewrite comparelA_unfold.
      unfold mk_oepairs, Oeset.compare, oeset_of_oset.
      rewrite compareAB_unfold, Oset.compare_eq_refl; simpl.
      assert (Aux := sort_is_unique (quick_sorted OA (a1 :: a2 :: nil)) 
                                    (quick_sorted OA (a2 :: a1 :: nil))); simpl; simpl in Aux.
      rewrite Aux; [trivial | ].
      refine (permut_trans _ _ (quick_permut _ _)).
      apply permut_sym; refine (permut_trans _ _ (quick_permut _ _)).
      apply (Pcons (R := fun x1 x2 => Oeset.compare OA x1 x2 = Eq) a2 a2 (l := a1 :: nil)
                       (a1 :: nil) nil (Oeset.compare_eq_refl _ _)).
      apply permut_refl.
    * {
        apply (Pcons 
               (map (fun e : A -> value => e a2) le, a2 :: nil)
               (map (fun e : A -> value => e a2) le, a2 :: nil)
               (l := (map (fun e : A -> value => e a1) le, a1 :: nil) :: nil) 
               ((map (fun e : A -> value => e a1) le, a1 :: nil) :: nil) nil). 
        - apply Oeset.compare_eq_refl.
        - rewrite <- app_nil_end; apply permut_refl.
      }
    * {
        apply (Pcons 
               (map (fun e : A -> value => e a2) le, a2 :: nil)
               (map (fun e : A -> value => e a2) le, a2 :: nil)
               (l := (map (fun e : A -> value => e a1) le, a1 :: nil) :: nil) 
               ((map (fun e : A -> value => e a1) le, a1 :: nil) :: nil) nil). 
        - apply Oeset.compare_eq_refl.
        - rewrite <- app_nil_end; apply permut_refl.
      }
Qed.

Lemma flg_switch :
  forall le acc lg1 a1 a2 lg2 , all_diff (map fst acc) ->
      equiv_groups (flg le acc (lg1 ++ a1 :: a2 :: lg2)) (flg le acc (lg1 ++ a2 :: a1 :: lg2)).
Proof.
intros le acc lg1 a1 a2 lg2 Hacc.
rewrite 2 flg_app; apply flg_eq_2.
- simpl; apply group_switch.
- apply all_diff_keys_flg; assumption.
- apply all_diff_keys_flg; assumption.
Qed.

Lemma flg_permut :
  forall le, 
    (forall e, In e le -> forall t1 t2, t1 =t= t2 -> e t1 = e t2) ->
    forall acc1 acc2 lg1 lg2, 
        equiv_groups acc1 acc2 -> all_diff (map fst acc1) ->  all_diff (map fst acc2) -> 
        (_permut (fun x y => Oeset.compare OA x y = Eq) lg1 lg2) ->
        equiv_groups (flg le acc1 lg1) (flg le acc2 lg2).
Proof.
intros le Hle acc1 acc2 lg1 lg2 Hacc Hacc1 Hacc2 Hlg.
rewrite <- permut_i_Si_permut in Hlg.
unfold equiv_groups; rewrite <- permut_i_Si_permut.
- revert acc1 acc2 Hacc Hacc1 Hacc2.
  induction Hlg; intros acc1 acc2 Hacc Hacc1 Hacc2.
  + constructor 3 with (flg le acc1 l2); 
      [ | rewrite permut_i_Si_permut; [apply flg_eq_2; trivial | ]].
    * {
        rewrite permut_i_Si_permut.
        - apply (flg_eq_3 le Hle l1 l2 acc1); trivial.
          revert l2 H; 
            induction l1 as [ | x1 l1]; intros [ | x2 l2] H; try inversion H; subst; trivial.
          simpl; rewrite H3; apply IHl1; trivial.
        - split.
          + intro; apply Oeset.compare_eq_refl.
          + do 3 intro; apply Oeset.compare_eq_trans.
          + do 2 intro; apply Oeset.compare_eq_sym.
      } 
    * {
        split.
        - intro; apply Oeset.compare_eq_refl.
        - do 3 intro; apply Oeset.compare_eq_trans.
        - do 2 intro; apply Oeset.compare_eq_sym.
      }
  + inversion H; subst.
    rewrite permut_i_Si_permut.
    *
      {
        apply permut_trans with (flg le acc1 (l0 ++ a2 :: b2 :: l3)).
        - apply flg_eq_3; trivial.
          clear H; induction l0 as [ | x0 l0]; simpl.
          + rewrite H0, H1.
            apply comparelA_eq_refl.
            intros; apply Oeset.compare_eq_refl.
          + rewrite Oeset.compare_eq_refl; apply IHl0.
        - apply permut_trans with  (flg le acc1 (l0 ++ b2 :: a2 :: l3)).
          + apply flg_switch; trivial.
          + apply flg_eq_2; trivial.
      }
    * {
        split.
        - intro; apply Oeset.compare_eq_refl.
        - do 3 intro; apply Oeset.compare_eq_trans.
        - do 2 intro; apply Oeset.compare_eq_sym.
      }
  + constructor 3 with (flg le acc1 l2).
    * apply IHHlg1; trivial.
      apply permut_refl.
    * apply IHHlg2; trivial.
- split.
  + intro; apply Oeset.compare_eq_refl.
  + do 3 intro; apply Oeset.compare_eq_trans.
  + do 2 intro; apply Oeset.compare_eq_sym.
- split.
  + intro; apply Oeset.compare_eq_refl.
  + do 3 intro; apply Oeset.compare_eq_trans.
  + do 2 intro; apply Oeset.compare_eq_sym.
Qed.

End Sec.
