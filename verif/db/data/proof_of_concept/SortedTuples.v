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

Require Import Arith NArith ZArith String List. 
Require Import ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData.
Require Import compcert.common.Values.

Module Tuple1.

Section Sec.

Hypothesis attribute : Type.
Hypothesis type : Type. 
Hypothesis value : Type.
Hypothesis type_of_attribute : attribute -> type. 
Hypothesis type_of_value : value -> type.
Hypothesis default_value : type -> value. 
Hypothesis OAtt : Oset.Rcd attribute. 
Hypothesis FAN : Fset.Rcd OAtt.
Hypothesis OT : Oset.Rcd type.
Hypothesis OVal : Oset.Rcd value.
Hypothesis FVal : Fset.Rcd OVal.

Definition tuple := (Fset.set FAN * (attribute -> value))%type.
Definition aug_tuple := (tuple * val)%type.

Definition abs: aug_tuple -> tuple := fst.

Definition support := fun (t : aug_tuple) => fst (abs t).

Definition dot := fun (t : aug_tuple) a => match t with ((_,f), _) => f a end.

Definition address := fun (t : aug_tuple) => snd t.

Definition mk_tuple (fa : Fset.set FAN) (f : attribute -> value) (p: val) : aug_tuple := ((fa, f), p).

Lemma support_mk_tuple_ok : forall fa f p, support (mk_tuple fa f p) =S= fa.
Proof.
intros fa f p; unfold mk_tuple; simpl; rewrite Fset.equal_spec; intros; apply refl_equal.
Qed.

Lemma dot_mk_tuple_ok : forall a fa f p, a inS fa -> dot (mk_tuple fa f p) a = f a.
Proof.
intros a fa f p Ha; unfold mk_tuple; simpl; apply refl_equal.
Qed.

Lemma address_mk_tuple_ok :
  forall (s : Fset.set FAN) (f : attribute -> value) (p : val), address (mk_tuple s f p) = p.
Proof.
  easy.
Qed. 

Definition tuple_compare (t1 t2 : aug_tuple) : comparison :=
  match t1, t2 with
      | ((fa1, f1), p1), ((fa2, f2), p2) =>
        compareAB (Fset.compare FAN) (comparelA (Oset.compare OVal)) (fa1, map f1 (Fset.elements FAN fa1)) (fa2, map f2 (Fset.elements FAN fa2))
end.

Definition OTuple : Oeset.Rcd aug_tuple.
Proof.
split with tuple_compare; unfold aug_tuple, tuple_compare.
- (* 1/5 *)
  intros [[fa1 t1] p1] [[fa2 t2] p2] [[fa3 t3] p3].
  apply compareAB_eq_trans.
  + apply Fset.compare_eq_trans.
  + apply comparelA_eq_trans.
    do 6 intro; apply Oset.compare_eq_trans.
- (* 1/4 *)
  intros [[fa1 t1] p1] [[fa2 t2] p2] [[fa3 t3] p3].
  apply compareAB_le_lt_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_eq_lt_trans.
  + apply comparelA_le_lt_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_eq_lt_trans.
- (* 1/3 *)
  intros [[fa1 t1] p1] [[fa2 t2] p2] [[fa3 t3] p3].
  apply compareAB_lt_le_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_lt_eq_trans.
  + apply comparelA_lt_le_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_lt_eq_trans.
- (* 1/2 *)
  intros [[fa1 t1] p1] [[fa2 t2] p2] [[fa3 t3] p3].
  apply compareAB_lt_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_eq_lt_trans.
  + apply Fset.compare_lt_eq_trans.
  + apply Fset.compare_lt_trans.
  + apply comparelA_lt_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_eq_lt_trans.
    * do 6 intro; apply Oset.compare_lt_eq_trans.
    * do 6 intro; apply Oset.compare_lt_trans.
- (* 1/1 *)
  intros [[fa1 t1] p1] [[fa2 t2] p2].
  apply compareAB_lt_gt.
  + apply Fset.compare_lt_gt.
  + apply comparelA_lt_gt.
    do 4 intro; apply Oset.compare_lt_gt.
Defined.

Definition FT : Feset.Rcd OTuple := Feset.build OTuple.
Definition BT : Febag.Rcd OTuple := Febag.build OTuple.
Definition CT := Fecol.mk_R FT BT.

Lemma tuple_eq_ok : 
  forall t1 t2, Oeset.compare OTuple t1 t2 = Eq <->
   support t1 =S= support t2 /\ (forall a, a inS support t1 -> dot t1 a = dot t2 a).
Proof.
intros [[fa1 f1] p1] [[fa2 f2] p2].
simpl support; simpl dot.
unfold Oeset.compare, FT, Feset.build, OTuple.
unfold tuple_compare.
unfold compareAB.
case_eq (Fset.compare FAN fa1 fa2); intro Hfa.
- cbn. rewrite <- Fset.compare_spec, Hfa.
  split.
  + intro Hf.
    split; [apply refl_equal | ].
    intros a Ha.
    rewrite Fset.compare_spec in Hfa.
    rewrite <- (Fset.elements_spec1 _ _ _ Hfa) in Hf.
    assert (Aux : map f1 ({{{fa1}}}) = map f2 ({{{fa1}}})).
    {
      assert (Aux := comparelA_eq_bool_ok (Oset.compare OVal)
                                        (map f1 ({{{fa1}}})) (map f2 ({{{fa1}}}))).
      rewrite Hf in Aux.
      apply Aux.
      intros; apply Oset.eq_bool_ok.
    } 
    rewrite <- map_eq in Aux.
    apply Aux.
    rewrite Fset.mem_elements, Oset.mem_bool_true_iff in Ha.
    apply Ha.
  + intros [_ Hf].
    rewrite Fset.compare_spec in Hfa.
    rewrite <- (Fset.elements_spec1 _ _ _ Hfa).
    replace (map f2 ({{{fa1}}})) with (map f1 ({{{fa1}}})).
    * apply comparelA_eq_refl.
      intros; apply Oset.compare_eq_refl.
    * rewrite <- map_eq.
      intros a Ha; apply Hf.
      rewrite Fset.mem_elements, Oset.mem_bool_true_iff; assumption.
- split; [intro Abs; discriminate Abs | ].
  intros [Abs _]; rewrite <- Fset.compare_spec in Abs.
  rewrite <- Hfa, <- Abs.
  apply refl_equal.
- split; [intro Abs; discriminate Abs | ].
  intros [Abs _]; rewrite <- Fset.compare_spec in Abs.
  rewrite <- Hfa, <- Abs.
  apply refl_equal.
Qed.

Definition T : Tuple.Rcd :=
(@Tuple.mk_R attribute type value type_of_attribute
                      type_of_value default_value _ FAN OT _ FVal
                       _ support dot address mk_tuple support_mk_tuple_ok dot_mk_tuple_ok address_mk_tuple_ok _ CT tuple_eq_ok).

End Sec.

End Tuple1.

(** ** Definition of variable names *)
Inductive varname : Set := VarN : N -> varname.

Definition VarN_of_N := VarN.
Definition N_of_VarN : varname -> N := 
 fun a => match a with VarN n => n end.

Definition OVN : Oset.Rcd varname.
apply Oemb with N_of_VarN.
intros [a1] [a2] H; simpl in H; apply f_equal; assumption.
Defined.

Require Import SortedAttributes Values.

Definition T : Tuple.Rcd := 
  Tuple1.T attribute Values.type Values.value 
           type_of_attribute Values.type_of_value Values.default_value 
           OAN FAN Values.OT Values.OVal Values.FVal.



