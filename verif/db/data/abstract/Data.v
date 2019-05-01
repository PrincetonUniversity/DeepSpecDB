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

Require Import Bool List NArith.
Require Import  BasicFacts ListFacts OrderedSet ListPermut FiniteSet FiniteBag.

(* Abstact *)
Module AData.

Record Rcd (data : Type) (OD : Oeset.Rcd data) : Type :=
  mk_R
    {
      att : Type;
      OAtt : Oset.Rcd att;
      FAtt : Fset.Rcd OAtt;
      empty_d : data;
      support : data -> Fset.set FAtt;
      support_eq : forall x1 x2, Oeset.compare OD x1 x2 = Eq -> support x1 =S= support x2;
    }.

End AData.

(* Map *)
Module MData.

Record Rcd (data : Type) (OD : Oeset.Rcd data) (AD : AData.Rcd _ OD) : Type :=
  mk_R
    {
      projection : Fset.set (AData.FAtt _ _ AD) -> data -> data;
      projection_eq_2 : 
        forall s x1 x2, Oeset.compare OD x1 x2 = Eq -> 
                        Oeset.compare OD (projection s x1) (projection s x2) = Eq;

      projection_idem : forall s1 s2, 
          Fset.subset (AData.FAtt _ _ AD) s1 s2 = true ->
          forall x, Oeset.compare OD (projection s1 (projection s2 x)) (projection s1 x) = Eq;

      projection_support_eq : 
        forall s t, s =S= AData.support _ _ AD t -> Oeset.compare OD (projection s t) t = Eq;
      support_projection_eq :
        forall s t, AData.support _ _ AD (projection s t) =S= s;
    }.

End MData.


(* Combine *)
Module CData.

Record Rcd (data : Type) (OD : Oeset.Rcd data) 
       (AD : AData.Rcd _ OD) (MD : MData.Rcd _ _ AD) : Type :=
  mk_R
    {
      compatible : data -> data -> bool;
      combine : data -> data -> data;
      combine_eq_1 :
        forall x1 x1' x2, Oeset.compare OD x1 x1' = Eq -> 
                          Oeset.compare OD (combine x1 x2) (combine x1' x2) = Eq;
      combine_eq_2 :
        forall x1 x2 x2', Oeset.compare OD x2 x2' = Eq -> 
                          Oeset.compare OD (combine x1 x2) (combine x1 x2') = Eq;
      combine_empty_2 : forall x, Oeset.compare OD (combine x (AData.empty_d _ _ AD)) x = Eq;

      combine_comm :
        forall u1 u2, compatible u1 u2 = true -> 
                      Oeset.compare OD (combine u1 u2) (combine u2 u1) = Eq;
      combine_assoc :
        forall u1 u2 u3, 
          Oeset.compare OD (combine u1 (combine u2 u3)) (combine (combine u1 u2) u3) = Eq;

      support_combine : 
        forall u u1 u2, Oeset.compare OD u (combine u1 u2) = Eq -> 
                        AData.support _ _ AD u =S= 
                        (AData.support _ _ AD u1 unionS AData.support _ _ AD u2);

      compatible_combine_1 :
        forall u1 u2 u3, compatible u1 u2 = true ->
                         compatible (combine u1 u2) u3 = 
                         compatible u1 u3 && compatible u2 u3;
      compatible_combine_2 :
        forall u1 u2 u3, compatible u2 u3 = true ->
                         compatible u1 (combine u2 u3) = 
                         compatible u1 u2 && compatible u1 u3;
      split_d :
        forall s1 s2 t x1 x2,
          AData.support _ _ AD x1 =S= s1 -> AData.support _ _ AD x2 =S= s2 -> 
          compatible x1 x2 = true ->
          (Oeset.compare OD t (combine x1 x2) = Eq) <-> 
          (Oeset.compare OD x1 (MData.projection _ _ _ MD s1 t) = Eq /\ 
           Oeset.compare OD x2 (MData.projection _ _ _ MD s2 t) = Eq /\ 
           AData.support _ _ AD t =S= (s1 unionS s2))
    }.

End CData.

Module Data.

Record Rcd (data : Type) (OD : Oeset.Rcd data) : Type :=
  mk_R
    {
      att : Type;
      OAtt : Oset.Rcd att;
      FAtt : Fset.Rcd OAtt;
      empty_d : data;
      support : data -> Fset.set FAtt;
      projection : Fset.set FAtt -> data -> data;
      compatible : data -> data -> bool;
      combine : data -> data -> data;

      support_eq : forall x1 x2, Oeset.compare OD x1 x2 = Eq -> support x1 =S= support x2;
      projection_eq_2 : 
        forall s x1 x2, Oeset.compare OD x1 x2 = Eq -> 
                        Oeset.compare OD (projection s x1) (projection s x2) = Eq;

      projection_idem : forall s1 s2, 
          Fset.subset FAtt s1 s2 = true ->
          forall x, Oeset.compare OD (projection s1 (projection s2 x)) (projection s1 x) = Eq;

      projection_support_eq : 
        forall s t, s =S= support t -> Oeset.compare OD (projection s t) t = Eq;
      support_projection_eq :
        forall s t, support (projection s t) =S= s;

      compatible_eq_1 :
        forall x1 x1' x2, Oeset.compare OD x1 x1' = Eq -> 
                          compatible x1 x2 = compatible x1' x2;
      compatible_eq_2 :
        forall x1 x2 x2', Oeset.compare OD x2 x2' = Eq -> 
                          compatible x1 x2 = compatible x1 x2';

      compatible_projection :
        forall s1 s2 t, compatible (projection s1 t) (projection s2 t) = true;
      compatible_comm : 
        forall u1 u2, compatible u1 u2 = compatible u2 u1;

      combine_eq_1 :
        forall x1 x1' x2, Oeset.compare OD x1 x1' = Eq -> 
                          Oeset.compare OD (combine x1 x2) (combine x1' x2) = Eq;
      combine_eq_2 :
        forall x1 x2 x2', Oeset.compare OD x2 x2' = Eq -> 
                          Oeset.compare OD (combine x1 x2) (combine x1 x2') = Eq;
      combine_empty_2 : forall x, Oeset.compare OD (combine x empty_d) x = Eq;

      combine_comm :
        forall u1 u2, compatible u1 u2 = true -> 
                      Oeset.compare OD (combine u1 u2) (combine u2 u1) = Eq;
      combine_assoc :
        forall u1 u2 u3, 
          Oeset.compare OD (combine u1 (combine u2 u3)) (combine (combine u1 u2) u3) = Eq;

      support_combine : 
        forall u u1 u2, Oeset.compare OD u (combine u1 u2) = Eq -> 
                        support u =S= (support u1 unionS support u2);

      compatible_combine_1 :
        forall u1 u2 u3, compatible u1 u2 = true ->
                         compatible (combine u1 u2) u3 = 
                         compatible u1 u3 && compatible u2 u3;
      compatible_combine_2 :
        forall u1 u2 u3, compatible u2 u3 = true ->
                         compatible u1 (combine u2 u3) = 
                         compatible u1 u2 && compatible u1 u3;
      split_d :
        forall s1 s2 t x1 x2,
          support x1 =S= s1 -> support x2 =S= s2 -> compatible x1 x2 = true ->
          (Oeset.compare OD t (combine x1 x2) = Eq) <-> 
          (Oeset.compare OD x1 (projection s1 t) = Eq /\ 
           Oeset.compare OD x2 (projection s2 t) = Eq /\ 
           support t =S= (s1 unionS s2))
    }.

Section Sec.

Hypothesis data : Type.
Hypothesis OD : Oeset.Rcd data.
Hypothesis D : Data.Rcd data OD.

Notation "x1 '=d=' x2" := (Oeset.compare OD x1 x2 = Eq) (at level 70, no associativity).
Notation "l1 '=P=' l2" := (_permut (@eq data) l1 l2) (at level 70, no associativity).
Notation "l1 '=PE=' l2" := (_permut (fun x y => Oeset.compare OD x y = Eq) l1 l2) 
                             (at level 70, no associativity).
Arguments combine {data} {OD}.
Arguments combine_eq_1 {data} {OD}.
Arguments combine_eq_2 {data} {OD}.
Arguments empty_d {data} {OD}.
Arguments support {data} {OD}.
Arguments support_eq {data} {OD}.
Arguments projection {data} {OD}.
Arguments projection_eq_2 {data} {OD}.
Arguments compatible {data} {OD}.
Arguments compatible_eq_1 {data} {OD}.
Arguments compatible_eq_2 {data} {OD}.
Arguments support_combine {data} {OD}.
Arguments support_projection_eq {data} {OD}.
Arguments split_d {data} {OD}.
Arguments compatible_comm {data} {OD}.
Arguments compatible_combine_1 {data} {OD}.
Arguments compatible_combine_2 {data} {OD}.
Arguments projection_support_eq {data} {OD}.

Definition d_join_list (f : data -> data -> bool) x l := map (combine D x) (filter (f x) l).

Definition theta_join_list f l1 l2 := flat_map (fun x1 => d_join_list f x1 l2) l1.

Lemma d_join_list_unfold :
  forall f x l, d_join_list f x l =  map (combine D x) (filter (f x) l).
Proof.
intros; apply refl_equal.
Qed.

Lemma theta_join_list_unfold : 
  forall f l1 l2, theta_join_list f l1 l2 = flat_map (fun x1 => d_join_list f x1 l2) l1.
Proof.
intros; apply refl_equal.
Qed.

Lemma d_join_list_app :
  forall f x l l', d_join_list f x (l ++ l') = d_join_list f x l ++ d_join_list f x l'.
Proof.
unfold d_join_list.
intros f x l; induction l as [ | x1 l]; intro l'; simpl; [apply refl_equal | ].
case (f x x1); simpl; rewrite IHl; trivial.
Qed.

Lemma theta_join_list_app_1 :
  forall f l1 l2 l, 
    theta_join_list f (l1 ++ l2) l = theta_join_list f l1 l ++ theta_join_list f l2 l.
Proof.
intros f l1 l2 l; unfold theta_join_list.
rewrite flat_map_app; apply refl_equal.
Qed.

Lemma theta_join_list_app_2 :
  forall f l1 l2 l, 
    theta_join_list f l (l1 ++ l2) =P= theta_join_list f l l1 ++ theta_join_list f l l2.
Proof.
intros f l1 l2 l; unfold theta_join_list.
revert l1 l2; induction l as [ | t l]; intros l1 l2; simpl; [apply Pnil | ].
rewrite d_join_list_app, <- 2 ass_app.
apply _permut_app1; [apply equivalence_eq | ].
assert (IH := IHl l1 l2).
rewrite (_permut_app1 (equivalence_eq _) (d_join_list f t l2)) in IH.
refine (_permut_trans _ IH _); [intros; subst; apply refl_equal | ].
rewrite 2 ass_app; apply _permut_app2; [apply equivalence_eq | ].
apply _permut_swapp; apply _permut_refl; intros; trivial.
Qed.

Lemma in_theta_join_list :  
  forall f l1 l2 x,
    In x (theta_join_list f l1 l2) <->
    (exists x1 x2, In x1 l1 /\ In x2 l2 /\ f x1 x2 = true /\ x = combine D x1 x2).
Proof.
intros f s1 s2 t; unfold theta_join_list, d_join_list.
rewrite in_flat_map; split.
- intros [x1 [Hx1 Ht]].
  rewrite in_map_iff in Ht; destruct Ht as [x2 [Ht Hx2]].
  rewrite filter_In in Hx2.
  destruct Hx2 as [Hx2 Hf].
  exists x1; exists x2; repeat split; trivial.
  apply sym_eq; assumption.
- intros [x1 [x2 [Hx1 [Hx2 [Hf Ht]]]]].
  exists x1; split; [assumption | ].
  rewrite in_map_iff; exists x2; split; [apply sym_eq; assumption | ].
  rewrite filter_In; split; assumption.
Qed.

Lemma theta_join_list_permut_eq_2 :
  forall f, (forall x1 x2 x1' x2', x1 =d= x1' -> x2 =d= x2' -> f x1 x2 = f x1' x2') -> 
    forall l1 l2 l2', l2 =PE= l2' -> theta_join_list f l1 l2 =PE= theta_join_list f l1 l2'.
Proof.
intros f Hf l1; induction l1 as [ | x1 l1]; intros l2 l2' H; simpl.
- apply permut_refl.
- apply _permut_app; [ | apply IHl1; assumption].
  clear IHl1; revert l2' H; induction l2 as [ | x2 l2]; intros l2' H.
  + inversion H; subst; apply permut_refl.
  + inversion H; clear H; subst.
    rewrite d_join_list_app, 2 (d_join_list_unfold _ _ (_ :: _)); simpl.
    rewrite <- (Hf _ _ _ _ (Oeset.compare_eq_refl _ _) H2).
    case (f x1 x2); simpl.
    * apply Pcons; [apply combine_eq_2; assumption | ].
      rewrite <- 2 d_join_list_unfold, <- d_join_list_app.
      apply IHl2; assumption.
    * rewrite <- 2 d_join_list_unfold, <- d_join_list_app; apply IHl2; assumption.
Qed.

Lemma theta_join_list_permut_eq_1 :
  forall f, (forall x1 x2 x1' x2', x1 =d= x1' -> x2 =d= x2' -> f x1 x2 = f x1' x2') -> 
    forall l1 l1' l2, l1 =PE= l1' -> theta_join_list f l1 l2 =PE= theta_join_list f l1' l2.
Proof.
intros f Hf l1 l1' l2 H1; rewrite 2 theta_join_list_unfold.
revert l1' l2 H1; induction l1 as [ | x1 l1]; intros l1' l2 H1.
- inversion H1; subst; apply permut_refl.
- inversion H1; subst.
  rewrite flat_map_app; simpl.
  assert (IH := IHl1 _ l2 H4).
  rewrite (permut_app1 _ (map (combine D x1) (filter (f x1) l2))) in IH.
  apply (permut_trans _ IH).
  rewrite flat_map_app, 2 ass_app.
  rewrite <- permut_app2.
  apply _permut_swapp; [ | apply permut_refl].
  clear l1 l0 l3 H4 IHl1 H1 IH.
  induction l2 as [ | x2 l2]; [apply permut_refl | simpl].
  rewrite (Hf _ _ _ _ H2 (Oeset.compare_eq_refl _ _)), (d_join_list_unfold _ _ (_ :: _)).
  simpl; case (f b x2); [ | apply IHl2].
  simpl; apply permut_cons; [ | apply IHl2].
  apply combine_eq_1; assumption.
Qed.

Lemma theta_join_list_permut_eq :
  forall f, (forall x1 x2 x1' x2', x1 =d= x1' -> x2 =d= x2' -> f x1 x2 = f x1' x2') -> 
    forall l1 l1' l2 l2', 
      l1 =PE= l1' -> l2 =PE= l2' ->
      theta_join_list f l1 l2 =PE= theta_join_list f l1' l2'.
Proof.
intros f Hf l1 l1' l2 l2' H1 H2.
apply (permut_trans _ (theta_join_list_permut_eq_1 _ Hf _ _ _ H1)).
apply theta_join_list_permut_eq_2; trivial.
Qed.

Lemma theta_join_list_mem_bool_eq_2 :
  forall f, (forall x1 x2 x1' x2', x1 =d= x1' -> x2 =d= x2' -> f x1 x2 = f x1' x2') -> 
    forall l1 l2 l2', 
      (forall t, Oeset.mem_bool OD t l2 = Oeset.mem_bool OD t l2') -> 
      forall t, Oeset.mem_bool OD t (theta_join_list f l1 l2) =
                Oeset.mem_bool OD t (theta_join_list f l1 l2').
Proof.
intros f Hf l1; induction l1 as [ | x1 l1]; intros l2 l2' H t; simpl; [trivial | ].
rewrite 2 Oeset.mem_bool_app; apply f_equal2; [ | apply IHl1; assumption].
assert (Aux : forall l2 l2' : list data,
                (forall t : data,
                   Oeset.mem_bool OD t l2 = Oeset.mem_bool OD t l2') ->
                forall t : data,
                  (exists a' : data, t =d= a' /\ In a' (d_join_list f x1 l2)) ->
                  exists a' : data, t =d= a' /\ In a' (d_join_list f x1 l2')).
{
  clear l2 l2' H t; intros l2 l2' H t [t' [Ht Ht']].
  unfold d_join_list in Ht'.
  rewrite in_map_iff in Ht'.
  destruct Ht' as [x2 [Ht' Hx2]].
  rewrite filter_In in Hx2.
  destruct Hx2 as [Hx2 Kx2].
  assert (Jx2 : Oeset.mem_bool OD x2 l2' = true).
  {
    rewrite <- H, Oeset.mem_bool_true_iff.
    exists x2; split; [ | assumption].
    apply Oeset.compare_eq_refl.
  }
  rewrite Oeset.mem_bool_true_iff in Jx2.
  destruct Jx2 as [x2' [Jx2 Jx2']].
  exists (combine D x1 x2'); split.
  - refine (Oeset.compare_eq_trans _ _ _ _ Ht _); rewrite <- Ht'.
    apply combine_eq_2; assumption.
      - unfold d_join_list; rewrite in_map_iff.
    exists x2'; split; [trivial | ].
    rewrite filter_In; split; trivial.
    rewrite <- Kx2; apply sym_eq; apply Hf; [ | trivial].
    apply Oeset.compare_eq_refl.
}
rewrite eq_bool_iff, 2 Oeset.mem_bool_true_iff; split; apply Aux; trivial.
intro u; rewrite H; apply refl_equal.
Qed.

Definition brute_left_join_list s1 s2 := theta_join_list (fun _ _ => true) s1 s2.

Fixpoint N_product_list ll :=
  match ll with
    | nil => (empty_d D :: nil)
    | s1 :: ll => brute_left_join_list s1 (N_product_list ll)
  end.

Definition N_product_bag (FD : Febag.Rcd OD) ll :=
  Febag.mk_bag FD (N_product_list (map (Febag.elements FD) ll)).

Fixpoint N_combine (lt : list data) : data :=
  match lt with
    | nil => empty_d D
    | x1 :: lt => combine D x1 (N_combine lt)
  end.

Lemma N_combine_unfold :
  forall lt, N_combine lt = match lt with
                                     | nil => empty_d D
                                     | x1 :: lt => combine D x1 (N_combine lt)
                                   end.
Proof.
intro lt; case lt; intros; apply refl_equal.
Qed.

Lemma brute_left_join_list_unfold :
  forall s1 s2, brute_left_join_list s1 s2 = theta_join_list (fun _ _ => true) s1 s2.
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma N_product_list_unfold :
  forall ll, N_product_list ll =
  match ll with
    | nil => (empty_d D :: nil)
    | s1 :: ll => brute_left_join_list s1 (N_product_list ll)
  end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma in_brute_left_join_list : 
  forall t s1 s2,
    In t (brute_left_join_list s1 s2) <->
    (exists x1 x2 : data, In x1 s1 /\ In x2 s2 /\ t = combine D x1 x2).
Proof.
intros t s1 s2; rewrite brute_left_join_list_unfold, in_theta_join_list.
split; intros [x1 [x2 [Hx1 [Hx2 H]]]]; exists x1; exists x2; repeat split; trivial.
apply (proj2 H).
Qed.

Lemma N_product_list_1 :
  forall s, comparelA (fun x y => Oeset.compare OD x y) (N_product_list (s :: nil)) s = Eq.
Proof.
intro s; simpl.
unfold brute_left_join_list.
rewrite theta_join_list_unfold; simpl.
induction s as [ | x1 s]; [apply refl_equal | simpl].
rewrite combine_empty_2; apply IHs.
Qed.

Lemma N_product_list_map_eq :
  forall (B : Type) (l : list B) f1 f2,
  (forall x, In x l -> comparelA (Oeset.compare OD) (f1 x) (f2 x) = Eq) ->
  comparelA (Oeset.compare OD) (N_product_list (map f1 l)) (N_product_list (map f2 l)) = Eq.
Proof.
intros B l; induction l as [ | a1 l]; intros f1 f2 Hf; simpl.
- rewrite Oeset.compare_eq_refl; trivial.
- unfold brute_left_join_list, theta_join_list.
  assert (H1 := Hf _ (or_introl _ (refl_equal _))).
  set (b1 := f1 a1) in *; clearbody b1.
  set (b2 := f2 a1) in *; clearbody b2.
  assert (IH := IHl f1 f2 (fun x h => Hf x (or_intror _ h))).
  set (l1 := N_product_list (map f1 l)) in *; clearbody l1.
  set (l2 := N_product_list (map f2 l)) in *; clearbody l2.
  revert b2 H1 l1 l2 IH; 
    induction b1 as [ | x1 b1]; 
    intros [ | x2 b2] H1 l1 l2 IH; simpl; trivial; try discriminate H1.
  simpl in H1.
  case_eq (Oeset.compare OD x1 x2); intro Ht;
  rewrite Ht in H1; try discriminate H1.
  apply comparelA_eq_app; [ | apply IHb1; trivial].
  clear b1 b2 IHb1 H1.
  revert x1 x2 Ht l2 IH; induction l1 as [ | u1 l1]; 
  intros x1 x2 Ht [ | u2 l2] IH; simpl; trivial; try discriminate IH.
  simpl in IH.
  case_eq (Oeset.compare OD u1 u2); intro Hu; rewrite Hu in IH;
  try discriminate IH.
  rewrite (Oeset.compare_eq_1 _ _ _ _ (combine_eq_1 D _ _ _ Ht)).
  rewrite <- (Oeset.compare_eq_2 _ _ _ _ (combine_eq_2 D _ _ _ Hu)).
  rewrite Oeset.compare_eq_refl.
  unfold d_join_list in IHl1; rewrite IHl1; trivial.
Qed.

Lemma in_N_product_list :
  forall t ll, In t (N_product_list ll) <->
               (exists llt, (forall si ti, List.In (si, ti) llt -> In ti si) /\
                            List.map (@fst _ _) llt = ll /\ 
                            t = N_combine (List.map (@snd _ _) llt)).
Proof.
intros t ll; revert t.
induction ll as [ | s1 ll]; intro t; rewrite N_product_list_unfold; split.
- intro H; simpl in H; destruct H as [H | H]; [ | contradiction H].
  subst t; exists nil; repeat split; intros; contradiction.
- intros [llt [H1 [H2 H3]]].
  destruct llt; [ | discriminate H2].
  simpl in H3; left; apply sym_eq; apply H3.
- rewrite in_brute_left_join_list.
  intros [x1 [x2 [Hx1 [Hx2 Ht]]]].
  rewrite IHll in Hx2.
  destruct Hx2 as [llt [H1 [H2 H3]]].
  exists ((s1, x1) :: llt); repeat split.
  + intros si ti Hi; simpl in Hi; destruct Hi as [Hi | Hi]; [ | apply H1; assumption].
    injection Hi; clear Hi; do 2 intro; subst; assumption.
  + simpl; apply f_equal; assumption.
  + rewrite Ht, H3; apply refl_equal.
- intros [llt [H1 [H2 H3]]].
  destruct llt as [ | [_s1 x1] llt]; [discriminate H2 | ].
  simpl in H2; injection H2; clear H2; intro H2; intro; subst _s1.
  rewrite in_brute_left_join_list.
  exists x1; exists (N_combine (map (snd (B:=data)) llt)); repeat split.
  + apply H1; left; apply refl_equal.
  + rewrite IHll; exists llt; repeat split; trivial.
    do 3 intro; apply H1; right; assumption.
  + rewrite H3; apply refl_equal.
Qed.


(** natural_join *)

Lemma nb_occ_theta_join_list :
  forall f l1 l2 t, 
    Oeset.nb_occ OD t (theta_join_list f l1 l2) =
    N.of_nat 
      (list_size 
         (fun x1 => 
            (match Oeset.compare OD x1 (projection D (support D x1) x1) with
               | Eq => 1 | _ => 0 end) * 
            list_size (fun x2 => 
                         if f x1 x2 
                         then match Oeset.compare OD (combine D x1 x2) t with
                                | Eq => 1 | _ => 0 end
                         else 0) l2)
         l1)%nat.
Proof.
intros f l1; induction l1 as [ | x1 l1]; intros l2 t; simpl; [apply refl_equal | ].
rewrite Oeset.nb_occ_app, IHl1, Nat2N.inj_add.
- apply f_equal2; [ | apply refl_equal].
  rewrite (Oeset.compare_lt_gt _ _ (projection _ _ _)), projection_support_eq; simpl;
    [ | apply Fset.equal_refl].
  clear l1 IHl1.
  rewrite Nat2N.inj_add, N.add_0_r.
  induction l2 as [ | x2 l2]; simpl; [apply refl_equal | ].
  rewrite d_join_list_unfold, filter_unfold.
  case_eq (f x1 x2); intro Hf; [ | simpl; apply IHl2].
  rewrite (map_unfold _ (_ :: _)), Oeset.nb_occ_unfold.
  rewrite Nat2N.inj_add; apply f_equal2.
  + rewrite Oeset.compare_lt_gt; case (Oeset.compare OD (combine D x1 x2) t); apply refl_equal.
  + rewrite <- IHl2; apply refl_equal.
Qed.


Definition natural_join_list s1 s2 := theta_join_list (compatible D) s1 s2.

Definition natural_join_set (FD : Feset.Rcd OD) s1 s2 := 
  Feset.mk_set FD (theta_join_list (compatible D) (Feset.elements FD s1) (Feset.elements FD s2)).

Lemma natural_join_list_unfold : 
  forall s1 s2, natural_join_list s1 s2 = theta_join_list (compatible D) s1 s2.
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma nb_occ_natural_join_list :
  forall l1 l2 s1 s2, 
    (forall t, In t l1 -> support D t =S= s1) ->
    (forall t, In t l2 -> support D t =S= s2) ->
    forall t, (Oeset.nb_occ OD t (natural_join_list l1 l2) =
              (Oeset.nb_occ OD (projection D s1 t) l1) *
              (Oeset.nb_occ OD (projection D s2 t) l2) *
              (if support D t =S?= (s1 unionS s2) then 1 else 0))%N.
Proof.
  intros l1 l2 s1 s2 H1 H2 t.
  rewrite natural_join_list_unfold, nb_occ_theta_join_list.
  revert l2 H2; induction l1 as [ | u1 l1]; intros l2 H2; simpl; [apply refl_equal | ].
  rewrite Nat2N.inj_add, Nat2N.inj_mul, IHl1, 2 N.mul_add_distr_r; trivial.
  - apply f_equal2; [ | apply refl_equal].
    rewrite (Oeset.compare_lt_gt _ _ (projection _ _ _)), projection_support_eq, N.mul_1_l; 
      [ | apply Fset.equal_refl].
    assert (Hu1 := H1 u1 (or_introl _ (refl_equal _))).
    clear l1 H1 IHl1.
    induction l2 as [ | u2 l2]; simpl; [rewrite N.mul_0_r, N.mul_0_l; apply refl_equal | ].
    rewrite Nat2N.inj_add, N.mul_add_distr_l, IHl2; [ | intros; apply H2; right; trivial].
    rewrite N.mul_add_distr_r.
    case_eq (support D t =S?= (s1 unionS s2)); 
      intro H; [ rewrite 2 N.mul_1_r | rewrite 2 N.mul_0_r];     
      (apply f_equal2; [ | apply refl_equal]).
    + case_eq (compatible D u1 u2); intro Hu.
      * assert (Hu2 := H2 u2 (or_introl _ (refl_equal _))).
        {
          case_eq (Oeset.compare OD t (combine D u1 u2)); intro Ht;
          rewrite (Oeset.compare_lt_gt _ (combine _ _ _) _), Ht.
          - rewrite (split_d D s1 s2 t u1 u2 Hu1 Hu2 Hu) in Ht.
            rewrite (Oeset.compare_eq_sym _ _ _ (proj1 Ht)).
            rewrite (Oeset.compare_eq_sym _ _ _ (proj1 (proj2 Ht))).
            apply refl_equal.
          - case_eq (Oeset.compare OD (projection D s1 t) u1); intro Ku1; trivial.
            case_eq (Oeset.compare OD (projection D s2 t) u2); intro Ku2; trivial.
            apply False_rec.
            assert (Abs : t =d= combine D u1 u2).
            {
              rewrite (split_d D s1 s2 t u1 u2); repeat split; trivial.
              - apply Oeset.compare_eq_sym; assumption.
              - apply Oeset.compare_eq_sym; assumption.
            }
            rewrite Abs in Ht; discriminate Ht.
          - case_eq (Oeset.compare OD (projection D s1 t) u1); intro Ku1; trivial.
            case_eq (Oeset.compare OD (projection D s2 t) u2); intro Ku2; trivial.
            apply False_rec.
            assert (Abs : t =d= combine D u1 u2).
            {
              rewrite (split_d D s1 s2 t u1 u2); repeat split; trivial.
              - apply Oeset.compare_eq_sym; assumption.
              - apply Oeset.compare_eq_sym; assumption.
            }
            rewrite Abs in Ht; discriminate Ht.
        } 
      * case_eq (Oeset.compare OD (projection D s1 t) u1); intro Ku1; trivial.
        case_eq (Oeset.compare OD (projection D s2 t) u2); intro Ku2; trivial.
        apply False_rec.
        assert (Abs : compatible D u1 u2 = true).
        {
          rewrite <- (compatible_eq_1 _ _ _ _ Ku1).
          rewrite <- (compatible_eq_2 _ _ _ _ Ku2).
          apply compatible_projection.
        }
        rewrite Abs in Hu; discriminate Hu.
    + case (compatible D u1 u2); [ | apply refl_equal].
      case_eq (Oeset.compare OD (combine D u1 u2) t); intro Ht;
      try (apply refl_equal).
      apply False_rec.
      assert (Abs : support D t =S= (s1 unionS s2)).
      {
        rewrite Oeset.compare_lt_gt, CompOpp_iff in Ht.
        rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine D t u1 u2 Ht)).
        apply Fset.union_eq; [assumption | ].
        apply H2; left; apply refl_equal.
      }
      rewrite Abs in H; discriminate H.
  - intros; apply H1; right; assumption.
Qed.

Section Optim.

Lemma pi_idempotent :
  forall s1 s2, Fset.subset (FAtt _ _ D) s1 s2 = true ->
    forall l x, Oeset.nb_occ OD x (map (projection D s1) (map (projection D s2) l)) = 
                Oeset.nb_occ OD x (map (projection D s1) l).
Proof.
intros s1 s2 Hs l x; apply permut_nb_occ.
rewrite map_map; apply permut_refl_alt.
induction l as [ | x1 l]; [apply refl_equal | ].
simpl; rewrite projection_idem; [ | apply Hs].
apply IHl.
Qed.

Hypothesis FD : Febag.Rcd OD.

Lemma map_filter_comm :
  forall (pi : data -> data) f l,  
    (forall x : data, In x l -> f x = f (pi x)) ->
    map pi (filter f l) = filter f (map pi l).
Proof.
intros pi f l H.
rewrite filter_map; apply f_equal.
apply filter_eq; apply H.
Qed.

Lemma natural_join_list_comm_aux :
  forall t1 l2 x, 
    Oeset.nb_occ OD x (natural_join_list (t1 :: nil) l2) = 
    Oeset.nb_occ OD x (natural_join_list l2 (t1 :: nil)).
Proof.
intros t1 l2 x; apply permut_nb_occ.
induction l2 as [ | t2 l2]; [apply permut_refl | ]; simpl in IHl2; simpl.
rewrite <- app_nil_end in IHl2.
rewrite <- app_nil_end, 2 d_join_list_unfold, 2 (filter_unfold _ (_ :: _)), (filter_unfold _ nil).
rewrite (compatible_comm D t2 t1).
case_eq (compatible D t1 t2); intro Ht; [ | apply IHl2].
simpl.
apply permut_cons; [ | apply IHl2].
apply combine_comm; assumption.
Qed.

Lemma natural_join_list_comm :
  forall l1 l2 x, 
    Oeset.nb_occ OD x (natural_join_list l1 l2) = Oeset.nb_occ OD x (natural_join_list l2 l1).
Proof.
intros l1 l2 x; apply permut_nb_occ; revert l2; clear x.
induction l1 as [ | t1 l1]; intros l2.
- induction l2 as [ | t2 l2]; [apply permut_refl | ]; simpl.
  refine (permut_trans _ _ IHl2); apply permut_refl.
- replace (t1 :: l1) with ((t1 :: nil) ++ l1); [ | apply refl_equal].
  unfold natural_join_list; rewrite theta_join_list_app_1.
  apply permut_trans with 
      (theta_join_list (compatible D) l2 (t1 :: nil) ++ 
                       theta_join_list (compatible D) l2 l1).
  + apply _permut_app; [ | apply IHl1].
    apply nb_occ_permut; apply natural_join_list_comm_aux.
  + apply permut_sym; apply _permut_incl with eq; [intros; subst; apply Oeset.compare_eq_refl | ].
    apply theta_join_list_app_2.
Qed.  

Lemma natural_join_list_assoc :
  forall l1 l2 l3 x, 
    Oeset.nb_occ OD x (natural_join_list l1 (natural_join_list l2 l3)) = 
    Oeset.nb_occ OD x (natural_join_list (natural_join_list l1 l2) l3).
Proof.
unfold natural_join_list.
intros l1 l2 l3 x; apply permut_nb_occ; clear x.
revert l2 l3.
induction l1 as [ | a1 l1]; intros l2 l3; simpl; [apply Pnil | ].
rewrite theta_join_list_app_1.
apply _permut_app; [ | apply IHl1].
clear l1 IHl1; unfold theta_join_list.
revert l3; induction l2 as [ | a2 l2]; intro l3; simpl; [apply Pnil | ].
rewrite d_join_list_app, (d_join_list_unfold _ _ (_ :: _)), (filter_unfold _ (_ :: _)).
rewrite map_if, (map_unfold _ (_ :: _)), flat_map_if_alt.
apply _permut_app; [ | apply IHl2].
clear l2 IHl2.
rewrite 3 d_join_list_unfold.
revert a1 a2; induction l3 as [ | a3 l3]; intros a1 a2; simpl.
- case (compatible D a1 a2); apply Pnil.
- rewrite map_if, (map_unfold _ (_ :: _)), filter_if, filter_unfold, if_if.
  rewrite map_if, (map_unfold _ (_ :: _)).
  case_eq (compatible D a1 a2); intro H12;
  assert (IH := IHl3 a1 a2); rewrite H12 in IH.
  + rewrite (compatible_combine_1 _ _ _ _ H12).
    case_eq (compatible D a2 a3); intro H23.
    * rewrite (compatible_combine_2 _ _ _ _ H23), H12.
      case_eq (compatible D a1 a3); intro H13; simpl; [ | apply IH].
      apply permut_cons; [apply combine_assoc | apply IH].
    * rewrite Bool.andb_false_l, Bool.andb_false_r; apply IH.
  + case_eq (compatible D a2 a3); intro H23.
    * rewrite (compatible_combine_2 _ _ _ _ H23), H12, Bool.andb_false_r.
      apply IH.
    * apply IH.
Qed.

Lemma filter_and : 
  forall f1 f2 (l : list data), filter (fun x => f1 x && f2 x) l = filter f1 (filter f2 l).
Proof.
intros f1 f2 l.
apply sym_eq; apply filter_filter.
Qed.

Lemma filter_comm : 
 forall f1 f2 (l : list data), filter f1 (filter f2 l) = filter f2 (filter f1 l).
Proof.
intros f1 f2 l; rewrite 2 filter_filter; apply filter_eq.
intros; apply Bool.andb_comm.
Qed.

Lemma min_nb_occ_filter :
  forall f1 f2, 
    (forall x y, Oeset.compare OD x y = Eq -> f1 x = f1 y) ->
    (forall x y, Oeset.compare OD x y = Eq -> f2 x = f2 y) ->
  forall l a,
    N.min (Oeset.nb_occ OD a (filter f1 l)) (Oeset.nb_occ OD a (filter f2 l)) =
    Oeset.nb_occ OD a (filter (fun x => f1 x && f2 x) l).
Proof.
intros f1 f2 f1_eq f2_eq l a.
rewrite Oeset.nb_occ_filter; [ | intros; apply f1_eq; assumption].
rewrite Oeset.nb_occ_filter; [ | intros; apply f2_eq; assumption].
rewrite Oeset.nb_occ_filter; [ | intros; apply f_equal2; [apply f1_eq | apply f2_eq]; assumption].
case (f1 a); [case (f2 a) | ]; simpl.
- apply N.min_id.
- apply N.min_0_r.
- apply N.min_0_l.
Qed.

Lemma max_nb_occ_filter :
  forall f1 f2 , 
    (forall x y, Oeset.compare OD x y = Eq -> f1 x = f1 y) ->
    (forall x y, Oeset.compare OD x y = Eq -> f2 x = f2 y) ->
  forall l a,
    N.max (Oeset.nb_occ OD a (filter f1 l)) (Oeset.nb_occ OD a (filter f2 l)) =
    Oeset.nb_occ OD a (filter (fun x => f1 x || f2 x) l).
Proof.
intros f1 f2 f1_eq f2_eq l a.
rewrite Oeset.nb_occ_filter; [ | intros; apply f1_eq; assumption].
rewrite Oeset.nb_occ_filter; [ | intros; apply f2_eq; assumption].
rewrite Oeset.nb_occ_filter; [ | intros; apply f_equal2; [apply f1_eq | apply f2_eq]; assumption].
case (f1 a); [case (f2 a) | ]; simpl.
- apply N.max_id.
- apply N.max_0_r.
- apply N.max_0_l.
Qed.

Lemma filter_natural_join_list :
  forall f l1 l2, 
    (forall x1 x2, In x1 l1 -> In x2 l2 -> f (combine D x1 x2) = f x1) ->
    filter f (natural_join_list l1 l2) = natural_join_list (filter f l1) l2.
Proof.
unfold natural_join_list, theta_join_list, d_join_list.
intros f l1; induction l1 as [ | x1 l1]; intros l2 H; simpl; [apply refl_equal | ].
rewrite filter_app, IHl1, (flat_map_if _ _ (fun x => x)), flat_map_unfold.
case_eq (f x1); intro Hx1; [apply f_equal2; [ | apply refl_equal] | ].
- assert (H' := fun x2 => H x1 x2 (or_introl _ (refl_equal _))).
  clear l1 IHl1 H.
  rewrite filter_map; apply f_equal. 
  rewrite filter_filter; apply filter_eq.
  intros x2 Hx2; rewrite (H' _ Hx2), Hx1; apply refl_equal.
- replace (filter f (map (combine D x1) (filter (compatible D x1) l2))) with (@nil data);
    [apply refl_equal | ].
  apply sym_eq.
  assert (H' := fun x2 => H x1 x2 (or_introl _ (refl_equal _))).
  clear l1 IHl1 H.
  induction l2 as [ | x2 l2]; [apply refl_equal | ].
  simpl; rewrite map_if, map_unfold, filter_if; simpl.
  rewrite (H' _ (or_introl _ (refl_equal _))), Hx1, IHl2.
  + case (compatible D x1 x2); apply refl_equal.
  + intros; apply H'; right; assumption.
- do 3 intro; apply H; right; assumption.
Qed.

Lemma filter_sum_nb_occ :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall l l1 l2 x, Oeset.nb_occ OD x l = (Oeset.nb_occ OD x l1 + Oeset.nb_occ OD x l2)%N ->
    Oeset.nb_occ OD x (filter f l) = 
    ((Oeset.nb_occ OD x (filter f l1)) + (Oeset.nb_occ OD x (filter f l2)))%N.
Proof.
intros f f_eq l l1 l2 x Hl.
rewrite Oeset.nb_occ_filter; [ | intros; apply f_eq; assumption].
rewrite Hl, 2 Oeset.nb_occ_filter.
- case (f x); apply refl_equal.
- intros; apply f_eq; assumption.
- intros; apply f_eq; assumption.
Qed.

Lemma filter_max_nb_occ :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall l l1 l2 x, 
    Oeset.nb_occ OD x l = N.max (Oeset.nb_occ OD x l1) (Oeset.nb_occ OD x l2) ->
    Oeset.nb_occ OD x (filter f l) = 
    N.max (Oeset.nb_occ OD x (filter f l1)) (Oeset.nb_occ OD x (filter f l2)).
Proof.
intros f f_eq l l1 l2 x Hl.
rewrite Oeset.nb_occ_filter; [ | intros; apply f_eq; assumption].
rewrite Hl, 2 Oeset.nb_occ_filter.
- case (f x); apply refl_equal.
- intros; apply f_eq; assumption.
- intros; apply f_eq; assumption.
Qed.

Lemma filter_min_nb_occ :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall l l1 l2 x, 
    Oeset.nb_occ OD x l = N.min (Oeset.nb_occ OD x l1) (Oeset.nb_occ OD x l2) ->
    Oeset.nb_occ OD x (filter f l) = 
    N.min (Oeset.nb_occ OD x (filter f l1)) (Oeset.nb_occ OD x (filter f l2)).
Proof.
intros f f_eq l l1 l2 x Hl.
rewrite Oeset.nb_occ_filter; [ | intros; apply f_eq; assumption].
rewrite Hl, 2 Oeset.nb_occ_filter.
- case (f x); apply refl_equal.
- intros; apply f_eq; assumption.
- intros; apply f_eq; assumption.
Qed.
  
Lemma filter_diff_nb_occ :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall l l1 l2 x, 
    Oeset.nb_occ OD x l = N.max 0 ((Oeset.nb_occ OD x l1) - (Oeset.nb_occ OD x l2)) ->
    Oeset.nb_occ OD x (filter f l) = 
    N.max 0 ((Oeset.nb_occ OD x (filter f l1)) - (Oeset.nb_occ OD x (filter f l2))).
Proof.
intros f f_eq l l1 l2 x Hl.
rewrite Oeset.nb_occ_filter; [ | intros; apply f_eq; assumption].
rewrite Hl, 2 Oeset.nb_occ_filter.
- case (f x); apply refl_equal.
- intros; apply f_eq; assumption.
- intros; apply f_eq; assumption.
Qed.

Fixpoint delta_list_rec (acc l : list data) : list data :=
  match l with 
  | nil => acc
  | x1 :: l => 
    if Oeset.mem_bool OD x1 acc 
    then delta_list_rec acc l 
    else delta_list_rec (x1 :: acc) l
  end.

Definition delta_list l := delta_list_rec nil l.

Lemma nb_occ_delta_list :
  forall x l, Oeset.nb_occ OD x (delta_list l) = N.min 1 (Oeset.nb_occ OD x l).
Proof.
intros x l; unfold delta_list.
apply trans_eq with (if Oeset.mem_bool OD x nil 
                     then Oeset.nb_occ OD x nil 
                     else if Oeset.mem_bool OD x l then 1%N else 0%N).
- generalize (@nil data).
  induction l as [ | x1 l]; intro acc; simpl.
  + case_eq (Oeset.mem_bool OD x acc); intro Hx; [apply refl_equal | ].
    apply Oeset.not_mem_nb_occ; apply Hx.
  + case_eq (Oeset.mem_bool OD x1 acc); intro Hx1.
    * rewrite IHl.
      case_eq (Oeset.mem_bool OD x acc); intro Hx; [apply refl_equal | ].
      case_eq (Oeset.eq_bool OD x x1); intro H; [ | apply refl_equal].
      unfold Oeset.eq_bool in H; rewrite compare_eq_true in H.
      rewrite (Oeset.mem_bool_eq_1 _ _ _ _ H), Hx1 in Hx.
      discriminate Hx.
    * rewrite IHl, (Oeset.mem_bool_unfold _ _ (_ :: _)), (Oeset.nb_occ_unfold _ _ (_ :: _)).
      {
        unfold Oeset.eq_bool; case_eq (Oeset.compare OD x x1); intro Hx.
        - rewrite 2 (Oeset.mem_bool_eq_1 _ _ _ _ Hx), Hx1.
          rewrite Oeset.not_mem_nb_occ; [ | rewrite (Oeset.mem_bool_eq_1 _ _ _ _ Hx); apply Hx1].
          apply refl_equal.
        - simpl; apply refl_equal.
        - simpl; apply refl_equal.
      } 
- simpl.
  case_eq (Oeset.mem_bool OD x l); intro Hx.
  + case_eq (Oeset.nb_occ OD x l); [intro Kx | intros p Kx].
    * rewrite (Oeset.nb_occ_not_mem _ _ _ Kx) in Hx; discriminate Hx.
    * destruct p; apply refl_equal.
  + rewrite (Oeset.not_mem_nb_occ _ _ _ Hx); apply refl_equal.
Qed.

Definition join theta l1 l2 := filter theta (natural_join_list l1 l2).

Definition semi_join theta s1 l1 l2 :=
  natural_join_list l1 (delta_list (map (projection D s1) (join theta l1 l2))).

Lemma nb_occ_semi_join :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall s1 s2 l1 l2 x1, 
    (forall x, In x l1 -> support D x =S= s1) ->
    (forall x, In x l2 -> support D x =S= s2) ->
    Oeset.nb_occ OD x1 (semi_join f s1 l1 l2) =
    ((Oeset.nb_occ OD x1 l1) *
    (if (existsb (fun x2 => compatible D x1 x2 && f (combine D x1 x2)) l2)
     then 1 else 0))%N.
Proof.
intros f f_eq s1 s2 l1 l2 x1 Hl1 Hl2.
unfold semi_join.
rewrite (nb_occ_natural_join_list _ _ s1 s1).
- rewrite nb_occ_delta_list.
  case_eq (support D x1 =S?= s1); intro Hx1.
  + do 2 (rewrite (Oeset.nb_occ_eq_1 OD (projection D s1 x1) x1); 
          [ | apply projection_support_eq; rewrite (Fset.equal_eq_2 _ _ _ _ Hx1); 
              apply Fset.equal_refl]).
    assert (Hs1 : support D x1 =S= (s1 unionS s1)).
    {
      rewrite (Fset.equal_eq_1 _ _ _ _ Hx1), Fset.equal_spec.
      intro; rewrite Fset.mem_union, Bool.orb_diag; apply refl_equal.
    }
    rewrite Hs1, N.mul_1_r.
    case_eq (Oeset.nb_occ OD x1 l1); [intro Kx1 | intros p1 Kx1].
    * rewrite 2 N.mul_0_l; apply refl_equal.
    * apply f_equal. 
      assert (Jx1 : Oeset.mem_bool OD x1 l1 = true).
      {
        apply (Oeset.nb_occ_mem OD x1 l1).
        rewrite Kx1; discriminate.
      }
      rewrite Oeset.mem_bool_true_iff in Jx1.
      destruct Jx1 as [y1 [Jx1 Hy1]].
      {
        case_eq (existsb (fun x2 : data => compatible D x1 x2 && f (combine D x1 x2)) l2);
          intro H.
        - rewrite existsb_exists in H.
          destruct H as [x2 [Hx2 H]].
          rewrite Bool.andb_true_iff in H; destruct H as [H1 H2].
          assert (Aux : Oeset.mem_bool OD x1 (map (projection D s1) (join f l1 l2)) = true).
          {
            rewrite Oeset.mem_bool_true_iff.
            exists (projection D s1 (combine D y1 x2)); split.
            - assert (Aux := Oeset.compare_eq_refl OD (combine D y1 x2)).
              rewrite (split_d D s1 s2 _ _ _ (Hl1 _ Hy1) (Hl2 _ Hx2)) in Aux.
              + rewrite (Oeset.compare_eq_1 _ _ _ _ Jx1).
                apply (proj1 Aux).
              + rewrite <- (compatible_eq_1 _ _ _ _ Jx1); assumption.
            - rewrite in_map_iff.
              eexists; split; [apply refl_equal | ].
              unfold join; rewrite filter_In; split.
              + unfold natural_join_list, theta_join_list.
                rewrite in_flat_map.
                exists y1; split; [assumption | ].
                unfold d_join_list; rewrite in_map_iff; exists x2; split; [apply refl_equal | ].
                rewrite filter_In; split; [assumption | ].
                rewrite <- (compatible_eq_1 _ _ _ _ Jx1); assumption.
              + rewrite <- H2; apply sym_eq.
                apply f_eq; apply combine_eq_1; assumption.
          }
          case_eq (Oeset.nb_occ OD x1 (map (projection D s1) (join f l1 l2))).
          + intro H; rewrite (Oeset.nb_occ_not_mem _ _ _ H) in Aux; discriminate Aux.
          + intros p H.
            destruct p; apply refl_equal.
        - case_eq (Oeset.nb_occ OD x1 (map (projection D s1) (join f l1 l2))).
          + intro; apply refl_equal.
          + intros p Hp; apply False_rec.
            rewrite <- not_true_iff_false, existsb_exists in H; apply H.
            assert (Lx1 : Oeset.mem_bool OD x1 (map (projection D s1) (join f l1 l2)) = true).
            {
              apply Oeset.nb_occ_mem; rewrite Hp; discriminate.
            }
            rewrite Oeset.mem_bool_true_iff in Lx1.
            destruct Lx1 as [z1 [Lx1 Hz1]].
            rewrite in_map_iff in Hz1.
            destruct Hz1 as [x [Hz1 Hx]]; subst z1.
            unfold join in Hx; rewrite filter_In in Hx.
            destruct Hx as [H1 H2].
            unfold natural_join_list, theta_join_list in H1; rewrite in_flat_map in H1.
            destruct H1 as [z1 [Hz1 H1]].
            unfold d_join_list in H1; rewrite in_map_iff in H1.
            destruct H1 as [x2 [Hx2 H1]]; subst x.
            rewrite filter_In in H1; destruct H1 as [H1 H1'].
            exists x2; split; [assumption | ].
            assert (Aux := Oeset.compare_eq_refl OD (combine D z1 x2)).
            {
              rewrite (split_d D s1 s2) in Aux.
              - rewrite Bool.andb_true_iff; split.
                + rewrite <- H1'; apply compatible_eq_1.
                  rewrite (Oeset.compare_eq_1 _ _ _ _ Lx1), Oeset.compare_lt_gt, (proj1 Aux).
                  apply refl_equal.
                + rewrite <- H2; apply f_eq.
                  apply combine_eq_1.
                  rewrite (Oeset.compare_eq_1 _ _ _ _ Lx1), Oeset.compare_lt_gt, (proj1 Aux).
                  apply refl_equal.
              - apply Hl1; assumption.
              - apply Hl2; assumption.
              - assumption.
            }
      }
  + assert (Hs1 : support D x1 =S?= (s1 unionS s1) = false).
    {
      rewrite <- Hx1; apply Fset.equal_eq_2.
      rewrite Fset.equal_spec; intro; rewrite Fset.mem_union, Bool.orb_diag.
      apply refl_equal.
    }
    rewrite Hs1, N.mul_0_r.
    case_eq (existsb (fun x2 : data => compatible D x1 x2 && f (combine D x1 x2)) l2); 
      intro H.
    * case_eq (Oeset.nb_occ OD x1 l1); [intros _; apply refl_equal | ].
      intros p Hp.
      assert (Aux : Oeset.mem_bool OD x1 l1 = true).
      {
        apply Oeset.nb_occ_mem; rewrite Hp; discriminate.
      }
      rewrite Oeset.mem_bool_true_iff in Aux.
      destruct Aux as [y1 [Kx1 Hy1]].
      rewrite (Fset.equal_eq_1 _ _ _ _ (support_eq D _ _ Kx1)), (Hl1 _ Hy1) in Hx1.
      discriminate Hx1.
    * rewrite N.mul_0_r; apply refl_equal.
- assumption.
- intros t Ht.
  assert (Kt := Oeset.mem_nb_occ _ _ _ (Oeset.in_mem_bool OD _ _ Ht)).  
  rewrite nb_occ_delta_list in Kt.
  case_eq (Oeset.nb_occ OD t (map (projection D s1) (join f l1 l2))).
  + intro Jt; rewrite Jt in Kt; apply False_rec; apply Kt; apply refl_equal.
  + intros p Hp.
    assert (Jt : Oeset.mem_bool OD t (map (projection D s1) (join f l1 l2)) = true).
    {
      apply Oeset.nb_occ_mem; rewrite Hp; discriminate.
    }
    rewrite Oeset.mem_bool_true_iff in Jt.
    destruct Jt as [t' [Jt Ht']].
    rewrite in_map_iff in Ht'.
    destruct Ht' as [y1 [Hx Hy1]]; subst t'.
    rewrite (Fset.equal_eq_1 _ _ _ _ (support_eq _ _ _ Jt)).
    apply support_projection_eq.
Qed.

Lemma join_semi_join :
  forall f, (forall x y, Oeset.compare OD x y = Eq -> f x = f y) ->
  forall s1 s2 l1 l2 x, 
    (forall x, In x l1 -> support D x =S= s1) ->
    (forall x, In x l2 -> support D x =S= s2) ->
    Oeset.nb_occ OD x (join f l1 l2) = 
    Oeset.nb_occ OD x (join f l1 (semi_join f s2 l2 l1)).
Proof.
intros f f_eq s1 s2 l1 l2 x Hl1 Hl2.
unfold join; do 2 (rewrite Oeset.nb_occ_filter; [ | intros; apply f_eq; trivial]).
rewrite (nb_occ_natural_join_list l1 l2 s1 s2 Hl1 Hl2).
rewrite (nb_occ_natural_join_list l1 _ s1 s2 Hl1).
- case_eq (f x); intro Hx; [ | apply refl_equal].
  case_eq (support D x =S?= (s1 unionS s2)); intro Kx;
    [ | rewrite 2 N.mul_0_r; apply refl_equal].
  rewrite 2 N.mul_1_r.
  rewrite (nb_occ_semi_join f f_eq s2 s1); trivial.
  case_eq (Oeset.nb_occ OD (projection D s1 x) l1).
  + intro H1; rewrite 2 N.mul_0_l; apply refl_equal.
  + intros p1 Hp1; apply f_equal.
    case_eq (Oeset.nb_occ OD (projection D s2 x) l2).
    * intro H2; rewrite N.mul_0_l; apply refl_equal.
    * intros p2 Hp2.
      assert (Aux : existsb
                      (fun x2 : data =>
                         compatible D (projection D s2 x) x2 && 
                                            f (combine D (projection D s2 x) x2)) l1 = true).
      {
        assert (Aux : Oeset.mem_bool OD (projection D s1 x) l1 = true).
        {
          apply Oeset.nb_occ_mem; rewrite Hp1; discriminate.
        }
        rewrite Oeset.mem_bool_true_iff in Aux.
        destruct Aux as [x1 [Hx1 H1]].
        rewrite existsb_exists; exists x1; split; [assumption | ].
        rewrite Bool.andb_true_iff; split.
        - rewrite <- (compatible_eq_2 _ _ _ _ Hx1).
          apply compatible_projection.
        - rewrite <- Hx; apply sym_eq; apply f_eq.
          rewrite (split_d D s2 s1).
          + split; [apply Oeset.compare_eq_refl | ].
            split.
            * rewrite Oeset.compare_lt_gt, Hx1; apply refl_equal.
            * rewrite (Fset.equal_eq_1 _ _ _ _ Kx), Fset.equal_spec.
              intro; rewrite 2 Fset.mem_union; apply Bool.orb_comm.
          + apply support_projection_eq.
          + apply Hl1; assumption.
          + rewrite <- (compatible_eq_2 _ _ _ _ Hx1).
            apply compatible_projection.
      } 
      rewrite Aux, N.mul_1_r; apply refl_equal.
- intros t Ht.
  unfold semi_join, natural_join_list, theta_join_list in Ht.
  rewrite in_flat_map in Ht.
  destruct Ht as [x2 [Hx2 Ht]].
  unfold d_join_list in Ht.
  rewrite in_map_iff in Ht.
  destruct Ht as [y2 [Ht Hy2]]; subst t.
  rewrite filter_In in Hy2; destruct Hy2 as [Hy2 H].
  assert (Ky2 := Oeset.in_mem_bool OD _ _ Hy2).
  generalize (Oeset.mem_nb_occ _ _ _ Ky2); rewrite nb_occ_delta_list.
  case_eq (Oeset.nb_occ OD y2 (map (projection D s2) (join f l2 l1))).
  + intros _ Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros p2 Hp2 _.
    assert (Jy2 : Oeset.mem_bool OD y2 (map (projection D s2) (join f l2 l1)) = true).
    {
      apply Oeset.nb_occ_mem; rewrite Hp2; discriminate.
    }
    rewrite Oeset.mem_bool_true_iff in Jy2.
    destruct Jy2 as [z2 [Jy2 Hz2]].
    rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_1 _ _ _ _ (Hl2 _ Hx2))).
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (support_eq _ _ _ Jy2))).
    rewrite in_map_iff in Hz2.
    destruct Hz2 as [u [Hz2 Hu]]; subst z2.
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (support_projection_eq _ _ _))).
    rewrite Fset.equal_spec; intro; rewrite Fset.mem_union; apply Bool.orb_diag.
Qed.

Lemma join_semi_join2 :
  forall f1 f2, (forall x y, Oeset.compare OD x y = Eq -> f1 x = f1 y) ->
                (forall x y, Oeset.compare OD x y = Eq -> f2 x = f2 y) ->
  forall s1 s2 s3 l1 l2 l3 x, 
    (forall x, In x l1 -> support D x =S= s1) ->
    (forall x, In x l2 -> support D x =S= s2) ->
    (forall x, In x l3 -> support D x =S= s3) ->
    (forall x x3, support D x =S= (s1 unionS s2) -> support D x3 =S= s3 ->
                  f1 (combine D x x3) = f1 x) ->
    let l2' := semi_join (fun x => f1 x && f2 x) s2 l2 (natural_join_list l1 l3) in
    Oeset.nb_occ OD x (semi_join f2 (s1 unionS s2) (join f1 l1 l2) l3) =
    Oeset.nb_occ OD x (semi_join f2 (s1 unionS s2) (join f1 l1 l2') l3).
Proof.
intros f1 f2 f1_eq f2_eq s1 s2 s3 l1 l2 l3 x Hs1 Hs2 Hs3 _Hf1 l2'.
assert (Hs2' : forall y, In y l2' -> support D y =S= s2).
{
  intros y; unfold l2', semi_join, natural_join_list, theta_join_list.
  rewrite in_flat_map.
  intros [x2 [Hx2 Hy]].
  unfold d_join_list in Hy; rewrite in_map_iff in Hy.
  destruct Hy as [y2 [Hy Hy2]]; subst y.
  rewrite filter_In in Hy2.
  assert (Ky2 := Oeset.mem_nb_occ _ _ _ (Oeset.in_mem_bool OD _ _ (proj1 Hy2))).
  rewrite nb_occ_delta_list in Ky2.
  assert (Jy2 : Oeset.mem_bool 
                  OD y2
                  (map (projection D s2)
                       (join 
                          (fun x : data => f1 x && f2 x) l2
                          (flat_map
                             (fun x1 : data => map (combine D x1) 
                                                   (filter (compatible D x1) l3))
                             l1))) = true).
  {
    apply Oeset.nb_occ_mem.
    destruct (Oeset.nb_occ 
                OD y2
                (map (projection D s2)
                     (join (fun x0 : data => f1 x0 && f2 x0) l2
                           (flat_map (fun x1 : data => map (combine D x1) 
                                                           (filter (compatible D x1) l3))
                                     l1)))); [ | discriminate].
    apply False_rec; apply Ky2; apply refl_equal.
    }
  rewrite Oeset.mem_bool_true_iff in Jy2.
  destruct Jy2 as [z2 [Jy2 Hz2]].
  rewrite in_map_iff in Hz2.
  destruct Hz2 as [z [Hz2 Hz]]; subst z2.
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_1 _ _ _ _ (Hs2 _ Hx2))).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (support_eq _ _ _ Jy2))).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (support_projection_eq _ _ _))).
  rewrite Fset.equal_spec; intro; rewrite Fset.mem_union; apply Bool.orb_diag.
}
rewrite 2 (nb_occ_semi_join f2 f2_eq (s1 unionS s2) s3).
- case_eq (existsb (fun x2 : data => compatible D x x2 && f2 (combine D x x2)) l3);
  intro K1; [rewrite 2 N.mul_1_r | rewrite 2 N.mul_0_r; apply refl_equal].
  unfold join.
  do 2 (rewrite Oeset.nb_occ_filter; [ | intros; apply f1_eq; assumption]).
  case_eq (f1 x); intro Hf1; [ | apply refl_equal].
  rewrite (nb_occ_natural_join_list l1 l2 s1 s2); trivial.
  rewrite (nb_occ_natural_join_list l1 l2' s1 s2); trivial.
  + case_eq (support D x =S?= (s1 unionS s2)); intro Hs;
      [rewrite 2 N.mul_1_r | rewrite 2 N.mul_0_r; apply refl_equal].
    case_eq (Oeset.nb_occ OD (projection D s1 x) l1);
      [intro Hx; rewrite 2 N.mul_0_l; apply refl_equal | ].
    intros p1 Hp1; apply f_equal.
    unfold l2'.
    assert (f1f2_eq : forall x y, Oeset.compare OD x y = Eq ->
            (fun x : data => f1 x && f2 x) x = (fun x : data => f1 x && f2 x) y).
    {
      intros x1 x2 H; apply f_equal2; [apply f1_eq | apply f2_eq]; assumption.
    }
    rewrite (nb_occ_semi_join _ f1f2_eq s2 (s1 unionS s3)); trivial.
    * rewrite <- (N.mul_1_r (Oeset.nb_occ OD (projection D s2 x) l2)) at 1.
      case_eq (Oeset.nb_occ OD (projection D s2 x) l2);
        [intro H; rewrite 2 N.mul_0_l; apply refl_equal | ].
      intros p2 Hp2; apply f_equal.
      assert (Aux : existsb
                      (fun x2 : data =>
                         compatible D (projection D s2 x) x2 &&
                                            (f1 (combine D (projection D s2 x) x2) && 
                                                f2 (combine D (projection D s2 x) x2)))
                      (natural_join_list l1 l3) = true).
      {
        rewrite existsb_exists in K1.
        destruct K1 as [x3 [Hx3 K1]].
        rewrite Bool.andb_true_iff in K1.
        destruct K1 as [K1 K2].
        rewrite existsb_exists.
        assert (Kp1 : Oeset.mem_bool OD (projection D s1 x) l1 = true).
        {
          apply Oeset.nb_occ_mem; rewrite Hp1; discriminate.
        }
        rewrite Oeset.mem_bool_true_iff in Kp1.
        destruct Kp1 as [x1 [Kp1 Hx1]].
        assert (Kp2 : Oeset.mem_bool OD (projection D s2 x) l2 = true).
        {
          apply Oeset.nb_occ_mem; rewrite Hp2; discriminate.
        }
        rewrite Oeset.mem_bool_true_iff in Kp2.
        destruct Kp2 as [x2 [Kp2 Hx2]].
        assert (Ks1 : s1 subS (s1 unionS s2)).
        {
          rewrite Fset.subset_spec; intros; rewrite Fset.mem_union; rewrite Bool.orb_true_iff.
          left; assumption.
        }
        assert (Ks2 : s2 subS (s1 unionS s2)).
          {
            rewrite Fset.subset_spec; intros; rewrite Fset.mem_union; rewrite Bool.orb_true_iff.
            right; assumption.
          }
        assert (H := Oeset.compare_eq_refl OD (combine D x x3)).
        rewrite (split_d D (s1 unionS s2) s3 (combine D x x3) x x3 Hs (Hs3 _ Hx3) K1) in H.
        assert (H12 : compatible D x1 x2 = true).
        {
          rewrite <- (compatible_eq_1 _ _ _ _ Kp1).
          rewrite <- (compatible_eq_2 _ _ _ _ Kp2).
          apply compatible_projection.
        }
        assert (H' : Oeset.compare OD x (combine D x1 x2) = Eq).
        {
          rewrite (split_d D s1 s2).
          - rewrite Oeset.compare_lt_gt, Kp1; split; [apply refl_equal | ].
            rewrite Oeset.compare_lt_gt, Kp2; split; [apply refl_equal | ].
            assumption.
          - apply Hs1; assumption.
          - apply Hs2; assumption.
          - assumption.
        }
        assert (H13 : compatible D x1 x3 = true).
        {
          rewrite (compatible_eq_2 _ _ _ _ (proj1 (proj2 H))).
          rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_eq_2 _ _ _ _ (proj1 H))) in Kp1.
          rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_idem _ _ _ _ _ Ks1 _)) in Kp1.
          rewrite <- (compatible_eq_1 _ _ _ _ Kp1).
          apply compatible_projection.
        }
        assert (H23 : compatible D x2 x3 = true).
        {
          rewrite (compatible_eq_2 _ _ _ _ (proj1 (proj2 H))).
          rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_eq_2 _ _ _ _ (proj1 H))) in Kp2.
          rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_idem _ _ _ _ _ Ks2 _)) in Kp2.
          rewrite <- (compatible_eq_1 _ _ _ _ Kp2).
          apply compatible_projection.
        }
        exists (combine D x1 x3); split.
        - unfold natural_join_list, theta_join_list.
          rewrite in_flat_map.
          exists x1; split; [assumption | ].
          unfold d_join_list.
          rewrite in_map_iff.
          exists x3; split; [apply refl_equal | ].
          rewrite filter_In; split; assumption.
        - rewrite (compatible_eq_1 _ _ _ _ Kp2), (compatible_combine_2 D), H23; 
            [ | assumption].
          rewrite compatible_comm, H12, Bool.andb_true_l.
          assert (Aux : combine D x x3 =d= combine D (projection D s2 x) (combine D x1 x3)).
          {
            rewrite (split_d D s2 (s1 unionS s3)).
            - split; [ | split].
              + rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_eq_2 _ _ _ _ (proj1 H))).
                apply projection_idem.
                rewrite Fset.subset_spec; intros; rewrite Fset.mem_union, Bool.orb_true_iff.
                right; assumption.
              + rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl. 
                rewrite (split_d D s1 s3).
                * rewrite <- (Oeset.compare_eq_1 _ _ _ _ Kp1).
                  rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_eq_2 _ _ _ _ (proj1 H))).
                  rewrite (Oeset.compare_eq_1 _ _ _ _ (projection_idem _ _ _ _ _ Ks1 _)).
                  split; [apply Oeset.compare_eq_sym; apply projection_idem; 
                          rewrite Fset.subset_spec; intros; 
                          rewrite Fset.mem_union, Bool.orb_true_iff; left; assumption | ].
                  split; 
                    [ | rewrite (Fset.equal_eq_1 _ _ _ _ (support_projection_eq _ _ _));
                        apply Fset.equal_refl].
                  rewrite (Oeset.compare_eq_1 _ _ _ _ (proj1 (proj2 H))).
                  apply Oeset.compare_eq_sym.
                  apply projection_idem; rewrite Fset.subset_spec; 
                    intros; rewrite Fset.mem_union, Bool.orb_true_iff; right; assumption.
                * apply Hs1; assumption.
                * apply Hs3; assumption.
                * assumption.
              + rewrite (Fset.equal_eq_1 
                           _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
                rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_1 _ _ _ _ Hs)).
                rewrite Fset.equal_spec; intro.
                rewrite 4 Fset.mem_union, Bool.orb_assoc.
                apply f_equal2; [apply Bool.orb_comm | ].
                apply (Fset.mem_eq_2 _ _ _ (Hs3 _ Hx3)).
            - apply support_projection_eq.
            - rewrite (Fset.equal_eq_1 
                           _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
              apply Fset.union_eq; [apply Hs1 | apply Hs3]; assumption.
            - rewrite (compatible_eq_1 _ _ _ _ Kp2), compatible_combine_2;
                [ | assumption].
              rewrite H23, compatible_comm, H12; trivial.
          }
          rewrite <- (f1_eq _ _ Aux), <- (f2_eq _ _ Aux), K2, Bool.andb_true_r.
          rewrite <- Hf1; apply _Hf1; trivial.
          apply Hs3; assumption.
      }
      rewrite Aux; apply refl_equal.
    * intros y Hy.
      unfold natural_join_list, theta_join_list in Hy.
      rewrite in_flat_map in Hy.
      destruct Hy as [x1 [Hx1 Hy]].
      unfold d_join_list in Hy.
      rewrite in_map_iff in Hy.
      destruct Hy as [x3 [Hy Hx3]]; subst y.
      rewrite filter_In in Hx3; destruct Hx3 as [Hx3 _].
      rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
      apply Fset.union_eq; [apply Hs1 | apply Hs3]; assumption.
- intros y Hy; unfold join in Hy.
  rewrite filter_In in Hy; destruct Hy as [Hy _].
  unfold natural_join_list, theta_join_list in Hy.
  rewrite in_flat_map in Hy.
  destruct Hy as [x1 [Hx1 Hy]].
  unfold d_join_list in Hy.
  rewrite in_map_iff in Hy.
  destruct Hy as [x2 [Hy Hx2]]; subst y.
  rewrite filter_In in Hx2; destruct Hx2 as [Hx2 _].
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
  apply Fset.union_eq; [apply Hs1 | apply Hs2']; assumption.
- assumption.
- intros y Hy; unfold join in Hy.
  rewrite filter_In in Hy; destruct Hy as [Hy _].
  unfold natural_join_list, theta_join_list in Hy.
  rewrite in_flat_map in Hy.
  destruct Hy as [x1 [Hx1 Hy]].
  unfold d_join_list in Hy.
  rewrite in_map_iff in Hy.
  destruct Hy as [x2 [Hy Hx2]]; subst y.
  rewrite filter_In in Hx2; destruct Hx2 as [Hx2 _].
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_combine _ _ _ _ (Oeset.compare_eq_refl _ _))).
  apply Fset.union_eq; [apply Hs1 | apply Hs2]; assumption.
- assumption.    
Qed.

End Optim.

End Sec. 

End Data.

