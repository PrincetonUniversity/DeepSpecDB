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
        FiniteSet FiniteBag FiniteCollection Partition DExpressions Data.

Require Import compcert.common.Values.
Require Import VST.veric.base.

(** ** Tuples, built upon attributes, abstract domains and abstract values. *)

Module Tuple.

Record Rcd : Type :=
mk_R 
  {
(** Basic ingredients, attributes, domains and values *)
     attribute : Type;
     type : Type;
     value : Type;
(** Typing attributes and values. *)
     type_of_attribute : attribute -> type;
     type_of_value : value -> type;
(** Default Values. *)
     default_value : type -> value;
     (** Attributes, types and values enjoy some comparison functions suitable to build ordered types. *)
     OAtt : Oset.Rcd attribute;
     A : Fset.Rcd OAtt;
     OType : Oset.Rcd type;
     OVal : Oset.Rcd value;
     FVal : Fset.Rcd OVal;
(** Abstract tuples. *)
     tuple : Type;
     support : tuple -> Fset.set A;
(* In case of NRA models need to add other accessors (paths expressions) *)
     dot_ : tuple -> attribute -> value;
     address: tuple -> val;
(** Building tuples with [mk_tuple] from a relevant set of attributes, and a function which associates a value to each of them. *)
     mk_tuple_ : Fset.set A -> (attribute -> value) -> val -> tuple;
 (** Properties of [mk_tuple], which behaves as a pair of finite set of attributes and a function.   *)
     support_mk_tuple_ : forall s f p, support (mk_tuple_ s f p) =S= s;
     dot_mk_tuple_ :
       forall a s f p, a inS s -> dot_ (mk_tuple_ s f p) a = f a;
     address_mk_tuple_:
       forall s f p, address (mk_tuple_ s f p) = p;
(** Comparison of tuples*)
     OTuple : Oeset.Rcd tuple;
(** Finite collections of tuples. *)
     CTuple : Fecol.Rcd OTuple;
(** The comparison function of tuples exactly identifies tuples which have the same set of relevant attributes, and which coincide point-wise on this common set. *)
     tuple_eq_ :
       forall t1 t2 : tuple, 
         (Oeset.compare OTuple t1 t2 = Eq) <-> 
         (support t1 =S= support t2 /\ forall a, a inS (support t1) -> dot_ t1 a = dot_ t2 a) 
  (* take care of equality when we shall handle sets of values *)
}.

Section Sec.

Notation "t1 '=t=' t2" := (Oeset.compare (OTuple _) t1 t2 = Eq) (at level 70, no associativity).
Notation "s1 '=P=' s2" := (_permut (@eq (Tuple.tuple _)) s1 s2) (at level 70, no associativity).
Notation "s1 '=PE=' s2" := (_permut (fun x y => Oeset.compare (Tuple.OTuple _) x y = Eq) s1 s2) (at level 70, no associativity).

Hypothesis T : Rcd.
Notation FTupleT := (Fecol.CSet (CTuple T)).
Notation setT := (Feset.set FTupleT).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Definition mk_tuple s f := 
  mk_tuple_ T s (fun a => if a inS? s then f a else default_value T (type_of_attribute T a)).

Lemma mk_tuple_mk_tuple_ :
  forall s f p, mk_tuple s f p =t= mk_tuple_ T s f p.
Proof.
intros s f p; unfold mk_tuple; rewrite tuple_eq_; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple_ _ _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple_ _ _ _ _)).
  apply Fset.equal_refl.
-  intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ T _ _ _)) in Ha.
   rewrite 2 dot_mk_tuple_, Ha; trivial.
Qed.

Definition empty_tuple := 
  mk_tuple (Fset.empty (A T)) (fun a => default_value T (type_of_attribute T a)) nullval.

Definition default_tuple s := mk_tuple s (fun a => default_value T (type_of_attribute T a)).

Definition dot (t : tuple T) (a : attribute T) :=
  if a inS? support T t
  then dot_ T t a
  else default_value T (type_of_attribute T a).

Lemma support_empty_tuple : support T empty_tuple =S= emptysetS.
Proof.
unfold empty_tuple, mk_tuple; apply support_mk_tuple_.
Qed.

Lemma support_mk_tuple : 
  forall s f p, support T (mk_tuple s f p) =S= s.
Proof.
intros s f; unfold mk_tuple; apply support_mk_tuple_.
Qed.

Lemma dot_mk_tuple : 
  forall a s f p, a inS s -> dot (mk_tuple s f p) a = f a.
Proof.
intros a s f p Ha; unfold dot, mk_tuple.
rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), dot_mk_tuple_, Ha; trivial.
Qed.

Lemma tuple_eq :
  forall t1 t2, t1 =t= t2 <-> (support T t1 =S= support T t2 /\ forall a, dot t1 a = dot t2 a).
Proof.
intros t1 t2; rewrite tuple_eq_; split; (intros [H1 H2]; split; [apply H1 | ]).
- intros a; unfold dot; rewrite <- (Fset.mem_eq_2 _ _ _ H1 a).
  case_eq (a inS? support T t1); intro Ha; [ | apply refl_equal].
  apply H2; assumption.
- intros a Ha.
  assert (Ka := H2 a); unfold dot in Ka.
  rewrite <- (Fset.mem_eq_2 _ _ _ H1), Ha in Ka.
  apply Ka.
Qed.

Lemma tuple_eq_support :
  forall t1 t2, t1 =t= t2 -> support T t1 =S= support T t2.
Proof.
intros t1 t2; rewrite tuple_eq; apply proj1.
Qed.

Lemma tuple_eq_dot_ :
  forall t1 t2, t1 =t= t2 -> forall a, a inS support T t1 -> dot_ T t1 a = dot_ T t2 a.          
Proof.
intros t1 t2 H a; rewrite tuple_eq_ in H.
apply (proj2 H).
Qed.

Lemma tuple_eq_dot :
  forall t1 t2, t1 =t= t2 -> forall a, dot t1 a = dot t2 a.          
Proof.
intros t1 t2 H a; rewrite tuple_eq in H.
apply (proj2 H).
Qed.

Lemma mk_tuple_eq_1 :
  forall s1 s2 f p1 p2, s1 =S= s2 -> mk_tuple s1 f p1 =t= mk_tuple s2 f p2.
Proof.
intros s1 s2 f p1 p2 H; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
  assumption.
- intro a; unfold dot; rewrite 2 (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)).
  rewrite <- (Fset.mem_eq_2 _ _ _ H);
  case_eq (a inS? s1); intro Ha; [ | apply refl_equal].
  unfold mk_tuple; rewrite 2 dot_mk_tuple_, <- (Fset.mem_eq_2 _ _ _ H); trivial.
  rewrite <- (Fset.mem_eq_2 _ _ _ H); apply Ha.
Qed.

Lemma mk_tuple_eq_2 :
  forall s f1 f2 p1 p2, (forall a, a inS s -> f1 a = f2 a) -> mk_tuple s f1 p1 =t= mk_tuple s f2 p2.
Proof.
intros s f1 f2 p1 p2 Hf; rewrite tuple_eq_; split.
- rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
  apply support_mk_tuple.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ha.
  unfold mk_tuple; rewrite 2 dot_mk_tuple_, Hf; trivial.
Qed.

Lemma mk_tuple_eq :
  forall s1 s2 f1 f2 p1 p2, s1 =S= s2 -> (forall a, a inS s1 -> a inS s2 -> f1 a = f2 a) ->
    mk_tuple s1 f1 p1 =t= mk_tuple s2 f2 p2.
Proof.
intros s1 s2 f1 f2 p1 p2 Hs Hf.
refine (Oeset.compare_eq_trans _ _ _ _ (mk_tuple_eq_1 _ _ _ p1 p2 Hs) _).
apply mk_tuple_eq_2.
intros a Ha; apply Hf; trivial.
rewrite (Fset.mem_eq_2 _ _ _ Hs); apply Ha.
Qed.

Lemma mk_tuple_id :
  forall t s p, support T t =S= s -> mk_tuple s (dot t) p =t= t.
Proof.
intros t s p H; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ H).
  apply Fset.equal_refl.
- intros a; case_eq (a inS? s); intro Ha.
  + rewrite dot_mk_tuple; trivial.
  + unfold dot; rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), (Fset.mem_eq_2 _ _ _ H), Ha.
    apply refl_equal.
Qed.


Lemma mk_tuple_eq_ :
  forall s1 s2 f1 f2 p1 p2, s1 =S= s2 -> (forall a, a inS s1 -> a inS s2 -> f1 a = f2 a) ->
    mk_tuple_ T s1 f1 p1 =t= mk_tuple_ T s2 f2 p2.
Proof.
intros s1 s2 f1 f2 p1 p2 Hs Hf.
refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_mk_tuple_ _ _ _)).
refine (Oeset.compare_eq_trans _ _ _ _ (Oeset.compare_eq_sym _ _ _ (mk_tuple_mk_tuple_ _ _ _)) _).
apply mk_tuple_eq; assumption.
Qed.

(** An attribute renaming. No assumptions are made at this point, neither about the compatibility of types, nor about the injectivity. *)
Definition renaming := list (attribute T * attribute T).

Definition apply_renaming rho :=
  fun a => 
    match Oset.find (OAtt T) a rho with
      | Some b => b
      | None => a
    end.

Definition tuple_as_pairs (t : tuple T) :=
  let support_t := Fset.elements (A T) (support T t) in
  List.map (fun a => (a, dot t a)) support_t.

Definition pairs_as_tuple t' (p: val) :=
  let s := Fset.mk_set (A T) (List.map (@fst _ _) t') in 
  mk_tuple s
    (fun a => 
       match Oset.find (OAtt T) a t' with 
         | Some b => b 
         | None => default_value T (type_of_attribute T a) 
       end) p.

Definition canonized_tuple t p := pairs_as_tuple (tuple_as_pairs t) p.

Lemma canonized_tuple_eq :
  forall t p, canonized_tuple t p =t= t.
Proof.
intros t p.
unfold canonized_tuple, tuple_as_pairs, pairs_as_tuple.
rewrite map_map; simpl; rewrite map_id; [ | intros; apply refl_equal].
rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  apply Fset.mk_set_idem.
- intro a; unfold dot, mk_tuple; 
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), Fset.mem_mk_set, <- Fset.mem_elements.
  case_eq (a inS? support T t); intro Ha; [ | apply refl_equal].
  rewrite dot_mk_tuple_, Fset.mem_mk_set, <- Fset.mem_elements, Ha;
    [ | rewrite Fset.mem_mk_set, <- Fset.mem_elements; apply Ha].
  rewrite Oset.find_map, Ha; [apply refl_equal | ].
  apply Fset.mem_in_elements; assumption.
Qed.

Lemma tuple_as_pairs_canonizes :
  forall t1 t2, t1 =t= t2 <-> tuple_as_pairs t1 = tuple_as_pairs t2.
Proof.
intros t1 t2; split; intro H.
- rewrite tuple_eq in H; destruct H as [H1 H2].
  unfold tuple_as_pairs; rewrite <- (Fset.elements_spec1 _ _ _ H1), <- map_eq.
  intros a Ha; apply f_equal; apply H2.
- refine (Oeset.compare_eq_trans _ _ _ _ _ (canonized_tuple_eq _ nullval)).
  unfold canonized_tuple; rewrite <- H; apply Oeset.compare_eq_sym.
  apply canonized_tuple_eq.
Qed.

(** Boolean version of [one_to_one_renaming] in order to be able to compute. *)
Definition one_to_one_renaming_bool s (rho : renaming) : bool :=
  Oset.one_to_one_bool (OAtt T) (OAtt T) s (apply_renaming rho).

Definition rename_tuple rho (t : tuple T) : tuple T :=
  mk_tuple (Fset.map (A T) (A T) rho (support T t))
           (fun ra : attribute T =>
              match
                Oset.find (OAtt T) ra
                          (map (fun a : attribute T => (rho a, dot t a))
                               ({{{support T t}}})) with
                | Some v => v
                | None => default_value T (type_of_attribute T ra)
              end) (address _ t).

Lemma rename_tuple_ok :
  forall rho t, 
    support T (rename_tuple rho t) =S= Fset.map _ (A T) rho (support T t) /\
    ((forall a1 a2, a1 inS support T t -> a2 inS support T t -> rho a1 = rho a2 -> a1 = a2) -> 
     forall a, a inS support T t -> dot (rename_tuple rho t) (rho a) = dot t a).
Proof.
intros rho t; unfold rename_tuple; split.
- apply support_mk_tuple.
- intros Hrho a Ha.
  assert (Hra : rho a inS Fset.map (A T) (A T) rho (support T t)).
  {
    rewrite Fset.mem_map; exists a; split; trivial.
  }
  rewrite dot_mk_tuple; [ | assumption].
  case_eq (Oset.find (OAtt T) (rho a)
                     (map (fun a0 : attribute T => (rho a0, dot t a0))
                          ({{{support T t}}}))).
  + intros v Hv.
    assert (Kv := Oset.find_some _ _ _ Hv).
    rewrite in_map_iff in Kv; destruct Kv as [a' [H1 H2]].
    injection H1; clear H1; intro; subst v; intro H1.
    apply f_equal; apply Hrho; trivial.
    apply Fset.in_elements_mem; assumption.
  + intro K; apply False_rec; apply (Oset.find_none _ _ _ K) with (dot t a).
    rewrite in_map_iff; exists a; split; trivial.
    apply Fset.mem_in_elements; assumption.
Qed.

Lemma rename_tuple_id_eq :
  forall rho t, (forall a, a inS support T t -> rho a = a) -> rename_tuple rho t =t= t.
Proof.
intros rho t H.
assert (H' : (Fset.map (A T) (A T) rho (support T t)) =S= support T t).
{
  rewrite Fset.equal_spec; intro a; rewrite eq_bool_iff, Fset.mem_map; split.
  - intros [b [Hb Kb]]; subst a.
    rewrite (H _ Kb); assumption.
  - intros Ha; exists a; split; trivial.
    apply H; assumption.
}
rewrite tuple_eq; split.
- unfold rename_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)); assumption.
- intro a.
  case_eq (a inS? support T t); intro Ha.
  + rewrite <- (proj2 (rename_tuple_ok rho t)).
    * apply f_equal; apply sym_eq; apply H; assumption.
    * do 4 intro; rewrite 2 H; trivial.
    * assumption.
  + unfold rename_tuple, dot.
    rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)),  (Fset.mem_eq_2 _ _ _ H'), Ha; 
      apply refl_equal.
Qed.

(** Compatibility of tuple renaming w.r.t. the equivalence of tuples. *)
Lemma rename_tuple_eq_2 :
  forall rho t1 t2, t1 =t= t2 -> rename_tuple rho t1 =t= rename_tuple rho t2.
Proof.
intros rho t1 t2 H.
rewrite tuple_eq in H; rewrite tuple_eq; split.
- unfold rename_tuple; 
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _));
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
  unfold Fset.map; rewrite <- (Fset.elements_spec1 _ _ _ (proj1 H)).
  apply Fset.equal_refl.
- intros a; unfold rename_tuple.
  unfold Fset.map; rewrite <- (Fset.elements_spec1 _ _ _ (proj1 H)).
  case_eq (a inS? Fset.mk_set (A T) (map rho ({{{support T t1}}}))); intro Ha.
  + rewrite 2 dot_mk_tuple; trivial.
    apply match_option_eq; apply f_equal.
    rewrite <- map_eq; intros b Hb; apply f_equal.
    apply (proj2 H).
  + unfold dot; rewrite 2 (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Ha; apply refl_equal.
Qed.

Lemma rename_tuple_eq_1 :
  forall rho1 rho2 t, 
    (forall a, a inS support T t -> rho1 a = rho2 a) ->
    rename_tuple rho1 t =t= rename_tuple rho2 t.
Proof.
intros rho1 rho2 t H.
rewrite tuple_eq; unfold rename_tuple.
assert (K : Fset.map (A T) (A T) rho1 (support T t) =S= Fset.map (A T) (A T) rho2 (support T t)).
{
  apply Fset.equal_refl_alt; unfold Fset.map; apply f_equal.
  rewrite <- map_eq; intros; apply H; apply Fset.in_elements_mem; assumption.
}
rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _));
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _));
  split; [assumption | ].
- intros a; unfold rename_tuple.
  case_eq (a inS? Fset.mk_set (A T) (map rho1 ({{{support T t}}}))); intro Ha.
  + rewrite 2 dot_mk_tuple; trivial.
    * apply match_option_eq; apply f_equal.
      rewrite <- map_eq; intros b Hb; apply f_equal2; [ | apply refl_equal].
      apply H; apply Fset.in_elements_mem; assumption.
    * rewrite <- (Fset.mem_eq_2 _ _ _ K); assumption.
  + unfold dot, mk_tuple; 
    rewrite 2 (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), <- (Fset.mem_eq_2 _ _ _ K).
    unfold Fset.map; rewrite Ha; apply refl_equal.
Qed.

Lemma rename_tuple_eq :
  forall rho1 rho2 t1 t2,  
    (forall a, a inS support T t1 -> rho1 a = rho2 a) -> t1 =t= t2 ->
    rename_tuple rho1 t1 =t= rename_tuple rho2 t2.
Proof.
intros rho1 rho2 t1 t2 Hrho Ht.
refine (Oeset.compare_eq_trans _ _ _ _ (rename_tuple_eq_1 _ _ _ Hrho) _).
apply rename_tuple_eq_2; assumption.
Qed.

(** Test whether t1 and t2 have compatible values on the common attributes. *)
Definition join_compatible_tuple (t1 t2 : tuple T) : bool :=
 Fset.for_all (A T)
   (fun a => 
      match Oset.compare (OVal T) (dot t1 a) (dot t2 a) with 
        | Eq => true 
        | Lt | Gt => false 
      end)
   (support T t1 interS support T t2).

Definition join_tuple (t1 t2 : tuple T) (p: val) : tuple T :=
  mk_tuple 
    (Fset.union (A T) (support T t1) (support T t2))
    (fun a => if Fset.mem (A T) a (support T t1) then dot t1 a else dot t2 a) p.

Lemma join_compatible_tuple_alt :
 forall t1 t2, 
   join_compatible_tuple t1 t2 = true <->
   (forall a, a inS support T t1 -> a inS support T t2 -> dot t1 a = dot t2 a).
Proof.
intros t1 t2; unfold join_compatible_tuple.
rewrite Fset.for_all_spec, forallb_forall; split.
- intros H a Ha1 Ha2.
  assert (Ha := H a).
  rewrite compare_eq_true, Oset.compare_eq_iff in Ha; apply Ha.
  rewrite Fset.elements_inter; split; 
  rewrite <- (Oset.mem_bool_true_iff (OAtt T)), <- Fset.mem_elements;
  assumption.
- intros H a Ha; rewrite Fset.elements_inter in Ha.
  rewrite compare_eq_true, Oset.compare_eq_iff; 
    apply H; apply Fset.in_elements_mem; [apply (proj1 Ha) | apply (proj2 Ha)].
Qed.

Lemma join_compatible_tuple_eq_1 :
  forall t1 t2 t, t1 =t= t2 ->
    join_compatible_tuple t1 t = join_compatible_tuple t2 t.
Proof.
intros t1 t2 t Ht. 
rewrite eq_bool_iff, 2 join_compatible_tuple_alt; split;
intros K a Ha Ka.
- rewrite <- (tuple_eq_dot _ _ Ht); apply K; [ | assumption].
  rewrite (Fset.mem_eq_2 _ _ _ (tuple_eq_support _ _ Ht)); assumption.
- rewrite (tuple_eq_dot _ _ Ht); apply K; [ | assumption].
  rewrite <- (Fset.mem_eq_2 _ _ _ (tuple_eq_support _ _ Ht)); assumption.
Qed. 

Lemma join_compatible_tuple_eq_2 :
  forall t1 t2 t, t1 =t= t2 ->
    join_compatible_tuple t t1 = join_compatible_tuple t t2.
Proof.
intros t1 t2 t Ht. 
rewrite eq_bool_iff, 2 join_compatible_tuple_alt; split;
intros K a Ha Ka.
- rewrite <- (tuple_eq_dot _ _ Ht); apply K; [assumption | ].
  rewrite (Fset.mem_eq_2 _ _ _ (tuple_eq_support _ _ Ht)); assumption.
- rewrite (tuple_eq_dot _ _ Ht); apply K; [assumption | ].
  rewrite <- (Fset.mem_eq_2 _ _ _ (tuple_eq_support _ _ Ht)); assumption.
Qed. 

Lemma join_compatible_tuple_eq :
  forall t1 t2 t1' t2', 
    t1 =t= t1' -> t2 =t= t2' -> join_compatible_tuple t1 t2 = join_compatible_tuple t1' t2'.
Proof.
intros t1 t2 t1' t2' H H'.
rewrite (join_compatible_tuple_eq_1 _ _ _ H); apply join_compatible_tuple_eq_2; assumption.
Qed.

Lemma join_compatible_tuple_comm :
  forall t1 t2, join_compatible_tuple t1 t2 = join_compatible_tuple t2 t1.
Proof.
intros t1 t2; rewrite eq_bool_iff; rewrite 2 join_compatible_tuple_alt; split;
intros H a Ha Ka; apply sym_eq; apply H; trivial.
Qed.

Lemma join_tuple_comm : 
  forall t1 t2 p12 p21, join_compatible_tuple t1 t2 = true -> join_tuple t1 t2 p12 =t= join_tuple t2 t1 p21.
Proof.
intros t1 t2 p12 p21 H; rewrite join_compatible_tuple_alt in H.
unfold join_tuple; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _));
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)), Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union; apply Bool.orb_comm.
- intro a; case_eq (a inS? support T t1); intro Ha1.
  + rewrite dot_mk_tuple, Ha1; [ | rewrite Fset.mem_union, Ha1; trivial].
    rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ha1, Bool.orb_true_r; trivial].
    case_eq (a inS? support T t2); intro Ha2; [ | apply refl_equal].
    apply (H a Ha1 Ha2).
  + case_eq (a inS? support T t2); intro Ha2.
    * rewrite 2 dot_mk_tuple, Ha1, Ha2; 
      [trivial | | ]; rewrite Fset.mem_union, Ha1, Ha2; trivial.
    * unfold dot; 
      rewrite 2 (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 2 Fset.mem_union, Ha1, Ha2; 
      apply refl_equal.
Qed.

Lemma join_tuple_assoc : 
  forall t1 t2 t3 pa pb pc pd, join_tuple t1 (join_tuple t2 t3 pa) pb =t= join_tuple (join_tuple t1 t2 pc) t3 pd.
Proof.
intros t1 t2 t3 *; unfold join_tuple; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (support_mk_tuple _ _ _))).
  rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.union_eq_1 _ _ _ _ (support_mk_tuple _ _ _))).
  apply Fset.union_assoc.
- intro a; case_eq (a inS? support T t1); intro Ha1.
  + rewrite (dot_mk_tuple a (Fset.union _ (support T t1) _) _), Ha1; 
    [ | rewrite Fset.mem_union, Ha1; apply refl_equal].
    rewrite dot_mk_tuple; 
      [ | rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 
          Fset.mem_union, Ha1; apply refl_equal].
    rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha1.
    rewrite dot_mk_tuple, Ha1; [ | rewrite Fset.mem_union, Ha1; apply refl_equal]. 
    apply refl_equal.
  + case_eq (a inS? support T t2); intro Ha2.
    * rewrite (dot_mk_tuple a (Fset.union _ (support T t1) _) _), Ha1;
      [ | rewrite Fset.mem_union, Ha1, Bool.orb_false_l, 
          (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha2; apply refl_equal].
      rewrite dot_mk_tuple, Ha2; [ | rewrite Fset.mem_union, Ha2; apply refl_equal].
      rewrite dot_mk_tuple; 
        [ | rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 
            Fset.mem_union, Ha1, Ha2; apply refl_equal].
      rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha1, Ha2.
      rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ha1, Ha2; apply refl_equal].
      rewrite Ha1; apply refl_equal.
    * {
        case_eq (a inS? (support T t3)); intro Ha3.
        - rewrite (dot_mk_tuple a (Fset.union _ (support T t1) _) _), Ha1;
          [ | rewrite Fset.mem_union, Ha1, Bool.orb_false_l, 
              (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha2, Ha3; 
              apply refl_equal].
          rewrite dot_mk_tuple, Ha2; [ | rewrite Fset.mem_union, Ha2, Ha3; apply refl_equal].
          rewrite dot_mk_tuple; 
            [ | rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 
                Fset.mem_union, Ha1, Ha2, Ha3; apply refl_equal].
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha1, Ha2.
          apply refl_equal.
        - unfold dot.
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha1.
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha2, Ha3.
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha3, 
          Bool.orb_false_r.
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha1, Ha2.
          apply refl_equal.
      }
Qed.

Lemma join_tuple_eq :
 forall p12 p21 t1 t2 s1 s2, t1 =t= s1 -> t2 =t= s2 -> join_tuple t1 t2 p12 =t= join_tuple s1 s2 p21.
Proof.
intros * H1 H2.
rewrite tuple_eq, Fset.equal_spec in H1, H2.
unfold join_tuple; apply mk_tuple_eq.
- rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union, (proj1 H1), (proj1 H2); apply refl_equal.
- intros a Ha Ka; case_eq (a inS? support T t1); intro Ha1.
  + rewrite <- (proj1 H1), Ha1; apply (proj2 H1).
  + rewrite Fset.mem_union, Ha1, Bool.orb_false_l in Ha.
    rewrite <- (proj1 H1), Ha1; apply (proj2 H2).
Qed.

Lemma join_tuple_eq_1 :
  forall x1 x1' x2 p12 p1'2, x1 =t= x1' -> join_tuple x1 x2 p12 =t= join_tuple x1' x2 p1'2.
Proof.
intros; apply join_tuple_eq; [assumption | apply Oeset.compare_eq_refl].
Qed.

Lemma join_tuple_eq_2 :
  forall x1 x2 x2' p12 p12', x2 =t= x2' -> join_tuple x1 x2 p12 =t= join_tuple x1 x2' p12'.
Proof.
intros; apply join_tuple_eq; [apply Oeset.compare_eq_refl | assumption].
Qed.

Lemma mk_tuple_dot_join_tuple_1 :
  forall s t1 t2 pmk pjoin, support T t1 =S= s -> mk_tuple s (dot (join_tuple t1 t2 pjoin)) pmk =t= t1.
Proof.
intros * Hs.
rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ Hs); apply Fset.equal_refl.
- rewrite Fset.equal_spec in Hs.
  intros a; unfold dot, mk_tuple; 
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), <- Hs.
  case_eq (a inS? support T t1); intro Ha; [ | apply refl_equal].
  rewrite dot_mk_tuple_; [ | rewrite <- Hs; assumption].
  unfold join_tuple, mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), 
    <- Hs, Fset.mem_union, Ha, dot_mk_tuple_, Fset.mem_union, Ha.
  + unfold dot; rewrite Ha; trivial.
  + rewrite Fset.mem_union, Ha; apply refl_equal.
Qed.

Lemma mk_tuple_dot_join_tuple_2 :
  forall s2 t1 t2 pmk pjoin, join_compatible_tuple t1 t2 = true -> 
                   support T t2 =S= s2 -> mk_tuple s2 (dot (join_tuple t1 t2 pjoin)) pmk =t= t2.
Proof.
intros * Hj Hs2.
refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t2 t1 pmk pjoin Hs2)).
apply mk_tuple_eq_2.
intros a Ha; apply tuple_eq_dot; apply join_tuple_comm; assumption.
Qed.

Lemma join_tuple_empty_1 :
  forall t p, join_tuple empty_tuple t p =t= t.
Proof.
intros; 
  refine (Oeset.compare_eq_trans 
            _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t empty_tuple p p (Fset.equal_refl _ _))).
unfold join_tuple; apply mk_tuple_eq.
- rewrite Fset.equal_spec; intro a; unfold empty_tuple.
  rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.empty_spec, 
  Bool.orb_false_l; trivial.
- intros a _ Ha; rewrite (Fset.mem_eq_2 _ _ _ support_empty_tuple), Fset.empty_spec.
  unfold dot, mk_tuple.
  rewrite Ha, (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), Fset.mem_union, Ha, Bool.orb_true_l.
  rewrite dot_mk_tuple_; rewrite Fset.mem_union, Ha; apply refl_equal.
Qed.

Lemma join_tuple_empty_2 :
  forall t p, join_tuple t empty_tuple p =t= t.
Proof.
intros; refine (Oeset.compare_eq_trans _ _ _ _ _ (join_tuple_empty_1 _ p)).
apply join_tuple_comm.
rewrite join_compatible_tuple_alt.
intros a _ Ha; unfold empty_tuple in Ha.
rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.empty_spec in Ha; discriminate Ha.
Qed.

Lemma split_tuple_empty :
  forall t t1 empt pmk pjoin, 
    empty_tuple =t= empt ->
    (t =t= t1 <-> (t1 =t= (mk_tuple (support T t1) (dot t) pmk) /\ (join_tuple t1 empt pjoin) =t= t)).
Proof.
intros * He; split; [intro Ht; split | intros [Ht Kt]].
- apply Oeset.compare_eq_sym; refine (Oeset.compare_eq_trans _ _ _ _ _ Ht).
  refine (Oeset.compare_eq_trans 
            _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t empty_tuple pmk pjoin (Fset.equal_refl _ _))).
  apply mk_tuple_eq.
  + rewrite Oeset.compare_lt_gt, CompOpp_iff, tuple_eq in Ht; apply (proj1 Ht).
  + intros a _ Ha; apply sym_eq; apply tuple_eq_dot.
    apply join_tuple_empty_2.
- refine (Oeset.compare_eq_trans _ _ _ _ _ (join_tuple_empty_2 _ pjoin)).
  apply Oeset.compare_eq_sym; apply join_tuple_eq; assumption.
-   refine (Oeset.compare_eq_trans _ _ _ _ _ (join_tuple_empty_2 _ pjoin)).
    apply Oeset.compare_eq_sym; refine (Oeset.compare_eq_trans _ _ _ _ _ Kt).
    apply join_tuple_eq; [ | assumption].
    apply Oeset.compare_eq_refl.
Qed.

Lemma split_tuple :
  forall s1 s2 t t1 t2 pjoin pmk1 pmk2,
    support T t1 =S= s1 -> support T t2 =S= s2 -> join_compatible_tuple t1 t2 = true ->
    (t =t= (join_tuple t1 t2 pjoin) <-> (t1 =t= mk_tuple s1 (dot t) pmk1 /\ 
                                   t2 =t= mk_tuple s2 (dot t) pmk2 /\ 
                                   support T t =S= (s1 unionS s2))).
Proof.
intros * Hs1 Hs2 Hj; split; [intro H | intros [H1 [H2 H3]]]; [split; [ | split] | ].
- apply Oeset.compare_eq_sym.
  refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t1 t2 pmk1 pjoin Hs1)).
  apply mk_tuple_eq_2; intros; apply tuple_eq_dot; assumption.
- apply Oeset.compare_eq_sym. 
  refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_2 _ t1 t2 pmk2 pjoin Hj Hs2)).
  apply mk_tuple_eq_2; intros; apply tuple_eq_dot. assumption.
- rewrite tuple_eq in H; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 H)).
  unfold join_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2).
  apply refl_equal.
- rewrite tuple_eq; split.
  + rewrite (Fset.equal_eq_1 _ _ _ _ H3).
    unfold join_tuple; rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
    rewrite Fset.equal_spec; intro a.
    rewrite 2 Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2).
    apply refl_equal.
  + assert (H : support T t =S= support T (join_tuple t1 t2 pjoin)).
    {
      rewrite (Fset.equal_eq_1 _ _ _ _ H3), Fset.equal_spec; intro a.
      unfold join_tuple.
      rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 2 Fset.mem_union; 
        rewrite (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2), <- Fset.mem_union.
      apply refl_equal.
    } 
    intro a; case_eq (a inS? support T t); intro Ha.
    * unfold dot; rewrite <- (Fset.mem_eq_2 _ _ _ H), Ha.
      assert (Ka : a inS (support T t1 unionS support T t2)).
      {
        rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2);
        rewrite <- Fset.mem_union, <- (Fset.mem_eq_2 _ _ _ H3); assumption.
      }
      unfold join_tuple, mk_tuple; rewrite dot_mk_tuple_, Ka; trivial.
      {
        case_eq (a inS? support T t1); intro Ha1.
        - rewrite (tuple_eq_dot _ _ H1); unfold dot.
          rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), <- (Fset.mem_eq_2 _ _ _ Hs1), Ha1.
          unfold mk_tuple; 
            rewrite dot_mk_tuple_, Ha, <- (Fset.mem_eq_2 _ _ _ Hs1), Ha1; trivial.
          rewrite <- (Fset.mem_eq_2 _ _ _ Hs1); assumption.
        - rewrite Fset.mem_union, Ha1, Bool.orb_false_l in Ka.
          rewrite (tuple_eq_dot _ _ H2); rewrite dot_mk_tuple.
          + unfold dot; rewrite Ha; apply refl_equal.
          + rewrite <- (Fset.mem_eq_2 _ _ _ Hs2); assumption.
      } 
    * unfold dot; rewrite <- (Fset.mem_eq_2 _ _ _ H), Ha.
      apply refl_equal.
Qed.

Lemma split_tuple_strong :
  forall s1 s2, (s1 interS s2) =S= (Fset.empty (A T)) ->
    forall u1 u2 a1 a2 pu pa, support T u1 =S= s1 -> support T u2 =S= s2 ->
                        support T a1 =S= s1 -> support T a2 =S= s2 ->
                        (join_tuple u1 u2 pu =t= join_tuple a1 a2 pa ->  u1 =t= a1 /\ u2 =t= a2).
Proof.
intros * Hs * Hu1 Hu2 Ha1 Ha2 Ht.
assert (Hj : forall x1 x2, support T x1 =S= s1 -> support T x2 =S= s2 ->
                           join_compatible_tuple x1 x2 = true).
{
  intros x1 x2 Hx1 Hx2.
  rewrite join_compatible_tuple_alt.
  intros a Ha Ka; apply False_rec.
  rewrite Fset.equal_spec in Hx1, Hx2, Hs.
  assert (Abs : a inS (s1 interS s2)).
  {
    rewrite Fset.mem_inter, <- Hx1, <- Hx2, Ha, Ka.
    apply refl_equal.
  }
  rewrite Hs, Fset.empty_spec in Abs; discriminate Abs.
}
rewrite (split_tuple s1 s2 _ _ _ pa nullval nullval) in Ht; trivial; [ | apply Hj; trivial].
- destruct Ht as [Ju1 [Ju2 Ht]]; split.
  + apply Oeset.compare_eq_sym; refine (Oeset.compare_eq_trans _ _ _ _ Ju1 _).
    apply mk_tuple_dot_join_tuple_1; trivial.
  + apply Oeset.compare_eq_sym; refine (Oeset.compare_eq_trans _ _ _ _ Ju2 _).
    apply mk_tuple_dot_join_tuple_2; trivial.
    apply Hj; trivial.
Qed.

Definition build_data : Data.Rcd _ (OTuple T).
Print Data.Rcd.
split with 
    (attribute T) 
    (OAtt T) 
    (A T) 
    empty_tuple 
    (support T)
    (fun s t => mk_tuple s (dot t) nullval) 
    join_compatible_tuple
    (fun t1 t2 => join_tuple t1 t2 nullval).
- intros x1 x2 Hx; rewrite tuple_eq in Hx; apply (proj1 Hx).
- intros s x1 x2 Hx; apply mk_tuple_eq_2; intros.
  rewrite tuple_eq in Hx; apply (proj2 Hx).
- intros s1 s2 Hs x; rewrite Fset.subset_spec in Hs.
  rewrite tuple_eq; split.
  + rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
    rewrite (Fset.equal_eq_2 _ _ _ _ (support_mk_tuple _ _ _)).
    apply Fset.equal_refl.
  + intro a; unfold mk_tuple, dot.
    rewrite 2 (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)).
    case_eq (a inS? s1); intro Ha; [ | apply refl_equal].
    rewrite dot_mk_tuple_; [ | assumption].
    rewrite dot_mk_tuple_; [ | apply Hs; assumption].
    rewrite Ha, (Hs _ Ha).
    rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple_ _ _ _ _)), (Hs _ Ha).
    rewrite dot_mk_tuple_; [ | assumption].
    rewrite Ha; apply refl_equal.
- intros s t Ht; rewrite tuple_eq.
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)); split; [assumption | ].
  intros a; unfold dot.
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)).
  rewrite <- (Fset.mem_eq_2 _ _ _ Ht); case_eq (a inS? s); intro Ha; [ | apply refl_equal].
  unfold mk_tuple; rewrite dot_mk_tuple_, Ha; [ | assumption].
  rewrite <- (Fset.mem_eq_2 _ _ _ Ht), Ha; apply refl_equal.
- intros s t; apply support_mk_tuple.
- do 4 intro; apply join_compatible_tuple_eq_1; assumption.
- do 4 intro; apply join_compatible_tuple_eq_2; assumption.
- intros s1 s2 t; rewrite join_compatible_tuple_alt.
  intros a Ha Ka; rewrite 2 dot_mk_tuple; trivial.
  + rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ka; apply Ka.
  + rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ha; apply Ha.
- intros; apply join_compatible_tuple_comm.
- intros *; apply join_tuple_eq_1.
- intros *; apply join_tuple_eq_2.
- intros *; apply join_tuple_empty_2.
- intros u1 u2 Hu; apply join_tuple_comm; trivial.
- intros; apply join_tuple_assoc.
- intros u u1 u2 Hu; rewrite tuple_eq in Hu.
  rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Hu)).
  unfold join_tuple.
  rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _ _)).
  apply Fset.equal_refl.
- intros u1 u2 u3 H; rewrite join_compatible_tuple_alt in H; unfold join_tuple.
  rewrite eq_bool_iff, Bool.andb_true_iff, 3 join_compatible_tuple_alt; split.
  + intro K; split.
    * intros a Ha Ka.
      rewrite <- (K a); 
        [ | rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ha; trivial 
          | apply Ka].
      rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ha; trivial].
      rewrite Ha; apply refl_equal.
    * intros a Ha Ka.
      rewrite <- (K a); 
        [ | rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 
              Fset.mem_union, Ha, Bool.orb_true_r; trivial 
          | apply Ka].
      rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ha, Bool.orb_true_r; trivial].
      case_eq (a inS? support T u1); intro Hu1; [ | apply refl_equal].
      apply sym_eq; apply H; trivial.
  + intros [H1 H2].
    intros a Ha Ka; rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ha.
    rewrite dot_mk_tuple; [ | assumption].
    case_eq (a inS? support T u1); intro Ha1.
    * apply H1; trivial.
    * rewrite Fset.mem_union, Ha1 in Ha.
      apply H2; trivial.
- intros u1 u2 u3 H; rewrite join_compatible_tuple_alt in H; unfold join_tuple.
  rewrite eq_bool_iff, Bool.andb_true_iff, 3 join_compatible_tuple_alt; split.
  + intro K; split.
    * intros a Ha Ka.
      rewrite (K a);
        [ | apply Ha 
          | rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), Fset.mem_union, Ka; trivial].
      rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ka; trivial].
      rewrite Ka; apply refl_equal.
    * intros a Ha Ka.
      rewrite (K a); 
        [ | apply Ha 
          | rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)), 
            Fset.mem_union, Ka, Bool.orb_true_r; trivial].
      rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ka, Bool.orb_true_r; trivial].
      case_eq (a inS? support T u2); intro Hu2; [ | apply refl_equal].
      apply H; trivial.
  + intros [H1 H2].
    intros a Ha Ka; rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _ _)) in Ka.
    rewrite dot_mk_tuple; [ | assumption].
    case_eq (a inS? support T u2); intro Ha2.
    * apply H1; trivial.
    * rewrite Fset.mem_union, Ha2 in Ka.
      apply H2; trivial.
- intros s1 s2 x t1 t2 H1 H2 H.
  apply split_tuple; trivial.
Defined.

(*
Fixpoint N_join_tuple (lt : list (tuple T)) : tuple T :=
  match lt with
    | nil => empty_tuple
    | t1 :: lt => join_tuple t1 (N_join_tuple lt)
  end.

Lemma N_join_tuple_unfold :
  forall lt, N_join_tuple lt = match lt with
                                     | nil => empty_tuple
                                     | t1 :: lt => join_tuple t1 (N_join_tuple lt)
                                   end.
Proof.
intro lt; case lt; intros; apply refl_equal.
Qed.

Lemma mem_support_N_join_tuple :
  forall a lt, a inS (support T (N_join_tuple lt)) <->
               (exists t, List.In t lt /\ a inS support T t).
Proof.
intros a lt; induction lt as [ | t1 l]; split.
- intro Ha; simpl in Ha.
  unfold empty_tuple in Ha.
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _)) in Ha.
  rewrite Fset.empty_spec in Ha; discriminate Ha.
- intros [t [Abs _]]; contradiction Abs.
- rewrite N_join_tuple_unfold.
  unfold join_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _)), Fset.mem_union, Bool.orb_true_iff.
  intros [Ha | Ha].
  + exists t1; split; [left | ]; trivial.
  + rewrite IHl in Ha.
    destruct Ha as [t [Ht Ha]].
    exists t; split; [right | ]; trivial.
- intros [t [Ht Ha]]; 
  rewrite N_join_tuple_unfold; unfold join_tuple; 
  rewrite (Fset.mem_eq_2 _ _ _ (support_mk_tuple _ _)), Fset.mem_union.
  simpl in Ht; destruct Ht as [Ht | Ht].
  + subst t1; rewrite Ha; apply refl_equal. 
  + rewrite Bool.orb_true_iff; right.
    rewrite IHl; exists t; split; trivial.
Qed.

Lemma N_join_compatible_tuple_eq :
  forall l,
    (forall t1 t2, List.In t1 l -> List.In t2 l -> join_compatible_tuple t1 t2 = true) ->
    forall t a, List.In t l -> a inS (support T t) -> dot (N_join_tuple l) a = dot t a.
Proof.
intro l; induction l as [ | t1 l]; intros Hl t a Ht Ha.  
- contradiction Ht.
- simpl N_join_tuple;
  simpl in Ht; destruct Ht as [Ht | Ht].
  + subst t1; unfold join_tuple; 
    rewrite dot_mk_tuple, Ha; [ | rewrite Fset.mem_union, Ha]; trivial.
  + unfold join_tuple.
    assert (Ka : a inS support T (N_join_tuple l)).
    {
      rewrite mem_support_N_join_tuple; exists t; split; trivial.
    }
    rewrite dot_mk_tuple; [ | rewrite Fset.mem_union, Ka, Bool.orb_true_r; trivial].
    case_eq (a inS? support T t1); intro Ha1.
    * assert (H := Hl t1 t (or_introl _ (refl_equal _)) (or_intror _ Ht)).
      rewrite join_compatible_tuple_alt in H.
      generalize (H a Ha1 Ha); unfold dot; rewrite Ha1, Ha; trivial.
    * apply (IHl (fun t1 t2 h1 h2 => Hl t1 t2 (or_intror _ h1) (or_intror h2)) t a Ht Ha).
Qed.



(** theta-join *)

Definition theta_join_list (f : tuple T -> tuple T -> bool) (s1 s2 : list (tuple T)) :=
  List.flat_map (fun t1 => d_join_list t1 f s2) s1.

Definition theta_join_set f (s1 s2 : setT) : setT :=
  Feset.mk_set FTupleT (theta_join_list f (Feset.elements _ s1) (Feset.elements _ s2)).

Definition theta_join_bag f s1 s2 :=
  Febag.mk_bag BTupleT (theta_join_list f (Febag.elements BTupleT s1) (Febag.elements BTupleT s2)).

Lemma theta_join_list_unfold :
  forall f s1 s2, 
    theta_join_list f s1 s2 =
    List.flat_map (fun t1 => map (join_tuple t1) (filter (f t1) s2)) s1.
Proof.
intros f s1 s2; apply refl_equal.
Qed.

Lemma theta_join_set_unfold :
  forall f s1 s2, 
    theta_join_set f s1 s2 =
    Feset.mk_set FTupleT (theta_join_list f (Feset.elements _ s1) (Feset.elements _ s2)).
Proof.
intros f s1 s2; apply refl_equal.
Qed.

Lemma theta_join_bag_unfold :
  forall f s1 s2, 
    theta_join_bag f s1 s2 = 
    Febag.mk_bag 
      BTupleT (theta_join_list f (Febag.elements BTupleT s1) (Febag.elements BTupleT s2)).
Proof.
intros f s1 s2; apply refl_equal.
Qed.

Lemma theta_join_list_eq_1 :
  forall f1 f2 s1 s2, 
    (forall x1 x2, In x1 s1 -> In x2 s2 -> f1 x1 x2 = f2 x1 x2) ->
    theta_join_list f1 s1 s2 = theta_join_list f2 s1 s2.
Proof.
intros f1 f2 s1 s2 H; rewrite 2 theta_join_list_unfold.
revert f1 f2 s2 H; induction s1 as [ | x1 s1]; intros f1 f2 s2 H; simpl.
- apply refl_equal.
- apply f_equal2.
  + assert (H' := fun y =>  H x1 y (or_introl _ (refl_equal _))).
    clear H; induction s2 as [ | x2 s2]; [apply refl_equal | ].
    simpl.
    rewrite (H' _ (or_introl _ (refl_equal _))).
    case (f2 x1 x2); [rewrite 2 (map_unfold _ (_ :: _)); apply f_equal | ]; 
    apply IHs2; intros; apply H'; right; assumption.
  + apply IHs1; intros; apply H; [right | ]; assumption.
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
rewrite (_permut_app1 (equivalence_eq _) (d_join_list t f l2)) in IH.
refine (_permut_trans _ IH _); [intros; subst; apply refl_equal | ].
rewrite 2 ass_app; apply _permut_app2; [apply equivalence_eq | ].
apply _permut_swapp; apply _permut_refl; intros; trivial.
Qed.

Lemma nb_occ_theta_join_list :
  forall f l1 l2 t, 
    Oeset.nb_occ (OTuple T) t (theta_join_list f l1 l2) =
    N.of_nat 
      (list_size 
         (fun t1 => 
            (match Oeset.compare (OTuple T) t1 (mk_tuple (support T t1) (dot t)) with
               | Eq => 1 | _ => 0 end) * 
            list_size (fun t2 => 
                         if f t1 t2 
                         then match Oeset.compare (OTuple T) (join_tuple t1 t2) t with
                                | Eq => 1 | _ => 0 end
                         else 0) l2)
         l1)%nat.
Proof.
intros f l1; induction l1 as [ | t1 l1]; intros l2 t; simpl; [apply refl_equal | ].
rewrite Oeset.nb_occ_app, IHl1, Nat2N.inj_add.
- apply f_equal2; [ | apply refl_equal].
  clear l1 IHl1.
  induction l2 as [ | t2 l2]; simpl.
  + rewrite Mult.mult_0_r; apply refl_equal.
  + rewrite d_join_list_unfold; case_eq (f t1 t2); intro Hf; [ | simpl; apply IHl2].
    rewrite Oeset.nb_occ_app, IHl2, 2 Nat2N.inj_mul, Nat2N.inj_add, 2 Oeset.nb_occ_unfold.
    rewrite (Oeset.compare_lt_gt _ _ (join_tuple _ _)), N.mul_add_distr_l.
    apply f_equal2; [ | apply refl_equal].
    case_eq  (Oeset.compare (OTuple T) (join_tuple t1 t2) t); intro Ht; simpl;
    [ | rewrite N.mul_0_r; trivial | rewrite N.mul_0_r; trivial].
    rewrite N.mul_1_r.
    assert (Ht' : t1 =t= (mk_tuple (support T t1) (dot t))).
    {
      apply Oeset.compare_eq_sym.
      refine (Oeset.compare_eq_trans 
                _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t1 t2 (Fset.equal_refl _ _))).
      apply mk_tuple_eq_2; intros; rewrite (tuple_eq_dot _ _ Ht).
      apply refl_equal.
    }
    rewrite Ht'; apply refl_equal.
Qed.

Lemma in_theta_join_list :  
  forall f s1 s2 t,
    In t (theta_join_list f s1 s2) <->
    (exists t1 t2 : tuple T, In t1 s1 /\ In t2 s2 /\ f t1 t2 = true /\ t = join_tuple t1 t2).
Proof.
intros f s1 s2 t.
rewrite theta_join_list_unfold, in_flat_map; split.
- intros [t1 [Ht1 Ht]].
  rewrite in_map_iff in Ht; destruct Ht as [t2 [Ht Ht2]].
  rewrite filter_In in Ht2.
  destruct Ht2 as [Ht2 Hf].
  exists t1; exists t2; repeat split; trivial.
  apply sym_eq; assumption.
- intros [t1 [t2 [Ht1 [Ht2 [Hf Ht]]]]].
  exists t1; split; [assumption | ].
  rewrite in_map_iff; exists t2; split; [apply sym_eq; assumption | ].
  rewrite filter_In; split; assumption.
Qed.

Lemma mem_theta_join_set :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
  forall (s1 s2 : setT) t,
    (t inSE (theta_join_set f s1 s2)) <-> 
    (exists t1, exists t2, t1 inSE s1 /\ t2 inSE s2 /\ f t1 t2 = true /\ t =t= join_tuple t1 t2).
Proof.
intros f Hf s1 s2 t.
rewrite theta_join_set_unfold, Feset.mem_mk_set, Oeset.mem_bool_true_iff; split.
- intros [t' [Ht Ht']].
  rewrite in_theta_join_list in Ht'.
  destruct Ht' as [t1 [t2 [Ht1 [Ht2 [H Ht']]]]]; subst t'; 
  exists t1; exists t2; repeat split; trivial.
  + apply (Feset.in_elements_mem _ _ _ Ht1).
  + apply (Feset.in_elements_mem _ _ _ Ht2).
- intros [t1 [t2 [Ht1 [Ht2 [H Ht]]]]].
  rewrite Feset.mem_elements, Oeset.mem_bool_true_iff in Ht1, Ht2.
  destruct Ht1 as [t1' [Ht1 Ht1']].
  destruct Ht2 as [t2' [Ht2 Ht2']].
  exists (join_tuple t1' t2'); repeat split; trivial.
  + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
    apply join_tuple_eq; assumption.
  + rewrite in_theta_join_list.
    exists t1'; exists t2'; repeat split; trivial.
    rewrite <- H; apply sym_eq; apply Hf; trivial.
Qed.

Lemma mem_theta_join_bag :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
  forall (s1 s2 : bagT) t,
    (t inBE (theta_join_bag f s1 s2)) <-> 
    (exists t1, exists t2, t1 inBE s1 /\ t2 inBE s2 /\ f t1 t2 = true /\ t =t= join_tuple t1 t2).
Proof.
intros f Hf s1 s2 t.
rewrite theta_join_bag_unfold, Febag.mem_mk_bag, Oeset.mem_bool_true_iff; split.
- intros [t' [Ht Ht']].
  rewrite in_theta_join_list in Ht'.
  destruct Ht' as [t1 [t2 [Ht1 [Ht2 [H Ht']]]]]; subst t'; 
  exists t1; exists t2; repeat split; trivial.
  + apply (Febag.in_elements_mem _ _ _ Ht1).
  + apply (Febag.in_elements_mem _ _ _ Ht2).
- intros [t1 [t2 [Ht1 [Ht2 [H Ht]]]]].
  rewrite Febag.mem_nb_occ, Febag.nb_occ_elements in Ht1, Ht2.
  case_eq (Ncompare (Oeset.nb_occ (OTuple T) t1 (Febag.elements BTupleT s1)) 0);
    intro Nt1; rewrite Nt1 in Ht1; try discriminate Ht1.
  assert (Kt1 : Oeset.mem_bool (OTuple T) t1 (Febag.elements _ s1) = true).
  {
    apply Oeset.nb_occ_mem.
    destruct (Oeset.nb_occ (OTuple T) t1 (Febag.elements BTupleT s1)).
    - discriminate Nt1.
    - discriminate.
  }
  rewrite Oeset.mem_bool_true_iff in Kt1; destruct Kt1 as [t1' [Ht1' Kt1]].
  case_eq (Ncompare (Oeset.nb_occ (OTuple T) t2 (Febag.elements BTupleT s2)) 0);
    intro Nt2; rewrite Nt2 in Ht2; try discriminate Ht2.
  assert (Kt2 : Oeset.mem_bool (OTuple T) t2 (Febag.elements _ s2) = true).
  {
    apply Oeset.nb_occ_mem.
    destruct (Oeset.nb_occ (OTuple T) t2 (Febag.elements BTupleT s2)).
    - discriminate Nt2.
    - discriminate.
  }
  rewrite Oeset.mem_bool_true_iff in Kt2; destruct Kt2 as [t2' [Ht2' Kt2]].
  exists (join_tuple t1' t2'); split.
  + refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
    apply join_tuple_eq; assumption.
  + rewrite in_theta_join_list.
    exists t1'; exists t2'; repeat split; trivial.
    rewrite <- H; apply sym_eq; apply Hf; trivial.
Qed.

Lemma theta_join_list_permut_eq_2 :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
    forall l1 l2 l2', l2 =PE= l2' -> theta_join_list f l1 l2 =PE= theta_join_list f l1 l2'.
Proof.
intros f Hf l1; induction l1 as [ | t1 l1]; intros l2 l2' H; simpl.
- apply permut_refl.
- apply _permut_app; [ | apply IHl1; assumption].
  clear IHl1; revert l2' H; induction l2 as [ | t2 l2]; intros l2' H.
  + inversion H; subst; apply permut_refl.
  + inversion H; clear H; subst.
    rewrite d_join_list_app, 2 (d_join_list_unfold _ _ (_ :: _)).
    rewrite <- (Hf _ _ _ _ (Oeset.compare_eq_refl _ _) H2).
    case (f t1 t2); simpl.
    * apply Pcons; [ | rewrite <- d_join_list_app; apply IHl2; assumption].
      apply join_tuple_eq; [apply Oeset.compare_eq_refl | assumption].
    * rewrite <- d_join_list_app; apply IHl2; assumption.
Qed.

Lemma theta_join_list_permut_eq_1 :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
    forall l1 l1' l2, l1 =PE= l1' -> theta_join_list f l1 l2 =PE= theta_join_list f l1' l2.
Proof.
intros f Hf l1 l1' l2 H1; rewrite 2 theta_join_list_unfold.
revert l1' l2 H1; induction l1 as [ | t1 l1]; intros l1' l2 H1.
- inversion H1; subst; apply permut_refl.
- inversion H1; subst.
  rewrite flat_map_app; simpl.
  assert (IH := IHl1 _ l2 H4).
  rewrite (permut_app1 _ (map (join_tuple t1) (filter (f t1) l2))) in IH.
  apply (permut_trans _ IH).
  rewrite flat_map_app, 2 ass_app.
  rewrite <- permut_app2.
  apply _permut_swapp; [ | apply permut_refl].
  clear l1 l0 l3 H4 IHl1 H1 IH.
  induction l2 as [ | t2 l2]; [apply permut_refl | simpl].
  rewrite (Hf _ _ _ _ H2 (Oeset.compare_eq_refl _ _)).
  case (f b t2); [ | apply IHl2].
  simpl; apply permut_cons; [ | apply IHl2].
  apply join_tuple_eq; [trivial | apply Oeset.compare_eq_refl].
Qed.

Lemma theta_join_list_permut_eq :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
    forall l1 l1' l2 l2', 
      l1 =PE= l1' -> l2 =PE= l2' ->
      theta_join_list f l1 l2 =PE= theta_join_list f l1' l2'.
Proof.
intros f Hf l1 l1' l2 l2' H1 H2.
apply (permut_trans _ (theta_join_list_permut_eq_1 _ Hf _ H1)).
apply theta_join_list_permut_eq_2; trivial.
Qed.

Lemma theta_join_list_mem_bool_eq_2 :
  forall f, (forall t1 t2 t1' t2', t1 =t= t1' -> t2 =t= t2' -> f t1 t2 = f t1' t2') -> 
    forall l1 l2 l2', 
      (forall t, Oeset.mem_bool (OTuple T) t l2 = Oeset.mem_bool (OTuple T) t l2') -> 
      forall t, Oeset.mem_bool (OTuple T) t (theta_join_list f l1 l2) =
                Oeset.mem_bool (OTuple T) t (theta_join_list f l1 l2').
Proof.
intros f Hf l1; induction l1 as [ | t1 l1]; intros l2 l2' H t; simpl; [trivial | ].
rewrite 2 Oeset.mem_bool_app; apply f_equal2; [ | apply IHl1; assumption].
assert (Aux : forall l2 l2' : list (tuple T),
                (forall t : tuple T,
                   Oeset.mem_bool (OTuple T) t l2 = Oeset.mem_bool (OTuple T) t l2') ->
                forall t : tuple T,
                  (exists a' : tuple T, t =t= a' /\ In a' (d_join_list t1 f l2)) ->
                  exists a' : tuple T, t =t= a' /\ In a' (d_join_list t1 f l2')).
{
  clear l2 l2' H t; intros l2 l2' H t [t' [Ht Ht']].
  unfold d_join_list in Ht'.
  rewrite in_map_iff in Ht'.
  destruct Ht' as [t2 [Ht' Ht2]].
  rewrite filter_In in Ht2.
  destruct Ht2 as [Ht2 Kt2].
  assert (Jt2 : Oeset.mem_bool (OTuple T) t2 l2' = true).
  {
    rewrite <- H, Oeset.mem_bool_true_iff.
    exists t2; split; [ | assumption].
    apply Oeset.compare_eq_refl.
  }
  rewrite Oeset.mem_bool_true_iff in Jt2.
  destruct Jt2 as [t2' [Jt2 Jt2']].
  exists (join_tuple t1 t2'); split.
  - refine (Oeset.compare_eq_trans _ _ _ _ Ht _); rewrite <- Ht'.
    apply join_tuple_eq; [ | assumption].
    apply Oeset.compare_eq_refl.
  - unfold d_join_list; rewrite in_map_iff.
    exists t2'; split; [trivial | ].
    rewrite filter_In; split; trivial.
    rewrite <- Kt2; apply sym_eq; apply Hf; [ | trivial].
    apply Oeset.compare_eq_refl.
}
rewrite eq_bool_iff, 2 Oeset.mem_bool_true_iff; split; apply Aux; trivial.
intro u; rewrite H; apply refl_equal.
Qed.

(** brute_left_join *)

Definition brute_left_join_list s1 s2 := theta_join_list (fun _ _ => true) s1 s2.

Definition brute_left_join_set s1 s2 := theta_join_set (fun _ _ => true) s1 s2.

Definition brute_left_join_bag s1 s2 := theta_join_bag (fun _ _ => true) s1 s2.

Fixpoint N_product_list ll :=
  match ll with
    | nil => (empty_tuple :: nil)
    | s1 :: ll => brute_left_join_list s1 (N_product_list ll)
  end.

Fixpoint N_product_set ll :=
  match ll with
    | nil => Feset.singleton FTupleT empty_tuple
    | s1 :: ll => brute_left_join_set s1 (N_product_set ll)
  end.

Fixpoint N_product_bag ll :=
  match ll with
    | nil => Febag.singleton BTupleT empty_tuple 
    | s1 :: ll => brute_left_join_bag s1 (N_product_bag ll)
  end.

Lemma brute_left_join_list_unfold :
  forall s1 s2, brute_left_join_list s1 s2 = theta_join_list (fun _ _ => true) s1 s2.
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma brute_left_join_set_unfold :
  forall s1 s2, 
    brute_left_join_set s1 s2 = 
    Feset.mk_set 
      _ (theta_join_list (fun _ _ => true) (Feset.elements _ s1) (Feset.elements _ s2)).
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma brute_left_join_bag_unfold :
  forall s1 s2, 
    brute_left_join_bag s1 s2 = 
    Febag.mk_bag 
      _ (theta_join_list (fun _ _ => true) (Febag.elements _ s1) (Febag.elements _ s2)).
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma N_product_list_unfold :
  forall ll, N_product_list ll =
  match ll with
    | nil => (empty_tuple :: nil)
    | s1 :: ll => brute_left_join_list s1 (N_product_list ll)
  end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma N_product_set_unfold :
  forall ll, N_product_set ll =
  match ll with
    | nil => Feset.singleton FTupleT empty_tuple
    | s1 :: ll => brute_left_join_set s1 (N_product_set ll)
  end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma N_product_bag_unfold :
  forall ll, N_product_bag ll =
  match ll with
    | nil => Febag.singleton BTupleT empty_tuple 
    | s1 :: ll => brute_left_join_bag s1 (N_product_bag ll)
  end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma in_brute_left_join_list : 
  forall t s1 s2,
    In t (brute_left_join_list s1 s2) <->
    (exists t1 t2 : tuple T, In t1 s1 /\ In t2 s2 /\ t = join_tuple t1 t2).
Proof.
intros t s1 s2; rewrite brute_left_join_list_unfold, in_theta_join_list.
split; intros [t1 [t2 [Ht1 [Ht2 H]]]]; exists t1; exists t2; repeat split; trivial.
apply (proj2 H).
Qed.

Lemma N_product_list_1 :
  forall s, comparelA (fun x y => Oeset.compare (Tuple.OTuple T) x y)
                      (N_product_list (s :: nil)) s = Eq.
Proof.
intro s; simpl.
unfold brute_left_join_list.
rewrite theta_join_list_unfold.
rewrite filter_true; [ | intros; apply refl_equal]; simpl.
induction s as [ | t1 s]; [apply refl_equal | simpl].
rewrite join_tuple_empty_2; apply IHs.
Qed.

Lemma N_product_list_map_eq :
  forall (A : Type) (l : list A) f1 f2,
  (forall x, In x l -> comparelA (Oeset.compare (OTuple T)) (f1 x) (f2 x) = Eq) ->
  comparelA (Oeset.compare (OTuple T)) 
            (N_product_list (map f1 l)) (N_product_list (map f2 l)) = Eq.
Proof.
intros A l; induction l as [ | a1 l]; intros f1 f2 Hf; simpl.
- rewrite Oeset.compare_eq_refl; trivial.
- unfold brute_left_join_list, theta_join_list.
  assert (H1 := Hf _ (or_introl _ (refl_equal _))).
  set (b1 := f1 a1) in *; clearbody b1.
  set (b2 := f2 a1) in *; clearbody b2.
  assert (IH := IHl f1 f2 (fun x h => Hf x (or_intror _ h))).
  set (l1 := N_product_list (map f1 l)) in *; clearbody l1.
  set (l2 := N_product_list (map f2 l)) in *; clearbody l2.
  revert b2 H1 l1 l2 IH; 
    induction b1 as [ | t1 b1]; 
    intros [ | t2 b2] H1 l1 l2 IH; simpl; trivial; try discriminate H1.
  simpl in H1.
  case_eq (Oeset.compare (OTuple T) t1 t2); intro Ht;
  rewrite Ht in H1; try discriminate H1.
  apply comparelA_eq_app; [ | apply IHb1; trivial].
  clear b1 b2 IHb1 H1.
  revert t1 t2 Ht l2 IH; induction l1 as [ | u1 l1]; 
  intros t1 t2 Ht [ | u2 l2] IH; simpl; trivial; try discriminate IH.
  simpl in IH.
  case_eq (Oeset.compare (OTuple T) u1 u2); intro Hu; rewrite Hu in IH;
  try discriminate IH.
  rewrite (join_tuple_eq _ _ _ _ Ht Hu).
  unfold d_join_list in IHl1; rewrite IHl1; trivial.
Qed.

Lemma N_product_bag_1 :
  forall s, N_product_bag (s :: nil) =BE= s.
Proof.
intro s; simpl; rewrite Febag.nb_occ_equal; intro t.
assert (H := N_product_list_1 (Febag.elements BTupleT s)); simpl in H.
unfold brute_left_join_list, theta_join_list in H.
unfold brute_left_join_bag, theta_join_bag, theta_join_list.
rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements.
apply permut_nb_occ; apply permut_refl_alt; simpl.
destruct (Febag.elements_singleton BTupleT empty_tuple) as [e [He Ke]].
rewrite Ke.
refine (comparelA_eq_trans _ _ _ _ _ _ H).
- do 6 intro; apply Oeset.compare_eq_trans.
- set (l := (Febag.elements BTupleT s)); clearbody l.
  induction l as [ | t1 l]; [apply refl_equal | ].
  simpl.
  rewrite (join_tuple_eq _ _ _ _ (Oeset.compare_eq_refl _ t1) (Oeset.compare_eq_sym _ _ _ He)).
  apply IHl.
Qed.


Lemma in_N_product_list :
  forall t ll, In t (N_product_list ll) <->
               (exists llt, (forall si ti, List.In (si, ti) llt -> In ti si) /\
                            List.map (@fst _ _) llt = ll /\ 
                            t = N_join_tuple (List.map (@snd _ _) llt)).
Proof.
intros t ll; revert t.
induction ll as [ | s1 ll]; intro t; rewrite N_product_list_unfold; split.
- intro H; simpl in H; destruct H as [H | H]; [ | contradiction H].
  subst t; exists nil; repeat split; intros; contradiction.
- intros [llt [H1 [H2 H3]]].
  destruct llt; [ | discriminate H2].
  simpl in H3; left; apply sym_eq; apply H3.
- rewrite in_brute_left_join_list.
  intros [t1 [t2 [Ht1 [Ht2 Ht]]]].
  rewrite IHll in Ht2.
  destruct Ht2 as [llt [H1 [H2 H3]]].
  exists ((s1, t1) :: llt); repeat split.
  + intros si ti Hi; simpl in Hi; destruct Hi as [Hi | Hi]; [ | apply H1; assumption].
    injection Hi; clear Hi; do 2 intro; subst; assumption.
  + simpl; apply f_equal; assumption.
  + rewrite Ht, H3; apply refl_equal.
- intros [llt [H1 [H2 H3]]].
  destruct llt as [ | [_s1 t1] llt]; [discriminate H2 | ].
  simpl in H2; injection H2; clear H2; intro H2; intro; subst _s1.
  rewrite in_brute_left_join_list.
  exists t1; exists (N_join_tuple (map (snd (B:=tuple T)) llt)); repeat split.
  + apply H1; left; apply refl_equal.
  + rewrite IHll; exists llt; repeat split; trivial.
    do 3 intro; apply H1; right; assumption.
  + rewrite H3; apply refl_equal.
Qed.

Lemma N_product_set_N_product_list :
  forall ls, N_product_set ls =SE= Feset.mk_set _ (N_product_list (map (Feset.elements _) ls)).
Proof.
intro ls; induction ls as [ | s1 ls]; simpl.
- rewrite Feset.equal_spec; intro t.
  rewrite Feset.singleton_spec, Feset.add_spec, Feset.empty_spec, Bool.orb_false_r.
  apply refl_equal.
- rewrite brute_left_join_set_unfold; apply Feset.mk_set_eq.
  intro t; unfold brute_left_join_list.
  apply theta_join_list_mem_bool_eq_2; clear t; [intros; trivial | ].
  intro t; rewrite <- Feset.mem_elements, (Feset.mem_eq_2 _ _ _ IHls), Feset.mem_mk_set.
  apply refl_equal.
Qed.

Lemma N_product_bag_N_product_list :
  forall ls, N_product_bag ls =BE= Febag.mk_bag _ (N_product_list (map (Febag.elements _) ls)).
Proof.
intro ls; rewrite Febag.nb_occ_equal; intro t; rewrite Febag.nb_occ_mk_bag; revert t.
induction ls as [ | s1 ls]; simpl.
- intro t; rewrite Febag.singleton_spec; unfold Oeset.eq_bool; simpl.
  case (Oeset.compare (OTuple T) t empty_tuple); apply refl_equal.
- intro t; rewrite brute_left_join_bag_unfold, Febag.nb_occ_mk_bag.
  unfold brute_left_join_list.
  apply permut_nb_occ; clear t.
  apply theta_join_list_permut_eq_2; [intros; trivial | ].
  apply nb_occ_permut; intro t; rewrite <- IHls, Febag.nb_occ_elements.
  apply refl_equal.
Qed.

Lemma N_product_bag_map_eq :
  forall (A : Type) (l : list A) f1 f2,
  (forall x, In x l ->  (f1 x) =BE= (f2 x)) ->
  (N_product_bag (map f1 l)) =BE= (N_product_bag (map f2 l)).
Proof.
intros A l f1 f2 Hl.
rewrite (Febag.equal_eq_1 _ _ _ _ (N_product_bag_N_product_list _)).
rewrite (Febag.equal_eq_2 _ _ _ _ (N_product_bag_N_product_list _)).
rewrite Febag.nb_occ_equal; intro t.
rewrite 2 Febag.nb_occ_mk_bag.
apply permut_nb_occ.
apply permut_refl_alt; rewrite 2 map_map.
apply N_product_list_map_eq.
intros a Ha; apply Febag.elements_spec1.
apply Hl; assumption.
Qed.

Lemma mem_N_product_bag :
  forall t ls, t inBE (N_product_bag ls) <-> 
               Oeset.mem_bool (OTuple T) t (N_product_list (map (Febag.elements _) ls)) = true.
Proof.
intros t ls.
rewrite (Febag.mem_eq_2 _ _ _ (N_product_bag_N_product_list _)).
rewrite Febag.mem_mk_bag; split; exact (fun h => h).
Qed.

(** natural_join *)

Definition natural_join_list s1 s2 := theta_join_list join_compatible_tuple s1 s2.

Definition natural_join_set s1 s2 := theta_join_set join_compatible_tuple s1 s2.

Definition natural_join_bag s1 s2 := theta_join_bag join_compatible_tuple s1 s2.

Fixpoint N_natural_join_list ll :=
  match ll with
    | nil => (empty_tuple :: nil) 
    | s1 :: ll => natural_join_list s1 (N_natural_join_list ll)
  end.

Fixpoint N_natural_join_set ll :=
  match ll with
    | nil => Feset.singleton FTupleT empty_tuple 
    | s1 :: ll => natural_join_set s1 (N_natural_join_set ll)
  end.

Fixpoint N_natural_join_bag ll :=
  match ll with
    | nil => Febag.singleton BTupleT empty_tuple 
    | s1 :: ll => natural_join_bag s1 (N_natural_join_bag ll)
  end.

Lemma natural_join_list_unfold :
  forall s1 s2, natural_join_list s1 s2 = theta_join_list join_compatible_tuple s1 s2.
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma natural_join_set_unfold :
  forall s1 s2, 
    natural_join_set s1 s2 =
    Feset.mk_set 
      _ (theta_join_list join_compatible_tuple (Feset.elements _ s1) (Feset.elements _ s2)).
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma natural_join_bag_unfold :
  forall s1 s2, 
    natural_join_bag s1 s2 = 
    Febag.mk_bag
      _ (theta_join_list join_compatible_tuple (Febag.elements _ s1) (Febag.elements _ s2)).
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma N_natural_join_list_unfold :
  forall ll, N_natural_join_list ll = 
  match ll with
    | nil => (empty_tuple :: nil) 
    | s1 :: ll => natural_join_list s1 (N_natural_join_list ll)
  end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma N_natural_join_set_unfold :
  forall ll, N_natural_join_set ll =
             match ll with
               | nil => Feset.singleton FTupleT empty_tuple 
               | s1 :: ll => natural_join_set s1 (N_natural_join_set ll)
             end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma N_natural_join_bag_unfold :
  forall ll, N_natural_join_bag ll =
             match ll with
               | nil => Febag.singleton BTupleT empty_tuple 
               | s1 :: ll => natural_join_bag s1 (N_natural_join_bag ll)
             end.
Proof.
intro ll; case ll; intros; apply refl_equal.
Qed.

Lemma in_natural_join_list : 
  forall t s1 s2,
    In t (natural_join_list s1 s2) <->
    (exists t1 t2 : tuple T,
     In t1 s1 /\ In t2 s2 /\ join_compatible_tuple t1 t2 = true /\ t = join_tuple t1 t2).
Proof.
intros t s1 s2; unfold natural_join_list; apply in_theta_join_list.
Qed.

Lemma mem_natural_join_set :
  forall t s1 s2,
    t inSE (natural_join_set s1 s2) <->
    (exists t1 t2 : tuple T,
       t1 inSE s1 /\ t2 inSE s2 /\ join_compatible_tuple t1 t2 = true /\ t =t= join_tuple t1 t2).
Proof.
intros t s1 s2; rewrite <- mem_theta_join_set.
- rewrite natural_join_set_unfold, theta_join_set_unfold; split; exact (fun h => h).
- intros; apply join_compatible_tuple_eq; assumption.
Qed.

Lemma mem_natural_join_bag :
  forall t s1 s2,
    t inBE (natural_join_bag s1 s2) <->
    (exists t1 t2 : tuple T,
       t1 inBE s1 /\ t2 inBE s2 /\ join_compatible_tuple t1 t2 = true /\ t =t= join_tuple t1 t2).
Proof.
intros t s1 s2; rewrite <- mem_theta_join_bag.
- rewrite natural_join_bag_unfold, theta_join_bag_unfold; split; exact (fun h => h).
- intros; apply join_compatible_tuple_eq; assumption.
Qed.

Lemma in_N_natural_join_list :
  forall t ll, 
    In t (N_natural_join_list ll) <->
    (exists llt, 
       (forall si ti, List.In (si, ti) llt -> In ti si) /\
       (forall s1 t1 s2 t2, 
          List.In (s1, t1) llt -> List.In (s2, t2) llt -> join_compatible_tuple t1 t2 = true) /\
       List.map (@fst _ _) llt = ll /\ t = N_join_tuple (List.map (@snd _ _) llt)).
Proof.
intros t ll; revert t.
induction ll as [ | s1 ll]; intro t; rewrite N_natural_join_list_unfold; split.
- intro H; simpl in H; destruct H as [H | H]; [ | contradiction H].
  subst t; exists nil; repeat split; intros; contradiction.
- intros [llt [H1 [H2 [H3 H4]]]].
  destruct llt; [ | discriminate H3].
  simpl in H4; left; apply sym_eq; apply H4.
- rewrite in_natural_join_list.
  + intros [t1 [t2 [Ht1 [Ht2 [Ht Kt]]]]].
    rewrite IHll in Ht2.
    destruct Ht2 as [llt [H1 [H2 [H3 H4]]]].
    exists ((s1, t1) :: llt); repeat split.
    * intros si ti Hi; simpl in Hi; destruct Hi as [Hi | Hi]; [ | apply H1; assumption].
      injection Hi; clear Hi; do 2 intro; subst; assumption.
    * assert (Aux : forall si ti, In (si, ti) llt -> join_compatible_tuple t1 ti = true).
      {
        intros si ti Hi.
        rewrite join_compatible_tuple_alt; intros a Ha Ka.
        apply trans_eq with (dot t2 a); subst t2.
        - rewrite join_compatible_tuple_alt in Ht; apply Ht; trivial.
          rewrite mem_support_N_join_tuple.
          exists ti; split; [ | assumption].
          rewrite in_map_iff; exists (si, ti); split; trivial.
        - apply N_join_compatible_tuple_eq; trivial.
          + intros t2 t3 Ht2 Ht3; rewrite in_map_iff in Ht2, Ht3.
            destruct Ht2 as [[s2 _t2] [Ht2 Kt2]]; simpl in Ht2; subst _t2.
            destruct Ht3 as [[s3 _t3] [Ht3 Kt3]]; simpl in Ht3; subst _t3.
            apply (H2 _ _ _ _ Kt2 Kt3).
          + rewrite in_map_iff; exists (si, ti); split; trivial.
      }
      intros si ti sj tj Hi Hj; simpl in Hi, Hj.
      {
        destruct Hi as [Hi | Hi]; destruct Hj as [Hj | Hj].
        - injection Hi; injection Hj; clear Hi Hj; intros; subst si sj ti tj.
          rewrite join_compatible_tuple_alt; intros; trivial.
        - injection Hi; clear Hi; intros; subst si ti.
          apply (Aux sj); trivial.
        - injection Hj; clear Hj; intros; subst sj tj.
          rewrite join_compatible_tuple_comm; apply (Aux si); trivial.
        - apply (H2 si ti sj tj); trivial.
      } 
    * rewrite map_unfold; apply f_equal; assumption.
    * rewrite map_unfold, N_join_tuple_unfold, Kt, H4.
      apply refl_equal.
- intros [llt [H1 [H2 [H3 H4]]]].
  destruct llt as [ | [_s1 t1] llt]; [discriminate H3 | ].
  simpl in H3; injection H3; clear H3; intro H3; intro; subst _s1.
  rewrite in_natural_join_list.
  exists t1; exists (N_join_tuple (map (snd (B:=tuple T)) llt)); repeat split.
  + apply H1; left; apply refl_equal.
  + rewrite IHll; exists llt; repeat split; trivial.
    * do 3 intro; apply H1; right; assumption.
    * intros si ti sj tj Hi Hj; apply (H2 si ti sj tj); right; assumption.
  + rewrite join_compatible_tuple_alt; intros a Ha Ka.
    rewrite mem_support_N_join_tuple in Ka.
    destruct Ka as [t2 [Ht2 Ka]].
    rewrite in_map_iff in Ht2.
    destruct Ht2 as [[s2 _t2] [Ht2 Kt2]]; simpl in Ht2; subst _t2.
    apply trans_eq with (dot t2 a).
    * assert (Ht := H2 _ _ _ _ (or_introl _ (refl_equal _)) (or_intror _ Kt2)).
      rewrite join_compatible_tuple_alt in Ht; apply Ht; trivial.
    * {
        apply sym_eq; apply N_join_compatible_tuple_eq; trivial.
        - intros ti tj Hi Hj; rewrite in_map_iff in Hi, Hj.
          destruct Hi as [[si _ti] [Hi Ki]]; simpl in Hi; subst _ti.
          destruct Hj as [[sj _tj] [Hj Kj]]; simpl in Hj; subst _tj.
          apply (H2 _ _ _ _ (or_intror _ Ki) (or_intror _ Kj)).
        - rewrite in_map_iff; exists (s2, t2); split; trivial.
      } 
  + rewrite H4; apply refl_equal.
Qed.

Lemma N_natural_join_set_N_natural_join_list :
  forall ls, N_natural_join_set ls =SE= 
             Feset.mk_set _ (N_natural_join_list (map (Feset.elements _) ls)).
Proof.
intro ls; induction ls as [ | s1 ls]; simpl.
- rewrite Feset.equal_spec; intro t.
  rewrite Feset.singleton_spec, Feset.add_spec, Feset.empty_spec, Bool.orb_false_r.
  apply refl_equal.
- rewrite natural_join_set_unfold; unfold natural_join_list.
  apply Feset.mk_set_eq; intro t.
  apply theta_join_list_mem_bool_eq_2; clear t.
  + do 6 intro; apply join_compatible_tuple_eq; assumption.
  + intro t; rewrite <- Feset.mem_elements, (Feset.mem_eq_2 _ _ _ IHls), Feset.mem_mk_set.
    apply refl_equal.
Qed.

Lemma nb_occ_natural_join_list :
  forall l1 l2 s1 s2, 
    (forall t, In t l1 -> support T t =S= s1) ->
    (forall t, In t l2 -> support T t =S= s2) ->
    forall t, (Oeset.nb_occ (OTuple T) t (natural_join_list l1 l2) =
              (Oeset.nb_occ (OTuple T) (mk_tuple s1 (dot t)) l1) *
              (Oeset.nb_occ (OTuple T) (mk_tuple s2 (dot t)) l2) *
              (if support T t =S?= (s1 unionS s2) then 1 else 0))%N.
Proof.
  intros l1 l2 s1 s2 H1 H2 t.
  rewrite natural_join_list_unfold, nb_occ_theta_join_list.
  revert l2 H2; induction l1 as [ | u1 l1]; intros l2 H2; simpl; [apply refl_equal | ].
  rewrite Nat2N.inj_add, Nat2N.inj_mul, IHl1, 2 N.mul_add_distr_r; trivial.
  - apply f_equal2; [ | apply refl_equal].
    assert (Hu1 := H1 u1 (or_introl _ (refl_equal _))).
    clear l1 H1 IHl1.
    induction l2 as [ | u2 l2]; simpl; [rewrite 2 N.mul_0_r, N.mul_0_l; apply refl_equal | ].
    rewrite Nat2N.inj_add, N.mul_add_distr_l, IHl2; [ | intros; apply H2; right; trivial].
    rewrite N.mul_add_distr_l, N.mul_add_distr_r.
    rewrite (Oeset.compare_eq_2 _ _ _ _ (mk_tuple_eq_1 _ _ _ Hu1)), Oeset.compare_lt_gt.
    case_eq (support T t =S?= (s1 unionS s2)); 
      intro H; [ rewrite 2 N.mul_1_r | rewrite 2 N.mul_0_r];     
      (apply f_equal2; [ | apply refl_equal]).
    + case_eq (join_compatible_tuple u1 u2); intro Hu.
      * assert (Hu2 := H2 u2 (or_introl _ (refl_equal _))).
        {
          case_eq (Oeset.compare (OTuple T) t (join_tuple u1 u2)); intro Ht;
          rewrite (Oeset.compare_lt_gt _ (join_tuple _ _) _), Ht.
          - rewrite (split_tuple s1 s2 t u1 u2 Hu1 Hu2 Hu) in Ht.
            rewrite (Oeset.compare_eq_sym _ _ _ (proj1 Ht)).
            rewrite (Oeset.compare_eq_sym _ _ _ (proj1 (proj2 Ht))).
            apply refl_equal.
          - case_eq (Oeset.compare (OTuple T) (mk_tuple s1 (dot t)) u1); intro Ku1; trivial.
            case_eq (Oeset.compare (OTuple T) (mk_tuple s2 (dot t)) u2); intro Ku2; trivial.
            apply False_rec.
            assert (Abs : t =t= join_tuple u1 u2).
            {
              rewrite (split_tuple s1 s2 t u1 u2); repeat split; trivial.
              - apply Oeset.compare_eq_sym; assumption.
              - apply Oeset.compare_eq_sym; assumption.
            }
            rewrite Abs in Ht; discriminate Ht.
          - case_eq (Oeset.compare (OTuple T) (mk_tuple s1 (dot t)) u1); intro Ku1; trivial.
            case_eq (Oeset.compare (OTuple T) (mk_tuple s2 (dot t)) u2); intro Ku2; trivial.
            apply False_rec.
            assert (Abs : t =t= join_tuple u1 u2).
            {
              rewrite (split_tuple s1 s2 t u1 u2); repeat split; trivial.
              - apply Oeset.compare_eq_sym; assumption.
              - apply Oeset.compare_eq_sym; assumption.
            }
            rewrite Abs in Ht; discriminate Ht.
        } 
      * rewrite N.mul_0_r.
        case_eq (Oeset.compare (OTuple T) (mk_tuple s1 (dot t)) u1); intro Ku1; trivial.
        case_eq (Oeset.compare (OTuple T) (mk_tuple s2 (dot t)) u2); intro Ku2; trivial.
        apply False_rec.
        assert (Abs : join_compatible_tuple u1 u2 = true).
        {
          rewrite join_compatible_tuple_alt.
          intros a Ha1 Ha2.
          rewrite <- (tuple_eq_dot _ _ Ku1), <- (tuple_eq_dot _ _ Ku2), 2 dot_mk_tuple.
          - apply refl_equal.
          - rewrite <- (Fset.mem_eq_2 _ _ _ (H2 u2 (or_introl _ (refl_equal _)))); assumption.
          - rewrite <- (Fset.mem_eq_2 _ _ _ Hu1); assumption.
        }
        rewrite Abs in Hu; discriminate Hu.
    + case (join_compatible_tuple u1 u2); [ | rewrite N.mul_0_r; apply refl_equal].
      case_eq (Oeset.compare (OTuple T) (join_tuple u1 u2) t); intro Ht;
      try (rewrite N.mul_0_r; apply refl_equal).
      apply False_rec.
      assert (Abs : support T t =S= (s1 unionS s2)).
      {
        rewrite tuple_eq in Ht.
        rewrite <- (Fset.equal_eq_1 _ _ _ _ (proj1 Ht)).
        unfold join_tuple.
        rewrite (Fset.equal_eq_1 _ _ _ _ (support_mk_tuple _ _)).
        rewrite Fset.equal_spec; intro a; rewrite 2 Fset.mem_union; apply f_equal2.
        - apply (Fset.mem_eq_2 _ _ _ Hu1).
        - apply (Fset.mem_eq_2 _ _ _ (H2 u2 (or_introl _ (refl_equal _)))).
      }
      rewrite Abs in H; discriminate H.
  - intros; apply H1; right; assumption.
Qed.

Definition natural_join f (c1 c2 : Fecol.collection (CTuple T)) :=
  match f with
    | FlagSet => 
      Fecol.Fset 
        (Feset.mk_set FTupleT (natural_join_list (Fecol.elements c1) (Fecol.elements c2)))
    | Flagbag => 
      Fecol.Fbag
        (Febag.mk_bag BTupleT (natural_join_list (Fecol.elements c1) (Fecol.elements c2)))
  end.

Lemma mem_natural_join :
  forall f t s1 s2,
    t inCE (natural_join f s1 s2) <->
    (exists t1 t2 : tuple T,
     t1 inCE s1 /\ t2 inCE s2 /\ join_compatible_tuple t1 t2 = true /\ t =t= join_tuple t1 t2).
Proof.
intros f t s1 s2; destruct f; simpl.
- rewrite Feset.mem_mk_set, Oeset.mem_bool_true_iff; split.
  + intros [t' [Ht Ht']].
    rewrite in_natural_join_list in Ht'.
    destruct Ht' as [t1 [t2 [Ht1 [Ht2 [Hj Ht']]]]]; subst t'.
    exists t1; exists t2; repeat split; trivial.
    * apply Fecol.in_elements_mem; assumption.
    * apply Fecol.in_elements_mem; assumption.
  + intros [t1 [t2 [Ht1 [Ht2 [H' Ht']]]]].
    rewrite Fecol.mem_elements, Oeset.mem_bool_true_iff in Ht1, Ht2.
    destruct Ht1 as [u1 [Ht1 Hu1]].
    destruct Ht2 as [u2 [Ht2 Hu2]].
    exists (join_tuple u1 u2); split.
    * refine (Oeset.compare_eq_trans _ _ _ _ Ht' _).
      apply join_tuple_eq; assumption.
    * rewrite in_natural_join_list.
      exists u1; exists u2; repeat split; trivial.
      rewrite <- H'; apply sym_eq; apply join_compatible_tuple_eq; assumption.
- rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff; split.
  + intros [t' [Ht Ht']]; rewrite in_natural_join_list in Ht'.
    destruct Ht' as [t1 [t2 [Ht1 [Ht2 [H' Ht']]]]]; subst t'.
    exists t1; exists t2; repeat split; trivial.
    * apply Fecol.in_elements_mem; assumption.
    * apply Fecol.in_elements_mem; assumption.
  + intros [t1 [t2 [Ht1 [Ht2 [H' Ht']]]]].
    rewrite Fecol.mem_elements, Oeset.mem_bool_true_iff in Ht1, Ht2.
    destruct Ht1 as [u1 [Ht1 Hu1]].
    destruct Ht2 as [u2 [Ht2 Hu2]].
    exists (join_tuple u1 u2); split.
    * refine (Oeset.compare_eq_trans _ _ _ _ Ht' _).
      apply join_tuple_eq; assumption.
    * rewrite in_natural_join_list.
      exists u1; exists u2; repeat split; trivial.
      rewrite <- H'; apply sym_eq; apply join_compatible_tuple_eq; assumption.
Qed.
*)

Definition compare_tuple_as_pairs t1 t2 :=
  comparelA (compareAB (Oset.compare (OAtt T)) (Oset.compare (OVal T))) t1 t2.

Definition OPTuple : Oset.Rcd (list ((attribute T) * (value T))).
Proof.
split with compare_tuple_as_pairs; unfold compare_tuple_as_pairs.
- intros l1 l2; apply comparelA_eq_bool_ok.
  intros [a1 v1] [a2 v2] H1 H2; apply compareAB_eq_bool_ok.
  + apply Oset.eq_bool_ok.
  + apply Oset.eq_bool_ok.
- intros l1 l2 l3; try comparelA_tac; try compareAB_tac; try oset_compare_tac.
- intros l1 l2; try comparelA_tac; try compareAB_tac; try oset_compare_tac.
Defined.

Definition FPTuple := Fset.build OPTuple.

(** Test whether t1 and t2 (tuple as pairs) have compatible values on the common attributes. *)
(*
Definition pjoin_compatible_tuple  (t1 t2 : list ((attribute T) * (value T))) : bool :=
  forallb 
    (fun x1 => match x1 with
                 | (a1, v1) => match Oset.find (OAtt T) a1 t2 with
                                 | Some v2 => Oset.eq_bool (OVal T) v1 v2
                                 | None => true
                               end
               end)
    t1.

Definition pjoin_tuple (t1 t2 : (list ((attribute T) * (value T)))) :=
  tuple_as_pairs (join_tuple (pairs_as_tuple t1) (pairs_as_tuple t2)).

Definition psigma_join (f : _ -> _ -> bool) (s1 s2 : Fset.set FPTuple) :=
Fset.fold FPTuple
  (fun t1 acc1 =>
   Fset.fold FPTuple
     (fun t2 (acc2 : Fset.set FPTuple) =>
      if f t1 t2 then pjoin_tuple t1 t2 addS acc2 else acc2) s2 acc1) s1
  (emptysetS).

Definition pnatural_join s1 s2 :=
  psigma_join (fun t1 t2 => pjoin_compatible_tuple t1 t2) s1 s2.

Lemma mem_psigma_join : 
  forall t f s1 s2,
    (t inS (psigma_join f s1 s2) <->
    (exists t1 t2, t1 inS s1 /\ t2 inS s2 /\ f t1 t2 = true /\ t = pjoin_tuple t1 t2)).
Proof.
intros t f s1 s2.
unfold psigma_join.
rewrite (Fset.mem_fold2 FPTuple f pjoin_tuple t (Fset.empty FPTuple) nil s1 s2);
  [ | intro; rewrite Fset.empty_spec; apply refl_equal].
rewrite Oset.mem_bool_true_iff.
split.
- intros Ht.
  rewrite in_fold_left2 in Ht.
  destruct Ht as [Ht | Ht]; [contradiction Ht | ].
  destruct Ht as [t1 [t2 [Ht1 [Ht2 [H K]]]]].
  exists t1; exists t2; split; [ | split; [ | split]].
  + apply Fset.in_elements_mem; assumption.
  + apply Fset.in_elements_mem; assumption.
  + assumption.
  + assumption.
- intros [t1 [t2 [Ht1 [Ht2 [H K]]]]].
  rewrite in_fold_left2; right.
  exists t1; exists t2; repeat split; trivial.
  + rewrite Fset.mem_elements, Oset.mem_bool_true_iff in Ht1; apply Ht1.
  + rewrite Fset.mem_elements, Oset.mem_bool_true_iff in Ht2; apply Ht2.
Qed.
      
Lemma mem_pnatural_join : 
  forall t s1 s2,
    t inS (pnatural_join s1 s2) <->
    (exists t1 t2, t1 inS s1 /\ t2 inS s2 /\ 
                   pjoin_compatible_tuple t1 t2 = true /\ t = pjoin_tuple t1 t2).
Proof.
intros t s1 s2.
unfold pnatural_join; apply mem_psigma_join.
Qed.
*)
(** A tuple is well-typed whenever for all its relevant attributes, the corresponding value has the same type of the attribute. *)

Definition well_typed_tuple (t : tuple T) :=
  forall a, a inS (support T t) -> type_of_value T (dot t a) = type_of_attribute T a.

Definition OLTuple : Oeset.Rcd (list (tuple T)).
split with (fun l1 l2 => 
              Oeset.compare (mk_oelists (OTuple T)) (quicksort (OTuple T) l1) 
                                        (quicksort (OTuple T) l2)).
- do 3 intro; apply Oeset.compare_eq_trans.
- do 3 intro; apply Oeset.compare_eq_lt_trans.
- do 3 intro; apply Oeset.compare_lt_eq_trans.
- do 3 intro; apply Oeset.compare_lt_trans.
- do 2 intro; apply Oeset.compare_lt_gt.
Defined.

End Sec.

End Tuple.

(** Exporting notation for equivalent tuples, finite sets of attributes and finite sets of tuples. *)

Notation "t1 '=t=' t2" := (Oeset.compare (Tuple.OTuple _) t1 t2 = Eq) (at level 70, no associativity).
Notation "s1 '=P=' s2" := (_permut (@eq (Tuple.tuple _)) s1 s2) (at level 70, no associativity).
Notation "s1 '=PE=' s2" := (_permut (fun x y => Oeset.compare (Tuple.OTuple _) x y = Eq) s1 s2) (at level 70, no associativity).

Notation setA := (Fset.set (Tuple.A _)).
Notation setT := (Feset.set (Fecol.CSet (Tuple.CTuple _))).
Notation collectionT := (Fecol.collection (Tuple.CTuple _)).
Notation listT := (list (Tuple.tuple _)).

(* Module Expression. *)

(* Section Sec. *)

(* Hypothesis T : Tuple.Rcd. *)

(* Import Tuple. *)

(* Notation FTupleT := (Fecol.CSet (CTuple T)). *)
(* (*  *)
(* Notation BTupleT := (Fecol.CBag (CTuple T)). *)
(* *) *)



(* End Expression. *)

(** ** Database Schemas: they have a name, and a sort, that is a finite set of relevant attributes. Moreover, one assumes that there is a comparison function over the relations' names which is suitable to define an ordered type upon them. *)
Module DatabaseSchema.

Record Rcd attribute (OAtt : Oset.Rcd attribute) (A : Fset.Rcd OAtt) : Type :=
mk_R 
  {    
     (** names for relations *)
     relname : Type;
     ORN : Oset.Rcd relname;
     basesort : relname -> Fset.set A
  }.

Section Instance.

Hypothesis T : Tuple.Rcd.

Hypothesis DBS : Rcd (Tuple.A T).

Import Tuple.
(** An instance is well-typed whenever it associates a set of well-typed tuples to each relname. *)

Definition well_typed_instance (I : relname DBS -> Fecol.collection (CTuple T)) :=
  forall (r : relname DBS) (t : tuple T), t inCE (I r) -> well_typed_tuple T t.

(** An instance is well-sorted whenever it associates to each relname a set of tuples whose support is _exactly_ the basesort of _that_ relname. *)
Definition well_sorted_instance (I : relname DBS -> Fecol.collection (CTuple T)) :=
 forall (r : relname DBS) (t : tuple T), t inCE (I r) -> support T t =S= basesort DBS r.

End Instance.

End DatabaseSchema.

Module _Data.

Record Rcd : Type :=
mk_rcd
  {
    predicate : Type;
    symb : Type;
    aggregate : Type;
    T : Tuple.Rcd;
    DBS : DatabaseSchema.Rcd (Tuple.A T);
    OP : Oset.Rcd predicate;
    OSymb : Oset.Rcd symb;
    OAgg : Oset.Rcd aggregate;
    default_type : Tuple.type T
  }.
End _Data.
