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

Require Import List Bool.
Require Import BasicFacts ListFacts OrderedSet Signatures.

Set Implicit Arguments.

Module Filter.
Section Sec.

Hypothesis o : Type.
Hypothesis O : Oeset.Rcd o.
Hypothesis theta : o -> bool.
Hypothesis theta_eq : forall x y, Oeset.compare O x y = Eq -> theta x = theta y.

Hypothesis C : Cursor.Rcd O.

Definition cursor := Cursor.cursor C.

Definition visited (c : cursor) := List.filter theta (Cursor.visited c).

Definition mk_filter : (Cursor.cursor C) -> cursor := fun q => q.

Definition coherent (c : cursor) : Prop := Cursor.coherent c.

Definition collection (c : cursor) := List.filter theta (Cursor.collection c).

Lemma mk_filter_collection c x :
  Oeset.mem_bool O x (collection (mk_filter c)) = true ->
  Oeset.mem_bool O x (Cursor.collection c) = true.
Proof.
  unfold mk_filter, collection.
  rewrite Oeset.mem_bool_filter; auto.
  now rewrite andb_true_iff.
Qed.

Definition reset (c : cursor) : cursor := Cursor.reset c.

Definition next (c : cursor) : (result o * cursor)  :=
  match (Cursor.next c) with
  | (Result e, c') => 
    if theta e then (Result e, c') else (No_Result, c')
  | rc' => rc'
  end.

Definition has_next (c: cursor) : Prop := fst (next c) <> Empty_Cursor.

Definition empty_cursor : cursor := Cursor.empty_cursor C.

Definition ubound (q : cursor) : nat := Cursor.ubound q.

Lemma visited_collection : 
        forall c, coherent c -> 
                  forall x, Oeset.mem_bool O x (visited c) = true -> 
                            Oeset.mem_bool O x (collection c) = true.
Proof.
unfold coherent, collection, visited.
intros c Hc x Hx.
rewrite Oeset.mem_filter in Hx; [ | intros; apply theta_eq; trivial].
rewrite Oeset.mem_filter; [ | intros; apply theta_eq; trivial].
destruct (theta x); [ | discriminate Hx].
apply (Cursor.visited_collection _ Hc _ Hx).
Qed.

Lemma reset_collection : forall c, collection (reset c) = collection c.
Proof.
unfold collection, reset.
intros c; rewrite Cursor.reset_collection; apply refl_equal.
Qed.

Lemma reset_visited : forall c, visited (reset c) = nil.
Proof.
unfold visited, reset.
intro c; rewrite Cursor.reset_visited; apply refl_equal.
Qed.

Lemma reset_coherent : forall c, coherent (reset c).
Proof.
unfold coherent, reset.
intro c; apply Cursor.reset_coherent.
Qed.

Lemma reset_reset : forall c, reset (reset c) = reset c.
Proof.
unfold reset.
intro c; apply Cursor.reset_reset.
Qed.

Lemma next_collection : forall c c' opt,
    coherent c -> next c = (opt, c') -> collection c' = collection c.
Proof.
unfold coherent, next, collection.
intros c c' opt Hc H.
case_eq (Cursor.next c); intros r c'' Hnc; rewrite Hnc in H.
assert (K := Cursor.next_collection _ c Hc Hnc).
destruct r as [e | | ].
- destruct (theta e); injection H; intros; subst.
  + rewrite K; apply refl_equal.
  + rewrite K; apply refl_equal.
- injection H; intros; subst; rewrite K; apply refl_equal.
- injection H; intros; subst; rewrite K; apply refl_equal.
Qed.

Lemma next_visited_Result : forall a c c',
    coherent c -> next c = (Result a, c') -> visited c' = a :: (visited c).
Proof.
unfold coherent, next, visited.
intros a c c' Hc H.
case_eq (Cursor.next c); intros r c'' Hnc; rewrite Hnc in H.
destruct r as [e | | ].
- case_eq (theta e); intro He; rewrite He in H; try discriminate H.
  injection H; intros; subst.
  rewrite (Cursor.next_visited_Result _ _ Hc Hnc); simpl; rewrite He.
  apply refl_equal.
- discriminate H.
- discriminate H.
Qed.

Lemma next_visited_No_Result : forall c c',
    coherent c -> next c = (No_Result, c') -> visited c' = visited c.
Proof.
unfold coherent, next, visited.
intros c c' Hc H.
case_eq (Cursor.next c); intros r c'' Hnc; rewrite Hnc in H.
destruct r as [e | | ].
- case_eq (theta e); intro He; rewrite He in H; try discriminate H.
  injection H; intros; subst.
  rewrite (Cursor.next_visited_Result _ _ Hc Hnc); simpl; rewrite He.
  apply refl_equal.
- injection H; intros; subst.
  rewrite (Cursor.next_visited_No_Result _ _ Hc Hnc); trivial.
- discriminate H.
Qed.
  
Lemma next_visited_Empty_Cursor : forall c c',
    coherent c -> next c = (Empty_Cursor, c') -> visited c' = visited c.
Proof.
unfold coherent, next, visited.
intros c c' Hc H.
case_eq (Cursor.next c); intros r c'' Hnc; rewrite Hnc in H.
destruct r as [e | | ].
- case_eq (theta e); intro He; rewrite He in H; try discriminate H.
- discriminate H.
- injection H; intros; subst.
  rewrite (Cursor.next_visited_Empty_Cursor _ _ Hc Hnc); trivial.
Qed.

Lemma next_Empty_Cursor : 
  forall c, coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor.
Proof.
unfold coherent, next.
intros c Hc.
case_eq (Cursor.next c); intros r c'' Hnc.
destruct r as [e | | ].
- case_eq (theta e); intro He; intro Abs; discriminate Abs.
- intro Abs; discriminate Abs.
- intros; simpl.
  assert (K : fst (Cursor.next (snd (Cursor.next c))) = Empty_Cursor).
  {
    apply (Cursor.next_Empty_Cursor _ c Hc).
    rewrite Hnc; trivial.
  } 
  rewrite Hnc in K; simpl in K.
  case_eq (Cursor.next c''); intros r c''' Hnc''; rewrite Hnc'' in K; simpl in K; subst r; trivial.
Qed.

Lemma next_coherent : forall c, coherent c -> coherent (snd (next c)).
Proof.
unfold coherent, next.
intros c Hc.
case_eq (Cursor.next c); intros r c'' Hnc.
destruct r as [e | | ].
- case_eq (theta e); intro He.
  + assert (H := Cursor.next_coherent _ _ Hc); rewrite Hnc in H; apply H.
  + assert (H := Cursor.next_coherent _ _ Hc); rewrite Hnc in H; apply H.
- assert (H := Cursor.next_coherent _ _ Hc); rewrite Hnc in H; apply H.
- assert (H := Cursor.next_coherent _ _ Hc); rewrite Hnc in H; apply H.
Qed.

Lemma has_next_spec : 
  forall c, coherent c -> ~ has_next c -> 
            comparelA (Oeset.compare O) (collection c) (rev (visited c)) = Eq.
Proof.
unfold coherent, has_next, next, collection, visited.
intros c Hc.
case_eq (Cursor.next c); intros r c'' Hnc.
destruct r as [e | | ].
- case_eq (theta e); intro He.
  + intro Abs; apply False_rec; apply Abs; simpl; discriminate.
  + intro Abs; apply False_rec; apply Abs; simpl; discriminate.
- intro Abs; apply False_rec; apply Abs; simpl; discriminate.
- intros _; simpl.
  assert (H : comparelA (Oeset.compare O) (Cursor.collection c) (rev (Cursor.visited c)) = Eq).
  {
    apply Cursor.has_next_spec; [assumption | ].
    rewrite Cursor.has_next_next_neg; [ | assumption].
    rewrite Hnc; intro Abs; apply Abs; apply refl_equal.
  } 
  rewrite <- filter_rev.
  revert H; generalize (Cursor.collection c) (rev (Cursor.visited c)).
  intro l1; induction l1 as [ | a1 l1]; intros [ | a2 l2] Hl; try discriminate Hl; trivial.
  simpl in Hl.
  case_eq (Oeset.compare O a1 a2); intro Ha; rewrite Ha in Hl; try discriminate Hl.
  simpl; rewrite <- (theta_eq _ _ Ha).
  case (theta a1); simpl.
  + rewrite Ha; apply IHl1; assumption.
  + apply IHl1; assumption.
Qed.

Lemma has_next_next_neg : forall c,
    coherent c -> (has_next c <-> fst (next c) <> Empty_Cursor).
Proof.
unfold coherent, has_next, next.
intros c Hc.
case_eq (Cursor.next c); intros r c'' Hnc.
destruct r as [e | | ]; [case_eq (theta e); intro He | | ]; split; exact (fun h => h).
Qed.

Lemma empty_cursor_collection : collection empty_cursor = nil.
Proof.
unfold collection, empty_cursor.
rewrite Cursor.empty_cursor_collection; apply refl_equal.
Qed.

Lemma empty_cursor_coherent : coherent empty_cursor.
Proof.
unfold coherent, empty_cursor.
apply Cursor.empty_cursor_coherent.
Qed.

Lemma empty_cursor_has_next : ~ has_next empty_cursor.
Proof.
unfold has_next, empty_cursor, next.
case_eq (Cursor.next (Cursor.empty_cursor C)); intros r c Hc.
destruct r as [e | | ].
- case (theta e).
  + assert (H := Cursor.empty_cursor_has_next C).
    rewrite Cursor.has_next_next_neg, Hc in H.
    * apply H.
    * apply Cursor.empty_cursor_coherent.
  + assert (H := Cursor.empty_cursor_has_next C).
    rewrite Cursor.has_next_next_neg, Hc in H.
    * apply False_rec; apply H; discriminate.
    * apply Cursor.empty_cursor_coherent.
- assert (H := Cursor.empty_cursor_has_next C).
  rewrite Cursor.has_next_next_neg, Hc in H.
  + apply H.
  + apply Cursor.empty_cursor_coherent.
- assert (H := Cursor.empty_cursor_has_next C).
  rewrite Cursor.has_next_next_neg, Hc in H.
  + apply H.
  + apply Cursor.empty_cursor_coherent.
Qed.
  
Lemma ubound_next_Empty : forall c : cursor,
                        coherent c -> fst (next c) = Empty_Cursor -> ubound (snd (next c)) <= ubound c.
Proof.
unfold coherent, next, ubound.
intros c Hc H.
case_eq (Cursor.next c); intros r c' Hnc; rewrite Hnc in H.
destruct r as [e | | ]; [destruct (theta e) | | ]; try discriminate H.
rewrite <- Hnc; apply Cursor.ubound_next_Empty; trivial.
rewrite Hnc; trivial.
Qed.

Lemma ubound_next_not_Empty : forall c : cursor,
    coherent c -> fst (next c) <> Empty_Cursor -> ubound (snd (next c)) < ubound c.
Proof.
unfold coherent, next, ubound.
intros c Hc H.
case_eq (Cursor.next c); intros r c' Hnc; rewrite Hnc in H.
refine (Lt.le_lt_trans _ _ _ _ (Cursor.ubound_next_not_Empty _ _ Hc _)).
- rewrite Hnc; destruct r as [e | | ]; [destruct (theta e) | | ]; apply le_n.
- rewrite Hnc. 
  destruct r as [e | | ].
  + discriminate.
  + discriminate.
  + apply H.
Qed.

Lemma next_reset : forall c, coherent c -> reset (snd (next c)) = reset c.
Proof.
unfold coherent, next, reset.
intros c Hc.
case_eq (Cursor.next c); intros r c'' Hnc.
destruct r as [e | | ].
- case_eq (theta e); intro He; simpl.
  + rewrite <- (Cursor.next_reset _ _ Hc), Hnc; apply refl_equal.
  + rewrite <- (Cursor.next_reset _ _ Hc), Hnc; apply refl_equal.
- rewrite <- (Cursor.next_reset _ _ Hc), Hnc; apply refl_equal.
- rewrite <- (Cursor.next_reset _ _ Hc), Hnc; apply refl_equal.
Qed.

(*
Lemma ubound_reset :
  forall c, coherent c -> ubound c <= ubound (reset c).
Proof.
unfold coherent, ubound, reset.
apply Cursor.ubound_reset.
Qed.
*)

Lemma iter_filter res : forall q (f1:o -> res -> res) acc1 (f2:o -> res -> res) acc2, 
    coherent q ->
    forall n, has_next (fst (iter next n q f1 acc1)) <-> 
              Cursor.has_next (fst (iter (@Cursor.next _ _ C) n q f2 acc2)).
Proof.
  intros q f1 acc1 f2 acc2 Hq n. unfold coherent in Hq. revert q acc1 acc2 Hq.
  induction n as [ |n IHn]; intros q acc1 acc2 Hq.
  - unfold iter, has_next, next; simpl. rewrite (Cursor.has_next_next_neg _ _ Hq). 
    destruct (Cursor.next q) as [[el| | ] c']; simpl.
    * case (theta el); simpl; split; discriminate.
    * reflexivity.
    * reflexivity.
  - unfold iter in *; rewrite !nat_iter_succ_r.
    assert (Hq' := Cursor.next_coherent _ _ Hq).
    case_eq (Cursor.next q); intros r' q' Hnq; rewrite Hnq in Hq'.
    assert (Hnq' := refl_equal (next q)).
    unfold next at 2 in Hnq'; rewrite Hnq in Hnq'; rewrite Hnq'.
    destruct r' as [e' | | ].
    + case (theta e'); apply IHn; trivial.
    + apply IHn; trivial.
    + apply IHn; trivial.
Qed.

Lemma ubound_complete res : 
  forall c (f:o -> res -> res) acc, coherent c -> forall p, ubound c <= p -> ~ has_next (fst (iter next p c f acc)).
Proof.
  unfold ubound. 
  intros q f acc Hq p Hp; unfold coherent in Hq.
  rewrite (iter_filter q f acc f acc); auto using Cursor.ubound_complete.
Qed.

Definition build : Cursor.Rcd O.
apply (Cursor.mk_R O collection visited coherent)
  with reset next has_next empty_cursor ubound.
- apply visited_collection.
- apply reset_collection.
- apply reset_visited.
- apply reset_coherent.
- apply next_collection.
- apply next_visited_Result.
- apply next_visited_No_Result.
- apply next_visited_Empty_Cursor.
- apply next_coherent.
- apply next_Empty_Cursor.
- apply next_reset.
- apply has_next_spec.
- apply has_next_next_neg.
- apply empty_cursor_collection.
- apply empty_cursor_coherent.
- apply empty_cursor_has_next.
- apply reset_reset.
- apply ubound_next_Empty.
- apply ubound_next_not_Empty.
(* - apply ubound_reset. *)
- apply ubound_complete.
Defined.

End Sec.
End Filter.

