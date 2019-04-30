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

Require Import List Nat.
Require Import BasicFacts OrderedSet Signatures.

Set Implicit Arguments.

Module SeqScan.
Section Sec.
Hypothesis o : Type.
Hypothesis O : Oeset.Rcd o.

Record cursor: Type :=
  mk_cursor
    { 
      visited: list o;
      to_visit: list o;
      collection: list o
    }.

Definition mk_seqcursor c := mk_cursor nil c c.

Lemma mk_seqcursor_collection l x :
  Oeset.mem_bool O x (collection (mk_seqcursor l)) = true ->
  Oeset.mem_bool O x l = true.
Proof. auto. Qed.

Definition coherent : cursor -> Prop :=
  fun c =>  c.(collection) = (rev c.(visited)) ++ c.(to_visit).

Definition reset (c:cursor) : cursor :=
  mk_cursor nil c.(collection) c.(collection).

Lemma reset_coherent:
  forall c:cursor, let c' := reset c in coherent c'.
Proof.
intros [l1 l2 c]; unfold coherent; simpl; trivial.
Qed.

Lemma reset_collection:
    forall c:cursor, collection (reset c) = (collection c).
Proof.
  unfold reset; reflexivity.
Qed.

Lemma reset_visited:
  forall c: cursor, visited (reset c) = nil.
Proof.
  unfold reset; reflexivity.
Qed.

Definition has_next : cursor ->  Prop :=
  fun c => to_visit c <> nil. 

Definition next : cursor -> (result o) * (cursor) :=
  fun c => match to_visit c with
           | nil => (Empty_Cursor, c)
           | el::li => (Result el, mk_cursor (el :: (visited c)) li (collection c))
           end.

Lemma visited_collection : 
  forall c, 
    coherent c ->
    forall x, Oeset.mem_bool O x (visited c) = true -> Oeset.mem_bool O x (collection c) = true.
Proof.
  intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c; simpl.
  intros x Hx; rewrite Oeset.mem_bool_app, Oeset.mem_bool_rev, Hx; apply refl_equal.
Qed.

Lemma has_next_spec_strong : 
  forall c, coherent c -> ~ (has_next c) -> collection c = rev (visited c).
Proof.
intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c; simpl.
unfold has_next; simpl.
destruct l2 as [ | a2 l2].
- intros _; rewrite <- app_nil_end; trivial.
- intro H; apply False_rec; apply H; discriminate.
Qed.

Lemma has_next_spec: 
  forall c, coherent c -> ~ (has_next c) ->
            comparelA (Oeset.compare O) (collection c) (rev (visited c)) = Eq.
Proof. 
intros.
rewrite has_next_spec_strong; trivial.
apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl.
Qed.

Lemma has_next_next_neg: forall c,
    coherent c -> (has_next c <-> fst (next c) <> Empty_Cursor).
Proof.
  intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c.
  unfold has_next, next; simpl.
  destruct l2 as [ | a2 l2]; split.
  - intro Abs; apply False_rec; apply Abs; apply refl_equal.
  - intro Abs; apply False_rec; apply Abs; apply refl_equal.
  - intros _; discriminate.
  - intros _; discriminate.
Qed.

Lemma next_collection:
  forall c c' opt, coherent c -> next c = (opt , c') -> (collection c') = (collection c).
Proof.
  intros [l1 l2 c] c' x Hc; unfold coherent in Hc; simpl in Hc; subst c.
  unfold next; simpl.
  destruct l2 as [ | a2 l2]; simpl;
    intro H; injection H; clear H; intros; subst; simpl; trivial.
Qed.

Lemma next_visited_No_Result:
    forall c c', coherent c -> next c = (No_Result, c') -> visited c' = visited c.
Proof.
  intros [l1 l2 c] c' Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
  destruct l2 as [ | a2 l2]; simpl.
  - intro H; discriminate H.
  - intro H; discriminate H.
Qed.  
  
Lemma next_visited_Empty_Cursor:
    forall c c', coherent c -> next c = (Empty_Cursor, c') -> (visited c') = (visited c).
Proof.
  intros [l1 l2 c] c' Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
  destruct l2 as [ | a2 l2]; simpl.
  - intro H; injection H; clear H; intros; subst; simpl; trivial.
  - intro H; discriminate H.
Qed.

Lemma next_Empty_Cursor : 
  forall c, coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor.
Proof.
intros [l1 l2 c] Hc; unfold next; simpl.
destruct l2 as [ | a2 l2]; simpl; trivial.
intro Abs; discriminate Abs.
Qed.

Lemma next_coherent: forall c, coherent c -> coherent (snd (next c)).
Proof.
intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
destruct l2 as [ | a2 l2]; unfold coherent; simpl; trivial.
- rewrite  app_assoc_reverse; simpl; trivial.
Qed.

Lemma next_reset_coherent: forall c, coherent c -> coherent (snd (next (reset c))).
Proof.
intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
unfold coherent.
destruct (rev l1) as [ | a1 k1]; simpl; trivial.
destruct l2 as [ | a2 l2]; simpl; trivial.
Qed.
  
    
Lemma next_visited_Result: 
  forall a c c', coherent c -> next c = (Result a, c') -> visited c' = a :: (visited c).
Proof.
intros a [l1 l2 c] c' Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
destruct l2 as [ | a2 l2]; unfold coherent; simpl.
- intro H; discriminate H.
- intro H; injection H; clear H; intros; subst; trivial.
Qed.

Lemma next_reset : forall c, coherent c -> reset (snd (next c)) = reset c.
Proof.
intros [l1 l2 c] Hc; unfold coherent in Hc; simpl in Hc; subst c; unfold next; simpl.
destruct l2 as [ | a2 l2]; unfold coherent; simpl; trivial.
Qed.

Definition empty_cursor : cursor := mk_cursor nil nil nil.
Lemma empty_cursor_collection : collection empty_cursor = nil.
Proof. reflexivity. Qed.
Lemma empty_cursor_coherent : coherent empty_cursor.
Proof. reflexivity. Qed.
Lemma empty_cursor_has_next : ~ has_next empty_cursor.
Proof. auto. Qed.

Definition ubound (c:cursor) : nat := List.length (to_visit c).

Lemma to_visit_iter res n : forall c (f:o -> res -> res) acc,
    to_visit (fst (iter next n c f acc)) = Nat.iter n (fun l => tl l) (to_visit c).
Proof.
induction n as [ | n]; intros c f acc; simpl; trivial.
assert (IH := IHn c f acc).
case_eq (iter next n c f acc); intros c' l H; rewrite H in IH; simpl in IH.
case_eq (next c'); intros r c'' Hc'; simpl.
unfold next in Hc'; rewrite IH in Hc'.
case_eq (Nat.iter n (fun l : list o => tl l) (to_visit c)).
- intro Hi; rewrite Hi in Hc'; injection Hc'; clear Hc'; do 2 intro; subst.
  rewrite IH, Hi; apply refl_equal.
- intros e1 l1 Hi; rewrite Hi in Hc'; injection Hc'; clear Hc'; intros; subst; simpl; trivial.
Qed.

Lemma iter_tl_length_list A (l:list A) :
    Nat.iter (List.length l) (fun l' => tl l') l = nil.
Proof.
  induction l as [ |x xs IHxs]; auto.
  change (Datatypes.length (x :: xs)) with (S (Datatypes.length xs)).
  now rewrite nat_iter_succ_r.
Qed.

Lemma reset_reset :
  forall c, reset (reset c) = reset c.
Proof.
intro c; unfold reset; simpl; apply refl_equal.
Qed.

Lemma ubound_next_Empty : 
  forall c, coherent c -> fst (next c) = Empty_Cursor -> ubound (snd (next c)) <= ubound c.
Proof.
intros c Hc H; unfold ubound.
destruct c as [l1 [ | a2 l2] l3]; unfold next in H; simpl in H.
- simpl; trivial.
- discriminate H.
Qed.

Lemma ubound_next_not_Empty : 
  forall c, coherent c -> fst (next c) <> Empty_Cursor -> ubound (snd (next c)) < ubound c.
Proof.
intros c Hc H; unfold ubound.
destruct c as [l1 [ | a2 l2] l3]; unfold next in H; simpl in H.
- apply False_rec; apply H; apply refl_equal.
- simpl; apply le_n.
Qed.

Lemma ubound_reset :
  forall c, coherent c -> ubound c <= ubound (reset c).
Proof.
intros c Hc; unfold ubound.
destruct c as [l1 l2 l3]; simpl.
unfold coherent in Hc; simpl in Hc; subst.
rewrite app_length; apply Plus.le_plus_r.
Qed.

Lemma ubound_complete res q (f:o -> res -> res) acc (Hq : coherent q) : 
  forall p, ubound q <= p -> ~ has_next (fst (iter next p q f acc)).
Proof.
  unfold has_next, ubound. intros p L H. apply H. clear H.
  rewrite to_visit_iter.
  rewrite (Minus.le_plus_minus _ _ L), PeanoNat.Nat.add_comm, nat_iter_plus. 
  rewrite iter_tl_length_list.
  set (n := p - length (to_visit q)); clearbody n; induction n; [trivial | ].
  simpl; rewrite IHn; trivial.
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
End SeqScan.
