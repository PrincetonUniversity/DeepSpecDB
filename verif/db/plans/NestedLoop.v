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

Require Import List Psatz.

Require Import BasicFacts ListFacts OrderedSet Signatures.

Set Implicit Arguments.

Module NestedLoop.
Section Sec.

Hypotheses o1 o2 o : Type.
Hypothesis O1 : Oeset.Rcd o1.
Hypothesis O2 : Oeset.Rcd o2.
Hypothesis O : Oeset.Rcd o.

Hypothesis build_ : o1 -> o2 -> o.
Hypothesis build_eq_1  : 
  forall x1 x1' x2, 
    Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
Hypothesis build_eq_2  : 
  forall x1 x2 x2', 
    Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.

Hypothesis C1 : Cursor.Rcd O1.
Hypothesis C2 : Cursor.Rcd O2.

Record cursor :=
  mk_cursor
    {
      visited: list o;
      outer: Cursor.cursor C1;
      inner: Cursor.cursor C2
    }.

Local Notation cross := (fun l1 l2 => flat_map (fun a => (map (build_ a) l2)) l1).

Lemma map_build_eq :
  forall a1 b1 l2 m2, 
    Oeset.compare O1 a1 b1 = Eq -> comparelA (Oeset.compare O2) l2 m2 = Eq ->
    comparelA (Oeset.compare O) (map (build_ a1) l2) (map (build_ b1) m2) = Eq.
Proof.
intros a1 b1 l2; induction l2 as [ | a2 l2]; intros [ | b2 m2] H1 H2; try discriminate H2; trivial.
simpl in H2.
case_eq (Oeset.compare O2 a2 b2); intro Ha2; rewrite Ha2 in H2; try discriminate H2.
simpl.
rewrite (Oeset.compare_eq_1 _ _ _ _ (build_eq_1 _ _ _ H1)).
rewrite (Oeset.compare_eq_1 _ _ _ _ (build_eq_2 _ _ _ Ha2)).
rewrite Oeset.compare_eq_refl.
apply IHl2; trivial.
Qed.

Lemma cross_eq : forall l1 l2 m1 m2,
    comparelA (Oeset.compare O1) l1 m1 = Eq -> comparelA (Oeset.compare O2) l2 m2 = Eq ->
    comparelA 
      (Oeset.compare O) 
      (flat_map (fun a => (map (build_ a) l2)) l1) 
      (flat_map (fun a => (map (build_ a) m2)) m1) = Eq.
Proof.
intro l1; induction l1 as [ | x1 l1]; 
  (intros l2 [ | y1 m1] m2 H1 H2; simpl; trivial; try discriminate H1).
simpl in H1.
case_eq (Oeset.compare O1 x1 y1); intro Hx1; rewrite Hx1 in H1; try discriminate H1.
apply comparelA_eq_app; [ | apply IHl1; trivial].
apply map_build_eq; trivial.
Qed.

Definition collection c :=
  cross (Cursor.collection (outer c)) (Cursor.collection (inner c)).

Definition coherent (c: cursor) : Prop :=
  (* the two underlying cursors are coherent *)
  Cursor.coherent (outer c) /\ Cursor.coherent (inner c) /\
  match (Cursor.visited (outer c)) with
  (* if the outer cursor has not been visited yet, so as the inner
     cursor *)
  | nil => visited c = nil /\ Cursor.visited (inner c) = nil
  (* otherwise, the visited elements are a partial cross-product *)
  | el :: li =>
    comparelA
      (Oeset.compare O)
      (visited c)
      ((cross (el::nil) (Cursor.visited (inner c))) ++
         (cross li (rev (Cursor.collection (inner c))))) = Eq
  end.

Lemma visited_collection : 
  forall c, coherent c ->
    forall x, Oeset.mem_bool O x (visited c) = true -> Oeset.mem_bool O x (collection c) = true.
Proof.
intros c Hc x Hx; unfold coherent in Hc; unfold collection.
destruct Hc as [Hc1 [Hc2 H]].
case_eq (Cursor.visited (outer c)).
- intro H1; rewrite H1 in H.
  rewrite (proj1 H) in Hx; discriminate Hx.
-  intros x1 l H1; rewrite H1 in H.
   rewrite (Oeset.mem_bool_eq_2 _ _ _ _ H), Oeset.mem_bool_app, Bool.orb_true_iff in Hx.
   destruct Hx as [Hx | Hx].
   + rewrite Oeset.mem_bool_true_iff in Hx.
     destruct Hx as [x' [Hx Hx']].
     rewrite in_flat_map in Hx'.
     destruct Hx' as [_x' [_Hx' Hx']].
     simpl in _Hx'; destruct _Hx' as [_Hx' | _Hx']; [ | contradiction _Hx']; subst _x'.
     rewrite in_map_iff in Hx'.
     destruct Hx' as [x2 [Hx' Hx2]]; subst x'.
     assert (Kx1 : Oeset.mem_bool O1 x1 (Cursor.collection (outer c)) = true).
     {
       apply (Cursor.visited_collection (outer c) Hc1).
       rewrite Oeset.mem_bool_true_iff, H1; exists x1; split; [ | left; trivial].
       apply Oeset.compare_eq_refl.
     }
     assert (Kx2 : Oeset.mem_bool O2 x2 (Cursor.collection (inner c)) = true).
     {
       apply (Cursor.visited_collection (inner c) Hc2).
       rewrite Oeset.mem_bool_true_iff; exists x2; split; [ | trivial].
       apply Oeset.compare_eq_refl.
     }
     rewrite Oeset.mem_bool_true_iff in Kx1, Kx2.
     destruct Kx1 as [y1 [Kx1 Hy1]].
     destruct Kx2 as [y2 [Ky2 Hy2]].
     rewrite (Oeset.mem_bool_eq_1 _ _ (build_ y1 y2)), Oeset.mem_bool_true_iff.
     * eexists; split; [apply Oeset.compare_eq_refl | ].
       rewrite in_flat_map; exists y1; split; [assumption | ].
       rewrite in_map_iff; exists y2; split; trivial.
     * rewrite (Oeset.compare_eq_1 _ _ _ _ Hx).
       rewrite (Oeset.compare_eq_1 _ _ _ _ (build_eq_1 _ _ _ Kx1)); apply build_eq_2; assumption.
   + rewrite Oeset.mem_bool_true_iff in Hx.
     destruct Hx as [x' [Hx Hx']].
     rewrite in_flat_map in Hx'.
     destruct Hx' as [y1 [Hx1 Hx']].
     rewrite in_map_iff in Hx'.
     destruct Hx' as [y2 [Hx' Hy2]]; subst x'.
     assert (Ky1 : Oeset.mem_bool O1 y1 (Cursor.collection (outer c)) = true).
     {
       apply (Cursor.visited_collection (outer c) Hc1).
       rewrite Oeset.mem_bool_true_iff, H1; exists y1; split; [ | right; trivial].
       apply Oeset.compare_eq_refl.
     }
     rewrite Oeset.mem_bool_true_iff in Ky1.
     destruct Ky1 as [z1 [Ky1 Hz1]].
     rewrite (Oeset.mem_bool_eq_1 _ _ (build_ z1 y2)), Oeset.mem_bool_true_iff.
     * eexists; split; [apply Oeset.compare_eq_refl | ].
       rewrite in_flat_map; exists z1; split; [assumption | ].
       rewrite in_map_iff; exists y2; split; [trivial | ].
       rewrite in_rev; assumption.
     * rewrite (Oeset.compare_eq_1 _ _ _ _ Hx).
       apply build_eq_1; assumption.
Qed.

Definition reset (c : cursor) : cursor :=
    mk_cursor nil (Cursor.reset (outer c)) (Cursor.reset (inner c)). 

Lemma reset_collection : forall c, collection (reset c) = collection c.
Proof.
intro c; unfold reset, collection; simpl.
rewrite 2 Cursor.reset_collection; apply refl_equal.
Qed.
    
Lemma reset_visited : forall c, visited (reset c) = nil.
Proof.
intro c; unfold reset; apply refl_equal.
Qed.
    
Lemma reset_coherent : forall c, coherent (reset c).
Proof.
intro c; unfold reset, coherent; simpl.
split; [apply Cursor.reset_coherent | ].
split; [apply Cursor.reset_coherent | ].
rewrite 2 Cursor.reset_visited; split; trivial.
Qed.

Definition next (c: cursor) : (result o * cursor) :=
  match Cursor.next (inner c) with
  | (Empty_Cursor, c2') =>
    match Cursor.next (outer c) with
    | (Empty_Cursor, _) => (Empty_Cursor, mk_cursor (visited c) (outer c) c2')
    | (No_Result, c1') => 
      let c2'' := Cursor.reset (inner c) in
      match Cursor.next c2'' with
      | (Empty_Cursor, _) => (Empty_Cursor, mk_cursor (visited c) c1' c2')
      | _ => (No_Result, mk_cursor (visited c) c1' c2')
      end
    | (Result e1, c1') =>
      let c2' := Cursor.reset (inner c) in
      match Cursor.next c2' with
      | (Empty_Cursor, c2') => (Empty_Cursor, mk_cursor (visited c) c1' c2')
      | (No_Result, c2') => (No_Result, mk_cursor (visited c) c1' c2')
      | (Result e2, c2') =>
        let e := (build_ e1 e2) in
        (Result e, mk_cursor (e :: visited c) c1' c2')
      end
    end
  | (Result e2, c2') =>
    match Cursor.visited (outer c) with
    | nil => match Cursor.next (outer c) with
             | (Empty_Cursor, c1') => (Empty_Cursor, mk_cursor (visited c) c1' (inner c))
             | (Result e1, c1') => let e := build_ e1 e2 in
                              (Result e, mk_cursor (e :: visited c) c1' c2')
             | (No_Result, c1') => (No_Result, mk_cursor (visited c) c1' (inner c))
          end
    | e1 :: _ => let e := build_ e1 e2 in
                (Result e, mk_cursor (e :: visited c) (outer c) c2')
    end
  | (No_Result, c2') =>
    (No_Result, mk_cursor (visited c) (outer c) c2')
  end.

Lemma next_collection : 
  forall c c' res, coherent c -> next c = (res, c') -> collection c' = collection c.
Proof.
intros c c' res Hc H; unfold coherent in Hc.
destruct Hc as [Hc1 [Hc2 Hc]].
unfold next in H.
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2; rewrite Hnc2 in H.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in H.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; injection H; clear H; intros H1 H2; subst; unfold collection; simpl.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1).
      rewrite (Cursor.next_collection _ _ Hc2 Hnc2).
      apply refl_equal.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1); apply refl_equal.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1).
      apply refl_equal.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in H.
    injection H; clear H; intros H1 H2; subst; unfold collection; simpl.
    rewrite (Cursor.next_collection _ _ Hc2 Hnc2); apply refl_equal.
- injection H; clear H; intros H1 H2; subst; unfold collection; simpl.
  rewrite (Cursor.next_collection _ _ Hc2 Hnc2); apply refl_equal.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
  destruct r1 as [e1 | | ].
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; injection H; clear H; intros H1 H2; subst; unfold collection; simpl.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1).
      rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent _) Hnc2').
      rewrite Cursor.reset_collection; apply refl_equal.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1).
      rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent _) Hnc2').
      rewrite Cursor.reset_collection; apply refl_equal.
    * rewrite (Cursor.next_collection _ _ Hc1 Hnc1).
      rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent _) Hnc2').
      rewrite Cursor.reset_collection; apply refl_equal.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; injection H; intros; subst res c'; unfold collection; simpl;
      rewrite (Cursor.next_collection _ _ Hc1 Hnc1), (Cursor.next_collection _ _ Hc2 Hnc2);
      apply refl_equal.
  + injection H; clear H; intros H1 H2; subst; unfold collection; simpl.
    rewrite (Cursor.next_collection _ _ Hc2 Hnc2).
    apply refl_equal.
Qed.

Lemma next_visited_Result: 
  forall e c c', coherent c -> next c = (Result e, c') -> visited c' = e :: visited c.
Proof.
intros e c c' Hc H; unfold coherent in Hc.
unfold next in H.
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2; rewrite Hnc2 in H.
destruct r2 as [e2 | | ]; try discriminate H.
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in H.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; try discriminate H.
    injection H; clear H; intros H1 H2; subst; simpl; trivial.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in H.
    injection H; clear H; intros H1 H2; subst; simpl; trivial.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
  destruct r1 as [e1 | | ]; try discriminate H.
  case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
  destruct r2 as [e2 | | ]; try discriminate H.
  + injection H; clear H; intros H1 H2; subst; simpl; trivial.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H;
      destruct r2 as [e2 | | ]; try discriminate H.
Qed.

Lemma next_visited_No_Result : 
  forall c c', coherent c -> next c = (No_Result, c') -> visited c' = visited c.
Proof.
intros c c' Hc H; unfold coherent in Hc.
unfold next in H.
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2; rewrite Hnc2 in H.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in H.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; try discriminate H.
    injection H; clear H; intros H1; subst; simpl; trivial.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in H; discriminate H.
- injection H; clear H; intros H1; subst; simpl; trivial.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
  destruct r1 as [e1 | | ]; try discriminate H.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; try discriminate H.
    injection H; clear H; intros H1; subst; simpl; trivial.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H;
      destruct r2 as [e2 | | ]; try discriminate H.
    * injection H; clear H; intros H1; subst; simpl; trivial.
    * injection H; clear H; intros H1; subst; simpl; trivial.
Qed.

Lemma next_visited_Empty_Cursor : 
  forall c c', coherent c -> next c = (Empty_Cursor, c') -> visited c' = visited c.
Proof.
intros c c' Hc H; unfold coherent in Hc.
unfold next in H.
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2; rewrite Hnc2 in H.
destruct r2 as [e2 | | ]; try discriminate H.
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in H.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; try discriminate H.
    injection H; clear H; intros H1; subst; simpl; trivial.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in H.
    discriminate H.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
  destruct r1 as [e1 | | ]; try discriminate H.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; try discriminate H.
    injection H; clear H; intros H1; subst; simpl; trivial.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H;
      destruct r2 as [e2 | | ]; try discriminate H.
    injection H; clear H; intros H1; subst; simpl; trivial.
  + injection H; clear H; intros H1; subst; simpl; trivial.
Qed.

Lemma next_coherent: forall c, coherent c -> coherent (snd (next c)).
Proof.
unfold coherent, next; intros c Hc.
destruct Hc as [Hc1 [Hc2 Hc]].
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1.
    destruct r1 as [e1 | | ]; simpl.
    * split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
      split; [assert (H2 := Cursor.next_coherent _ _ Hc2); rewrite Hnc2 in H2; apply H2 | ].
      rewrite (Cursor.next_visited_Result _ _ Hc1 Hnc1), Hvc1, <- 2 app_nil_end.
      rewrite (Cursor.next_visited_Result _ _ Hc2 Hnc2), map_unfold, Oeset.compare_eq_refl.
      rewrite (proj1 Hc), (proj2 Hc); apply refl_equal.
    * split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
      split; [assumption | ].
      rewrite (Cursor.next_visited_No_Result _ _ Hc1 Hnc1), Hvc1; apply Hc.
    * split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
      split; [assumption | ].
      rewrite (Cursor.next_visited_Empty_Cursor _ _ Hc1 Hnc1), Hvc1.
      apply Hc.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in Hc; simpl.
    split; [assumption | ].
    split; [assert (H2 := Cursor.next_coherent _ _ Hc2); rewrite Hnc2 in H2; apply H2 | ].
    rewrite Hvc1, (Cursor.next_visited_Result _ _ Hc2 Hnc2), map_unfold, <- app_nil_end; simpl.
    rewrite Oeset.compare_eq_refl, (Cursor.next_collection _ _ Hc2 Hnc2).
    simpl flat_map in Hc; rewrite <- app_nil_end in Hc; apply Hc.
- simpl; split; [assumption | ].
  split; [assert (H2 := Cursor.next_coherent _ _ Hc2); rewrite Hnc2 in H2; apply H2 | ].
  case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc; split; [apply (proj1 Hc) | ].
    rewrite <- (proj2 Hc).
    apply (Cursor.next_visited_No_Result _ _ Hc2 Hnc2).
  + intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
    simpl flat_map in Hc; rewrite <- app_nil_end in Hc.
    rewrite <- app_nil_end.
    rewrite (Cursor.next_collection _ _ Hc2 Hnc2).
    rewrite (Cursor.next_visited_No_Result _ _ Hc2 Hnc2).
    apply Hc.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; simpl.
  destruct r1 as [e1 | | ].
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'.
    destruct r2 as [e2 | | ]; simpl.
    * rewrite (Cursor.next_visited_Result _ _ Hc1 Hnc1), <- app_nil_end.
      rewrite (Cursor.next_visited_Result _ _ (Cursor.reset_coherent (inner c)) Hnc2').
      rewrite map_unfold; simpl; rewrite Oeset.compare_eq_refl.
      rewrite Cursor.reset_visited, map_unfold; simpl app.
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
          split; [assert (Hc2' := Cursor.reset_coherent (inner c));
                  assert (Hc2'' := Cursor.next_coherent _ _ Hc2'); rewrite Hnc2' in Hc2''; 
                  apply Hc2'' | ].
          rewrite (proj1 Hc); apply refl_equal.
        - intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
          rewrite <- (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          simpl flat_map in Hc; 
            rewrite <- app_nil_end, (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent (inner c)) Hnc2').
          rewrite Cursor.reset_collection.
          split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
          split; [assert (Hc2' := Cursor.reset_coherent (inner c));
                  assert (Hc2'' := Cursor.next_coherent _ _ Hc2'); rewrite Hnc2' in Hc2''; 
                  apply Hc2'' | ].
          refine (comparelA_eq_trans _ _ _ _ _ Hc _).
          + do 6 intro; apply Oeset.compare_eq_trans.
          + simpl.
            apply comparelA_eq_app;
                     [ | apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl].
            apply map_build_eq; [apply Oeset.compare_eq_refl | ].
            rewrite <- (rev_involutive (Cursor.visited (inner c))).
            apply comparelA_rev_eq; rewrite comparelA_lt_gt; 
              [ | intros; apply Oeset.compare_lt_gt].
            rewrite CompOpp_iff; apply (Cursor.has_next_spec Hc2).
            intro H; rewrite (Cursor.has_next_next_neg _ _ Hc2), Hnc2 in H.
            apply H; apply refl_equal.
      }
    * split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
      split; [assert (Hc2' := Cursor.reset_coherent (inner c));
      assert (Hc2'' := Cursor.next_coherent _ _ Hc2'); rewrite Hnc2' in Hc2''; apply Hc2'' | ].
      rewrite (Cursor.next_visited_Result _ _ Hc1 Hnc1), <- app_nil_end.
      rewrite (Cursor.next_visited_No_Result _ _ (Cursor.reset_coherent (inner c)) Hnc2').
      rewrite Cursor.reset_visited; simpl.
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          rewrite (proj1 Hc); apply refl_equal.
        - intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
          rewrite <- (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          simpl flat_map in Hc; 
            rewrite <- app_nil_end, (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent (inner c)) Hnc2').
          rewrite Cursor.reset_collection.
          refine (comparelA_eq_trans _ _ _ _ _ Hc _).
          + do 6 intro; apply Oeset.compare_eq_trans.
          + simpl. 
            apply comparelA_eq_app;
                     [ | apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl].
            apply map_build_eq; [apply Oeset.compare_eq_refl | ].
            rewrite <- (rev_involutive (Cursor.visited (inner c))).
            apply comparelA_rev_eq; rewrite comparelA_lt_gt; 
              [ | intros; apply Oeset.compare_lt_gt].
            rewrite CompOpp_iff; apply (Cursor.has_next_spec Hc2).
            intro H; rewrite (Cursor.has_next_next_neg _ _ Hc2), Hnc2 in H.
            apply H; apply refl_equal.
      }
    * split; [assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; apply H1 | ].
      split; [assert (Hc2' := Cursor.reset_coherent (inner c));
      assert (Hc2'' := Cursor.next_coherent _ _ Hc2'); rewrite Hnc2' in Hc2''; apply Hc2'' | ].
      rewrite (Cursor.next_visited_Result _ _ Hc1 Hnc1), <- app_nil_end.
      rewrite (Cursor.next_visited_Empty_Cursor _ _ (Cursor.reset_coherent (inner c)) Hnc2').
      rewrite Cursor.reset_visited; simpl.
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          rewrite (proj1 Hc); apply refl_equal.
        - intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
          rewrite <- (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          simpl flat_map in Hc; 
            rewrite <- app_nil_end, (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2) in Hc.
          rewrite (Cursor.next_collection _ _ (Cursor.reset_coherent (inner c)) Hnc2').
          rewrite Cursor.reset_collection.
          refine (comparelA_eq_trans _ _ _ _ _ Hc _).
          + do 6 intro; apply Oeset.compare_eq_trans.
          + simpl. 
            apply comparelA_eq_app;
                     [ | apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl].
            apply map_build_eq; [apply Oeset.compare_eq_refl | ].
            rewrite <- (rev_involutive (Cursor.visited (inner c))).
            apply comparelA_rev_eq; rewrite comparelA_lt_gt; 
              [ | intros; apply Oeset.compare_lt_gt].
            rewrite CompOpp_iff; apply (Cursor.has_next_spec Hc2).
            intro H; rewrite (Cursor.has_next_next_neg _ _ Hc2), Hnc2 in H.
            apply H; apply refl_equal.
      }
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'.
    assert (H1 := Cursor.next_coherent _ _ Hc1); rewrite Hnc1 in H1; simpl in H1.
    assert (H2 := Cursor.next_coherent _ _ Hc2); rewrite Hnc2 in H2; simpl in H2.
    assert (K1 := Cursor.next_visited_No_Result _ _ Hc1 Hnc1).
    assert (K2 := Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2).
    assert (K2' := Cursor.next_collection _ _ Hc2 Hnc2).
    simpl in Hc.
    destruct r2 as [e2 | | ]; simpl; 
      (split; [apply H1 | ]; split; [apply H2 | ]; rewrite K1, K2;
       case_eq (Cursor.visited (outer c)); 
       [intro Hvc1 | intros v1 lv1 Hvc1]; rewrite Hvc1 in Hc; [trivial | rewrite K2'; trivial]).
  + simpl.
    split; [assumption | ].
    split; [assert (H2 := Cursor.next_coherent _ _ Hc2); rewrite Hnc2 in H2; apply H2 | ].
    rewrite (Cursor.next_visited_Empty_Cursor _ _ Hc2 Hnc2).
    case_eq (Cursor.visited (outer c)).
    * intro Hvc1; rewrite Hvc1 in Hc; apply Hc.
    * intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
      rewrite (Cursor.next_collection _ _ Hc2 Hnc2).
      apply Hc.
Qed.

Lemma next_Empty_Cursor : 
  forall c, coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor.
Proof.
unfold coherent, next; intros c Hc H.
destruct Hc as [Hc1 [Hc2 Hc]].
case_eq (Cursor.next (inner c)); intros r2 c2' Hnc2; rewrite Hnc2 in H.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc.
    case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; simpl.
    * destruct (Cursor.visited (outer c)); discriminate H.
    * destruct (Cursor.visited (outer c)); discriminate H.
    * rewrite (Cursor.next_visited_Empty_Cursor _ _ Hc1 Hnc1), Hvc1, Hnc2.
      assert (K : fst (Cursor.next (snd (Empty_Cursor (A := o1), c1'))) = Empty_Cursor).
      {
        rewrite <- Hnc1.
        apply Cursor.next_Empty_Cursor; [assumption | ].
        rewrite Hnc1; trivial.
      }
      simpl in K.
      case_eq (Cursor.next c1'); intros r1 c1'' Hnc1'; rewrite Hnc1' in K; simpl in K; subst r1.
      apply refl_equal.
  + intros v1 lv1 Hvc1; rewrite Hvc1 in H; discriminate H.
- discriminate H.
- case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
  destruct r1 as [e1 | | ].
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; try discriminate H.
    simpl.
    rewrite (Cursor.next_visited_Result _ _ Hc1 Hnc1).
    assert (K : fst (Cursor.next (snd (Cursor.next (Cursor.reset (inner c))))) = Empty_Cursor).
    {
      apply (Cursor.next_Empty_Cursor _ _ (Cursor.reset_coherent (inner c))).
      rewrite Hnc2'; trivial.
    }
    rewrite Hnc2' in K; simpl in K.
    case_eq (Cursor.next c2''); intros r2 c2''' Hnc2''; rewrite Hnc2'' in K; simpl in K; subst r2.
    case_eq (Cursor.next c1'); intros r1 c1'' Hnc1'.
    assert (K := Cursor.next_reset _ _ (Cursor.reset_coherent (inner c))).
    rewrite Hnc2' in K; simpl in K; rewrite K, Cursor.reset_reset, Hnc2'.
    destruct r1; trivial.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
    destruct r2 as [e2 | | ]; try discriminate H.
    simpl.
    assert (K : fst (Cursor.next (snd (Cursor.next (inner c)))) = Empty_Cursor).
    {
      apply (Cursor.next_Empty_Cursor _ _ Hc2).
      rewrite Hnc2; trivial.
    }
    rewrite Hnc2 in K; simpl in K.
    case_eq (Cursor.next c2'); intros r2 c2''' Hnc2''; rewrite Hnc2'' in K; simpl in K; subst r2.
    assert (K := Cursor.next_reset _ _ Hc2).
    rewrite Hnc2 in K; simpl in K; rewrite K, Hnc2'.
    case_eq (Cursor.next c1'); intros r1 c1'' Hnc1'.
    destruct r1; trivial.
  + simpl.
    assert (K : fst (Cursor.next (snd (Cursor.next (inner c)))) = Empty_Cursor).
    {
      apply (Cursor.next_Empty_Cursor _ _ Hc2).
      rewrite Hnc2; trivial.
    }
    rewrite Hnc2 in K; simpl in K.
    case_eq (Cursor.next c2'); intros r2 c2'' Hnc2'; rewrite Hnc2' in K; simpl in K; subst r2.
    rewrite Hnc1; trivial.
Qed.

Definition has_next (c : cursor) : Prop := fst (next c) <> Empty_Cursor.

Lemma has_next_spec: 
  forall c, coherent c -> ~ (has_next c) -> 
            comparelA (Oeset.compare O) (collection c) (rev (visited c)) = Eq.
Proof.
unfold coherent; intros c [Hc1 [Hc2 Hc]] H.
unfold has_next in H; unfold collection.
case_eq (fst (next c)).
- intros a Ha; rewrite Ha in H; apply False_rec; apply H; discriminate.
- intros Ha; rewrite Ha in H; apply False_rec; apply H; discriminate.
- clear H; intro H.
  unfold next in H.
  case_eq (Cursor.next (inner c)).
  intros r2 c2' Hnc2; rewrite Hnc2 in H.
  destruct r2 as [e2 | | ]; try discriminate H.
  + case_eq (Cursor.visited (outer c)).
    * intro Hvc1; rewrite Hvc1 in H.
      case_eq (Cursor.next (outer c)).
      intros r1 c1' Hnc1; rewrite Hnc1 in H.
      destruct r1 as [e1 | | ]; try discriminate H.
      rewrite Hvc1 in Hc.
      rewrite (proj1 Hc); simpl.
      assert (H1 : comparelA (Oeset.compare O1) (Cursor.collection (outer c))
         (rev (Cursor.visited (outer c))) = Eq).
      {
        apply (Cursor.has_next_spec Hc1).
        intro H1.
        rewrite Cursor.has_next_next_neg, Hnc1 in H1.
        - apply H1; apply refl_equal.
        - apply Hc1.
      }
      rewrite Hvc1 in H1.
      destruct (Cursor.collection (outer c)); [ | discriminate H1].
      apply refl_equal.
    * intros v1 lv1 Hvc1; rewrite Hvc1 in H; discriminate H.
  + case_eq (Cursor.next (outer c)); intros r1 c1' Hnc1; rewrite Hnc1 in H.
    destruct r1 as [e1 | | ]; try discriminate H.
    * case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
      destruct r2 as [e2 | | ]; try discriminate H.
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          rewrite (proj1 Hc).
          assert (H2 : comparelA (Oeset.compare O2) (Cursor.collection (inner c))
                                 (rev (Cursor.visited (inner c))) = Eq).
          {
            apply (Cursor.has_next_spec Hc2).
            intro H2.
            rewrite Cursor.has_next_next_neg, Hnc2 in H2.
            - apply H2; apply refl_equal.
            - apply Hc2.
          }
          rewrite (proj2 Hc) in H2.
          destruct (Cursor.collection (inner c)); [ | discriminate H2].
          simpl; rewrite flat_map_nil; [ | intros; apply refl_equal].
          apply refl_equal.
        - intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
          assert (H2 : comparelA (Oeset.compare O2) (Cursor.collection (Cursor.reset (inner c)))
                                 (rev (Cursor.visited (Cursor.reset (inner c)))) = Eq).
          {
            apply Cursor.has_next_spec.
            - apply Cursor.reset_coherent.
            - intro H2; rewrite Cursor.has_next_next_neg, Hnc2' in H2.
              + apply H2; apply refl_equal.
              + apply Cursor.reset_coherent.
          }
          rewrite Cursor.reset_visited, (Cursor.reset_collection (inner c)) in H2.
          assert (K2 : comparelA (Oeset.compare O2) (Cursor.collection (inner c))
                                 (rev (Cursor.visited (inner c))) = Eq).
          {
            apply (Cursor.has_next_spec Hc2).
            intro K2; rewrite Cursor.has_next_next_neg, Hnc2 in K2.
            - apply K2; apply refl_equal.
            - apply Hc2.
          }
          destruct (Cursor.collection (inner c)); [ | discriminate H2].
          destruct (Cursor.visited (inner c)) as [ | v2 lv2].
          + simpl in Hc; rewrite flat_map_nil in Hc; [ | intros; apply refl_equal].
            destruct (visited c) as [ | v lv]; [ | discriminate Hc].
            simpl; rewrite flat_map_nil; [ | intros; apply refl_equal].
            apply refl_equal.
          + simpl in K2; destruct (rev lv2); discriminate K2.
      }
    * case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2'' Hnc2'; rewrite Hnc2' in H.
      destruct r2; try discriminate H.
      assert (H2 : Cursor.collection (inner c) = nil).
      {
        rewrite <-  (Cursor.reset_collection (inner c)).
        apply Cursor.visited_nil_next_empty.
        - apply Cursor.reset_coherent.
        - apply Cursor.reset_visited.
        - rewrite Hnc2'; trivial.
      }
      rewrite H2, flat_map_nil; [ | intros; trivial].
      rewrite H2, (Cursor.empty_collection _ _ Hc2 H2) in Hc; simpl in Hc.
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          rewrite (proj1 Hc); trivial.
        - intros v1 lv1 Hvc1; rewrite Hvc1, flat_map_nil in Hc; [ | intros; trivial].
          destruct (visited c); [trivial | discriminate Hc].
      }
    * assert (K1 : comparelA (Oeset.compare O1) (Cursor.collection (outer c))
                                 (rev (Cursor.visited (outer c))) = Eq).
      {
        apply (Cursor.has_next_spec Hc1).
        intro K1; rewrite Cursor.has_next_next_neg, Hnc1 in K1.
        - apply K1; apply refl_equal.
        - apply Hc1.
      }
      {
        case_eq (Cursor.visited (outer c)).
        - intro Hvc1; rewrite Hvc1 in Hc.
          rewrite (proj1 Hc).
          rewrite Hvc1 in K1.
          destruct (Cursor.collection (outer c)); [ | discriminate K1].
          apply refl_equal.
        - intros v1 lv1 Hvc1; rewrite Hvc1 in Hc.
          generalize (comparelA_rev_eq _ _ _ Hc); clear Hc; intro Hc.
          rewrite comparelA_lt_gt; [ | intros; apply Oeset.compare_lt_gt].
          rewrite CompOpp_iff.
          refine (comparelA_eq_trans _ _ _ _ _ Hc _); 
            [do 6 intro; apply Oeset.compare_eq_trans | ].
          simpl; rewrite rev_app_distr, <- app_nil_end, <- map_rev.
          rewrite Hvc1 in K1; simpl in K1.
          assert (K2 : comparelA (Oeset.compare O2) (Cursor.collection (inner c))
                                 (rev (Cursor.visited (inner c))) = Eq).
          {
            apply (Cursor.has_next_spec Hc2).
            intro K2; rewrite Cursor.has_next_next_neg, Hnc2 in K2.
            - apply K2; apply refl_equal.
            - apply Hc2.
          }
          rewrite comparelA_lt_gt, CompOpp_iff; [ | intros; apply Oeset.compare_lt_gt].
          refine (comparelA_eq_trans _ _ _ _ _ (cross_eq _ _ _ _ K1 K2) _);
            [do 6 intro; apply Oeset.compare_eq_trans | ].
          rewrite flat_map_app; apply comparelA_eq_app.
          + revert K2; set (l2 := rev (Cursor.visited (inner c))); clearbody l2.
            set (m2 := Cursor.collection (inner c)); clearbody m2.
            revert l2 m2; generalize lv1; intro l1; 
              induction l1 as [ | a1 l1]; intros l2 m2 H2; [apply refl_equal | ].
            simpl.
            rewrite flat_map_app, rev_app_distr.
            apply comparelA_eq_app; [apply IHl1; assumption | ].
            rewrite map_rev, rev_involutive; simpl; rewrite <- app_nil_end.
            apply map_build_eq; [apply Oeset.compare_eq_refl | ].
            rewrite comparelA_lt_gt, H2; [trivial | ].
            intros; apply Oeset.compare_lt_gt.
          + simpl; rewrite <- app_nil_end.
            apply comparelA_eq_refl.
            intros; apply Oeset.compare_eq_refl.
      }
Qed.

Lemma has_next_next_neg: 
  forall c, coherent c -> (has_next c <-> fst (next c) <> Empty_Cursor).
Proof.
intros c Hc.
unfold has_next; split; exact (fun h => h).
Qed.

Definition empty_cursor : cursor :=
    mk_cursor nil (Cursor.empty_cursor C1) (Cursor.empty_cursor C2).

Lemma empty_cursor_collection : collection empty_cursor = nil.
Proof.
unfold collection, empty_cursor; simpl.
now rewrite (Cursor.empty_cursor_collection C1).
Qed.

Lemma empty_cursor_coherent : coherent empty_cursor.
Proof.
unfold coherent, empty_cursor; simpl.
split; [apply Cursor.empty_cursor_coherent | ].
split; [apply Cursor.empty_cursor_coherent | ].
rewrite Cursor.empty_cursor_collection, 2 Cursor.empty_collection.
- split; trivial.
- apply Cursor.empty_cursor_coherent.
- apply Cursor.empty_cursor_collection.
- apply Cursor.empty_cursor_coherent.
- apply Cursor.empty_cursor_collection.
Qed.

Lemma empty_cursor_has_next : ~ has_next empty_cursor.
Proof.
unfold has_next, next, empty_cursor; simpl.
assert (H2 := Cursor.empty_cursor_has_next C2).
rewrite Cursor.has_next_next_neg in H2.
case_eq (Cursor.next (Cursor.empty_cursor C2)); intros r2 c2' Hnc2; rewrite Hnc2 in H2.
destruct r2 as [e2 | | ].
- apply False_rec; apply H2; discriminate.
- apply False_rec; apply H2; discriminate.
- assert (H1 := Cursor.empty_cursor_has_next C1).
  rewrite Cursor.has_next_next_neg in H1.
  case_eq (Cursor.next (Cursor.empty_cursor C1)); intros r1 c1' Hnc1; rewrite Hnc1 in H1.
  destruct r1 as [e1 | | ].
  + apply False_rec; apply H1; discriminate.
  + apply False_rec; apply H1; discriminate.
  + intro H; apply H; trivial.
  + apply Cursor.empty_cursor_coherent.
- apply Cursor.empty_cursor_coherent.
Qed.

 Lemma coherent_iter res :
  forall n c (f:o -> res -> res) acc, coherent c -> coherent (fst (iter next n c f acc)).
Proof.
intro n; induction n as [ | n]; intros c f acc Hc; simpl; [assumption | ].
assert (IH := IHn c f acc Hc).
case_eq (iter next n c f acc); intros c' l H; rewrite H in IH; simpl in IH.
assert (K := next_coherent IH).
case_eq (next c'); intros r c'' Hc'; rewrite Hc' in K; apply K.
Qed.

Definition ubound c := 
 Cursor.ubound (inner c) + (Cursor.ubound (outer c) * (S (Cursor.ubound (Cursor.reset (inner c))))).

Lemma reset_next : forall c : cursor, coherent c -> reset (snd (next c)) = reset c.
Proof.
intros c Hc; unfold coherent in Hc; unfold next, reset, ubound; simpl.
destruct Hc as [Hc1 [Hc2 Hc]].
case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2.
destruct r2 as [e2 | | ]; simpl.
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1.
    case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ]; simpl.
    * replace c1 with (snd (Result e1, c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      replace c2 with (snd (Result e2, c2)); [ | apply refl_equal].
      rewrite <- Hnc2, Cursor.next_reset; [ | assumption].
      trivial.
    * replace c1 with (snd (No_Result (A := o1), c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      apply refl_equal.
    * replace c1 with (snd (Empty_Cursor (A := o1), c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      apply refl_equal.
  + intros v1 lv1 Hvc1; simpl.
    replace c2 with (snd (Result e2, c2)); [ | apply refl_equal].
    rewrite <- Hnc2, Cursor.next_reset; [ | assumption].
    trivial.
- replace c2 with (snd (No_Result (A := o2), c2)); [ | apply refl_equal].
  rewrite <- Hnc2, Cursor.next_reset; [ | assumption].
  apply refl_equal.
- case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
  destruct r1 as [e1 | | ]; simpl.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
    destruct r2 as [e2 | | ]; simpl.
    * replace c1 with (snd (Result e1, c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      replace c2' with (snd (Result e2, c2')); [ | apply refl_equal].
      rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset;[ | apply Cursor.reset_coherent].
      apply refl_equal.
    * replace c1 with (snd (Result e1, c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      replace c2' with (snd (No_Result (A := o2), c2')); [ | apply refl_equal].
      rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset; [ | apply Cursor.reset_coherent].
      apply refl_equal.
    * replace c1 with (snd (Result e1, c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [ | assumption].
      replace c2' with (snd (Empty_Cursor (A := o2), c2')); [ | apply refl_equal].
      rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset; [ | apply Cursor.reset_coherent].
      apply refl_equal.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
    assert (H1 : Cursor.reset c1 = Cursor.reset (outer c)).
    {    
      replace c1 with (snd (No_Result (A := o1), c1)); [ | apply refl_equal].
      rewrite <- Hnc1, Cursor.next_reset; [trivial | assumption].
    }
    assert (H2 : Cursor.reset c2 = Cursor.reset (inner c)).
    {
      replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | apply refl_equal].
      rewrite <- Hnc2, Cursor.next_reset; [trivial | assumption].
    }
    destruct r2 as [e2 | | ]; simpl; rewrite H1, H2; apply refl_equal.
  + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | apply refl_equal].
    rewrite <- Hnc2, Cursor.next_reset; [ | assumption].
    apply refl_equal.
Qed.

Lemma reset_reset : forall c, reset (reset c) = reset c.
Proof.
intro c; unfold reset, ubound; simpl.
rewrite 2 Cursor.reset_reset.
 apply refl_equal.
Qed.

Lemma ubound_next_Empty :
  forall c, coherent c -> fst (next c) = Empty_Cursor -> ubound (snd (next c)) <= ubound c.
Proof.
intros c Hc; destruct Hc as [Hc1 [Hc2 Hc]].
unfold next, ubound.
case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc.
    case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ].
    * intro Abs; discriminate Abs.
    * intro Abs; discriminate Abs.
    * intros _; simpl.
      {
        apply Plus.plus_le_compat_l.
        apply PeanoNat.Nat.mul_le_mono_nonneg_r.
        - apply le_0_n.
        - replace c1 with (snd (Empty_Cursor (A := o1), c1)); [ | trivial].
          rewrite <- Hnc1; apply Cursor.ubound_next_Empty; [assumption | ].
          rewrite Hnc1; trivial.
      }
  + intros v1 lv1 Hvc1 Abs; discriminate Abs.
- intro Abs; discriminate Abs. 
- case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
  destruct r1 as [e1 | | ]; simpl.
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
    destruct r2 as [e2 | | ].
    * intro Abs; discriminate Abs.
    * intro Abs; discriminate Abs.
    * intros _; simpl.
      {
        apply Le.le_trans with (Cursor.ubound (outer c) * S (Cursor.ubound (Cursor.reset (inner c)))).
        - apply Le.le_trans with (S (Cursor.ubound c1) * S (Cursor.ubound (Cursor.reset (inner c)))).
          + simpl. replace (S
    (Cursor.ubound (Cursor.reset (inner c)) +
     Cursor.ubound c1 * S (Cursor.ubound (Cursor.reset (inner c))))) with
    (Cursor.ubound (Cursor.reset (inner c)) +
     (S (Cursor.ubound c1 * S (Cursor.ubound (Cursor.reset (inner c)))))) by lia.
            apply Plus.plus_le_compat.
            * replace c2' with (snd (Empty_Cursor (A := o2), c2')); [ | trivial].
              rewrite <- Hnc2'; apply Cursor.ubound_next_Empty; [apply Cursor.reset_coherent | ].
              rewrite Hnc2'; trivial.
            * replace c2' with (snd (Empty_Cursor (A := o2), c2')); [ | trivial].
              rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset.
              lia.
              apply Cursor.reset_coherent.
          + apply PeanoNat.Nat.mul_le_mono_nonneg_r.
            * apply le_0_n.
            * replace c1 with (snd (Result e1, c1)); [ | trivial].
              rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
              rewrite Hnc1; discriminate.
        - apply Plus.le_plus_r.
      }
  + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
    destruct r2 as [e2 | | ]; try discriminate.
    intros _; simpl.
    apply Plus.plus_le_compat.
    * replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
      rewrite <- Hnc2, Cursor.ubound_next_Empty; [apply le_n | assumption | ].
      rewrite Hnc2; trivial.
    * {
        apply PeanoNat.Nat.mul_le_mono_nonneg.
        - apply le_0_n.
        - replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
          rewrite <- Hnc1; apply Lt.lt_le_weak; apply Cursor.ubound_next_not_Empty; [assumption | ].
          rewrite Hnc1; discriminate.
        - apply le_0_n.
        - replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
          rewrite <- Hnc2, Cursor.next_reset; [apply le_n | assumption].
      }
  + intros _; apply Plus.plus_le_compat.
    * replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
      rewrite <- Hnc2, Cursor.ubound_next_Empty; [apply le_n | assumption | ].
      rewrite Hnc2; trivial.
    * apply PeanoNat.Nat.mul_le_mono_nonneg_l; [apply le_0_n | ].
      replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
      rewrite <- Hnc2, Cursor.next_reset; [apply le_n | trivial].
Qed.

Lemma ubound_next_not_Empty :
  forall c, coherent c -> fst (next c) <> Empty_Cursor -> ubound (snd (next c)) < ubound c.
Proof.
intros c Hc; destruct Hc as [Hc1 [Hc2 Hc]].
unfold next, ubound.
case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2.
destruct r2 as [e2 | | ].
- assert (Hb2 : Cursor.ubound (snd (Cursor.next (inner c))) < Cursor.ubound (inner c)).
  {
    apply (Cursor.ubound_next_not_Empty _ _ Hc2).
    rewrite Hnc2; discriminate.
  }
  rewrite Hnc2 in Hb2; simpl in Hb2.
  case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc.
    case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ].
    * simpl; intros _.
      {
        apply Plus.plus_lt_le_compat; [assumption | ].
        replace c2 with (snd (Result e2, c2)); [ | trivial].
        rewrite <- Hnc2, Cursor.next_reset; trivial.
        apply Mult.mult_le_compat_r.
        replace c1 with (snd (Result e1, c1)); [ | trivial].
        rewrite <- Hnc1.
        apply Lt.lt_le_weak; apply (Cursor.ubound_next_not_Empty _ _ Hc1).
        rewrite Hnc1; discriminate.
      }
    * simpl; intros _.
      {
        apply Plus.plus_le_lt_compat; [apply le_n | ].
        apply Mult.mult_lt_compat_r.
        - replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
          rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
          rewrite Hnc1; discriminate.
        - lia.
      }
    *  intro Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros v1 lv1 Hcv1 _; simpl.
    apply Plus.plus_lt_le_compat; [apply Hb2 | ].
    replace c2 with (snd (Result e2, c2)); [ | trivial].
    rewrite <- Hnc2, Cursor.next_reset; [apply le_n | trivial].
- assert (Hb2 : Cursor.ubound (snd (Cursor.next (inner c))) < Cursor.ubound (inner c)).
  {
    apply (Cursor.ubound_next_not_Empty _ _ Hc2).
    rewrite Hnc2; discriminate.
  }
  rewrite Hnc2 in Hb2; simpl in Hb2.
  intros _; simpl.
  apply Plus.plus_lt_le_compat; [assumption | ].
  apply Mult.mult_le_compat_l.
  replace c2 with (snd (No_Result (A := o2), c2)); [ | trivial].
  rewrite <- Hnc2, Cursor.next_reset; trivial.
- case_eq (Cursor.visited (outer c)).
  + intro Hvc1; rewrite Hvc1 in Hc.
    case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ].
    * case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
      {
        destruct r2 as [e2 | | ].
        - simpl; intros _.
          apply Lt.lt_le_trans with (Cursor.ubound (outer c) * (S (Cursor.ubound (Cursor.reset (inner c))))).
          + apply Lt.lt_le_trans with
                (Cursor.ubound (Cursor.reset (inner c)) + Cursor.ubound c1 * (S (Cursor.ubound (Cursor.reset c2')))).
            * apply Plus.plus_lt_compat_r.
              replace c2' with (snd (Result e2, c2')); [ | trivial].
              rewrite <- Hnc2'.
              apply Cursor.ubound_next_not_Empty; [apply Cursor.reset_coherent | ].
              rewrite Hnc2'; discriminate.
            * replace c2' with (snd (Result e2, c2')); [ | trivial].
              rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset; 
                [ | apply Cursor.reset_coherent].
              apply Le.le_trans with (S (Cursor.ubound c1) * (S (Cursor.ubound (Cursor.reset (inner c)))));
                [simpl; lia | ].
              apply Mult.mult_le_compat_r.
              replace c1 with (snd (Result e1, c1)); [ | trivial].
              rewrite <- Hnc1.
              apply (Cursor.ubound_next_not_Empty _ _ Hc1).
              rewrite Hnc1; discriminate.
          + apply Plus.le_plus_r.
        - simpl; intros _.
          apply Lt.lt_le_trans with (Cursor.ubound (outer c) * (S (Cursor.ubound (Cursor.reset (inner c))))).
          + apply Lt.lt_le_trans with
                (Cursor.ubound (Cursor.reset (inner c)) + Cursor.ubound c1 * (S (Cursor.ubound (Cursor.reset c2')))).
            * apply Plus.plus_lt_compat_r.
              replace c2' with (snd (No_Result (A := o2), c2')); [ | trivial].
              rewrite <- Hnc2'.
              apply Cursor.ubound_next_not_Empty; [apply Cursor.reset_coherent | ].
              rewrite Hnc2'; discriminate.
            * replace c2' with (snd (No_Result (A := o2), c2')); [ | trivial].
              rewrite <- Hnc2', Cursor.next_reset, Cursor.reset_reset; 
                [ | apply Cursor.reset_coherent].
              apply Le.le_trans with (S (Cursor.ubound c1) * (S (Cursor.ubound (Cursor.reset (inner c)))));
                [simpl; lia | ].
              apply Mult.mult_le_compat_r.
              replace c1 with (snd (Result e1, c1)); [ | trivial].
              rewrite <- Hnc1.
              apply (Cursor.ubound_next_not_Empty _ _ Hc1).
              rewrite Hnc1; discriminate.
          + apply Plus.le_plus_r.
        - intro Abs; apply False_rec; apply Abs; apply refl_equal.
      }
    * case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
      {
        destruct r2 as [e2 | | ].
        - simpl; intros _. 
          apply Plus.plus_le_lt_compat.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2; apply Cursor.ubound_next_Empty; trivial.
            rewrite Hnc2; trivial.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2, Cursor.next_reset; trivial.
            apply Mult.mult_lt_compat_r.
            * replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
              rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
              rewrite Hnc1; discriminate.
            * lia.
        - simpl; intros _. 
          apply Plus.plus_le_lt_compat.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2; apply Cursor.ubound_next_Empty; trivial.
            rewrite Hnc2; trivial.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2, Cursor.next_reset; trivial.
            apply Mult.mult_lt_compat_r.
            * replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
              rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
              rewrite Hnc1; discriminate.
            * lia.
        - intro Abs; apply False_rec; apply Abs; apply refl_equal.
      }
    * intro Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros v1 lv1 Hcv1 H; simpl.
    case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ].
    * {
        case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'.
        assert (H2 : Cursor.ubound (Cursor.reset c2') = Cursor.ubound (Cursor.reset (inner c))).
        {
          replace c2' with (snd (r2, c2')); [ | trivial].
          rewrite <- Hnc2'.
          rewrite Cursor.next_reset, Cursor.reset_reset; trivial.
          apply Cursor.reset_coherent.
        }
        destruct r2 as [e2 | | ].
        - simpl.
          apply Lt.lt_le_trans with  (Cursor.ubound (outer c) * (S (Cursor.ubound (Cursor.reset (inner c))))).
          + rewrite H2.
            apply Lt.lt_le_trans with (Cursor.ubound (Cursor.reset (inner c)) + 
                                        Cursor.ubound c1 * (S (Cursor.ubound (Cursor.reset (inner c))))).
            * apply Plus.plus_lt_le_compat; [ | apply le_n].
              replace c2' with (snd (Result e2, c2')); [ | trivial].
              rewrite <- Hnc2'.
              apply Cursor.ubound_next_not_Empty; [apply Cursor.reset_coherent | ].
              rewrite Hnc2'; discriminate.
            * apply Le.le_trans with (S (Cursor.ubound c1) * (S (Cursor.ubound (Cursor.reset (inner c))))); 
                 [simpl; lia | ].
               apply Mult.mult_le_compat_r.
               replace c1 with (snd (Result e1, c1)); [ | trivial].
               rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
               rewrite Hnc1; discriminate.
          + apply Plus.le_plus_r.
        - simpl.
          apply Lt.lt_le_trans with  (Cursor.ubound (outer c) * (S (Cursor.ubound (Cursor.reset (inner c))))).
          + rewrite H2.
            apply Lt.lt_le_trans with (Cursor.ubound (Cursor.reset (inner c)) + 
                                        Cursor.ubound c1 * (S (Cursor.ubound (Cursor.reset (inner c))))).
            * apply Plus.plus_lt_le_compat; [ | lia].
              replace c2' with (snd (No_Result (A := o2), c2')); [ | trivial].
              rewrite <- Hnc2'.
              apply Cursor.ubound_next_not_Empty; [apply Cursor.reset_coherent | ].
              rewrite Hnc2'; discriminate.
            * apply Le.le_trans with (S (Cursor.ubound c1) * (S (Cursor.ubound (Cursor.reset (inner c))))); 
                 [simpl; lia | ].
               apply Mult.mult_le_compat_r.
               replace c1 with (snd (Result e1, c1)); [ | trivial].
               rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
               rewrite Hnc1; discriminate.
          + apply Plus.le_plus_r.
        - rewrite Hnc1, Hnc2' in H; apply False_rec; apply H; apply refl_equal.
      }
    * rewrite Hnc1 in H.
      case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'; rewrite Hnc2' in H.
      assert (H2 : Cursor.ubound (Cursor.reset c2) = Cursor.ubound (Cursor.reset (inner c))).
      {
        replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
        rewrite <- Hnc2.
        rewrite Cursor.next_reset; trivial.
      }
      {
        destruct r2 as [e2 | | ].
        - simpl.
          apply Plus.plus_le_lt_compat.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2; apply Cursor.ubound_next_Empty; [assumption | ].
            rewrite Hnc2; trivial.
          + rewrite H2.
            apply Mult.mult_lt_compat_r.
            * replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
              rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
              rewrite Hnc1; discriminate.
            * lia.
        - simpl.
          apply Plus.plus_le_lt_compat.
          + replace c2 with (snd (Empty_Cursor (A := o2), c2)); [ | trivial].
            rewrite <- Hnc2; apply Cursor.ubound_next_Empty; [assumption | ].
            rewrite Hnc2; trivial.
          + rewrite H2.
            apply Mult.mult_lt_compat_r.
            * replace c1 with (snd (No_Result (A := o1), c1)); [ | trivial].
              rewrite <- Hnc1; apply Cursor.ubound_next_not_Empty; [assumption | ].
              rewrite Hnc1; discriminate.
            * lia.
        - apply False_rec; apply H; apply refl_equal.
      }
    * rewrite Hnc1 in H.
      apply False_rec; apply H; apply refl_equal.
Qed.

(*
Lemma ubound_reset :
  forall c, coherent c -> ubound c <= ubound (reset c).
Proof.
intros c Hc; unfold coherent in Hc; destruct Hc as [Hc1 [Hc2 Hc]].
unfold ubound.
apply Plus.plus_le_compat.
- apply Cursor.ubound_reset; assumption.
- apply Mult.mult_le_compat.
  + apply Cursor.ubound_reset; assumption.
  + apply Cursor.ubound_reset; apply Cursor.reset_coherent.
Qed.
*)

Lemma ubound_complete res :
forall (c : cursor) (f : o -> res -> res) (acc : res),
  coherent c -> forall p : nat, ubound c <= p -> ~ has_next (fst (iter next p c f acc)).
Proof.
intros c f acc Hc p Hp.
rewrite has_next_next_neg; [ | apply coherent_iter; assumption].
intro H; elim H; clear H.
{
  (* rewrite (fst_iter_eq next p c f acc cons (visited c)). *)
  revert c Hp Hc acc; induction p as [ | n]; 
    intros c Hn Hc acc.
  - simpl in Hc; destruct Hc as [Hc1 [Hc2 Hc]].
    unfold next; unfold ubound in Hn; simpl.
    case_eq (Cursor.ubound (inner c)).
    + intro H2; rewrite H2 in Hn; simpl in Hn.
      assert (K2 : ~ Cursor.has_next (fst (iter Cursor.next 0 (inner c) cons nil))).
      {
        apply (Cursor.ubound_complete (c := inner c) cons nil Hc2 0).
        rewrite H2; apply le_n.
      }
      simpl in K2; rewrite Cursor.has_next_next in K2; [ | assumption].
      case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2; rewrite Hnc2 in K2; simpl in K2; subst r2.
      case_eq (Cursor.ubound (outer c)).
      * intro H1.
        assert (K1 : ~ Cursor.has_next (fst (iter Cursor.next 0 (outer c) cons nil))).
        {
          apply (Cursor.ubound_complete (c := outer c) cons nil Hc1 0).
          rewrite H1; apply le_n.
        }
        simpl in K1; rewrite Cursor.has_next_next in K1; [ | assumption].
        case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1; rewrite Hnc1 in K1; simpl in K1; subst r1.
        apply refl_equal.
      * intros n1 H1; rewrite H1 in Hn.
        {
          case_eq (Cursor.ubound (Cursor.reset (inner c))).
          - intro H2'.
            assert (K2' : ~ Cursor.has_next (fst (iter Cursor.next 0 (Cursor.reset (inner c)) 
                                                       cons nil))).
            {
              apply (Cursor.ubound_complete (c := Cursor.reset (inner c)) 
                                            cons nil
                                            (Cursor.reset_coherent _) 0).
              rewrite H2'; apply le_n.
            }
            simpl in K2'; rewrite Cursor.has_next_next in K2'; [ | apply Cursor.reset_coherent].
            case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
            destruct r1 as [e1 | | ].
            + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'; rewrite Hnc2' in K2'.
              simpl in K2'; subst r2.
              apply refl_equal.
            + case_eq (Cursor.next (Cursor.reset (inner c))); intros r2 c2' Hnc2'; rewrite Hnc2' in K2'.
              simpl in K2'; subst r2.
              apply refl_equal.
            + apply refl_equal.
          - intros n2' H2'; rewrite H2' in Hn; simpl in Hn; inversion Hn.
        }
    + intros n2 H2; rewrite H2 in Hn; simpl in Hn; inversion Hn.
  - case_eq (next c); intros r c' Hnc; destruct r as [e | | ].
    + assert (Aux : ubound (snd (next c)) < ubound c).
      {
        apply (ubound_next_not_Empty Hc); rewrite Hnc; discriminate.
      }
      rewrite Hnc in Aux; simpl in Aux.
      replace (S n) with (n + 1); [ | rewrite PeanoNat.Nat.add_comm; trivial].
      unfold iter; rewrite nat_iter_plus; simpl Nat.iter at 2; rewrite Hnc.
      assert (IH : fst (next (fst (iter next n c' f (f e acc)))) = Empty_Cursor).
      {
        apply (IHn c').
        - apply le_S_n.
          refine (Le.le_trans _ _ _ Aux Hn).
        - generalize (next_coherent Hc); rewrite Hnc; exact (fun h => h).
      }
      unfold iter in IH; rewrite IH; trivial.
    + assert (Aux : ubound (snd (next c)) < ubound c).
      {
        apply (ubound_next_not_Empty Hc); rewrite Hnc; discriminate.
      }
      rewrite Hnc in Aux; simpl in Aux.
      replace (S n) with (n + 1); [ | rewrite PeanoNat.Nat.add_comm; trivial].
      unfold iter; rewrite nat_iter_plus; simpl Nat.iter at 2; rewrite Hnc.
      assert (IH : fst (next (fst (iter next n c' f acc))) = Empty_Cursor).
      {
        apply (IHn c').
        - apply le_S_n.
          refine (Le.le_trans _ _ _ Aux Hn).
        - generalize (next_coherent Hc); rewrite Hnc; exact (fun h => h).
      }
      unfold iter in IH; rewrite IH; trivial.
    + apply (iter_Empty_Cursor coherent _ next_coherent next_Empty_Cursor _ _ _ _ Hc).
      rewrite Hnc; trivial.
}
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
- apply reset_next.
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
End NestedLoop.
