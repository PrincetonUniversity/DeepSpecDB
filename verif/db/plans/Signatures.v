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

Require Import BasicFacts OrderedSet.

Set Implicit Arguments.

Inductive result (A : Type) :=
| Result: A -> result A
| No_Result: result A
| Empty_Cursor: result A.

Lemma not_not_empty_cursor :
  forall (A : Type) (r : result A), ~ r <> Empty_Cursor _ -> r = Empty_Cursor _.
Proof.
intros A r H.
destruct r as [a | | ]; trivial.
- apply False_rec; apply H; discriminate.
- apply False_rec; apply H; discriminate.
Qed.

Arguments No_Result {_}.
Arguments Empty_Cursor {_}.

Definition iter (elt cursor res : Type) (next : cursor -> result elt * cursor) n c (f:elt -> res -> res) (acc:res) := 
  Nat.iter n (fun (c'l : cursor * res) =>
                let (c',l) := c'l in
                let (r, c'') := next c' in
                let l' :=
                    match r with
                    | Result r' => f r' l
                    | No_Result => l
                    | _ => l
                    end in
                (c'', l')) (c,acc).

Lemma fst_iter_eq :
  forall elt cursor res next n c f1 acc1 f2 acc2,
    fst (@iter elt cursor res next n c f1 acc1) = fst (@iter elt cursor res next n c f2 acc2).
Proof.
intros elt cursor res next n; induction n as [ | n]; intros c f1 acc1 f2 acc2; [apply refl_equal | ].
simpl.
assert (IH := IHn c f1 acc1 f2 acc2).
case_eq (iter next n c f1 acc1); intros c1' l1 H1.
case_eq (iter next n c f2 acc2); intros c2' l2 H2.
rewrite H1, H2 in IH; simpl in IH; subst c2'.
destruct (next c1'); apply refl_equal.
Qed.

Lemma iter_Empty_Cursor :
  forall (elt cursor res : Type) coherent (next : cursor -> result elt * cursor),
    (forall c, coherent c -> coherent (snd (next c))) -> 
    (forall c, coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor) ->
    forall n (c : cursor) (f:elt -> res -> res) acc, coherent c -> fst (next c) = Empty_Cursor ->
                               fst (next (fst (iter next n c f acc))) = Empty_Cursor.
Proof.
intros elt cursor res coherent next next_coherent next_Empty_Cursor.
intro n; induction n as [ | n]; intros c f acc Hc H.
- case_eq (next c); intros r c' Hnc; rewrite Hnc in H; simpl in H; subst r.
  simpl; rewrite Hnc; trivial.
- replace (S n) with (n + 1); [ | rewrite PeanoNat.Nat.add_comm; trivial].
  unfold iter; rewrite nat_iter_plus; simpl Nat.iter at 2.
  case_eq (next c); intros r c' Hnc; rewrite Hnc in H; simpl in H; subst r.
  assert (IH : fst (next (fst (iter next n c' f acc))) = Empty_Cursor).
  {
    apply IHn.
    - generalize (next_coherent _ Hc); rewrite Hnc; exact (fun h => h).
    - generalize (next_Empty_Cursor _ Hc); rewrite Hnc; simpl.
      intro H; apply H; apply refl_equal.
  }
  unfold iter in IH; apply IH.
Qed.

Module Cursor.
Record Rcd (elt : Type) (Elt : Oeset.Rcd elt) : Type :=
  mk_R
    {
      cursor : Type;

      collection : cursor -> list elt;
      visited : cursor -> list elt;
      coherent : cursor -> Prop;
      visited_collection : 
        forall c, coherent c -> 
                  forall x, Oeset.mem_bool Elt x (visited c) = true -> 
                            Oeset.mem_bool Elt x (collection c) = true;

      reset : cursor -> cursor;
      (* reset preserves the collection *)
      reset_collection : forall c, collection (reset c) = collection c;
      (* reset restarts the visited elements of the cursor *)
      reset_visited : forall c, visited (reset c) = nil;
      (* reset returns a coherent cursor *)
      reset_coherent : forall c, coherent (reset c);

      next : cursor -> result elt * cursor;
      (* next preserves the collection *)
      next_collection : forall c c' opt,
          coherent c -> next c = (opt, c') -> collection c' = collection c;
      (* next adds the returned element to visited *)
      next_visited_Result : forall a c c',
          coherent c -> next c = (Result a, c') -> visited c' = a :: (visited c);
      next_visited_No_Result : forall c c',
          coherent c -> next c = (No_Result, c') -> visited c' = visited c;
      next_visited_Empty_Cursor : forall c c',
          coherent c -> next c = (Empty_Cursor, c') -> visited c' = visited c;
      (* next preserves coherence *)
      next_coherent : forall c, coherent c -> coherent (snd (next c));
      next_Empty_Cursor : 
        forall c, coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor;
      next_reset : forall c, coherent c -> reset (snd (next c)) = reset c;

      has_next : cursor -> Prop;
      (* when a cursor has no element left, visited contains all the
         elements of the collection *)
      has_next_spec : 
        forall c, coherent c -> ~ has_next c -> 
                  comparelA (Oeset.compare Elt) (collection c) (rev (visited c)) = Eq;
      (* a cursor has new elements if and only if next may return something *)
      has_next_next_neg : forall c,
          coherent c -> (has_next c <-> fst (next c) <> Empty_Cursor);

      empty_cursor : cursor;
      empty_cursor_collection : collection empty_cursor = nil;
      empty_cursor_coherent : coherent empty_cursor;
      empty_cursor_has_next : ~ has_next empty_cursor;

      (* an upper bound on the number of iterations before the cursor
         has been fully visited *)
      ubound : cursor -> nat;
      reset_reset : forall c, reset (reset c) = reset c;
      ubound_next_Empty : 
        forall c, coherent c -> fst (next c) = Empty_Cursor ->
                  ubound (snd (next c)) <= ubound c;
      ubound_next_not_Empty: 
        forall c, coherent c -> fst (next c) <> Empty_Cursor ->
                  ubound (snd (next c)) < ubound c;
      (* ubound_reset : *)
      (*   forall c, coherent c -> ubound c <= ubound (reset c); *)
      (* this upper bound is indeed complete *)
      ubound_complete : 
        forall res c (f:elt -> res -> res) acc, coherent c -> forall p, ubound c <= p -> ~ has_next (fst (iter next p c f acc));
    }.

Arguments cursor {elt} {Elt} r.
Arguments next {elt} {Elt} {r} c.
Arguments reset {elt} {Elt} {r} c.
Arguments ubound {elt} {Elt} {r} c.
Arguments collection {elt} {Elt} {r} c.
Arguments visited {elt} {Elt} {r} c.
Arguments coherent {elt} {Elt} {r} c.
Arguments visited_collection {elt} {Elt} {r} c.
Arguments has_next {elt} {Elt} {r} c.
Arguments reset_visited {elt} {Elt} {r} c.
Arguments reset_coherent {elt} {Elt} {r} c.
Arguments ubound_complete {elt} {Elt} {r} {res} {c} f acc h.
Arguments has_next_spec {elt} {Elt} {r} {c} h1 h2.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.
Hypothesis C : Rcd OA.


  (* General properties *)

  Lemma empty_collection : forall (c : cursor C),
      coherent c -> (collection c) = nil -> (visited c) = nil.
  Proof.
    intros c Hc Hcol. case_eq (visited c); trivial.
    intros y l Heq. 
    assert (Oeset.mem_bool OA y (visited c) = true).
    {
      rewrite Heq, Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
    }
    generalize (visited_collection _ Hc _ H); rewrite Hcol; discriminate.
  Qed.

  Lemma has_next_next : forall (c : cursor C),
      coherent c -> (~ has_next c <-> fst (next c) = Empty_Cursor).
  Proof.
    intros c Hc; split; intro H.
    - case_eq (fst (next c)); auto.
      * intros t Ht. elim H. rewrite has_next_next_neg; auto.
        rewrite Ht. discriminate.
      * intros Ht. elim H. rewrite has_next_next_neg; auto.
        rewrite Ht. discriminate.
    - intro H1. rewrite has_next_next_neg in H1; auto.
  Qed.

  Lemma visited_nil_next_empty :
    forall (c : cursor C), coherent c -> visited c = nil -> fst (next c) = Empty_Cursor ->
              collection c = nil.
    Proof.
      intros c Hc H1 H2.
      assert (H3 : ~ has_next c).
      {
        rewrite has_next_next, H2; trivial.
      }
      assert (H := has_next_spec Hc H3).
      rewrite H1 in H.
      destruct (collection c); [trivial | discriminate H].
    Qed.

  (* Properties of iter *)

  Lemma iter_coherent res n : forall (c : cursor C) (f:A -> res -> res) acc,
      coherent c -> coherent (fst (iter next n c f acc)).
  Proof.
    induction n as [ |n IHn]; auto.
    intros c f acc Hc. unfold iter in *. rewrite nat_iter_succ_r.
    case_eq (next c). intros r c'' Heq.
    apply IHn. apply next_coherent in Hc. now rewrite Heq in Hc.
  Qed.

  Lemma iter_collection res n : forall (c : cursor C) (f:A -> res -> res) acc,
      coherent c -> collection (fst (iter next n c f acc)) = collection c.
  Proof.
    induction n as [ |n IHn]; auto.
    intros c f acc Hc. unfold iter in *. rewrite nat_iter_succ_r.
    case_eq (next c). intros r c'' Heq.
    rewrite IHn.
    - eapply next_collection; eauto.
    - apply next_coherent in Hc. now rewrite Heq in Hc.
  Qed.

  Lemma iter_visited_gen res (f:A -> res -> res) n :
    forall acc (c : cursor C),
      coherent c ->
      let (c',l') := iter next n c f (List.fold_right f acc (visited c)) in
      (List.fold_right f acc (visited c')) = l'.
  Proof.
    induction n as [ |n IHn].
    - simpl. reflexivity.
    - intros acc c Hc. unfold iter. rewrite nat_iter_succ_r.
      case_eq (next c). intros r c'' Heq.
      change (Nat.iter n
      (fun c'l : cursor C * res =>
       let (c', l) := c'l in
       let (r0, c''0) := next c' in
       (c''0,
       match r0 with
       | Result r' => f r' l
       | No_Result => l
       | Empty_Cursor => l
       end))
      (c'',
      match r with
      | Result r' => f r' (fold_right f acc (visited c))
      | No_Result => fold_right f acc (visited c)
      | Empty_Cursor => fold_right f acc (visited c)
      end)) with (iter next n c'' f (match r with
      | Result r' => f r' (fold_right f acc (visited c))
      | No_Result => fold_right f acc (visited c)
      | Empty_Cursor => fold_right f acc (visited c)
      end)).
      assert (Hc'': coherent c'') by (apply next_coherent in Hc; now rewrite Heq in Hc).
      assert (Hc''v: visited c'' = match r with
                                     | Result r' => r' :: visited c
                                     | No_Result => visited c
                                     | Empty_Cursor => visited c
                                     end).
      {
        case_eq r; [intro t| | ]; intro; subst r.
        - now apply next_visited_Result.
        - now apply next_visited_No_Result.
        - now apply next_visited_Empty_Cursor.
      }
      generalize (IHn acc _ Hc''). rewrite Hc''v. case r; intros; auto.
  Qed.


  Lemma iter_visited n : 
    forall (c : cursor C), 
      coherent c -> let (c',l') := iter next n c cons (visited c) in visited c' = l'.
  Proof.
    induction n as [ |n IHn]; auto.
    - reflexivity.
    - intros c Hc. unfold iter in *. rewrite nat_iter_succ_r.
      case_eq (next c). intros r c'' Heq.
      assert (Hc'': coherent c'') by (apply next_coherent in Hc; now rewrite Heq in Hc).
      assert (Hc''v: visited c'' = match r with
                                     | Result r' => r' :: visited c
                                     | No_Result => visited c
                                     | Empty_Cursor => visited c
                                     end).
      + case_eq r; [intro t| | ]; intro; subst r.
        * now apply next_visited_Result.
        * now apply next_visited_No_Result.
        * now apply next_visited_Empty_Cursor.
      + generalize (IHn _ Hc''). now rewrite Hc''v.
  Qed.


  Lemma iter_empty acc n : forall (c : cursor C),
    coherent c ->
    fst (Cursor.next c) = Empty_Cursor ->
    snd (iter Cursor.next n c cons acc) = acc.
  Proof.
    induction n as [ |n IHn]; intros c Hc H; auto.
    unfold iter. rewrite nat_iter_succ_r.
    case_eq (next c). intros r c' Heq2. rewrite Heq2 in H. simpl in H. subst r.
    change (Nat.iter n
       (fun c'l : cursor C * list A =>
        let (c'0, l) := c'l in
        let (r, c'') := next c'0 in
        (c'',
        match r with
        | Result r' => r' :: l
        | No_Result => l
        | Empty_Cursor => l
        end)) (c', acc)) with (iter next n c' cons acc).
    case_eq (next c'). intros r c0 Heq.
    assert (H1:fst (next c) = Empty_Cursor) by now rewrite Heq2.
    generalize (next_Empty_Cursor _ _ Hc H1). rewrite Heq2. simpl. rewrite Heq. simpl. intro; subst r.
    apply IHn.
    - generalize (next_coherent _ _ Hc). now rewrite Heq2.
    - now rewrite Heq.
  Qed.


  Lemma iter_app n : forall (c : cursor C) acc1 acc2,
    snd (iter Cursor.next n c cons (acc1 ++ acc2)) = (snd (iter Cursor.next n c cons acc1)) ++ acc2.
  Proof.
    induction n as [ |n IHn]; auto.
    intros c acc1 acc2. unfold iter. rewrite !nat_iter_succ_r.
    case_eq (next c); intros r c'' Heq.
    change (Nat.iter n
       (fun c'l : cursor C * list A =>
        let (c', l) := c'l in
        let (r0, c''0) := next c' in
        (c''0,
        match r0 with
        | Result r' => r' :: l
        | No_Result => l
        | Empty_Cursor => l
        end))
       (c'',
       match r with
       | Result r' => r' :: acc1 ++ acc2
       | No_Result => acc1 ++ acc2
       | Empty_Cursor => acc1 ++ acc2
       end)) with (iter Cursor.next n c'' cons (match r with
       | Result r' => r' :: acc1 ++ acc2
       | No_Result => acc1 ++ acc2
       | Empty_Cursor => acc1 ++ acc2
       end)).
    change (Nat.iter n
       (fun c'l : cursor C * list A =>
        let (c', l) := c'l in
        let (r0, c''0) := next c' in
        (c''0,
        match r0 with
        | Result r' => r' :: l
        | No_Result => l
        | Empty_Cursor => l
        end))
       (c'',
       match r with
       | Result r' => r' :: acc1
       | No_Result => acc1
       | Empty_Cursor => acc1
       end)) with (iter Cursor.next n c'' cons (match r with
       | Result r' => r' :: acc1
       | No_Result => acc1
       | Empty_Cursor => acc1
       end)).
    case r; [intro a; change (a :: acc1 ++ acc2) with ((a::acc1) ++ acc2)| | ]; apply IHn.
  Qed.

  Lemma iter_nil n : forall (c : cursor C) acc,
    snd (iter Cursor.next n c cons acc) = (snd (iter Cursor.next n c cons nil)) ++ acc.
  Proof.
    intros c acc. change acc with (nil ++ acc) at 1. now apply iter_app.
  Qed.


  Lemma iter_le n1 : forall n2, n2 <= n1 -> forall (c:cursor C),
    exists l, snd (iter Cursor.next n1 c cons nil) = l ++ snd (iter Cursor.next n2 c cons nil).
  Proof.
    induction n1 as [ |n1 IHn1]; intros n2 Hn2 c.
    - assert (n2 = 0) by lia. subst n2. simpl. now exists nil.
    - case_eq n2.
      + intro; subst n2.
        change (snd (iter next 0 c cons nil)) with (@nil A).
        now exists (snd (iter next (S n1) c cons nil)); rewrite app_nil_r.
      + intros p Hp; subst n2. assert (Hp:p <= n1) by lia.
        unfold iter. rewrite !nat_iter_succ_r.
        case_eq (next c). intros r c'' Heq.
        change (Nat.iter n1
         (fun c'l : cursor C * list A =>
          let (c', l0) := c'l in
          let (r0, c''0) := next c' in
          (c''0,
          match r0 with
          | Result r' => r' :: l0
          | No_Result => l0
          | Empty_Cursor => l0
          end))
         (c'',
         match r with
         | Result r' => r' :: nil
         | No_Result => nil
         | Empty_Cursor => nil
         end)) with (iter Cursor.next n1 c'' cons (match r with
         | Result r' => r' :: nil
         | No_Result => nil
         | Empty_Cursor => nil
         end)).
        change (Nat.iter p
         (fun c'l : cursor C * list A =>
          let (c', l0) := c'l in
          let (r0, c''0) := next c' in
          (c''0,
          match r0 with
          | Result r' => r' :: l0
          | No_Result => l0
          | Empty_Cursor => l0
          end))
         (c'',
         match r with
         | Result r' => r' :: nil
         | No_Result => nil
         | Empty_Cursor => nil
         end)) with (iter Cursor.next p c'' cons (match r with
         | Result r' => r' :: nil
         | No_Result => nil
         | Empty_Cursor => nil
         end)).
        destruct (IHn1 _ Hp c'') as [l' Hl'].
        rewrite !(iter_nil _ _ (match r with
         | Result r' => r' :: nil
         | No_Result => nil
         | Empty_Cursor => nil
         end)), Hl'.
        rewrite <- app_assoc. now exists l'.
  Qed.


  (* Materialize *)

  Definition materialize (c : cursor C) :=
    let c' := reset c in
    List.rev (snd (iter next (ubound c') c' cons nil)).

  Lemma materialize_collection c :
    comparelA (Oeset.compare OA) (materialize c) (collection c) = Eq.
  Proof.
    unfold materialize.
    assert (Hr := reset_coherent c).
    assert (H := ubound_complete cons nil Hr _ (le_n _)).
    apply (has_next_spec (iter_coherent _ _ cons nil Hr)) in H.
    rewrite iter_collection in H; trivial.
    rewrite reset_collection in H.
    rewrite comparelA_lt_gt, CompOpp_iff.
    - refine (comparelA_eq_trans _ _ _ _ _ H _).
      + do 6 intro; apply Oeset.compare_eq_trans.
      + apply comparelA_rev_eq.
        case_eq (iter next (ubound (reset c)) (reset c) cons nil). intros c' l' Heq. simpl.
        generalize (iter_visited (ubound (reset c)) _ Hr).
        rewrite (reset_visited c), Heq. 
        apply comparelA_eq_refl_alt.
        intros; apply Oeset.compare_eq_refl.
    - intros; apply Oeset.compare_lt_gt.
  Qed.

End Sec.

End Cursor.

Arguments Cursor.cursor {elt} {Elt} r.
Arguments Cursor.next {elt} {Elt} {r} c.
Arguments Cursor.reset {elt} {Elt} {r} c.
Arguments Cursor.ubound {elt} {Elt} {r} c.
Arguments Cursor.collection {elt} {Elt} {r} c.
Arguments Cursor.visited {elt} {Elt} {r} c.
Arguments Cursor.coherent {elt} {Elt} {r} c.
Arguments Cursor.visited_collection {elt} {Elt} {r} c.
Arguments Cursor.has_next {elt} {Elt} {r} c.
Arguments Cursor.reset_visited {elt} {Elt} {r} c.
Arguments Cursor.reset_coherent {elt} {Elt} {r} c.
Arguments Cursor.reset_collection {elt} {Elt} {r} c.
Arguments Cursor.ubound_complete {elt} {Elt} {r} {res} {c} f acc h.
Arguments Cursor.has_next_spec {elt} {Elt} {r} {c} h1 h2.

Module Index.
  Record Rcd (o1 o2 : Type) (O1 : Oeset.Rcd o1) (O2 : Oeset.Rcd o2) : Type :=
  mk_R
    {
      (* projection on the index *)
      proj : o1 -> o2;
      proj_eq :
        forall x y, Oeset.compare O1 x y = Eq -> Oeset.compare O2 (proj x) (proj y) = Eq;
      (* comparison between two indices *)
      P : o2 -> o2 -> bool;
      P_eq_1 : forall x1 x2 y, Oeset.compare O2 x1 x2 = Eq -> P x1 y = P x2 y;
      P_eq_2 : forall x y1 y2, Oeset.compare O2 y1 y2 = Eq -> P x y1 = P x y2;
      C1 : Cursor.Rcd O1;
      (* representation of data *)
      containers : Type;
      (* the elements of a container *)
      c1 : containers -> list o1;
      (* from_list : list o1 -> containers; useless *)
      dummy_containers : containers;
      (* indexing function *)
      i : containers -> o2 -> Cursor.cursor C1;
      (* the collection of an indexed cursor contains the filtered
         elements of the container w.r.t. P *)
      i_collection :
        forall c x, comparelA (Oeset.compare O1)
                              (Cursor.collection (i c x))
                              (filter (fun y => P x (proj y)) (c1 c)) = Eq;
      (* a fresh indexed cursor has not been visited yet *)
      i_visited : forall c x, Cursor.visited (i c x) = nil;
      (* a fresh indexed cursor is coherent *)
      i_coherent : forall c x, Cursor.coherent (i c x)
    }.
End Index.

