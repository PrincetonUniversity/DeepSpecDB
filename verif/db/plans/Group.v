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

Require Import List Psatz NArith.
Require Import BasicFacts OrderedSet.
Require Import Signatures SeqScan.

Set Implicit Arguments.


Section Group.

  Variable elt : Type.
  Variable Elt : Oeset.Rcd elt.
  Variable C : Cursor.Rcd Elt.

  Variable key : Type.
  Variable Key : Oeset.Rcd key.

  Variable proj : elt -> key.
  Variable theta : list elt -> bool.
  Variable build : list elt -> elt.

(*  Fixpoint assoc e ls :=
    match ls with
    | nil => (proj e, (e::nil))::nil
    | (k,l)::ls =>
      match Oeset.compare Key k (proj e) with
      | Eq => (k,e::l)::ls
      | _ => (k,l)::(assoc e ls)
      end
    end.
*)

Notation assoc := (group Key proj).

  Definition group (c : Cursor.cursor C) :=
    let c' := Cursor.reset c in
    SeqScan.mk_seqcursor (
        List.map (fun l => build (snd l))
                 (List.filter
                    (fun l => theta (snd l))
                    (snd (iter Cursor.next (Cursor.ubound c') c' assoc nil))
                 )
      ).


  Hypothesis proj_eq : forall e1 e2,
      Oeset.compare Elt e1 e2 = Eq ->
      Oeset.compare Key (proj e1) (proj e2) = Eq.
  Hypothesis build_eq : forall l1 l2,
    comparelA (Oeset.compare Elt) l1 l2 = Eq ->
    Oeset.compare Elt (build l1) (build l2) = Eq.
  Hypothesis theta_eq : forall l1 l2,
    comparelA (Oeset.compare Elt) l1 l2 = Eq -> theta l1 = theta l2.


  Definition OL : Oeset.Rcd (list elt) := mk_oelists Elt.
  Definition OKL : Oeset.Rcd (key * list elt) := mk_oepairs Key OL.
  Definition OKLleft : Oeset.Rcd (key * list elt) := mk_oepairsleft (list elt) Key.


  Lemma assoc_eq (x1 x2 : elt) (Heqx : Oeset.compare Elt x1 x2 = Eq) :
    forall (y1 y2 : list (key * list elt)),
      comparelA (Oeset.compare OKL) y1 y2 = Eq ->
      comparelA (Oeset.compare OKL) (assoc x1 y1) (assoc x2 y2) = Eq.
  Proof.
    induction y1 as [ |[k1 l1] ys1 IHys1]; intros [ |[k2 l2] ys2]; simpl.
    - intros _. now rewrite (proj_eq _ _ Heqx), Heqx.
    - discriminate.
    - discriminate.
    - case_eq (Oeset.compare Key k1 k2); try discriminate. intro Heqk.
      case_eq (comparelA (Oeset.compare Elt) l1 l2); try discriminate. intros Heql Heqys.
      case_eq (Oeset.compare Key k1 (proj x1)); intro Heq4.
      + replace (Oeset.compare Key k2 (proj x2)) with Eq; simpl.
        * now rewrite Heqk, Heqx, Heql.
        * symmetry. apply (Oeset.compare_eq_trans _ _ k1).
          {
            now apply Oeset.compare_eq_sym.
          }
          {
            apply (Oeset.compare_eq_trans _ _ (proj x1)); trivial.
            now apply proj_eq.
          }
      + replace (Oeset.compare Key k2 (proj x2)) with Lt; simpl.
        * rewrite Heqk, Heql. now apply IHys1.
        * symmetry. apply (Oeset.compare_eq_lt_trans _ _ k1).
          {
            now apply Oeset.compare_eq_sym.
          }
          {
            apply (Oeset.compare_lt_eq_trans _ _ (proj x1)); trivial.
            now apply proj_eq.
          }
      + replace (Oeset.compare Key k2 (proj x2)) with Gt; simpl.
        * rewrite Heqk, Heql. now apply IHys1.
        * symmetry. apply (Oeset.compare_eq_gt_trans _ _ k1).
          {
            now apply Oeset.compare_eq_sym.
          }
          {
            apply (Oeset.compare_gt_eq_trans _ _ (proj x1)); trivial.
            now apply proj_eq.
          }
  Qed.


  Lemma assoc_nb_occ_key e : forall ls,
      (forall p, (Oeset.nb_occ OKLleft p ls <= 1)%N) ->
      forall p,
        (Oeset.compare Key (fst p) (proj e) <> Eq ->
         Oeset.nb_occ OKLleft p (assoc e ls) = Oeset.nb_occ OKLleft p ls)
        /\
        (Oeset.compare Key (fst p) (proj e) = Eq ->
         Oeset.nb_occ OKLleft p (assoc e ls) = 1%N).
  Proof.
    induction ls as [ |[k l] ls IHls]; intros Hls [k' l']; simpl; split; intro H.
    - case_eq (Oeset.compare Key k' (proj e)); auto; try lia.
      intro H'. now elim H.
    - now rewrite H.
    - simpl in Hls. assert (H':forall p : key * list elt, (Oeset.nb_occ OKLleft p ls <= 1)%N).
      {
        intros [k1 l1]. generalize (Hls (k1, l1)). case (compareAl (Oeset.compare Key) (k1, l1) (k, l)); lia.
      }
      assert (IH:=IHls H'). clear IHls. destruct (IH (k', l')) as [IH1 _]. assert (IH':=IH1 H); clear IH1.
      case_eq (Oeset.compare Key k (proj e)); intro Heqk; auto; simpl; now rewrite IH'.
    - simpl in Hls. assert (H':forall p : key * list elt, (Oeset.nb_occ OKLleft p ls <= 1)%N).
      {
        intros [k1 l1]. generalize (Hls (k1, l1)). case (compareAl (Oeset.compare Key) (k1, l1) (k, l)); lia.
      }
      assert (IH:=IHls H'). clear IHls. destruct (IH (k', l')) as [_ IH2]. assert (IH':=IH2 H); clear IH2.
      case_eq (Oeset.compare Key k (proj e)); intro Heqk; simpl.
      + assert (H0:Oeset.compare Key k' k = Eq) by (eauto using Oeset.compare_eq_trans, Oeset.compare_eq_sym).
        rewrite H0. generalize (Hls (k',l')). simpl. rewrite H0. intro H1.
        now replace (Oeset.nb_occ OKLleft (k', l') ls) with 0%N by lia.
      + replace (Oeset.compare Key k' k) with Gt; auto.
        symmetry. rewrite Oeset.compare_lt_gt. apply Oeset.compare_eq_sym in H.
        now rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Heqk H).
      + replace (Oeset.compare Key k' k) with Lt; auto.
        symmetry. rewrite Oeset.compare_lt_gt. apply Oeset.compare_eq_sym in H.
        now rewrite (Oeset.compare_gt_eq_trans _ _ _ _ Heqk H).
  Qed.


  Lemma assoc_nb_occ e ls (Hls: forall p, (Oeset.nb_occ OKLleft p ls <= 1)%N) p :
    (Oeset.nb_occ OKLleft p (assoc e ls) <= 1)%N.
  Proof.
    destruct (assoc_nb_occ_key e ls Hls p) as [H1 H2].
    case_eq (Oeset.compare Key (fst p) (proj e)); intro Heq.
    - now rewrite H2.
    - rewrite H1; auto. now rewrite Heq.
    - rewrite H1; auto. now rewrite Heq.
  Qed.


  Lemma buckets_nb_occ_strong : forall n (c : Cursor.cursor C) acc,
    (forall p, (Oeset.nb_occ OKLleft p acc <= 1)%N) ->
    forall p, (Oeset.nb_occ OKLleft p (snd (iter Cursor.next n c assoc acc)) <= 1)%N.
  Proof.
    induction n as [ |n IHn]; intros c acc Hacc p; auto.
    unfold iter. rewrite nat_iter_succ_r. case_eq (Cursor.next c); intros t c'' Heq.
    change (Nat.iter n
           (fun c'l : Cursor.cursor C * list (key * list elt) =>
            let (c', l) := c'l in
            let (r, c''0) := Cursor.next c' in
            (c''0,
            match r with
            | Result r' => assoc r' l
            | No_Result => l
            | Empty_Cursor => l
            end))
           (c'',
           match t with
           | Result r' => assoc r' acc
           | No_Result => acc
           | Empty_Cursor => acc
           end)) with (iter Cursor.next n c'' assoc (match t with
           | Result r' => assoc r' acc
           | No_Result => acc
           | Empty_Cursor => acc
           end)).
    apply IHn. intro p'. destruct t as [r'| | ]; auto.
    now apply assoc_nb_occ.
  Qed.


  Lemma buckets_nb_occ (c : Cursor.cursor C) n p :
    (Oeset.nb_occ OKLleft p (snd (iter Cursor.next n c assoc nil)) <= 1)%N.
  Proof.
    apply buckets_nb_occ_strong. intros; simpl; lia.
  Qed.


  Lemma buckets_collection q :
    comparelA (Oeset.compare OKL)
              (snd (iter Cursor.next (Cursor.ubound (Cursor.reset q)) (Cursor.reset q) assoc nil))
              (fold_left (fun a e => assoc e a) (Cursor.collection (r:=C) q) nil)
    = Eq.
  Proof.
    assert (Hr := Cursor.reset_coherent q).
    assert (H := Cursor.ubound_complete assoc nil Hr _ (le_n _)).
    apply (Cursor.has_next_spec (Cursor.iter_coherent _ _ _ assoc nil Hr)) in H.
    rewrite Cursor.iter_collection in H; trivial.
    rewrite Cursor.reset_collection in H.
    generalize (Cursor.iter_visited_gen _ assoc (Cursor.ubound (Cursor.reset q)) nil _ (Cursor.reset_coherent q)). rewrite Cursor.reset_visited. simpl.
    case_eq (iter Cursor.next (Cursor.ubound (Cursor.reset q)) (Cursor.reset q) assoc nil); intros c' l' Heq. intro; subst l'.
    simpl. rewrite Heq in H. simpl in H.
    apply (Oeset.compare_eq_sym (mk_oelists OKL)).
    apply (fold_left_rev_right_eq _ Elt); trivial.
    now intros; apply assoc_eq.
  Qed.


  Lemma group_collection q :
    comparelA (Oeset.compare Elt)
              (Cursor.collection (r:=SeqScan.SeqScan.build Elt) (group q))
              (List.map build (List.filter theta (List.map snd (List.fold_left (fun acc e => assoc e acc) (Cursor.collection q) nil))))
    = Eq.
  Proof.
    rewrite ListFacts.filter_map, map_map. unfold group. simpl.
    apply (comparelA_map_eq_2 OKL).
    - intros [k1 l1] [k2 l2]. simpl.
      destruct (Oeset.compare Key k1 k2); try discriminate.
      apply build_eq.
    - apply comparelA_eq_filter.
      + intros [k1 l1] [k2 l2]. simpl. intros _.
        destruct (Oeset.compare Key k1 k2); try discriminate.
        apply theta_eq.
      + apply buckets_collection.
  Qed.

End Group.
