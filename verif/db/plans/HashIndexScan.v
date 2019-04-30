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

Require Import Equalities SetoidList FMaps FMapWeakList.
Require Import OrderedSet ListFacts.
Require Import Signatures SeqScan Filter.

Set Implicit Arguments.


Module Type OESET.
  Parameter o : Type.
  Parameter O : Oeset.Rcd o.
End OESET.


Module HashIndexScan (O1E O2E: OESET).

  Local Notation o1 := O1E.o.
  Local Notation O1 := O1E.O.
  Local Notation o2 := O2E.o.
  Local Notation O2 := O2E.O.

  Module O2M <: DecidableType.
    Definition t : Type := o2.
    Definition eq : o2 -> o2 -> Prop := fun x y => Oeset.compare O2 x y = Eq.
    Definition eq_refl : forall x, eq x x := Oeset.compare_eq_refl _.
    Definition eq_sym : forall x y, eq x y -> eq y x := Oeset.compare_eq_sym _.
    Definition eq_trans : forall x y z, eq x y -> eq y z -> eq x z := Oeset.compare_eq_trans _.
    Lemma eq_dec : forall x y, { eq x y } + { ~ (eq x y) }.
    Proof.
      intros x y; unfold eq. case (Oeset.compare O2 x y); auto; right; discriminate.
    Defined.
  End O2M.

  Module Containers := FMapWeakList.Raw(O2M).

  Module Eqke <: Equalities.EqualityType.
    Definition t := (o2 * list o1)%type.
    Definition eq := @Containers.PX.eqke (list o1).
    Lemma eq_equiv : Equivalence eq. Proof. apply Containers.PX.eqke_equiv. Qed.
  End Eqke.


  Section HashIndexScan.

    Variable C1 : Cursor.Rcd O1.
    Variable unhashed_elem : list o1.
    Variable mk_cursor : list o1 -> Cursor.cursor C1.
    Hypothesis mk_cursor_collection : forall l x,
        Oeset.mem_bool O1 x (Cursor.collection (mk_cursor l)) = true ->
        Oeset.mem_bool O1 x l = true.

    Variable proj : o1 -> o2.
    Hypothesis proj_eq :
      forall x y, Oeset.compare O1 x y = Eq -> Oeset.compare O2 (proj x) (proj y) = Eq.
    (* Definition C1 := SeqScan.build O1. *)

    Definition P : o2 -> o2 -> bool :=
      fun x y => match Oeset.compare O2 x y with Eq => true | _ => false end.
    Lemma P_eq_1 x1 x2 y (H:Oeset.compare O2 x1 x2 = Eq) : P x1 y = P x2 y.
    Proof.
      unfold P. apply Oeset.compare_eq_sym in H. case_eq (Oeset.compare O2 x1 y); intro Heq.
      - now rewrite (Oeset.compare_eq_trans _ _ _ _ H Heq).
      - now rewrite (Oeset.compare_eq_lt_trans _ _ _ _ H Heq).
      - now rewrite (Oeset.compare_eq_gt_trans _ _ _ _ H Heq).
    Qed.
    Lemma P_eq_2 x y1 y2 (H:Oeset.compare O2 y1 y2 = Eq) : P x y1 = P x y2.
    Proof.
      unfold P. case_eq (Oeset.compare O2 x y1); intro Heq.
      - now rewrite (Oeset.compare_eq_trans _ _ _ _ Heq H).
      - now rewrite (Oeset.compare_lt_eq_trans _ _ _ _ Heq H).
      - now rewrite (Oeset.compare_gt_eq_trans _ _ _ _ Heq H).
    Qed.

    Record containers' : Type := mk_containers
      {
        (* the hash table *)
        hash : Containers.t (Cursor.cursor C1);
        (* the elements are associated to the corresponding key *)
        keys : forall x e, Containers.PX.MapsTo x e hash -> forall a, Oeset.mem_bool O1 a (Cursor.collection e) = true -> P x (proj a) = true;
        (* the hash table has no key duplicate *)
        noDup : NoDupA (@Containers.PX.eqk _) hash
      }.
    Definition containers := containers'.

    Program Definition dummy_containers : containers :=
      @mk_containers (Containers.empty _) _ _.
    Next Obligation.
      elim (Containers.empty_1 H).
    Qed.
    Next Obligation.
      apply Containers.empty_NoDup.
    Qed.

    Definition c1 : containers -> list o1 :=
      fun c => List.flat_map (fun x => Cursor.materialize _ (snd x)) (Containers.elements (hash c)).
    Definition kc1 : containers -> list (o2 * list o1) :=
      fun c => map (fun x => match x with (k,y) => (k, Cursor.materialize _ y) end) 
                   (Containers.elements (hash c)).

    Definition i : containers -> o2 -> Cursor.cursor C1 :=
      fun c x => match Containers.find x (hash c) with
                 | None => Cursor.empty_cursor C1
                 | Some l => Cursor.reset l
                 end.


    Lemma MapsToCompat {A:Type} x y (l:A) c :
      Containers.PX.MapsTo x l c -> Oeset.compare O2 x y = Eq -> Containers.PX.MapsTo y l c.
    Proof.
      unfold Containers.PX.MapsTo. intros HInA Heq.
      apply InA_eqA with (x:=(x,l)); trivial.
      - apply Containers.PX.eqke_equiv.
      - now split.
    Qed.

    Lemma InA_weak {A:Type} x : forall m,
        InA (Containers.PX.eqke (elt:=A)) x m ->
        InA (Containers.PX.eqk (elt:=A)) x m.
    Proof.
      induction m as [ |y ys IHys]; intro H; inversion H; subst.
      - constructor. unfold Containers.PX.eqk, Containers.PX.eqke in *. now destruct H1.
      - constructor 2. now apply IHys.
    Qed.


    Lemma i_collection : forall c x,
        comparelA (Oeset.compare O1)
                  (Cursor.collection (i c x))
                  (filter (fun y => P x (proj y)) (c1 c)) = Eq.
    Proof.
      intros [c keysc NoDupc] x. unfold i.
      simpl.
      case_eq (Containers.find (elt:=Cursor.cursor C1) x c).
      - intros l fd.
        rewrite Cursor.reset_collection.
        generalize (Containers.find_2 fd).
        intro ctn_maps.
        unfold c1.
        simpl.
        assert (H20:forall e, Containers.PX.MapsTo x e c -> e = l) by
            (intros e He; apply (Containers.find_1 NoDupc) in He; rewrite He in fd; now injection fd).
        assert (H4:=Containers.elements_1 ctn_maps).
        assert (H10:=@Containers.elements_2 _ c).
        assert (H30:=Containers.elements_3w NoDupc).
        induction (Containers.elements (elt:=Cursor.cursor C1) c) as [ |[y z] m IHm].
        + simpl. inversion H4.
        + simpl. inversion H4; subst.
          * destruct H0 as [H5 H6]. simpl in *. subst z.
            replace (Cursor.collection l) with ((Cursor.collection l) ++ nil) at 1 by now rewrite app_nil_r.
            rewrite ListFacts.filter_app.
            apply comparelA_eq_app.
            { rewrite filter_true.
              - apply (Oeset.compare_eq_sym (mk_oelists O1)).
                now apply Cursor.materialize_collection.
              - intros b Hb. apply (keysc _ _ ctn_maps).
                erewrite Oeset.mem_bool_eq_2.
                + apply Oeset.in_mem_bool. eexact Hb.
                + apply (Oeset.compare_eq_sym (mk_oelists O1)).
                  now apply Cursor.materialize_collection. }
            { rewrite filter_false.
              - reflexivity.
              - intros b Hb. rewrite in_flat_map in Hb.
                destruct Hb as [[d ld] [Hd1 Hd2]]. simpl in Hd2.
                assert (H11: Containers.PX.MapsTo d ld c).
                {
                  apply H10. apply In_InA.
                  - apply Containers.PX.eqke_equiv.
                  - now constructor 2.
                }
                assert (H300:Oeset.mem_bool O1 b (Cursor.collection ld) = true).
                {
                  erewrite Oeset.mem_bool_eq_2.
                  - eapply (Oeset.in_mem_bool _ _ _ Hd2).
                  - apply (Oeset.compare_eq_sym (mk_oelists O1)).
                    now apply Cursor.materialize_collection.
                }
                generalize (keysc _ _ H11 b H300).
                unfold P in *. case_eq (Oeset.compare O2 d (proj b)); try discriminate. intros Hd2' _.
                case_eq (Oeset.compare O2 x (proj b)); trivial.
                intro Heq. apply Oeset.compare_eq_sym in Heq.
                assert (H:=Oeset.compare_eq_trans _ _ _ _ Hd2' Heq).
                assert (Hd1':Containers.PX.MapsTo d ld m) by (exact (In_InA (Containers.PX.eqke_equiv _) Hd1)).
                apply (MapsToCompat _ Hd1') in H.
                assert (H21: Containers.PX.MapsTo x ld c) by (apply H10; now constructor 2).
                apply H20 in H21. subst ld. inversion H30; subst.
                apply (MapsToCompat _ H) in H5. elim H2. now apply InA_weak.
            }
          * replace (Cursor.collection l) with (nil ++ (Cursor.collection l)) at 1 by reflexivity.
            rewrite ListFacts.filter_app.
            apply comparelA_eq_app.
            { rewrite filter_false.
              - reflexivity.
              - intros b Hb.
                assert (H40:InA (Containers.PX.eqke (elt:=_)) (y, z) ((y, z) :: m)) by now constructor.
                assert (H300:Oeset.mem_bool O1 b (Cursor.collection z) = true).
                {
                  erewrite Oeset.mem_bool_eq_2.
                  - eapply (Oeset.in_mem_bool _ _ _ Hb).
                  - apply (Oeset.compare_eq_sym (mk_oelists O1)).
                    now apply Cursor.materialize_collection.
                }
                generalize (keysc _ _ (H10 _ _ H40) b H300). clear H40 H300.
                unfold P in *. case_eq (Oeset.compare O2 y (proj b)); try discriminate. intros H41 _.
                case_eq (Oeset.compare O2 x (proj b)); trivial.
                intro Heq. apply Oeset.compare_eq_sym in H41.
                assert (H43:=Oeset.compare_eq_trans _ _ _ _ Heq H41).
                inversion H30; subst.
                assert (H44:InA (Containers.PX.eqk (elt:=_)) (y, l) m).
                {
                  apply InA_eqA with (x:=(x,l)); trivial.
                  - apply Containers.PX.eqk_equiv.
                  - now apply InA_weak.
                }
                elim H2. clear c keysc NoDupc x fd ctn_maps H20 H4 H10 H30 IHm H0 b Hb H41 Heq H43 H2 H3.
                induction m as [ |[x1 x2] xs IHxs]; inversion H44; subst.
                + now constructor.
                + constructor 2; auto.
            }
            {
              apply IHm; trivial.
              - intros d ld Hd. apply H10. now constructor 2.
              - now inversion H30; subst.
            }
      - intro Hfind. unfold c1. simpl. assert (H1:forall e, ~ Containers.PX.MapsTo x e c).
        + intros e He. apply Containers.find_1 in He; trivial.
          rewrite He in Hfind. discriminate.
        + symmetry. rewrite filter_false.
          * symmetry. now rewrite Cursor.empty_cursor_collection.
          * intros b Hb.
            rewrite in_flat_map in Hb.
            destruct Hb as [[d ld] [Hd1 Hd2]]. simpl in Hd2.
            apply (In_InA (eqA:=Containers.PX.eqke (elt:=_)) (Containers.PX.eqke_equiv _)) in Hd1.
            apply Containers.elements_2 in Hd1.
            apply (Oeset.in_mem_bool O1) in Hd2.
            assert (H300:comparelA (Oeset.compare O1) (Cursor.materialize C1 ld) (Cursor.collection ld) = Eq) by now apply Cursor.materialize_collection.
            rewrite (Oeset.mem_bool_eq_2 _ _ _ _ H300) in Hd2. clear H300.
            apply (keysc _ _ Hd1) in Hd2. unfold P in *.
            revert Hd2. case_eq (Oeset.compare O2 d (proj b)); try discriminate. intros Hd2 _.
            case_eq (Oeset.compare O2 x (proj b)); trivial.
            intro Heq. apply Oeset.compare_eq_sym in Heq.
            assert (H:=Oeset.compare_eq_trans _ _ _ _ Hd2 Heq).
            apply (MapsToCompat _ Hd1) in H. now elim (H1 ld).
    Qed.

    Lemma i_visited c x : Cursor.visited (i c x) = nil.
    Proof.
      unfold i. case (Containers.find (elt:=Cursor.cursor C1) x (hash c)).
      - intros; apply Cursor.reset_visited.
      - apply Cursor.empty_collection.
        + apply Cursor.empty_cursor_coherent.
        + apply Cursor.empty_cursor_collection.
    Qed.

    Lemma i_coherent c x : Cursor.coherent (i c x).
    Proof.
      unfold i. case (Containers.find (elt:=Cursor.cursor C1) x (hash c)).
      - intros; apply Cursor.reset_coherent.
      - apply Cursor.empty_cursor_coherent.
    Qed.

    (* A more efficient version *)
    (* Definition mk_hash : Containers.t (Cursor.cursor C1) := *)
    (*   (List.fold_left (fun h t => Containers.add (proj t) (mk_cursor (t::nil)) h) unhashed_elem (Containers.empty _)). *)

    Fixpoint mk_hash_aux l :=
      match l with
      | nil => Containers.empty _
      | t::ts => Containers.add (proj t) (mk_cursor (t::nil)) (mk_hash_aux ts)
      end.
    Definition mk_hash := mk_hash_aux unhashed_elem.

    Lemma mk_hash_properties :
      (forall x e, Containers.PX.MapsTo x e mk_hash ->
                   forall a, OrderedSet.Oeset.mem_bool O1 a (Cursor.collection e) = true ->
                             P x (proj a) = true) /\
      (NoDupA (Containers.PX.eqk (elt:=_)) mk_hash).
    Proof.
      unfold mk_hash. induction unhashed_elem as [ |t ts [IHts1 IHts2]]; simpl; split.
      - intros x e H. now inversion H.
      - now apply Containers.empty_NoDup.
      - intros x e H1 a H2. case_eq (Oeset.compare O2 (proj t) x); intro Heq.
        + assert (H3:NoDupA (Containers.PX.eqk (elt:=Cursor.cursor C1)) (Containers.add (proj t) (mk_cursor (t :: nil)) (mk_hash_aux ts))) by now apply Containers.add_NoDup.
          apply (Containers.find_1 H3) in H1.
          assert (HeqSym:=Oeset.compare_eq_sym _ _ _ Heq).
          rewrite (Containers.add_eq IHts2 (mk_cursor (t :: nil)) HeqSym) in H1.
          inversion H1. subst e. clear H1.
          apply mk_cursor_collection in H2.
          simpl in H2. revert H2; case_eq (Oeset.eq_bool O1 a t); try discriminate; intros H2 _.
          rewrite Oeset.eq_bool_true_compare_eq in H2.
          apply proj_eq in H2. rewrite <- (P_eq_1 _ _ _ Heq).
          unfold P. now rewrite Oeset.compare_eq_sym.
        + apply (IHts1 _ e); auto.
          eapply Containers.add_3; eauto.
          intro H; rewrite H in Heq; discriminate.
        + apply (IHts1 _ e); auto.
          eapply Containers.add_3; eauto.
          intro H; rewrite H in Heq; discriminate.
      - now apply Containers.add_NoDup.
    Qed.

    Lemma mk_hash_keys :
      forall x e, Containers.PX.MapsTo x e mk_hash ->
      forall a, OrderedSet.Oeset.mem_bool O1 a (Cursor.collection e) = true ->
                P x (proj a) = true.
    Proof (proj1 mk_hash_properties).

    Lemma mk_hash_noDup :
      SetoidList.NoDupA (Containers.PX.eqk (elt:=_)) mk_hash.
    Proof (proj2 mk_hash_properties).

    Definition mk_hash_index_scan : containers :=
      mk_containers mk_hash_keys mk_hash_noDup.

    Definition build : Index.Rcd O1 O2.
      apply Index.mk_R with proj P C1 containers c1 i.
      - apply proj_eq.
      - apply P_eq_1.
      - apply P_eq_2.
      - exact dummy_containers.
      - apply i_collection.
      - apply i_visited.
      - apply i_coherent.
    Defined.

  End HashIndexScan.


  Section Simple.

    Local Notation cursor := (SeqScan.build O1).
    Definition simple_build := build cursor.
    Definition mk_simple_hash_index_scan l :=
      mk_hash_index_scan cursor l (@SeqScan.mk_seqcursor _).

  End Simple.


  Section Filter.

    Variable theta : o1 -> bool.
    Variable theta_eq : forall x y : o1, Oeset.compare O1 x y = Eq -> theta x = theta y.

    Local Notation cursor := (Filter.build theta theta_eq (SeqScan.build O1)).

    Definition filter_build := build cursor.
    Definition mk_filter_hash_index_scan l :=
      mk_hash_index_scan cursor l (fun l => Filter.mk_filter (SeqScan.build O1) (SeqScan.mk_seqcursor l)).

  End Filter.

End HashIndexScan.
