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

Require Import List VectorDef Bvector.
Require Import OrderedSet.
Require Import Signatures SeqScan.

Set Implicit Arguments.


Module BitmapIndexScan.

  Section BitmapIndexScan.

    Variable o1 o2 : Type.
    Variable O1 : Oeset.Rcd o1.
    Variable O2 : Oeset.Rcd o2.
    Variable proj : o1 -> o2.
    Hypothesis proj_eq :
      forall x y, Oeset.compare O1 x y = Eq -> Oeset.compare O2 (proj x) (proj y) = Eq.
    Variable P : o2 -> o2 -> bool.
    Hypothesis P_eq_1 : forall x1 x2 y, Oeset.compare O2 x1 x2 = Eq -> P x1 y = P x2 y.
    Hypothesis P_eq_2 : forall x y1 y2, Oeset.compare O2 y1 y2 = Eq -> P x y1 = P x y2.


    Record containers : Type := mk_containers
      {
        (* the number of elements in the relation *)
        size : nat;
        (* all the elements of the relation *)
        collection : Vector.t o1 size;
        (* a bitmap associated to every index *)
        bitmap : o2 -> Bvector size;
        (* each bitmap associates to true exactly the elements matching
           the corresponding index *)
        coherent : forall n x0, nth (bitmap x0) n = P x0 (proj (nth collection n))
      }.

    Program Definition dummy_containers : containers :=
      @mk_containers O (Vector.nil o1) (fun _ => Bnil) _.
    Next Obligation.
      inversion n.
    Qed.
    
    Definition c1 : containers -> list o1 := fun c => to_list (collection c).
    
    Definition C1 := SeqScan.build O1.
    
    Definition i : containers -> o2 -> Cursor.cursor C1 :=
      fun c x0 => let col := List.rev (fold_left2 (fun acc (b:bool) y => if b then (y::acc)%list else acc) List.nil (bitmap c x0) (collection c)) in
                  SeqScan.mk_cursor List.nil col col.

    
    Lemma fold_left2_rem n (l1:t bool n) (l2:t o1 n) : forall acc0,
        (fold_left2 (fun acc (b:bool) y => if b then (y::acc)%list else acc%list) acc0 l1 l2) = ((List.rev (List.map snd (List.filter fst (to_list (map2 pair l1 l2))))) ++ acc0)%list.
    Proof.
      apply (rect2 (fun m t1 t2 => forall acc0 : list o1,
                        fold_left2
                          (fun (acc : list o1) (b : bool) (y : o1) =>
                             if b then (y :: acc)%list else acc) acc0 t1 t2 =
                        (List.rev (List.map snd (filter fst (to_list (map2 pair t1 t2)))) ++ acc0)%list)); auto.
      intros m v1 v2 IH b y acc.
      change (
          fold_left2
            (fun (acc0 : list o1) (b0 : bool) (y0 : o1) =>
               if b0 then (y0 :: acc0)%list else acc0)
            (if b then (y :: acc)%list else acc) v1 v2 =
          (List.rev
            (List.map snd (filter fst ((b,y)::(to_list (map2 pair v1 v2)))%list)) ++
            acc)%list
        ). simpl.
      rewrite IH. case b; auto.
      simpl. now rewrite <- app_assoc.
    Qed.


    Lemma i_collection c x : comparelA (Oeset.compare O1) (Cursor.collection (i c x)) (filter (fun y => P x (proj y)) (c1 c)) = Eq.
    Proof.
      unfold c1. destruct c as [size col bitmap coh]. simpl.
      rewrite fold_left2_rem, app_nil_r, rev_involutive.
      assert (H:forall (n : Fin.t size), (bitmap x)[@n] = P x (proj col[@n])) by auto.
      clear coh. revert H. generalize (bitmap x). intro b.
      apply (rect2 (fun n0 v1 v2 => (forall n : Fin.t n0, v1[@n] = P x (proj v2[@n])) ->
                                    comparelA (Oeset.compare O1) (List.map snd (filter fst (to_list (map2 pair v1 v2))))
                                              (filter (fun y => P x (proj y)) (to_list v2)) = Eq)).
      - reflexivity.
      - intros n v1 v2 IH b' y coh.
        change (
            comparelA (Oeset.compare O1)
                      (List.map snd (filter fst ((b',y)::(to_list (map2 pair v1 v2)))%list))
                      (filter (fun y0 : o1 => P x (proj y0)) (y::(to_list v2))%list) = Eq
          ). simpl.
        assert (H:forall n0 : Fin.t n, v1[@n0] = P x (proj v2[@n0])) by (intro m; apply (coh (Fin.FS m))).
        apply IH in H. clear IH.
        generalize (coh Fin.F1). clear coh. simpl. case (P x (proj y)); intro Heq; subst b'.
        + simpl. now rewrite Oeset.compare_eq_refl.
        + auto.
    Qed.

    Lemma i_visited c x : Cursor.visited (i c x) = List.nil. Proof. reflexivity. Qed.

    Lemma i_coherent c x : Cursor.coherent (i c x). Proof. reflexivity. Qed.

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

  End BitmapIndexScan.

End BitmapIndexScan.
