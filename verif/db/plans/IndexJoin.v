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

(*
Require Import List Equalities SetoidList.
Require Import Signatures Utils.
*)
Require Import List Psatz.
Require Import BasicFacts ListFacts OrderedSet Signatures.

Module IndexJoin.
Section Sec.
Hypothesis o1 o2 op o : Type.
Hypothesis O1 : Oeset.Rcd o1.
Hypothesis O2 : Oeset.Rcd o2.
Hypothesis OP : Oeset.Rcd op.
Hypothesis O : Oeset.Rcd o.

Hypothesis projS1 : o1 -> op.
Hypothesis projS1_eq : 
  forall x1 x2, Oeset.compare O1 x1 x2 = Eq -> Oeset.compare OP (projS1 x1) (projS1 x2) = Eq.

Hypothesis S1 : Cursor.Rcd O1.
Hypothesis S2 : Index.Rcd O2 OP.
Hypothesis build_ : o1 -> o2 -> o.
Hypothesis build_eq_1  : 
  forall x1 x1' x2, 
    Oeset.compare O1 x1 x1' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1' x2) = Eq.
Hypothesis build_eq_2  : 
  forall x1 x2 x2', 
    Oeset.compare O2 x2 x2' = Eq -> Oeset.compare O (build_ x1 x2) (build_ x1 x2') = Eq.

Record cursor :=
  mk_cursor
    {
      visited: list o;
      outer : Cursor.cursor S1;
      inner : Cursor.cursor (Index.C1 S2);
      containers2: Index.containers S2
    }.

Definition mk_index_join_cursor o i :=
  mk_cursor nil o (Cursor.empty_cursor (Index.C1 S2)) i.

Definition S2P := Index.P S2.
Definition projS2 := Index.proj S2.

Definition BoolXO : Oeset.Rcd (bool * o).
split with (compareAB bool_compare (Oeset.compare O)).  
- intros [b1 x1] [b2 x2] [b3 x3]; apply compareAB_eq_trans.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + apply Oeset.compare_eq_trans.
- intros [b1 x1] [b2 x2] [b3 x3]; apply compareAB_le_lt_trans.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + apply Oeset.compare_eq_lt_trans.
- intros [b1 x1] [b2 x2] [b3 x3]; apply compareAB_lt_le_trans.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + apply Oeset.compare_lt_eq_trans.
- intros [b1 x1] [b2 x2] [b3 x3]; apply compareAB_lt_trans.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + destruct b1; destruct b2; destruct b3; trivial; discriminate.
  + apply Oeset.compare_lt_trans.
- intros [b1 x1] [b2 x2]; apply compareAB_lt_gt.
  + destruct b1; destruct b2; trivial.
  + apply Oeset.compare_lt_gt.
Defined.

Definition cross2 l1 l2 :=
  flat_map 
    (fun a => List.rev 
                (fold_left (fun acc b => 
                              if S2P (projS1 a) (projS2 b) 
                              then (build_ a b) :: acc else acc) l2 nil)) l1.

Lemma cross2_no_fold_aux a : forall (l2 : list o2) l,
    fold_left (fun acc b => if S2P (projS1 a) (projS2 b) then (build_ a b)::acc else acc) l2 l
    = (List.rev (map (fun r => snd r) (filter (fun (r:bool * o) => let (b,_) := r in b) (map (fun b => (S2P (projS1 a) (projS2 b), build_ a b)) l2)))) ++ l.
Proof.
  induction l2.
  - simpl. intro l; trivial.
  - simpl in *. intro l.
    case_eq (S2P (projS1 a) (projS2 a0)).
    + intros projTr. simpl. rewrite IHl2.
      rewrite <- app_assoc. reflexivity.
        + intros projFl. rewrite IHl2. reflexivity.
Qed.


Lemma cross2_no_fold l1 l2 : 
  cross2 l1 l2 =
  flat_map (fun a => map (fun r => snd r) (filter (fun (r:bool * o) => let (b,_) := r in b) (map (fun b => (S2P (projS1 a) (projS2 b), build_ a b)) l2))) l1.
Proof.
  unfold cross2. induction l1 as [ |x xs IHxs]; simpl; auto.
  now rewrite cross2_no_fold_aux, IHxs, app_nil_r, rev_involutive.
Qed.

Definition cross2_inv l1 l2 :=
  flat_map (fun a => fold_left (fun acc b => if S2P (projS1 a) (projS2 b) then (build_ a b)::acc else acc) l2 nil) l1.


Lemma cross2_inv_no_fold l1 l2 : cross2_inv l1 l2 =
                                 flat_map (fun a => List.rev (map (fun r => snd r) (filter (fun (r:bool * o) => let (b,_) := r in b) (map (fun b => (S2P (projS1 a) (projS2 b), build_ a b)) l2)))) l1.
Proof.
  unfold cross2. induction l1 as [ |x xs IHxs]; simpl; auto.
  now rewrite cross2_no_fold_aux, IHxs, app_nil_r.
Qed.

Lemma filter_ctn: forall (A:Type) (l:list A) P f,
    filter (fun r: bool* o => let (b, _) := r in b)
           (map (fun b => (P b, f b)) (filter P l)) =
    filter (fun r: bool* o => let (b, _) := r in b) (map (fun b => (P b, f b)) l).
Proof.
  intros A l P f.
  induction l.
  - simpl; trivial.
  - simpl. case_eq (P a).
    + intros paTr. simpl. rewrite paTr.
      rewrite IHl. reflexivity.
    + intros paFl. rewrite IHl. reflexivity.
Qed.

Definition collection (hjc: cursor) :=
  (cross2 (Cursor.collection (outer hjc))
          (Index.c1 S2 (containers2 hjc))).

Definition coherent (hjc: cursor) : Prop :=
  Cursor.coherent (outer hjc) /\ Cursor.coherent (inner hjc) /\
  (Cursor.has_next (inner hjc) -> (Cursor.visited (outer hjc) <> nil)) /\
  match (Cursor.visited (outer hjc)) with
  | nil => (visited hjc) = nil /\ (Cursor.visited (inner hjc) = nil)
  | el::li => (Cursor.collection (inner hjc) = Cursor.collection (Index.i S2
                                                                  (containers2 hjc) (projS1 el))) /\
              comparelA (Oeset.compare O)  (visited hjc)
                      ((List.rev (cross2_inv (el::nil) (Cursor.visited (inner hjc)))) 
                         ++ (cross2_inv li (Index.c1 S2 (containers2 hjc)))) = Eq
  end.

    Definition reset (hjc: cursor): cursor :=
      mk_cursor nil (Cursor.reset (outer hjc)) (Cursor.empty_cursor _) (containers2 hjc).
    
    Lemma reset_collection : forall c, collection (reset c) = collection c.
    Proof.
      intros [vis s1 s2 ctn]. unfold collection. simpl.
      generalize (Cursor.reset_collection s1).
      intros s1_col. rewrite s1_col. reflexivity.
    Qed.
      
    Lemma reset_visited : forall c, visited (reset c) = nil.
    Proof.
      intros [vis s1 s2 ctn]. simpl. reflexivity.
    Qed.

  Lemma reset_coherent : forall c, coherent (reset c).
    Proof.
      intros [vis s1 s2 ctn].
      unfold coherent. simpl.
      split.
      - generalize (Cursor.reset_coherent s1).
        intros s1_ch. trivial.
      - split.
        + apply Cursor.empty_cursor_coherent.
        + split.
          * intro H. now elim (Cursor.empty_cursor_has_next (Index.C1 S2)).
          * rewrite Cursor.reset_visited. split; trivial.
            apply (Cursor.empty_collection _ _ (Cursor.empty_cursor_coherent (Index.C1 S2)) 
                                           (Cursor.empty_cursor_collection (Index.C1 S2))).
    Qed.

    Definition next (hjc: cursor): (result o * cursor) :=
      match (Cursor.next (inner hjc)) with
      | (Empty_Cursor, s2') =>
        match Cursor.next (outer hjc) with
        | (Empty_Cursor, s1') =>
          (Empty_Cursor, mk_cursor (visited hjc) s1' (inner hjc) (containers2 hjc))
        | (No_Result, s1') =>
          (No_Result, mk_cursor (visited hjc) s1' (inner hjc) (containers2 hjc))
        | (Result tpl1, s1') =>
          let new_s2 := Index.i S2 (containers2 hjc) (projS1 tpl1) in
          match (Cursor.next new_s2) with
          | (Empty_Cursor, s2') =>
            (No_Result, mk_cursor (visited hjc) s1' new_s2 (containers2 hjc))
          | (No_Result, s2') =>
            (No_Result, mk_cursor (visited hjc) s1' s2' (containers2 hjc))
          | (Result tpl2, s2') =>
            let tpl_ := (build_ tpl1 tpl2) in
            (Result tpl_, mk_cursor (tpl_::(visited hjc)) s1' s2' (containers2 hjc))
          end
        end
      | (Result tpl2, s2') =>
        match (Cursor.visited (outer hjc)) with
        | nil => (No_Result, mk_cursor (visited hjc) (outer hjc) s2' (containers2 hjc))
        | el1::_ =>
          let tpl_ := build_ el1 tpl2 in
          (Result tpl_, mk_cursor (tpl_::(visited hjc)) (outer hjc) s2' (containers2 hjc))
        end
      | (No_Result, s2') =>
        (No_Result, mk_cursor (visited hjc) (outer hjc) s2' (containers2 hjc))
      end.


    Lemma next_collection: forall c c' opt,
        coherent c -> next c = (opt, c') -> collection c' = collection c.
    Proof.
      intros c c' opt coh nhj.
      apply sym_eq.
      unfold coherent in coh. simpl in *.
      destruct coh as [ coh1 [coh2 coh] ].
      unfold next in nhj.
      case_eq (Cursor.next (inner c)).
      intros r c0 s2_c_nxt. rewrite s2_c_nxt in nhj.
      case_eq r.
      - intros t r'. subst r. 
        case_eq (Cursor.visited (outer c)).
        + intros s1_vis. rewrite s1_vis in nhj.
          unfold collection. destruct c' in *.
          injection nhj. intros ctn c0' c1' vis' nt.
          simpl in *. rewrite c1', ctn. reflexivity.
        + intros t0 l s1_vis. rewrite s1_vis in nhj.
          destruct c' in *. injection nhj.
          intros e1_ctn eq_c0 eq_c1 eq_build eq_wj.
          unfold collection. simpl. rewrite e1_ctn, eq_c1. reflexivity.
      - intros r'. subst r. destruct c' in *. unfold collection. simpl.
        injection nhj. intros eq_ctn eq_c0 eq_c1 eq_vis ntsf.
        rewrite eq_ctn, eq_c1. reflexivity.
      - intros r'. subst r. case_eq (Cursor.next (outer c)).
        intros r' c1 s1_nxt. rewrite s1_nxt in nhj. case_eq r'.
        + intros t r''. subst r'.
          case_eq (Cursor.next (Index.i S2 (containers2 c) (projS1 t))).
          intros r' s2 s2_nxt. rewrite s2_nxt in nhj. case_eq r'.
          * intros t0 r. subst r'. destruct c' in *.
            unfold collection. simpl. injection nhj.
            intros eq_ctn eq_s2 eq_c1 eq_bld eq_wj.
            rewrite eq_ctn. generalize (Cursor.next_collection _ _ coh1 s1_nxt).
            intros s1_col. rewrite <- eq_c1, s1_col. reflexivity.
          * intros r. subst r'. destruct c'. unfold collection. simpl.
            injection nhj. intros eq_ctn eq_s2 eq_c1 eq_vis nts.
            rewrite <- eq_ctn, <- eq_c1.
            generalize (Cursor.next_collection _ _ coh1 s1_nxt).
            intros s1_col. rewrite s1_col. reflexivity.
          * intros r. subst r'. destruct c'. unfold collection. simpl.
            injection nhj. intros eq_ctn eq_s2 eq_c1 eq_vis nts.
            rewrite eq_ctn, <- eq_c1.
            generalize (Cursor.next_collection _ _ coh1 s1_nxt). intros s1_col.
            rewrite s1_col. reflexivity.
        + intros r. subst r'. destruct c'. unfold collection. simpl.
          injection nhj. intros eq_ctn eq_c0 eq_c1 eq_vis nst.
          rewrite eq_ctn, <- eq_c1.
          generalize (Cursor.next_collection _ _ coh1 s1_nxt). intros s1_col.
          rewrite s1_col. reflexivity.
        + intros r. subst r'. destruct c'. unfold collection. simpl.
          injection nhj. intros eq_ctn eq_c0 eq_c1 eq_vis empt.
          rewrite <- eq_c1, eq_ctn.
          generalize (Cursor.next_collection _ _ coh1 s1_nxt).
          intros s1_col. rewrite s1_col. reflexivity.
    Qed.

    Lemma next_visited_Result: forall a c c',
        coherent c -> next c = (Result a, c') ->
        (visited c') = a::(visited c).
    Proof.
      intros a [vis s1 s2 ctn] [vis' s1' s2' ctn'] coh nxtHJ; simpl in *.
      unfold next in nxtHJ. simpl in nxtHJ.
      case_eq (Cursor.next s2).
      intros r c s2_nxt. rewrite s2_nxt in nxtHJ.
      case_eq r.
      - intros t r'. subst r.
        case_eq (Cursor.visited s1). intros s1_vis.
        + rewrite s1_vis in nxtHJ.
          case_eq (Cursor.next s1). intros r' c0 s1_next.
          discriminate.
        + intros t0 l s1_vis. rewrite s1_vis in nxtHJ.
          injection nxtHJ. intros eq_ctn eq_c eq_s1 bld_to bld_to_t.
          rewrite bld_to_t in bld_to. symmetry in bld_to. trivial.
      - intro r'. subst r. discriminate.
      - intro r'. subst r. case_eq (Cursor.next s1).
        intros r' c0 s1_nxt. rewrite s1_nxt in nxtHJ.
        case_eq r'.
        + intros t r''. subst r'.
          case_eq (Cursor.next (Index.i S2 ctn (projS1 t))).
          intros r c1 s2_cnxt. rewrite s2_cnxt in nxtHJ.
          case_eq r.
          * intros t0 r'. subst r. injection nxtHJ.
            intros eq_ctn eq_c1 eq_c0 bld_vis bld_ta.
            rewrite bld_ta in bld_vis. symmetry in bld_vis. trivial.
          * intros r'. subst r. discriminate.
          * intros r'. subst r. discriminate.
        + intros r''. subst r'. discriminate. 
        + intros r''. subst r'. discriminate.
    Qed.
    
    Lemma next_visited_No_Result : forall c c',
        coherent c -> next c = (No_Result, c') -> visited c' = visited c.
    Proof.
      intros [vis s1 s2 ctn] [vis' s1' s2' ctn'] coh nhj. apply sym_eq; simpl.
      unfold next in nhj. simpl in nhj.
      case_eq (Cursor.next s2). intros r c s2_nxt.
      rewrite s2_nxt in nhj. case_eq r.
      - intros t r'. subst r. case_eq (Cursor.visited s1).
        + intros s1_vis_nil. rewrite s1_vis_nil in nhj.
          case_eq (Cursor.next s1). intros r c0 s1_nxt.
          injection nhj. intros ctn_' s2_' s1_' vis_'. trivial.
        + intros t0 l s1_vis. rewrite s1_vis in nhj.
          discriminate.
      - intros r'. subst r. injection nhj.
        intros eq_ctn eq_c eq_c0 eq_vis. trivial.
      - intros r'. subst r. case_eq (Cursor.next s1).
        intros r c0 s1_next. rewrite s1_next in nhj.
        case_eq r.
        + intros t r'. subst r.
          case_eq (Cursor.next (Index.i S2 ctn (projS1 t))).
          intros r c1 s2c_nxt. rewrite s2c_nxt in nhj.
          case_eq r.
          * intros t0 r'. subst r. discriminate.
          * intros r'. subst r. injection nhj.
            intros eq_ctn eq_c eq_c0 eq_vis. trivial.
          * intros r'. subst r. injection nhj.
            intros eq_ctn eq_c eq_c0 eq_vis. trivial.
        + intros r'. subst r. injection nhj.
          intros eq_ctn eq_c eq_c0 eq_vis. trivial.
        + intros r'. subst r. discriminate.
    Qed.

    
  Lemma next_visited_Empty_Cursor : forall c c',
        coherent c -> next c = (Empty_Cursor, c') -> visited c' = visited c.
  Proof.
    intros [vis s1 s2 ctn] [vis' s1' s2' ctn'] coh nhj. apply sym_eq. simpl.
    unfold next in nhj. simpl in nhj.
      case_eq (Cursor.next s2). intros r c s2_nxt.
      rewrite s2_nxt in nhj. case_eq r.
      - intros t r'. subst r. case_eq (Cursor.visited s1).
        + intros s1_vis_nil. rewrite s1_vis_nil in nhj.
          case_eq (Cursor.next s1). intros r c0 s1_nxt.
          discriminate.
        + intros t0 l s1_vis. rewrite s1_vis in nhj.
          discriminate.
      - intros r'. subst r. discriminate.
      - intros r'. subst r. case_eq (Cursor.next s1).
        intros r c0 s1_next. rewrite s1_next in nhj.
        case_eq r.
        + intros t r'. subst r.
          case_eq (Cursor.next (Index.i S2 ctn (projS1 t))).
          intros r c1 s2c_nxt. rewrite s2c_nxt in nhj.
          case_eq r.
          * intros t0 r'. subst r. discriminate.
          * intros r'. subst r. discriminate.
          * intros r'. subst r. discriminate.
        + intros r'. subst r. discriminate.
        + intros r'. subst r. injection nhj.
          intros eq_ctn eq_c eq_c0 eq_vis. trivial.
    Qed.
    
  Lemma next_coherent : forall c, coherent c -> coherent (snd (next c)).
  Proof.
    intros [vis s1 s2 ctn] coh.
    unfold coherent in coh. simpl in coh.
    destruct coh as [ coh1 [coh2 coh] ].
    unfold next. simpl.
    case_eq (Cursor.next s2). intros r c s2_nxt.
    case_eq r.
    - intros t r'. subst r.
      case_eq (Cursor.visited s1).
      + intros s1_vis. rewrite s1_vis in coh.
        destruct coh as [coh coh']. unfold snd.
        unfold coherent; simpl. split.
        * trivial.
        * split.
          { generalize (Cursor.next_coherent _ _ coh2).
            intro s2_coh. rewrite s2_nxt in s2_coh.
            unfold snd in s2_coh. trivial.
          }
          { split.
            - assert (fst (Cursor.next s2) <> Empty_Cursor).
              + rewrite s2_nxt. unfold fst. discriminate.
              + rewrite <- Cursor.has_next_next_neg in H.
                * intros s2_hn. apply coh in H. elim H. trivial.
                * trivial.             
            - rewrite s1_vis. destruct coh' as [coh3 coh4]. split.
              + trivial.
              + assert (Cursor.has_next s2).
                * rewrite Cursor.has_next_next_neg.
                  { rewrite s2_nxt; unfold fst; discriminate. }
                  { trivial. }
                * apply coh in H. elim H. trivial.
          }
      + intros t0 l s1_vis. simpl in *. unfold coherent. simpl.
        split.
        * trivial.
        * split.
          { generalize (Cursor.next_coherent _ _ coh2).
            intros s2_coh_snd. rewrite s2_nxt in s2_coh_snd.
            simpl in *. trivial.
          }
          { rewrite s1_vis in *. destruct coh as [coh3 [coh4 coh5]].
            split.
            - intros H1 H2; discriminate.
            - split.
              + generalize (Cursor.next_collection _ _ coh2 s2_nxt).
                intros s2_eq_c. rewrite <- s2_eq_c in coh4. trivial.
              + rewrite cross2_no_fold_aux in *. rewrite !app_nil_r in *. rewrite rev_involutive in coh5. (* rewrite coh5. *)
                generalize (Cursor.next_visited_Result _ _ coh2 s2_nxt).
                intros s2_c_vis. rewrite s2_c_vis. simpl.
                generalize (Cursor.next_collection _ _ coh2 s2_nxt).
                intros eq_col. case_eq (S2P (projS1 t0) (projS2 t)).
                * intros s2p_true.
                  simpl.
                  rewrite rev_app_distr. simpl. rewrite rev_involutive.
                  rewrite Oeset.compare_eq_refl; assumption.
                * intros proj_Fl.
                  assert (Oeset.mem_bool O2 t (Cursor.collection c) = true).
                  { apply Cursor.visited_collection.
                    - generalize (Cursor.next_coherent _ _ coh2).
                      intros coh_snd. rewrite s2_nxt in coh_snd.
                      unfold snd in coh_snd. trivial.
                    - rewrite s2_c_vis. 
                      rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; trivial.
                  }
                  { rewrite eq_col in H. rewrite coh4 in H.
                    generalize (Index.i_collection S2 ctn (projS1 t0)).
                    intros eqList. rewrite (Oeset.mem_bool_eq_2 O2 _ _ _ eqList) in H.
                    rewrite Oeset.mem_bool_filter, Bool.andb_true_iff in H.
                    - destruct H as [H1 H2]; unfold S2P, projS2 in proj_Fl.
                      rewrite H1 in proj_Fl.
                      discriminate.
                    - intros x y _ Hxy; apply Index.P_eq_2.
                      apply Index.proj_eq; assumption.
                  } 
          }
    - intros r_nt. subst r. simpl. unfold coherent. simpl.
      split.
      + trivial.
      + split.
        * generalize (Cursor.next_coherent _ _ coh2).
          intros s2_coh_nxt. rewrite s2_nxt in s2_coh_nxt.
          simpl in *. trivial.
        * case_eq (Cursor.visited s1).
          { intros s1_vis_nil. rewrite s1_vis_nil in coh.
            destruct coh as [coh3 coh4].
            split.
            - intro s2_hn. elim coh3.
              + rewrite Cursor.has_next_next_neg.
                * rewrite s2_nxt. unfold fst. discriminate.
                * trivial.
              + trivial.
            - generalize (Cursor.next_visited_No_Result _ _ coh2 s2_nxt).
              intros s2_vis_eq. destruct coh4 as [coh4 coh5].
              split.
              + trivial.
              + rewrite coh5 in s2_vis_eq. trivial.
           }
          { intros t l s1_vis. rewrite s1_vis in coh.
            destruct coh as [coh3 coh4].
            split.
            - intros s2_hn.
              assert (Cursor.has_next s2).
              + rewrite Cursor.has_next_next_neg.
                * rewrite s2_nxt. unfold fst. discriminate.
                * trivial.
              + apply coh3 in H. trivial.
            - destruct coh4 as [coh4 coh5]. split.
              * generalize (Cursor.next_collection _ _ coh2 s2_nxt).
                intros eq_col. rewrite <- eq_col in coh4. trivial.
              * rewrite <- coh5. rewrite !cross2_no_fold_aux.
                generalize (Cursor.next_visited_No_Result _ _ coh2 s2_nxt).
                intros s2_cvis. rewrite s2_cvis. reflexivity.
          }
    - intros r_em. subst r. case_eq (Cursor.next s1).
      intros r c0 s1_nxt. case_eq r.
      + intros t r_wl. subst r. case_eq (Cursor.next (Index.i S2 ctn (projS1 t))).
        intros r c1 s2_c_nxt.
        case_eq r.
        * intros t0 r_wl. subst r. simpl in *. unfold coherent. simpl.
          split.
          { generalize (Cursor.next_coherent _ _ coh1).
            intros s1_coh_nxt. rewrite s1_nxt in s1_coh_nxt.
            simpl in *. trivial.
          }
          { split.
            - generalize (Cursor.next_coherent _ _ coh2).
              intros s2_coh_nxt.
              generalize (Index.i_coherent S2 ctn (projS1 t)).
              intros s2_c_coh.
              generalize (Cursor.next_coherent _ _ s2_c_coh).
              intros s2_cnxt. rewrite s2_c_nxt in s2_cnxt.
              unfold snd in s2_cnxt. trivial.
            - destruct coh as [coh3 coh4]. split.
              + intros s2_chn. intro.
                generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite H in s1_vis. discriminate.
              + generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1_vis. split.
                * generalize (Index.i_coherent S2 ctn (projS1 t)). intros s_coh.
                  generalize (Cursor.next_collection _ _ s_coh s2_c_nxt).
                  intros s2_col_eq. trivial.
                * case_eq (Cursor.visited s1).
                  { intros s1_vis_nil. rewrite s1_vis_nil in *.
                    destruct coh4 as [coh4 coh5]. subst vis.
                    simpl. rewrite app_nil_r. rewrite app_nil_r.
                    generalize (Index.i_coherent S2 ctn (projS1 t)).
                    intros s2_coh_ctn.
                    generalize (Index.i_visited S2 ctn (projS1 t)). intros s2cvis.
                    generalize (Cursor.next_visited_Result _ _ s2_coh_ctn s2_c_nxt).
                    intros s2_cvis_. rewrite s2cvis in s2_cvis_.
                    rewrite s2_cvis_. simpl. case_eq (S2P (projS1 t) (projS2 t0)).
                    - intros tr. simpl. rewrite Oeset.compare_eq_refl; reflexivity.
                    - intros fl.
                      assert (Oeset.mem_bool O2 t0 (Cursor.collection c1) = true).
                      + apply Cursor.visited_collection.
                        * generalize (Cursor.next_coherent _ _ s2_coh_ctn).
                          intros coh_snd. rewrite s2_c_nxt in coh_snd.
                          unfold snd in coh_snd. trivial.
                        * rewrite s2_cvis_. 
                          rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl.
                          reflexivity.                        
                      + generalize (Index.i_collection S2 ctn (projS1 t)).
                        intros eqList.
                        generalize (Cursor.next_collection _ _ s2_coh_ctn s2_c_nxt).
                        intros eq_col. rewrite eq_col in H.
                        rewrite (Oeset.mem_bool_eq_2 _ _ _ _ eqList) in H.
                        rewrite Oeset.mem_bool_filter, Bool.andb_true_iff in H.
                        * destruct H as [H1 H2]. unfold S2P, projS2 in fl; rewrite H1 in fl.
                          discriminate.
                        * intros x y _ Hxy. 
                          apply Index.P_eq_2. apply Index.proj_eq; assumption.
                  }
                  { intros t1 l s1vis. rewrite s1vis in coh4.
                    destruct coh4 as [coh4 coh5].
                    assert (~ Cursor.has_next s2).
                    - rewrite Cursor.has_next_next_neg.
                      + rewrite s2_nxt. unfold fst. intro. apply H. trivial.
                      + trivial.
                    - generalize (Cursor.has_next_spec coh2 H).
                      intro col_s2.
                      generalize (Index.i_coherent S2 ctn (projS1 t)). intros coh_ctn.
                      generalize (Cursor.next_visited_Result _ _ coh_ctn s2_c_nxt).
                      intros s2cvis1.
                      rewrite !cross2_no_fold_aux.
                      assert (comparelA (Oeset.compare O2)(Cursor.visited s2) (rev (Cursor.collection s2)) = Eq).
                      + rewrite <- (rev_involutive (Cursor.visited s2)).
                        apply comparelA_rev_eq.
                        rewrite comparelA_lt_gt, col_s2; trivial.
                        intros; apply Oeset.compare_lt_gt.
                      + generalize (Index.i_visited S2 ctn (projS1 t)).
                        intros vis_ctn. rewrite vis_ctn in s2cvis1.
                        rewrite s2cvis1. rewrite !app_nil_r.
                        clear col_s2. rewrite coh4 in H0.
                        generalize (Index.i_collection S2 ctn (projS1 t1)).
                        intros eq_ctn.
                        (* rewrite eq_ctn. *) rewrite !rev_involutive. simpl.
                        case_eq (S2P (projS1 t) (projS2 t0)).
                        * intros projTr.
                          rewrite cross2_no_fold_aux. simpl. 
                          rewrite Oeset.compare_eq_refl.
                          {
                            refine (comparelA_eq_trans _ _ _ _ _ coh5 _).
                            - do 6 intro; apply Oeset.compare_eq_trans.
                            - apply comparelA_eq_app.
                              + rewrite app_nil_r. rewrite cross2_no_fold_aux.
                                rewrite !app_nil_r. rewrite rev_involutive.
                                rewrite <- map_rev.
                                rewrite <- !filter_rev, <- map_rev.
                                rewrite <- (filter_ctn _ (rev (Index.c1 S2 ctn))).
                                apply (comparelA_map_eq_2 BoolXO O (fun r : bool * o => snd r)).
                                * intros [b1 x1] [b2 x2] K; simpl in K.
                                  destruct (bool_compare b1 b2); try discriminate K.
                                  apply K.
                                * apply comparelA_eq_filter.
                                  intros [b1 x1] [b2 x2] K; simpl in K; simpl.
                                  destruct b1; destruct b2; trivial; discriminate.
                                  {
                                    apply (comparelA_map_eq_2 O2 BoolXO).
                                    - intros x1 x2 Hx; simpl.
                                      rewrite (build_eq_2 _ _ _ Hx).
                                      unfold S2P, projS2.
                                      rewrite (Index.P_eq_2 S2 _ _ _ (Index.proj_eq S2 _ _ Hx)).
                                      destruct ((Index.P S2 (projS1 t1) (Index.proj S2 x2))); trivial.
                                    - refine (comparelA_eq_trans _ _ _ _ _ H0 _).
                                      + do 6 intro; apply Oeset.compare_eq_trans.
                                      + rewrite filter_rev; apply comparelA_rev_eq.
                                        assumption.
                                  }
                              + apply comparelA_eq_refl. 
                                intros; apply Oeset.compare_eq_refl.
                          }
                        * intros projFl.
                          assert (Oeset.mem_bool O2 t0 (Cursor.collection c1) = true).
                          { apply Cursor.visited_collection.
                            - generalize (Cursor.next_coherent _ _ coh_ctn).
                              intros s2_coh.
                              rewrite s2_c_nxt in s2_coh.
                              unfold snd in s2_coh. trivial.
                            - rewrite s2cvis1, Oeset.mem_bool_unfold, Oeset.compare_eq_refl.
                              reflexivity.
                          }
                          { generalize (Cursor.next_collection _ _ coh_ctn s2_c_nxt).
                            intros s2_col_eq. rewrite s2_col_eq in H1.
                            generalize (Index.i_collection S2 ctn (projS1 t)).
                            intros eq_s1t. rewrite (Oeset.mem_bool_eq_2 _ _ _ _ eq_s1t) in H1.
                            rewrite Oeset.mem_bool_filter, Bool.andb_true_iff in H1.
                            - destruct H1 as [H1 H2].
                              unfold S2P, projS2 in projFl; rewrite projFl in H1. discriminate.
                            - intros x y _ Hxy; rewrite (Index.P_eq_2 S2 _ _ _ (Index.proj_eq S2 _ _ Hxy)).
                              apply refl_equal.
                          }
                  }
          }
        * intros r'; subst r. destruct coh as [coh3 coh4].
          unfold coherent; simpl. split.
          { generalize (Cursor.next_coherent _ _ coh1). intros s1_nxtcoh.
            rewrite s1_nxt in s1_nxtcoh. unfold snd in s1_nxtcoh.
            trivial.
          }
          { split.
            - generalize (Index.i_coherent S2 ctn (projS1 t)). intros s2_cohi.
              generalize (Cursor.next_coherent _ _ s2_cohi). intros s2cn.
              rewrite s2_c_nxt in s2cn. unfold snd in s2cn. trivial.
            - split.
              + intros s2_hnc1. intros s1nil.
                generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1nil in s1_vis. discriminate.
              + generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1_vis. split.
                * generalize (Index.i_coherent S2 ctn (projS1 t)). intros s2coh.
                  generalize (Cursor.next_collection _ _ s2coh s2_c_nxt).
                  intros s2_col. trivial.
                * case_eq (Cursor.visited s1).
                  { intros s1_vis_nil. rewrite s1_vis_nil in *.
                    destruct coh4 as [coh4 coh5].
                    generalize (Index.i_coherent S2 ctn (projS1 t)).
                    intros s2_coh_ctn.
                    generalize (Cursor.next_visited_No_Result _ _ s2_coh_ctn s2_c_nxt).
                    intros s2_c_vis.
                    generalize (Index.i_visited S2 ctn (projS1 t)).
                    intros s2cvis. rewrite s2cvis in *. rewrite s2_c_vis.
                    simpl. now subst vis.
                  }
                  { intros t0 l s1_vis_. rewrite s1_vis_ in coh4.
                    destruct coh4 as [coh4 coh5].
                    refine (comparelA_eq_trans _ _ _ _ _ coh5 _); 
                      [do 6 intro; apply Oeset.compare_eq_trans | ].
                    rewrite !cross2_no_fold_aux. simpl.
                    rewrite !app_nil_r.
                    generalize (Index.i_coherent S2 ctn (projS1 t)).
                    intros coh_ctn.
                    generalize (Cursor.next_visited_No_Result _ _ coh_ctn s2_c_nxt).
                    intros s2_cvis. generalize (Index.i_visited S2 ctn (projS1 t)).
                    intros s2_c_visctn. rewrite s2_c_visctn in s2_cvis.
                    rewrite s2_cvis. simpl. rewrite cross2_no_fold_aux.
                    rewrite rev_involutive, app_nil_r.
                    assert (~Cursor.has_next s2).
                    - rewrite Cursor.has_next_next_neg.
                      + rewrite s2_nxt; unfold fst. intros neg.
                        apply neg. reflexivity.
                      + trivial.
                    - generalize (Cursor.has_next_spec coh2 H).
                      intros s2_col_rev.
                      assert (comparelA (Oeset.compare O2) (rev (Cursor.collection s2)) (Cursor.visited s2) = Eq).
                      + rewrite <- (rev_involutive (Cursor.visited s2)). apply comparelA_rev_eq; trivial.
                      + rewrite <- map_rev.
                        generalize (Index.i_collection S2 ctn (projS1 t0)).
                        intros eq_ctn2.
                        apply comparelA_eq_app; 
                          [ | apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl].
                        apply (comparelA_map_eq_2 BoolXO O (fun r : bool * o => snd r)).
                        * intros [b1 x1] [b2 x2] K; simpl in K.
                          destruct (bool_compare b1 b2); try discriminate K.
                          apply K.
                        * rewrite <- (filter_ctn _ (Index.c1 S2 ctn)).
                          rewrite <- filter_rev.
                          {
                            apply comparelA_eq_filter.
                            intros [b1 x1] [b2 x2] K; simpl in K; simpl.
                            destruct b1; destruct b2; trivial; discriminate.
                            rewrite <- map_rev.
                            apply (comparelA_map_eq_2 O2 BoolXO).
                            - intros x1 x2 Hx; simpl.
                              rewrite (build_eq_2 _ _ _ Hx).
                              unfold S2P, projS2.
                              rewrite (Index.P_eq_2 S2 _ _ _ (Index.proj_eq S2 _ _ Hx)).
                              destruct ((Index.P S2 (projS1 t0) (Index.proj S2 x2))); trivial.
                            - rewrite comparelA_lt_gt, CompOpp_iff in H0;
                                [ | intros; apply Oeset.compare_lt_gt].
                              refine (comparelA_eq_trans _ _ _ _ _ H0 _).
                              + do 6 intro; apply Oeset.compare_eq_trans.
                              + apply comparelA_rev_eq.
                                rewrite coh4; assumption.
                          }
                  }
          }
        * intros r'; subst r. unfold coherent; simpl.
          destruct coh as [coh3 coh4]. split.
            { generalize (Cursor.next_coherent _ _ coh1). intros s1_nxtcoh.
            rewrite s1_nxt in s1_nxtcoh. unfold snd in s1_nxtcoh.
            trivial.
          }
          { split.
            - generalize (Index.i_coherent S2 ctn (projS1 t)). intros s2_cohi.
              generalize (Cursor.next_coherent _ _ s2_cohi). intros s2cn.
              rewrite s2_c_nxt in s2cn. unfold snd in s2cn. trivial.
            - split.
              + intros s2_hnc1. intros s1nil.
                generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1nil in s1_vis. discriminate.
              + generalize (Cursor.next_visited_Result _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1_vis. split.
                * generalize (Index.i_coherent S2 ctn (projS1 t)). intros s2coh.
                  generalize (Cursor.next_collection _ _ s2coh s2_c_nxt).
                  intros s2_col. symmetry in s2_col; trivial.
                * case_eq (Cursor.visited s1).
                  { intros s1_vis_; rewrite s1_vis_ in *.
                    destruct coh4 as [coh4 coh5]. subst vis.
                    simpl. rewrite !app_nil_r.
                    rewrite Index.i_visited. reflexivity.
                  }
                  { rewrite cross2_no_fold_aux.
                    intros t0 l s1_vis_s1. rewrite s1_vis_s1 in coh4.
                    destruct coh4 as [coh4  coh5]. 
                    refine (comparelA_eq_trans _ _ _ _ _ coh5 _); 
                      [do 6 intro; apply Oeset.compare_eq_trans | ].
                    assert (~Cursor.has_next s2).
                    - intro. rewrite Cursor.has_next_next_neg in H.
                      + rewrite s2_nxt in H. unfold fst in H.
                        apply H. reflexivity.
                      + trivial.
                    - rewrite !app_nil_r.
                      generalize (Cursor.has_next_spec coh2 H).
                      intros s2_col_s2.
                      assert (comparelA (Oeset.compare O2) (rev (Cursor.collection s2)) (Cursor.visited s2) = Eq).
                      + rewrite <- (rev_involutive (Cursor.visited s2)). apply comparelA_rev_eq. now symmetry.
                      + rewrite coh4 in H0.
                        assert (~ Cursor.has_next (Index.i S2 ctn (projS1 t))).
                        * rewrite Cursor.has_next_next_neg.
                          { rewrite s2_c_nxt. unfold fst. intro. apply H1.
                            reflexivity.
                          }
                          { generalize (Index.i_coherent S2 ctn (projS1 t)).
                            intro; trivial.
                          }
                        * generalize (Index.i_coherent S2 ctn (projS1 t)).
                          intros s2_ctn_coh. rewrite cross2_no_fold_aux.
                          generalize (Cursor.has_next_spec s2_ctn_coh H1).
                          intros s2_col_vis.
                          assert (comparelA (Oeset.compare O2) (rev (Cursor.collection (Index.i S2 ctn (projS1 t)))) (Cursor.visited (Index.i S2 ctn (projS1 t))) = Eq).
                          { rewrite <- (rev_involutive (Cursor.visited (Index.i S2 ctn (projS1 t)))).
                            apply comparelA_rev_eq. now symmetry.
                          }
                          { rewrite !app_nil_r, !rev_involutive.
                            simpl.
                            rewrite cross2_no_fold_aux.
                            generalize (Index.i_visited S2 ctn (projS1 t)).
                            intros s2_vis_ctn. rewrite s2_vis_ctn.
                            simpl. apply comparelA_eq_app.
                            - generalize (Index.i_collection S2 ctn (projS1 t0)).
                              intros eqListA.
                              rewrite <- (filter_ctn _ (Index.c1 S2 ctn)).
                              rewrite <- map_rev. rewrite <- filter_rev. rewrite <- map_rev. rewrite app_nil_r.
                              apply (comparelA_map_eq_2 BoolXO O (fun r : bool * o => snd r)).
                              * intros [b1 x1] [b2 x2] K; simpl in K.
                                destruct (bool_compare b1 b2); try discriminate K.
                                apply K.
                              * {
                                  apply comparelA_eq_filter. 
                                  - intros [b1 x1] [b2 x2] K; simpl in K; simpl.
                                    destruct b1; destruct b2; trivial; discriminate.
                                  - apply (comparelA_map_eq_2 O2 BoolXO).
                                    + intros x1 x2 Hx; simpl.
                                      rewrite (build_eq_2 _ _ _ Hx).
                                      unfold S2P, projS2.
                                      rewrite (Index.P_eq_2 S2 _ _ _ (Index.proj_eq S2 _ _ Hx)).
                                      destruct ((Index.P S2 (projS1 t0) (Index.proj S2 x2))); trivial.
                                    + rewrite comparelA_lt_gt, CompOpp_iff in H0;
                                        [ | intros; apply Oeset.compare_lt_gt].
                                      refine (comparelA_eq_trans _ _ _ _ _ H0 _).
                                      * do 6 intro; apply Oeset.compare_eq_trans.
                                      * apply comparelA_rev_eq.
                                        assumption.
                                }
                            - apply comparelA_eq_refl.
                              intros; apply Oeset.compare_eq_refl.
                          }
                  }
          }
      + intros r'; subst r. unfold coherent; simpl.
        destruct coh as [coh3 coh4]. split.
        * generalize (Cursor.next_coherent _ _ coh1). intros s1_nxtcoh.
          rewrite s1_nxt in s1_nxtcoh. unfold snd in s1_nxtcoh.
          trivial.
        * split.
          { generalize (Cursor.next_coherent _ _ coh2). intros s2cn.
            rewrite s2_nxt in s2cn. unfold snd in s2cn. trivial.
          }
          { split.
            - intros s2_hnc1. intro s1nil.
              rewrite Cursor.has_next_next_neg in s2_hnc1.
              + rewrite s2_nxt in s2_hnc1. unfold fst in s2_hnc1.
                apply s2_hnc1. trivial.
              + trivial.
            - generalize (Cursor.next_visited_No_Result _ _ coh1 s1_nxt).
              intros s1_vis. case_eq (Cursor.visited s1).
              + intros s1_nil. rewrite s1_nil in coh4.
                rewrite s1_nil in s1_vis. rewrite s1_vis.
                destruct coh4 as [coh4 coh5]. split.
                * trivial.
                * generalize (Cursor.next_visited_Empty_Cursor _ _ coh2 s2_nxt).
                  intros s2_vis_eq. rewrite coh5 in s2_vis_eq.
                  symmetry in s2_vis_eq. trivial.
              + intros t l s1_vis_. rewrite s1_vis_ in s1_vis.
                rewrite s1_vis. rewrite s1_vis_ in coh4.
                destruct coh4 as [coh4 coh5].
                generalize (Cursor.next_collection _ _ coh2 s2_nxt).
                intros s2_c. split.
                * exact coh4. 
                * {
                    refine (comparelA_eq_trans _ _ _ _ _ coh5 _).
                    - do 6 intro; apply Oeset.compare_eq_trans.
                    - generalize (Cursor.next_visited_Empty_Cursor _ _ coh2 s2_nxt).
                      intros s2_vis. rewrite <- s2_vis. apply comparelA_eq_refl.
                      intros; apply Oeset.compare_eq_refl.
                  } 
          }
      + intros r'. subst r. unfold coherent; simpl.
        destruct coh as [coh3 coh4]. split.
        * generalize (Cursor.next_coherent _ _ coh1).
          intros s1_nxt_coh. rewrite s1_nxt in s1_nxt_coh.
          unfold snd in s1_nxt_coh. trivial.
        * split.
          { generalize (Cursor.next_coherent _ _ coh2).
            intros s2_nxt_coh. rewrite s2_nxt in s2_nxt_coh.
            unfold snd in s2_nxt_coh. trivial.
          }
          { split.
            - intros s2_hn. intro.
              rewrite Cursor.has_next_next_neg in s2_hn.
              + rewrite s2_nxt in s2_hn. unfold fst in s2_hn.
                apply s2_hn. trivial.
              + trivial.
            - case_eq (Cursor.visited s1).
              + intros s1_nil. rewrite s1_nil in coh4.
                generalize (Cursor.next_visited_Empty_Cursor _ _ coh1 s1_nxt).
                intros s1_vis. rewrite s1_nil in s1_vis. rewrite s1_vis.
                destruct coh4 as [coh4 coh5]. split.
                * trivial.
                * generalize (Cursor.next_visited_Empty_Cursor _ _ coh2 s2_nxt).
                  intros s2_vis_eq. rewrite coh5 in s2_vis_eq.
                  symmetry in s2_vis_eq. trivial.
              + intros t l s1_vis_.
                generalize (Cursor.next_visited_Empty_Cursor _ _ coh1 s1_nxt).
                intros s1_c0. rewrite s1_vis_ in s1_c0.
                rewrite s1_c0. rewrite s1_vis_ in coh4.
                destruct coh4 as [coh4 coh5].
                generalize (Cursor.next_collection _ _ coh2 s2_nxt).
                intros s2_c. split.
                * exact coh4.
                * {
                    refine (comparelA_eq_trans _ _ _ _ _ coh5 _).
                    - do 6 intro; apply Oeset.compare_eq_trans.
                    - generalize (Cursor.next_visited_Empty_Cursor _ _ coh2 s2_nxt).
                      intros s2_vis. rewrite <- s2_vis. apply comparelA_eq_refl.
                      intros; apply Oeset.compare_eq_refl.
                  }
          }
  Qed.
  
  Definition has_next (hjc : cursor) :Prop :=
      (fst (next hjc) <> Empty_Cursor).

  Lemma has_next_spec : forall c, 
      coherent c -> ~ has_next c -> comparelA (Oeset.compare O) (collection c) (rev (visited c)) = Eq.
  Proof.
    intros [vis s1 s2 ctn] coh not_hn. simpl.
    unfold collection. simpl.
    unfold coherent in coh. simpl in *.
    destruct coh as [coh1 [coh2 [coh3 coh]]].
    unfold has_next in not_hn.
    unfold next in not_hn; simpl in *.
    case_eq (Cursor.next s2). intros r' c s2_nxt. rewrite s2_nxt in not_hn.
    case_eq r'.
    - intros t r. subst r'. case_eq (Cursor.visited s1).
      + intros s1_vis_nil. rewrite s1_vis_nil in not_hn.
        unfold fst in not_hn. assert (Cursor.has_next s2).
        * rewrite Cursor.has_next_next_neg.
          { rewrite s2_nxt.
            unfold fst.
            discriminate.
          }
          { trivial.
          }
        * apply coh3 in H. rewrite s1_vis_nil in H. elim H. trivial.
      + intros t0 l s1_vis_el. rewrite s1_vis_el in not_hn. 
        unfold fst in not_hn. elim not_hn. discriminate.
    - intros r. subst r'. unfold fst in not_hn. elim not_hn. discriminate.
    - intros r. subst r'. case_eq (Cursor.next s1). intros r c' s1_nxt.
      rewrite s1_nxt in not_hn. case_eq r.
      + intros t r'. subst r. case_eq (Cursor.next (Index.i S2 ctn (projS1 t))).
        intros r c0 s2_cnext. rewrite s2_cnext in not_hn. case_eq r.
        * intros t0' r'. subst r. elim not_hn. discriminate.
        * intros r'. subst r. elim not_hn. discriminate.
        * intros r'. subst r. elim not_hn. discriminate.
      + intros r'. subst r. elim not_hn. discriminate.
      + intros r'. subst r. unfold fst in not_hn.
        case_eq (Cursor.visited s1).
        * intros s1_vis_nil. rewrite s1_vis_nil in coh.
          destruct coh as [coh4 coh]. assert (~ Cursor.has_next s1).
          { rewrite Cursor.has_next_next.
            - rewrite s1_nxt; reflexivity.
            - trivial.
          }
          { generalize (Cursor.has_next_spec coh1 H).
            intros s1_col. rewrite s1_vis_nil in s1_col.
            destruct (Cursor.collection s1); [ | discriminate s1_col].
            subst vis. reflexivity.
          }
        * intros t l s1_vis. rewrite s1_vis in coh.
          rewrite app_nil_r in coh. destruct coh as [coh4 coh].
          assert (~ Cursor.has_next s2).
          { rewrite Cursor.has_next_next.
            - rewrite s2_nxt; reflexivity.
            - trivial.
          }
          { generalize (Cursor.has_next_spec coh2 H).
            intros col2_rev_vis.
            assert (comparelA (Oeset.compare O2) (Cursor.visited s2) (rev (Cursor.collection s2)) = Eq).
            - rewrite <- (rev_involutive (Cursor.visited s2)). 
              apply comparelA_rev_eq; rewrite comparelA_lt_gt, CompOpp_iff; [assumption | ].
              intros; apply Oeset.compare_lt_gt.
            - clear col2_rev_vis. rewrite coh4 in H0.
              assert (coh':comparelA (Oeset.compare O) vis
          (rev
             (fold_left
                (fun (acc : list o) (b : o2) =>
                 if S2P (projS1 t) (projS2 b) then build_ t b :: acc else acc)
                (rev (Cursor.collection (Index.i S2 ctn (projS1 t)))) nil) ++ cross2_inv l (Index.c1 S2 ctn)) = Eq).
              { refine (comparelA_eq_trans _ _ _ _ _ coh _);
                  [do 6 intro; apply Oeset.compare_eq_trans | ].
                apply comparelA_eq_app.
                - apply comparelA_rev_eq. rewrite !cross2_no_fold_aux. rewrite !app_nil_r. 
                  apply comparelA_rev_eq.
                  apply (comparelA_map_eq_2 BoolXO O (fun r : bool * o => snd r)).
                  + intros [b1 x1] [b2 x2] K; simpl in K.
                    destruct (bool_compare b1 b2); try discriminate K.
                    apply K.
                    + apply comparelA_eq_filter. 
                      * intros [b1 x1] [b2 x2] K; simpl in K; simpl.
                        destruct b1; destruct b2; trivial; discriminate.
                      * { apply (comparelA_map_eq_2 O2 BoolXO).
                          - intros x1 x2 Hx; simpl.
                            rewrite (build_eq_2 _ _ _ Hx).
                            unfold S2P, projS2.
                            rewrite (Index.P_eq_2 S2 _ _ _ (Index.proj_eq S2 _ _ Hx)).
                            destruct ((Index.P S2 (projS1 t) (Index.proj S2 x2))); trivial.
                          - assumption.
                        }
                - apply comparelA_eq_refl; intros; apply Oeset.compare_eq_refl.
              }
              clear coh. assert (coh:=coh'). clear coh'. assert (~ Cursor.has_next s1).
              + rewrite Cursor.has_next_next.
                * rewrite s1_nxt. reflexivity.
                * trivial.
              + generalize (Cursor.has_next_spec coh1 H1).
                intros s1_col_vis. rewrite cross2_no_fold_aux in coh.
                rewrite app_nil_r, rev_involutive in coh.
                apply comparelA_eq_trans with (rev (rev
             (map (fun r : bool * o => snd r)
                (filter (fun r : bool * o => let (b, _) := r in b)
                   (map (fun b : o2 => (S2P (projS1 t) (projS2 b), build_ t b))
                      (Cursor.collection (Index.i S2 ctn (projS1 t)))))) ++
           cross2_inv l (Index.c1 S2 ctn))).
                * do 6 intro; apply Oeset.compare_eq_trans.
                * rewrite rev_app_distr, rev_involutive.
                  rewrite !cross2_no_fold. rewrite cross2_inv_no_fold. rewrite s1_vis in s1_col_vis.
                  apply comparelA_eq_trans with
                  (flat_map
        (fun a : o1 =>
         map (fun r : bool * o => snd r)
           (filter (fun r : bool * o => let (b, _) := r in b)
              (map (fun b : o2 => (S2P (projS1 a) (projS2 b), build_ a b)) (Index.c1 S2 ctn))))
        (rev (t :: l))); [do 6 intro; apply Oeset.compare_eq_trans | | ].
                  { apply (comparelA_flat_map_eq_2 O1 O).
                    - intros x1 x2 Hx; apply comparelA_map_eq_2 with BoolXO.
                      + intros [b1 y1] [b2 y2] Hy; simpl in Hy.
                        destruct (bool_compare b1 b2); try discriminate Hy.
                        apply Hy.
                      + apply comparelA_eq_filter.
                        * intros [b1 y1] [b2 y2] Hy1 Hy; simpl in Hy.
                          destruct b1; destruct b2; try discriminate Hy; trivial.
                        * apply (comparelA_map_eq_1 O2).
                          intro y; unfold S2P; simpl.
                          rewrite (Index.P_eq_1 _ _ _ _ (projS1_eq _ _ Hx)), (build_eq_1 _ _ _ Hx).
                          rewrite (Oset.compare_eq_refl Obool); trivial.
                    - assumption.
                  }
                  simpl; rewrite flat_map_app; simpl.
                  {
                    apply comparelA_eq_app.
                    - rewrite flat_map_rev. 
                      apply (comparelA_flat_map_eq_1 O1).
                      intro x1; rewrite rev_involutive; apply comparelA_eq_refl.
                      intros; apply Oeset.compare_eq_refl.
                    - rewrite <- app_nil_end; apply comparelA_map_eq_2 with BoolXO.
                      + intros [b1 y1] [b2 y2] Hy; simpl in Hy.
                        destruct (bool_compare b1 b2); try discriminate Hy.
                        apply Hy.
                      + generalize (Index.i_collection S2 ctn (projS1 t)).
                        intros eq_ctn2.
                        rewrite <- (filter_ctn _ (Index.c1 S2 ctn)).
                        apply comparelA_eq_filter.
                        * intros [b1 y1] [b2 y2] Hy1 Hy; simpl in Hy.
                          destruct b1; destruct b2; try discriminate Hy; trivial.
                        * {
                            apply (comparelA_map_eq_2 O2).
                            - intros y1 y2 Hy; simpl.
                              rewrite (build_eq_2 _ _ _ Hy); unfold S2P, projS2.
                              rewrite (Index.P_eq_2 _ _ _ _ (Index.proj_eq _ _ _ Hy)).
                              rewrite (Oset.compare_eq_refl Obool); trivial.
                            - rewrite comparelA_lt_gt, CompOpp_iff; [assumption | ].
                              intros; apply Oeset.compare_lt_gt.
                          }
                  } 
                * apply comparelA_rev_eq; rewrite <- map_rev, <- filter_rev, <- map_rev.
                  rewrite comparelA_lt_gt, CompOpp_iff; [assumption | ].
                  intros; apply Oeset.compare_lt_gt.
          }
  Qed.

  Lemma has_next_next_neg : forall c,
      coherent c -> (has_next c <-> fst (next c) <> Empty_Cursor).
  Proof.
    Proof.
    intros [vis s1 s2 ctn] coh.
    split.
    - intro hn. unfold has_next in hn. trivial.
    - intro fst_n. unfold has_next. trivial.
  Qed.

  Lemma visited_collection : 
    forall c, coherent c ->
              forall x, Oeset.mem_bool O x (visited c) = true -> Oeset.mem_bool O x (collection c) = true.
  Proof.
    intros [vis s1 s2 ctn] coh x eq_vis; simpl in *.
    unfold coherent in coh; simpl in coh.
    destruct coh as [coh1 [coh2 [coh3 coh4]]].
    unfold collection; simpl.
    case_eq (Cursor.visited s1).
    - intros s1_vis; rewrite s1_vis in coh4.
      destruct coh4 as [coh4 coh5]. subst vis.
      discriminate eq_vis.
    - intros t l s1_vis; rewrite s1_vis in coh4.
      destruct coh4 as [coh4 coh5].
      rewrite app_nil_r in coh5. rewrite (Oeset.mem_bool_eq_2 _ _ _ _ coh5) in eq_vis.
      rewrite Oeset.mem_bool_app, Bool.orb_true_iff in eq_vis.
      destruct eq_vis as [H|H].
      + rewrite cross2_no_fold_aux, app_nil_r in H.
        rewrite rev_involutive in H.
        rewrite Oeset.mem_bool_true_iff in H.
        { destruct H as [x' [Hx Hx']]; rewrite in_map_iff in Hx'.
          destruct Hx' as [[b0 x0] [_Hx0 H]]; simpl in _Hx0; subst x'.
          rewrite filter_In in H; destruct H as [H1 H2]; subst b0.
          rewrite in_map_iff in H1.
          destruct H1 as [x2 [H2 H3]]; injection H2; clear H2; do 2 intro; subst x0.
          rewrite cross2_no_fold, Oeset.mem_bool_true_iff.
          assert (Ht : Oeset.mem_bool O1 t (Cursor.collection s1) = true).
          {
            apply (Cursor.visited_collection _ coh1); apply Oeset.in_mem_bool; rewrite s1_vis; left; trivial.
          }
          rewrite Oeset.mem_bool_true_iff in Ht; destruct Ht as [x1 [Ht Hx1]].
          assert (Hx2 : Oeset.mem_bool O2 x2 (Cursor.collection s2) = true).
          {
            apply (Cursor.visited_collection _ coh2); apply Oeset.in_mem_bool; trivial.
          }
          generalize (Index.i_collection S2 ctn (projS1 t)); rewrite <- coh4; intro H.
          rewrite (Oeset.mem_bool_eq_2 _ _ _ _ H) in Hx2 ; clear H.
          rewrite Oeset.mem_bool_filter, Bool.andb_true_iff, Oeset.mem_bool_true_iff in Hx2.
          * destruct Hx2 as [K1 [y2 [K2 K3]]].
            exists (build_ x1 y2).
            {
              split.
              - refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
                refine (Oeset.compare_eq_trans _ _ _ _ (build_eq_1 _ _ _ Ht) _).
                apply build_eq_2; assumption.
              - rewrite in_flat_map; exists x1; split; [assumption | ].
                rewrite in_map_iff.
                eexists (true, _); split; [apply refl_equal | ].
                rewrite filter_In; split; [ | trivial].
                rewrite in_map_iff.
                exists y2; split; [ | trivial].
                apply f_equal2; [ | apply refl_equal].
                unfold S2P, projS2.
                rewrite <- (Index.P_eq_2 _ _ _ _ (Index.proj_eq S2 _ _ K2)), <- K1.
                apply Index.P_eq_1; rewrite Oeset.compare_lt_gt, CompOpp_iff; apply projS1_eq; trivial.
            }
          * intros; apply Index.P_eq_2; apply Index.proj_eq; assumption.
        }
      + unfold cross2_inv in H.
        rewrite Oeset.mem_bool_true_iff in H.
        { destruct H as [x' [Hx Hx']]; rewrite in_flat_map in Hx'.
          destruct Hx' as [x0 [_Hx0 H]]; simpl in _Hx0.
          rewrite cross2_no_fold_aux, <- app_nil_end in H.
          rewrite <- map_rev, <- filter_rev, <- map_rev, in_map_iff in H.
          destruct H as [[b0 _x0] [__Hx0 H]]; simpl in __Hx0; subst _x0.
          rewrite filter_In, in_map_iff in H.
          destruct H as [H Hb0]; subst b0.
          destruct H as [x2 [H Hx2]].
          injection H; clear H; do 2 intro; subst x'.
          rewrite cross2_no_fold, Oeset.mem_bool_true_iff.
          assert (Ht : Oeset.mem_bool O1 x0 (Cursor.collection s1) = true).
          {
            apply (Cursor.visited_collection _ coh1); apply Oeset.in_mem_bool; rewrite s1_vis; right; trivial.
          }
          rewrite Oeset.mem_bool_true_iff in Ht; destruct Ht as [x1 [Ht Hx1]].
          assert (Kx2 : Oeset.mem_bool 
                          O2 x2 (filter (fun y : o2 => Index.P S2 (projS1 x0) (Index.proj S2 y)) 
                                        (Index.c1 S2 ctn)) =
                        true).
          {
            rewrite Oeset.mem_bool_filter, Bool.andb_true_iff.
            - split; [apply H0 | ].
              apply Oeset.in_mem_bool; rewrite in_rev; assumption.
            - intros; apply Index.P_eq_2; apply Index.proj_eq; assumption.
          }              
          rewrite Oeset.mem_bool_filter, Bool.andb_true_iff, Oeset.mem_bool_true_iff in Kx2.
          * destruct Kx2 as [K1 [y2 [K2 K3]]].
            exists (build_ x1 y2).
            {
              split.
              - refine (Oeset.compare_eq_trans _ _ _ _ Hx _).
                refine (Oeset.compare_eq_trans _ _ _ _ (build_eq_1 _ _ _ Ht) _).
                apply build_eq_2; assumption.
              - rewrite in_flat_map; exists x1; split; [assumption | ].
                rewrite in_map_iff.
                eexists (true, _); split; [apply refl_equal | ].
                rewrite filter_In; split; [ | trivial].
                rewrite in_map_iff.
                exists y2; split; [ | trivial].
                apply f_equal2; [ | apply refl_equal].
                unfold S2P, projS2.
                rewrite <- (Index.P_eq_2 _ _ _ _ (Index.proj_eq S2 _ _ K2)), <- K1.
                apply Index.P_eq_1; rewrite Oeset.compare_lt_gt, CompOpp_iff; apply projS1_eq; trivial.
            }
          * intros; apply Index.P_eq_2; apply Index.proj_eq; assumption.
        }
  Qed.

  Definition empty_cursor : cursor := 
    mk_cursor nil (Cursor.empty_cursor S1) (Cursor.empty_cursor (Index.C1 S2)) (Index.dummy_containers S2).

  Lemma empty_cursor_collection : collection empty_cursor = nil.
  Proof.
    unfold collection, empty_cursor. simpl. now rewrite Cursor.empty_cursor_collection.
  Qed.

  Lemma empty_cursor_coherent : coherent empty_cursor.
  Proof.
    unfold coherent, empty_cursor. simpl. repeat split.
    - apply Cursor.empty_cursor_coherent.
    - apply Cursor.empty_cursor_coherent.
    - intro H. now elim (Cursor.empty_cursor_has_next (Index.C1 S2)).
    - rewrite Cursor.empty_collection.
      + split; [apply refl_equal | ].
        apply Cursor.empty_collection.
        * apply Cursor.empty_cursor_coherent.
        * apply Cursor.empty_cursor_collection.
      + apply Cursor.empty_cursor_coherent.
      + apply Cursor.empty_cursor_collection.
  Qed.

  Lemma empty_cursor_has_next : ~ has_next empty_cursor.
  Proof.
    unfold has_next, next, empty_cursor. simpl.
    assert (H1 : exists c1', Cursor.next (Cursor.empty_cursor S1) = (Empty_Cursor, c1')).
    {
      case_eq (Cursor.next (Cursor.empty_cursor S1)).
      intros r c' Hnc; exists c'; apply f_equal2; [ | apply refl_equal].
      destruct (Cursor.has_next_next _ _ (Cursor.empty_cursor_coherent S1)) as [H _].
      rewrite Hnc in H; apply H.
      apply Cursor.empty_cursor_has_next.
    }
    assert (H2 : exists c2', Cursor.next (Cursor.empty_cursor (Index.C1 S2)) = (Empty_Cursor, c2')).
    {
      case_eq (Cursor.next (Cursor.empty_cursor (Index.C1 S2))).
      intros r c' Hnc; exists c'; apply f_equal2; [ | apply refl_equal].
      destruct (Cursor.has_next_next _ _ (Cursor.empty_cursor_coherent (Index.C1 S2))) as [H _].
      rewrite Hnc in H; apply H.
      apply Cursor.empty_cursor_has_next.
    }
    destruct H1 as [c1 H1]; destruct H2 as [c2 H2]; rewrite H1, H2; simpl.
    intro Abs; apply Abs; apply refl_equal.
  Qed.


Lemma next_Empty_Cursor : forall c : cursor,
      coherent c -> fst (next c) = Empty_Cursor -> fst (next (snd (next c))) = Empty_Cursor.
Proof.
intros [v c1 c2 ctn2] Hc; unfold next; unfold coherent in Hc; simpl in Hc; destruct Hc as [Hc1 [Hc2 Hc]].
simpl.
case_eq (Cursor.next c2); intros r2 c2' Hnc2.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited c1).
  + intros Hvc1 Abs; discriminate Abs.
  + intros v1 lv1 Hvc1 Abs; discriminate Abs.
- intro Abs; discriminate Abs.
- case_eq (Cursor.next c1); intros r1 c1' Hnc1.
  destruct r1 as [e1 | | ].
  + case_eq (Cursor.next (Index.i S2 ctn2 (projS1 e1))); intros r2 c2'' Hnc2'.
    destruct r2 as [e2 | | ]; intro H; try discriminate H. 
  + intro H; discriminate H.
  + intros _; simpl.
    rewrite Hnc2.
    assert (H1 := Cursor.next_Empty_Cursor _ c1 Hc1); rewrite Hnc1 in H1; simpl in H1.
    case_eq (Cursor.next c1'); intros r1 c1'' Hnc1'; rewrite Hnc1' in H1; simpl in H1.
    rewrite H1; [ | apply refl_equal]; trivial.
Qed.

Lemma next_reset : forall c : cursor, coherent c -> reset (snd (next c)) = reset c.
Proof.
intros [v c1 c2 ctn2] Hc; unfold next, reset; 
  unfold coherent in Hc; simpl in Hc; destruct Hc as [Hc1 [Hc2 Hc]].
simpl.
case_eq (Cursor.next c2); intros r2 c2' Hnc2.
destruct r2 as [e2 | | ].
- case_eq (Cursor.visited c1); simpl.
  + intros Hvc1; apply refl_equal.
  + intros v1 lv1 Hvc1; apply refl_equal.
- simpl; apply refl_equal.
- simpl; case_eq (Cursor.next c1); intros r1 c1' Hnc1.
  destruct r1 as [e1 | | ].
  + case_eq (Cursor.next (Index.i S2 ctn2 (projS1 e1))); intros r2 c2'' Hnc2'.
    destruct r2 as [e2 | | ]; simpl;
      assert (H1 := Cursor.next_reset _ _ Hc1);
      rewrite Hnc1 in H1; simpl in H1; rewrite H1; apply refl_equal.
  + simpl.
    assert (H1 := Cursor.next_reset _ _ Hc1);
      rewrite Hnc1 in H1; simpl in H1; rewrite H1; apply refl_equal.
  + simpl.
    assert (H1 := Cursor.next_reset _ _ Hc1);
      rewrite Hnc1 in H1; simpl in H1; rewrite H1; apply refl_equal.
Qed.


Lemma reset_reset (c : cursor) : reset (reset c) = reset c.
Proof. unfold reset. simpl. now rewrite Cursor.reset_reset. Qed.


Fixpoint sumf {A:Type} (f:A -> nat) (l:list A) :=
  match l with
  | nil => 0
  | x::xs => (f x) + (sumf f xs)
  end.
Definition iter' {A} := fun (next:Cursor.cursor S1 -> result A * Cursor.cursor S1) n c acc =>
                      Nat.iter n
                               (fun c'l : (Cursor.cursor S1) * list (option A) =>
                                  let (c', l) := c'l in
                                  let (r, c'') := next c' in
                                  let l' := match r with
                                            | Result r' => Some r' :: l
                                            | No_Result => None :: l
                                            | Empty_Cursor => l
                                            end in
                                  (c'', l')) (c, acc).
Definition ubound c : nat :=
  sumf (fun tpl1 => match tpl1 with Some tpl1 => S (Cursor.ubound (Index.i S2 (containers2 c) (projS1 tpl1))) | None => 1 end)
         (snd (iter' Cursor.next (Cursor.ubound (outer c)) (outer c) nil))
  +
  Cursor.ubound (inner c).


Lemma sumf_app A (f:A -> nat) :
  forall l1 l2, sumf f (l1 ++ l2) = (sumf f l1) + (sumf f l2).
Proof.
  induction l1 as [ |x xs IHxs]; intro ys; auto.
  simpl. rewrite IHxs. lia.
Qed.


Lemma iter'_empty acc n : forall c,
    Cursor.coherent c ->
    fst (Cursor.next c) = Empty_Cursor ->
    snd (iter' Cursor.next n c acc) = acc.
Proof.
  induction n as [ |n IHn]; intros c Hc H; auto.
  unfold iter'. rewrite nat_iter_succ_r.
  case_eq (Cursor.next c). intros r c' Heq2. rewrite Heq2 in H. simpl in H. subst r.
  change (Nat.iter n
                   (fun c'l : Cursor.cursor S1 * list (option o1) =>
                      let (c'0, l) := c'l in
                      let (r, c'') := Cursor.next c'0 in
                      (c'',
                       match r with
                       | Result r' => Some r' :: l
                       | No_Result => None :: l
                       | Empty_Cursor => l
                       end)) (c', acc)) with (iter' Cursor.next n c' acc).
  case_eq (Cursor.next c'). intros r c0 Heq.
  assert (H1:fst (Cursor.next c) = Empty_Cursor) by now rewrite Heq2.
  generalize (Cursor.next_Empty_Cursor _ _ Hc H1). rewrite Heq2. simpl. rewrite Heq. simpl. intro; subst r.
  apply IHn.
  - generalize (Cursor.next_coherent _ _ Hc). now rewrite Heq2.
  - now rewrite Heq.
Qed.


Lemma iter'_app n : forall c acc1 acc2,
    snd (iter' Cursor.next n c (acc1 ++ acc2)) = (snd (iter' Cursor.next n c acc1)) ++ acc2.
Proof.
  induction n as [ |n IHn]; auto.
  intros c acc1 acc2. unfold iter'. rewrite !nat_iter_succ_r.
  case_eq (Cursor.next c); intros r c'' Heq.
  change (Nat.iter n
       (fun c'l : Cursor.cursor S1 * list (option o1) =>
        let (c', l) := c'l in
        let (r0, c''0) := Cursor.next c' in
        (c''0,
        match r0 with
        | Result r' => Some r' :: l
        | No_Result => None :: l
        | Empty_Cursor => l
        end))
       (c'',
       match r with
       | Result r' => Some r' :: acc1 ++ acc2
       | No_Result => None :: acc1 ++ acc2
       | Empty_Cursor => acc1 ++ acc2
       end)) with (iter' Cursor.next n c'' (match r with
                                            | Result r' => Some r' :: acc1 ++ acc2
                                            | No_Result => None :: acc1 ++ acc2
                                            | Empty_Cursor => acc1 ++ acc2
                                            end)).
  change (Nat.iter n
       (fun c'l : Cursor.cursor S1 * list (option o1) =>
        let (c', l) := c'l in
        let (r0, c''0) := Cursor.next c' in
        (c''0,
        match r0 with
        | Result r' => Some r' :: l
        | No_Result => None :: l
        | Empty_Cursor => l
        end))
       (c'',
       match r with
       | Result r' => Some r' :: acc1
       | No_Result => None :: acc1
       | Empty_Cursor => acc1
       end)) with (iter' Cursor.next n c'' (match r with
                                            | Result r' => Some r' :: acc1
                                            | No_Result => None :: acc1
                                            | Empty_Cursor => acc1
                                            end)).
  case r; [intro a; change (Some a :: acc1 ++ acc2) with ((Some a::acc1) ++ acc2)|change (None :: acc1 ++ acc2) with ((None :: acc1) ++ acc2)| ]; apply IHn.
Qed.

Lemma iter'_nil n : forall c acc,
    snd (iter' Cursor.next n c acc) = (snd (iter' Cursor.next n c nil)) ++ acc.
Proof.
  intros c acc. change acc with (nil ++ acc) at 1. now apply iter'_app.
Qed.


Lemma iter'_le n1 : forall n2, n2 <= n1 -> forall c,
  exists l, snd (iter' Cursor.next n1 c nil) = l ++ snd (iter' Cursor.next n2 c nil).
Proof.
  induction n1 as [ |n1 IHn1]; intros n2 Hn2 c.
  - assert (n2 = 0) by lia. subst n2. simpl. now exists nil.
  - case_eq n2.
    + intro; subst n2.
      change (snd (iter' Cursor.next 0 c nil)) with (@nil (option o1)).
      now exists (snd (iter' Cursor.next (S n1) c nil)); rewrite app_nil_r.
    + intros p Hp; subst n2. assert (Hp:p <= n1) by lia.
      unfold iter'. rewrite !nat_iter_succ_r.
      case_eq (Cursor.next c). intros r c'' Heq.
      change (Nat.iter n1
         (fun c'l : Cursor.cursor S1 * list (option o1) =>
          let (c', l0) := c'l in
          let (r0, c''0) := Cursor.next c' in
          (c''0,
          match r0 with
          | Result r' => Some r' :: l0
          | No_Result => None :: l0
          | Empty_Cursor => l0
          end))
         (c'',
         match r with
         | Result r' => Some r' :: nil
         | No_Result => None :: nil
         | Empty_Cursor => nil
         end)) with (iter' Cursor.next n1 c'' (match r with
         | Result r' => Some r' :: nil
         | No_Result => None :: nil
         | Empty_Cursor => nil
         end)).
        change (Nat.iter p
         (fun c'l : Cursor.cursor S1 * list (option o1) =>
          let (c', l0) := c'l in
          let (r0, c''0) := Cursor.next c' in
          (c''0,
          match r0 with
          | Result r' => Some r' :: l0
          | No_Result => None :: l0
          | Empty_Cursor => l0
          end))
         (c'',
         match r with
         | Result r' => Some r' :: nil
         | No_Result => None :: nil
         | Empty_Cursor => nil
         end)) with (iter' Cursor.next p c'' (match r with
         | Result r' => Some r' :: nil
         | No_Result => None :: nil
         | Empty_Cursor => nil
         end)).
        destruct (IHn1 _ Hp c'') as [l' Hl'].
        rewrite !(iter'_nil _ _ (match r with
         | Result r' => Some r' :: nil
         | No_Result => None :: nil
         | Empty_Cursor => nil
         end)), Hl'.
        rewrite <- app_assoc. now exists l'.
  Qed.


Lemma ubound_next_Empty (c:cursor):
  coherent c ->
  fst (next c) = Empty_Cursor -> ubound (snd (next c)) <= ubound c.
Proof.
  intros [Hc1 [Hc2 [Hc3 Hc]]].
  unfold next, ubound.
  case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2.
  destruct r2 as [e2 | | ].
  - case_eq (Cursor.visited (outer c)); discriminate.
  - intro Abs; discriminate Abs.
  - case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ]; simpl.
    + case_eq (Cursor.next (Index.i S2 (containers2 c) (projS1 e1))); intros r2 c2' Hnc2'.
      destruct r2 as [e2 | | ]; discriminate.
    + discriminate.
    + intros _.
      generalize (Cursor.next_coherent _ _ Hc1). rewrite Hnc1. simpl. intro Hc4.
      assert (H1:fst (Cursor.next (outer c)) = Empty_Cursor) by now rewrite Hnc1.
      generalize (Cursor.next_Empty_Cursor _ _ Hc1 H1). rewrite Hnc1. simpl. intro H2.
      rewrite (iter'_empty _ _ _ Hc4 H2); simpl. lia.
Qed.


Lemma ubound_next_not_Empty (c : cursor) :
  coherent c ->
  fst (next c) <> Empty_Cursor -> ubound (snd (next c)) < ubound c.
Proof.
  intros [Hc1 [Hc2 Hc]].
  unfold next, ubound.
  case_eq (Cursor.next (inner c)); intros r2 c2 Hnc2.
  destruct r2 as [e2 | | ].
  - assert (Hb2 : Cursor.ubound (snd (Cursor.next (inner c))) < Cursor.ubound (inner c)).
    {
      apply (Cursor.ubound_next_not_Empty _ _ Hc2).
      rewrite Hnc2; discriminate.
    }
    rewrite Hnc2 in Hb2; simpl in Hb2.
    case_eq (Cursor.visited (outer c)); intros; simpl; lia.
  - assert (Hb2 : Cursor.ubound (snd (Cursor.next (inner c))) < Cursor.ubound (inner c)).
    {
      apply (Cursor.ubound_next_not_Empty _ _ Hc2).
      rewrite Hnc2; discriminate.
    }
    rewrite Hnc2 in Hb2; simpl in Hb2.
    intros _; simpl; lia.
  - case_eq (Cursor.next (outer c)); intros r1 c1 Hnc1.
    destruct r1 as [e1 | | ].
    + case_eq (Cursor.next (Index.i S2 (containers2 c) (projS1 e1))); intros r2 c2' Hnc2'.
      destruct r2 as [e2 | | ].
      * simpl; intros _.
        assert (H10:fst (Cursor.next (outer c)) <> Empty_Cursor) by now rewrite Hnc1.
        generalize (Cursor.ubound_next_not_Empty _ _ Hc1 H10). clear H10. rewrite Hnc1. simpl. intro H1.
        assert (exists bo, Cursor.ubound (outer c) = S bo /\ Cursor.ubound c1 <= bo).
        { revert H1. clear.
          case (Cursor.ubound (outer c)); try lia.
          intros n Hn. exists n. lia. }
        destruct H as [bo [H2 H3]]. clear H1.
        rewrite H2. unfold iter' at 2. rewrite nat_iter_succ_r, Hnc1. simpl.
        change (Nat.iter bo
          (fun c'l : Cursor.cursor S1 * list (option o1) =>
           let (c', l) := c'l in
           let (r, c'') := Cursor.next c' in
           (c'',
           match r with
           | Result r' => Some r' :: l
           | No_Result => None :: l
           | Empty_Cursor => l
           end)) (c1, Some e1 :: nil)) with (iter' Cursor.next bo c1 (Some e1::nil)).
        rewrite (iter'_nil _ _ (Some e1::nil)), sumf_app. simpl.
        rewrite Plus.plus_assoc_reverse.
        apply Plus.plus_le_lt_compat.
        {
          destruct (iter'_le _ _ H3 c1) as [l Hl].
          rewrite Hl, sumf_app. lia.
        }
        {
          assert (H1:fst (Cursor.next (Index.i S2 (containers2 c) (projS1 e1))) <> Empty_Cursor) by now rewrite Hnc2'.
          generalize (Cursor.ubound_next_not_Empty _ _ (Index.i_coherent _ _ _) H1).
          rewrite Hnc2'. simpl. lia.
        }
      * simpl; intros _.
        assert (H10:fst (Cursor.next (outer c)) <> Empty_Cursor) by now rewrite Hnc1.
        generalize (Cursor.ubound_next_not_Empty _ _ Hc1 H10). clear H10. rewrite Hnc1. simpl. intro H1.
        assert (exists bo, Cursor.ubound (outer c) = S bo /\ Cursor.ubound c1 <= bo).
        { revert H1. clear.
          case (Cursor.ubound (outer c)); try lia.
          intros n Hn. exists n. lia. }
        destruct H as [bo [H2 H3]]. clear H1.
        rewrite H2. unfold iter' at 2. rewrite nat_iter_succ_r, Hnc1. simpl.
        change (Nat.iter bo
          (fun c'l : Cursor.cursor S1 * list (option o1) =>
           let (c', l) := c'l in
           let (r, c'') := Cursor.next c' in
           (c'',
           match r with
           | Result r' => Some r' :: l
           | No_Result => None :: l
           | Empty_Cursor => l
           end)) (c1, Some e1 :: nil)) with (iter' Cursor.next bo c1 (Some e1::nil)).
        rewrite (iter'_nil _ _ (Some e1::nil)), sumf_app. simpl.
        rewrite Plus.plus_assoc_reverse.
        apply Plus.plus_le_lt_compat.
        {
          destruct (iter'_le _ _ H3 c1) as [l Hl].
          rewrite Hl, sumf_app. lia.
        }
        {
          assert (H1:fst (Cursor.next (Index.i S2 (containers2 c) (projS1 e1))) <> Empty_Cursor) by now rewrite Hnc2'.
          generalize (Cursor.ubound_next_not_Empty _ _ (Index.i_coherent _ _ _) H1).
          rewrite Hnc2'. simpl. lia.
        }
      * simpl; intros _.
        assert (H10:fst (Cursor.next (outer c)) <> Empty_Cursor) by now rewrite Hnc1.
        generalize (Cursor.ubound_next_not_Empty _ _ Hc1 H10). clear H10. rewrite Hnc1. simpl. intro H1.
        assert (exists bo, Cursor.ubound (outer c) = S bo /\ Cursor.ubound c1 <= bo).
        { revert H1. clear.
          case (Cursor.ubound (outer c)); try lia.
          intros n Hn. exists n. lia. }
        destruct H as [bo [H2 H3]]. clear H1.
        rewrite H2. unfold iter' at 2. rewrite nat_iter_succ_r, Hnc1. simpl.
        change (Nat.iter bo
          (fun c'l : Cursor.cursor S1 * list (option o1) =>
           let (c', l) := c'l in
           let (r, c'') := Cursor.next c' in
           (c'',
           match r with
           | Result r' => Some r' :: l
           | No_Result => None :: l
           | Empty_Cursor => l
           end)) (c1, Some e1 :: nil)) with (iter' Cursor.next bo c1 (Some e1::nil)).
        rewrite (iter'_nil _ _ (Some e1::nil)), sumf_app. simpl.
        rewrite Plus.plus_assoc_reverse.
        apply Plus.plus_le_lt_compat.
        {
          destruct (iter'_le _ _ H3 c1) as [l Hl].
          rewrite Hl, sumf_app. lia.
        }
        {
          lia.
        }
    + simpl; intros _.
      assert (H10:fst (Cursor.next (outer c)) <> Empty_Cursor) by now rewrite Hnc1.
      generalize (Cursor.ubound_next_not_Empty _ _ Hc1 H10). clear H10. rewrite Hnc1. simpl. intro H1.
      assert (exists bo, Cursor.ubound (outer c) = S bo /\ Cursor.ubound c1 <= bo).
      { revert H1. clear.
        case (Cursor.ubound (outer c)); try lia.
        intros n Hn. exists n. lia. }
      destruct H as [bo [H2 H3]]. clear H1.
      rewrite H2. unfold iter' at 2. rewrite nat_iter_succ_r, Hnc1.
      change (Nat.iter bo
          (fun c'l : Cursor.cursor S1 * list (option o1) =>
           let (c', l) := c'l in
           let (r, c'') := Cursor.next c' in
           (c'',
           match r with
           | Result r' => Some r' :: l
           | No_Result => None :: l
           | Empty_Cursor => l
           end)) (c1, None :: nil)) with (iter' Cursor.next bo c1 (None :: nil)).
      rewrite (iter'_nil _ _ (None::nil)), sumf_app. simpl.
      rewrite Plus.plus_assoc_reverse.
      apply Plus.plus_le_lt_compat.
      {
        destruct (iter'_le _ _ H3 c1) as [l Hl].
        rewrite Hl, sumf_app. lia.
      }
      {
        lia.
      }
    + simpl; intro H; now elim H.
Qed.


Lemma coherent_iter res :
  forall n c (f:o -> res -> res) acc, coherent c -> coherent (fst (iter next n c f acc)).
Proof.
  intro n; induction n as [ | n]; intros c f acc Hc; simpl; [assumption | ].
  assert (IH := IHn c f acc Hc).
  case_eq (iter next n c f acc); intros c' l H; rewrite H in IH; simpl in IH.
  assert (K := next_coherent _ IH).
  case_eq (next c'); intros r c'' Hc'; rewrite Hc' in K; apply K.
Qed.


Lemma ubound_complete res :
  forall (c : cursor) (f : o -> res -> res) (acc : res),
    coherent c -> forall p : nat, ubound c <= p -> ~ has_next (fst (iter next p c f acc)).
Proof.
  intros c f acc Hc p Hp.
  rewrite has_next_next_neg; [ | apply coherent_iter; assumption].
  intro H; elim H; clear H.
  {
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
        case_eq (Cursor.next (outer c)). intros [tpl1| | ] c0 Heq.
        * case_eq (Cursor.ubound (outer c)).
          {
            intro H.
            assert(H100:Cursor.ubound (outer c) <= 0) by lia.
            generalize (Cursor.ubound_complete cons nil Hc1 0 H100).
            intro H1; elim H1. simpl.
            now rewrite (Cursor.has_next_next_neg _ _ Hc1), Heq.
          }
          {
            intros n Hn'. revert Hn. rewrite Hn'. unfold iter'. rewrite nat_iter_succ_r, Heq.
            change (Nat.iter n
                             (fun c'l : Cursor.cursor S1 * list (option o1) =>
                                let (c', l) := c'l in
                                let (r, c'') := Cursor.next c' in
                                (c'',
                                 match r with
                                 | Result r' => Some r' :: l
                                 | No_Result => None :: l
                                 | Empty_Cursor => l
                                 end)) (c0, Some tpl1 :: nil)) with (iter' Cursor.next n c0 (Some tpl1::nil)).
            rewrite iter'_nil, sumf_app. simpl. lia.
          }
        * case_eq (Cursor.ubound (outer c)).
          {
            intro H.
            assert(H100:Cursor.ubound (outer c) <= 0) by lia.
            generalize (Cursor.ubound_complete cons nil Hc1 0 H100).
            intro H1; elim H1. simpl.
            now rewrite (Cursor.has_next_next_neg _ _ Hc1), Heq.
          }
          {
            intros n Hn'. revert Hn. rewrite Hn'. unfold iter'. rewrite nat_iter_succ_r, Heq.
            change (Nat.iter n
                             (fun c'l : Cursor.cursor S1 * list (option o1) =>
                                let (c', l) := c'l in
                                let (r, c'') := Cursor.next c' in
                                (c'',
                                 match r with
                                 | Result r' => Some r' :: l
                                 | No_Result => None :: l
                                 | Empty_Cursor => l
                                 end)) (c0, None :: nil)) with (iter' Cursor.next n c0 (None::nil)).
            rewrite iter'_nil, sumf_app. simpl. lia.
          }
        * reflexivity.
      + intros n Hn'. revert Hn. rewrite Hn'. lia.
    - case_eq (next c); intros r c' Hnc; destruct r as [e | | ].
      + assert (Aux : ubound (snd (next c)) < ubound c).
        {
          apply (ubound_next_not_Empty _ Hc); rewrite Hnc; discriminate.
        }
        rewrite Hnc in Aux; simpl in Aux.
        replace (S n) with (n + 1); [ | rewrite PeanoNat.Nat.add_comm; trivial].
        unfold iter; rewrite nat_iter_plus; simpl Nat.iter at 2; rewrite Hnc.
        assert (IH : fst (next (fst (iter next n c' f (f e acc)))) = Empty_Cursor).
        {
          apply (IHn c').
          - apply le_S_n.
            refine (Le.le_trans _ _ _ Aux Hn).
          - generalize (next_coherent _ Hc); rewrite Hnc; exact (fun h => h).
        }
        unfold iter in IH; rewrite IH; trivial.
      + assert (Aux : ubound (snd (next c)) < ubound c).
        {
          apply (ubound_next_not_Empty _ Hc); rewrite Hnc; discriminate.
        }
        rewrite Hnc in Aux; simpl in Aux.
        replace (S n) with (n + 1); [ | rewrite PeanoNat.Nat.add_comm; trivial].
        unfold iter; rewrite nat_iter_plus; simpl Nat.iter at 2; rewrite Hnc.
        assert (IH : fst (next (fst (iter next n c' f acc))) = Empty_Cursor).
        {
          apply (IHn c').
          - apply le_S_n.
            refine (Le.le_trans _ _ _ Aux Hn).
          - generalize (next_coherent _ Hc); rewrite Hnc; exact (fun h => h).
        }
        unfold iter in IH; rewrite IH; trivial.
      + apply (iter_Empty_Cursor coherent _ next_coherent next_Empty_Cursor _ _ _ _ Hc).
        rewrite Hnc; trivial.
  }
Qed.


Definition build :=
  Cursor.mk_R
    O
    collection visited coherent visited_collection
    reset reset_collection reset_visited reset_coherent
    next next_collection next_visited_Result next_visited_No_Result next_visited_Empty_Cursor
    next_coherent next_Empty_Cursor next_reset
    has_next has_next_spec has_next_next_neg
    empty_cursor empty_cursor_collection empty_cursor_coherent empty_cursor_has_next
    ubound reset_reset ubound_next_Empty ubound_next_not_Empty ubound_complete.

End Sec.
End IndexJoin.
