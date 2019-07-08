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

Require Import ListFacts OrderedSet FiniteSet.
Require Import Signatures SeqScan IndexJoin HashIndexScan.
Require Import FlatData.

Module Type TUPLE.
  Parameter T : Tuple.Rcd.
End TUPLE.

Module QEP (TPL : TUPLE).

  Local Notation o := (Tuple.tuple TPL.T).
  Local Notation O := (Tuple.OTuple TPL.T).
  Local Notation attribute := (Tuple.attribute TPL.T).
  Local Notation proj := (fun la t => List.map (Tuple.dot _ t) la).
  Local Notation build := (fun t1 t2 => Tuple.join_tuple TPL.T t1 t2 (Tuple.address _ t1)).

  Module OE <: OESET.
    Definition o := o.
    Definition O := O.
  End OE.

  Module LV <: OESET.
    Definition o := list (Tuple.value TPL.T).
    Definition O := (OrderedSet.oeset_of_oset (OrderedSet.mk_olists (Tuple.OVal TPL.T))).
  End LV.

  Lemma build_eq_1 :
    forall t1 t2 t, t1 =t= t2 -> build t1 t =t= build t2 t.
  Proof.
    intros *. apply Tuple.join_tuple_eq_1.
  Qed.
  
  Lemma build_eq_2 :
    forall t t1 t2, t1 =t= t2 -> build t t1 =t= build t t2.
  Proof.
    intros *; apply Tuple.join_tuple_eq_2.
  Qed.
  
  Lemma proj_eq : 
    forall la (t1 t2 : o), t1 =t= t2 -> Oeset.compare LV.O (proj la t1) (proj la t2) = Eq.
  Proof.
    do 4 intro; apply Oeset.compare_eq_refl_alt.
    rewrite <- map_eq.
    do 2 intro; apply Tuple.tuple_eq_dot; assumption.
  Qed.

  Lemma theta_eq : 
    forall (theta : o -> bool),
      (forall s f p1 p2, theta (Tuple.mk_tuple _ s f p1) = theta (Tuple.mk_tuple _ s f p2)) ->
      forall t1 t2,
      t1 =t= t2 ->      
      theta (Tuple.canonized_tuple TPL.T t1 (Tuple.address _ t1)) = theta (Tuple.canonized_tuple TPL.T t2 (Tuple.address _ t2)).
  Proof.
    intros theta htheta t1 t2 H.
    unfold Tuple.canonized_tuple.
    rewrite Tuple.tuple_as_pairs_canonizes in H.
    rewrite H.
    unfold Tuple.pairs_as_tuple.
    apply htheta.
  Qed.
  
  Module HashIndexScan := HashIndexScan OE LV.

  (* Augmenting the tuple type:
     The theta filtering predicate must be equal on same tuple at different addresses. *)

  Inductive index : Type :=
  | SimpleHashIndexScan : list attribute -> list o -> index
  | FilterHashIndexScan :
      forall (theta : o -> bool) (htheta: forall s f p1 p2, theta (Tuple.mk_tuple _ s f p1) = theta (Tuple.mk_tuple _ s f p2)), list attribute -> list o -> index.

  Inductive cursor : Type :=
  | SeqScan : list o -> cursor
  | IndexJoin : list attribute -> cursor -> index -> cursor.
    
  Definition type_index (i:index) : Index.Rcd O LV.O :=
    match i with
    | SimpleHashIndexScan la _ => HashIndexScan.simple_build (proj la) (proj_eq _)
    | FilterHashIndexScan theta htheta la _ =>
         HashIndexScan.filter_build _ (theta_eq theta htheta) (proj la) (proj_eq _)
    end.

  Fixpoint type_cursor (c : cursor) : Cursor.Rcd O :=
    match c with
    | SeqScan l => SeqScan.build O
    | IndexJoin la c i =>
      IndexJoin.build 
        _ _ _ _ _ _ _ _ 
        (proj la) (proj_eq la) (type_cursor c) (type_index i) build build_eq_1 build_eq_2
    end.

  Definition eval_index (i:index) : Index.containers (type_index i) :=
    match i return Index.containers (type_index i) with
    | SimpleHashIndexScan la l => HashIndexScan.mk_simple_hash_index_scan l (SeqScan.mk_seqcursor_collection O) (proj la) (proj_eq _)
    | FilterHashIndexScan theta htheta la l =>
         HashIndexScan.mk_filter_hash_index_scan _ _ l (fun l x H => SeqScan.mk_seqcursor_collection O l x (Filter.Filter.mk_filter_collection _ (theta_eq theta htheta) _ _ _ H)) (proj la) (proj_eq _)
    end.

  Fixpoint eval_cursor (c:cursor) : Cursor.cursor (type_cursor c) :=
    match c return Cursor.cursor (type_cursor c) with
    | SeqScan l => SeqScan.mk_seqcursor l
    | IndexJoin la c i =>
        IndexJoin.mk_index_join_cursor 
         _ _ _ _ _ _ _ (type_cursor c) (type_index i) (eval_cursor c) (eval_index i)
    end.

Lemma eval_index_unfold :
  forall i, eval_index i =
    match i return Index.containers (type_index i) with
    | SimpleHashIndexScan la l => HashIndexScan.mk_simple_hash_index_scan l (SeqScan.mk_seqcursor_collection O) (proj la) (proj_eq _)
    | FilterHashIndexScan theta htheta la l =>
         HashIndexScan.mk_filter_hash_index_scan _ (theta_eq theta htheta) l (fun l x H => SeqScan.mk_seqcursor_collection O l x (Filter.Filter.mk_filter_collection _ (theta_eq theta htheta) _ _ _ H)) (proj la) (proj_eq _)
    end.
Proof.
intro i; case i; intros; apply refl_equal.
Qed.

Lemma eval_cursor_unfold :
  forall c, eval_cursor c =
    match c return Cursor.cursor (type_cursor c) with
    | SeqScan l => SeqScan.mk_seqcursor l
    | IndexJoin la c i =>
        IndexJoin.mk_index_join_cursor 
         _ _ _ _ _ _ _ (type_cursor c) (type_index i) (eval_cursor c) (eval_index i)
    end.
Proof.
intro c; case c; intros; apply refl_equal.
Qed.

End QEP.
