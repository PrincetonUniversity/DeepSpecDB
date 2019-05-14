Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import Coq.Strings.Ascii.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.

Require Import DB.functional.trie.
Require Import DB.functional.btree.
Require Import DB.representation.trie.

Require Import Top.db_operations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* types from .c file *)
Definition Node := Tstruct _Node noattr.
Definition Column := Tstruct _Column noattr.
Definition Schema := Tstruct _Schema noattr.
Definition Element := Tstruct _Element noattr.
Definition DBIndex := Tstruct _DBIndex noattr.


Definition _list : ident := 2%positive.
Definition t_list := Tstruct _list noattr.

(* FUNCTIONAL MODEL *)

Inductive col_t : Type := Int | Str.

(* Schema type - has a list of column types AND the ordered list of indices of PK columns *)
Record schema : Type := mk_schema
                          { col_types : list col_t ;
                            pk_indices : list Z ;
                            range : Forall (fun i => 0 <= i < Z.of_nat (length col_types)) pk_indices ;
                            nodup : NoDup pk_indices }.

Program Definition schema_tail sch := match col_types sch with
                              | [] => sch
                              | hd :: tl =>                                (* or x <> 0? *)
                                mk_schema tl (map (fun x => x - 1) (filter (fun x => x >=? 1) (pk_indices sch))) _ _ end.
Next Obligation.
  destruct sch. simpl in *.
  subst col_types0. simpl Datatypes.length in range0.
  rewrite Forall_map.
  induction pk_indices0; inversion range0; inversion nodup0. apply Forall_nil.
  simpl. case_eq (a >=? 1); intro h. 
  apply Forall_cons. simpl. apply Forall_inv in range0. rewrite Z.geb_le in h.
  rewrite Nat2Z.inj_succ in range0. omega.
  auto.
  auto.
Defined.

Next Obligation.
  destruct sch. simpl in *.
  induction pk_indices0. simpl. apply NoDup_nil.
  simpl. case_eq (a >=? 1); intro h; inversion nodup0; inversion range0. simpl. apply NoDup_cons.
  intro k. apply list_in_map_inv in k.
  destruct k as [x1 [p1 p2]].
  rewrite filter_In in p2. destruct p2 as [p21 p22].
  replace x1 with a in p21 by omega. auto.
  auto. auto.
Defined.

(* element type - what tuples in the DB consist of *)
Inductive elt : Type := 
  | int_elt: ptrofs -> elt
  | string_elt: list byte -> elt. 

Inductive col_types_compat : col_t -> elt -> Prop :=
| compat_int : forall n, col_types_compat Int (int_elt n)
| compat_str : forall s, col_types_compat Str (string_elt s).

Definition is_valid_elt_list (sch : schema) (le : list elt) : Prop :=
  Forall2 col_types_compat (col_types sch) le.

Record tuple (sch : schema) := mk_tuple
                                 { elts : list elt ;
                                   adequacy : is_valid_elt_list sch elts }.

Arguments elts {sch}.

Lemma is_valid_nil (sch : schema) (h : is_valid_elt_list sch []) : col_types sch = [] /\ pk_indices sch = [].
Proof.
  destruct sch.
  inversion h. simpl in H |- *. clear h. rewrite <- H in range0.
  destruct pk_indices0. easy. apply Forall_inv in range0. simpl in range0. omega.
Qed.

Lemma tuple_schema_length_eq (sch : schema) (t : tuple sch) : length (col_types sch) = length (elts t).
Proof.
  destruct sch, t as [elts ad]. simpl. unfold is_valid_elt_list in ad.
  simpl in ad. apply mem_lemmas.Forall2_length in ad. auto.
Qed.  

Program Definition tuple_tail {sch} (t : tuple sch) : tuple (schema_tail sch) :=
  mk_tuple (schema_tail sch) (tail (elts t)) _.
Next Obligation.
  destruct sch, t. simpl.
  inversion adequacy0; simpl in *;
  subst elts0; subst col_types0; simpl; easy.
Qed.  

Lemma elts_tuple_tail {sch} (t : tuple sch) : elts (tuple_tail t) = tail (elts t).
reflexivity.
Qed.

Definition table (sch : schema) := list (tuple sch).

Definition empty_table (sch : schema) : table sch := []. 


(* REPRESENTATION IN MEMORY *)


(* ----------------------------- SCHEMA ------------------------------- *)

Definition val_of_col_t (c : col_t) : val := match c with
                                             | Int => Vptrofs (Ptrofs.zero)
                                             | Str => Vptrofs (Ptrofs.one)
                                             end.

Fixpoint coltype_rep (sh: share) (col: col_t) (p: val) : mpred :=
data_at sh size_t (val_of_col_t col) p.

Fixpoint listcol_rep  (sh: share) (lst: list col_t) (p: val) : mpred := 
 match lst with 
   | t::hs => EX y: val, coltype_rep sh t p * listcol_rep sh hs y
   | _ => !! (p = nullval) && emp
 end.

Fixpoint listpk_rep (sh: share) (lst: list Z) (p: val) : mpred :=
 match lst with
  | h :: hs => EX y: val, data_at sh size_t (Vptrofs(Ptrofs.repr h)) p * listpk_rep sh hs y
  | _ => !! (p = nullval) && emp
 end.

Definition schema_rep (sh: share) (sch: schema) (p: val) : mpred :=
EX x: val, EX y: val, listcol_rep sh (col_types sch) x * listpk_rep sh (pk_indices sch) y.

Definition num_cols (sch: schema) : nat :=
length (col_types sch).

Definition schlen (sch: schema) : nat :=
length (col_types sch) + length (pk_indices sch).

(* ----------------------------- TUPLE ------------------------------- *)


Definition elt_rep (sh: share) (Q: mpred) (e: elt) (p: val) : mpred := 
  match e with
  | int_elt n => data_at sh (size_t) (Vptrofs(n)) p
  | string_elt s => EX q: val, data_at sh (tptr tschar) q p * 
    !! (Q |-- (EX sh': share, !! readable_share sh' && cstring sh' s q * TT))
  end.

Program Fixpoint tuple_rep (sh: share) (Q: mpred) {sch} (t: tuple sch) (p: val) {measure (length (elts t))} : mpred :=
 match elts t with 
 | h :: hs => EX y: val, elt_rep sh Q h p * tuple_rep sh Q (tuple_tail t) y
 | _ => !! (p = nullval) && emp
 end.
Local Obligation Tactic := idtac. (* otherwise removes some hyp... *)
Next Obligation.
  intros.
  rewrite elts_tuple_tail. destruct (elts t). easy. simpl. omega.
Qed.
Next Obligation.
  easy.
Qed.

Print iter_sepcon.

  (* representing an array of data as a list of tuples *)
Definition db_rep (sh: share) (sch: schema) (data: list (tuple sch)) (p: val): mpred :=
  iter_sepcon 
  !! data_at_ sh (tarray size_t (Z.of_nat (num_cols sch * length data))) p.


(* ----------------------------- INDEX ------------------------------- *)

Import Trie.

 Inductive db_index: Type :=
  | int_index: relation val -> cursor val -> db_index
  | string_index: trie val -> db_index.

Fixpoint db_index_rep (dbind: db_index) (numrec: nat) (p: val)  : mpred :=
  match dbind with 
  | int_index rel cur => relation_rep rel numrec * cursor_rep cur p
  | string_index tr => trie_rep tr
  end.

(*
Definition relation_rep (r:relation val) (numrec:nat) :mpred :=
  match r with
  (n,prel) =>
    malloc_token Tsh trelation prel *
    data_at Tsh trelation (getval n, (Vint(Int.repr(Z.of_nat(numrec))), (Vint (Int.repr (Z.of_nat(get_depth r)))))) prel *
    btnode_rep n
  end.
*)

(*
Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  match r with (_,prel) =>
               data_at Tsh tcursor (prel,(
                                    Vint(Int.repr((Zlength c) - 1)),(
                                    List.rev (map (fun x => (Vint(Int.repr(rep_index (snd x)))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.
*)

(*
  Fixpoint trie_rep (t: trie val): mpred :=
    match t with
    | Trie.trienode_of addr tableform listform =>
      BTree.table_rep tableform addr * (* that actually at this address we store a B+ tree *)
      iter_sepcon (compose (@bordernode_rep trie_rep) snd) listform
    end.
*)







