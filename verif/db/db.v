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

(* ----------------------------- SCHEMA ------------------------------- *)

Inductive col_t : Type := Int | Str.

(* Schema type - has a list of column types AND the ordered list of indices of PK columns *)
Record schema_t: Type := mk_schema
  { col_types : list col_t
  ; pk_indices : list Z }.


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

Definition schema_rep (sh: share) (sch: schema_t) (p: val) : mpred :=
EX x: val, EX y: val, listcol_rep sh (col_types sch) x * listpk_rep sh (pk_indices sch) y.

Definition num_cols (sch: schema_t) : nat :=
length (col_types sch).

Definition schlen (sch: schema_t) : nat :=
length (col_types sch) + length (pk_indices sch).

(* ----------------------------- TUPLE ------------------------------- *)

(* element type - what tuples in the DB consist of *)



 Inductive elt_t : Type := 
  | int_elt: ptrofs -> elt_t
  | string_elt: list byte -> elt_t. 

(* a tuple is a list of elements *)
Definition tuple_t : Type := list elt_t.

Definition elt_rep (sh: share) (Q: mpred) (e: elt_t) (p: val) : mpred := 
  match e with
  | int_elt n => data_at sh (size_t) (Vptrofs(n)) p
  | string_elt s => EX q: val, data_at sh (tptr tschar) q p * 
    !! (Q |-- (EX sh': share, !! readable_share sh' && cstring sh' s q * TT))
  end.

Fixpoint tuple_rep (sh: share) (Q: mpred) (t: tuple_t) (p: val) : mpred := 
 match t with 
 | h :: hs => EX y: val, elt_rep sh Q h p * tuple_rep sh Q hs y
 | _ => !! (p = nullval) && emp
end.

(* representing an array of data as a list of tuples *)
Definition db_rep (sh: share) (sch: schema_t) (data: list tuple_t) (p: val): mpred :=
  !! (Forall (fun l => length l = num_cols sch) data)
   && data_at_ sh (tarray size_t (Z.of_nat (num_cols sch * length data))) p.


Fixpoint is_valid_tuple (sch : schema_t) (t : tuple_t) : Prop :=
  match col_types sch, t with
  | Int :: colts, int_elt n :: elts => is_valid_tuple (mk_schema colts (pk_indices sch)) elts
  | Str :: colts, string_elt s :: elts => is_valid_tuple (mk_schema colts (pk_indices sch)) elts
  | [], [] => True
  | _, _ => False
  end.

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







