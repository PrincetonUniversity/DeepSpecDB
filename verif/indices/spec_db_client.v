Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.db_client.
Require Import indices.db_cursor.
Require Import indices.ordered_interface.
Require Import indices.btree_instance.
Require Import indices.spec_BtreeIndexASI.
Require Import indices.verif_stringlist.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec.
Require Import btrees.btrees.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import FunInd.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import OrderedIndex.
Import DB_Cursor.

(* ================= STRUCTS ================= *)

(* the database cursor that holds a tree structure and a cursor structure 
    ( basically a wrapper struct for two pointers *)
Definition btree_cursor_t := Tstruct _BtreeCursor noattr.
Definition entry := Tunion _entry noattr.
Definition domain := Tstruct _domain noattr.
Definition attr_lst := Tstruct _attribute_list noattr.
Definition index_attr := Tstruct _index_attributes noattr.

(* The renamed void*-equivalent structs *)
Definition key_t := Tstruct _key_t noattr.
Definition value_t := Tstruct _value_t noattr.
Definition index_t := Tstruct _index_t noattr.
Definition db_cursor_t := Tstruct _db_cursor_t noattr.

(* ================= STRING REP ================= *)
(* convert between Coq string type & list of bytes *)
Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => O
  | String c s' => S (length s')
  end.

Definition string_rep (s: string) (p: val) : mpred := !! (~ List.In Byte.zero (string_to_list_byte s)) &&
  data_at Ews (tarray tschar (Z.of_nat(length(s)) + 1)) (map Vbyte (string_to_list_byte s ++ [Byte.zero])) p.

Lemma length_string_list_byte_eq:
  forall str: string, Z.of_nat (length str) = Zlength (string_to_list_byte str).
Proof.
  intros str. induction str.
  - simpl. auto.
  - unfold length; fold length. unfold string_to_list_byte; fold string_to_list_byte.
     autorewrite with sublist. rewrite <- IHstr. apply Nat2Z.inj_succ.
Qed.

Definition string_rep_local_facts:
  forall s p, string_rep s p |-- !! (is_pointer_or_null p /\ 
  0 <= Z.of_nat (length s) + 1 <= Ptrofs.max_unsigned).
Proof.
  intros. assert (K: string_rep s p |-- cstring Ews (string_to_list_byte s) p).
  unfold string_rep. unfold cstring. rewrite length_string_list_byte_eq. entailer!.
  sep_apply K. sep_apply cstring_local_facts. entailer!. 
  rewrite length_string_list_byte_eq. split.
  assert (M: 0 <= Zlength (string_to_list_byte s)). apply Zlength_nonneg. omega.
  rewrite <- initialize.max_unsigned_modulus in H. omega.
Qed.
Hint Resolve string_rep_local_facts: saturate_local.

Lemma list_byte_eq: forall s str, string_to_list_byte s = string_to_list_byte str <-> s = str.
Proof. 
  split.
  { intros. generalize dependent str. induction s.
  - intros. inversion H. destruct str.
     + auto.
     + inversion H1.
  - intros. destruct str.
     + inversion H.
     + simpl in H. set (b:= Byte.repr (Z.of_N (Ascii.N_of_ascii a))) in *. 
        set (b0:= Byte.repr (Z.of_N (Ascii.N_of_ascii a0))) in *. assert (K: b = b0) by congruence.
        unfold b, b0 in K.
        apply f_equal with (f:= Byte.unsigned) in K. rewrite !Byte.unsigned_repr in K.
        apply N2Z.inj in K.
        apply f_equal with (f:= Ascii.ascii_of_N) in K.
        rewrite !Ascii.ascii_N_embedding in K. f_equal. auto. inversion H. auto.
        apply ascii_range. apply ascii_range. }
  { intros. f_equal. auto. }
Qed.

Lemma list_byte_neq: forall s str, 
  string_to_list_byte s <> string_to_list_byte str -> s <> str.
Proof.
  intros. generalize dependent str. induction s.
  - unfold not. intros. apply H. apply list_byte_eq in H0. auto.
  - unfold not. intros. apply H. apply list_byte_eq. auto.
Qed.

(* ================= ENTRY REP ================= *)
Definition entry_rep_int (e_ptr : val) (e: val) :=
  malloc_token Ews entry e_ptr * data_at Ews entry (inl e) e_ptr.

Definition entry_rep_string (e_ptr : val) (e: val) := 
  EX s: string,
  malloc_token Ews entry e_ptr *
  (* e is a ptr to a string *)
  data_at Ews entry (inr e) e_ptr *
  malloc_token Ews (tarray tschar (Z.of_nat (length s) + 1)) e *
  string_rep s e.

(* ================= ATTR LIST REP ================= *)

Fixpoint attr_lst_rep (l: list (string * Z)) (p: val): mpred :=
  match l with
  | [] => !!(p = nullval) && emp
  | (s, d) :: tl => EX q:val, EX str_ptr: val, 
                    malloc_token Ews attr_lst p *
                    data_at Ews attr_lst (str_ptr, ((Vlong (Int64.repr d)), q)) p *
                    string_rep s str_ptr *
                    malloc_token Ews (tarray tschar (Z.of_nat (length s) + 1)) str_ptr *
                    attr_lst_rep tl q
  end.


Definition attr_lst_local_facts:
  forall l p, attr_lst_rep l p |-- !! (is_pointer_or_null p /\ (p=nullval <-> l = [])).
Proof.
  intros l. induction l as [ | [] tl]; intro p; simpl.
  + entailer!. easy.
  + Intros q str_ptr. unfold string_rep. entailer!. now apply field_compatible_nullval1 in H1.
Qed.
Hint Resolve attr_lst_local_facts: saturate_local.

Definition attr_lst_valid_pointer:
  forall l p, attr_lst_rep l p |-- valid_pointer p.
Proof. intros [|[]] p; cbn; entailer. Qed.
Hint Resolve attr_lst_valid_pointer: valid_pointer.

Definition attr_lst_hole_rep (lst0: list (string * Z)) (lst: list (string * Z)) (p0 p: val) : mpred :=
  attr_lst_rep lst0 p0 * (attr_lst_rep lst0 p0 -* attr_lst_rep lst p). 


(* ================= INDEX ATTR REP ================= *)

Definition index_attr_rep (attr: list (string * Z)) (pk_attr: list (string * Z)) (p: val)  (q: val) (s: val) :=
  malloc_token Ews index_attr s *
  data_at Ews index_attr (p, q) s *
  attr_lst_rep attr p *
  attr_lst_rep pk_attr q.

(* ================= BTREE CURSOR ================= *)

Definition btree_cursor: db_cursor btree_index :=
{|  db_cursor_type := db_cursor_t;
    db_key_type := key_t;
    db_value_type := value_t;
    db_index_type := index_t;

    db_entry_rep := fun e_ptr int_val => entry_rep_int e_ptr int_val;

    db_cursor_rep := fun cur tree_ptr cur_ptr wrap_ptr =>
        (cursor_repr btree_index cur cur_ptr *
        malloc_token Ews btree_cursor_t wrap_ptr * 
        data_at Ews btree_cursor_t (tree_ptr, cur_ptr) wrap_ptr)%logic;
|}.

(* ================= SPECS ================= *)

Definition exit_spec := (_exit, exit_spec').
Definition malloc_spec := (_malloc, malloc_spec').
Definition free_spec := (_free, free_spec').

Definition btree_create_index_spec := 
  (_btree_create_index, create_index_spec_vp btree_index btree_cursor).
Definition btree_cardinality_spec := 
  (_btree_cardinality, (cardinality_spec_vp btree_index btree_cursor)).
Definition btree_cursor_has_next_spec :=
  (_btree_cursor_has_next, cursor_has_next_spec_vp btree_index btree_cursor).
Definition btree_move_to_next_spec :=
  (_btree_move_to_next, move_to_next_spec_vp btree_index btree_cursor).
Definition btree_move_to_first_spec :=
  (_btree_move_to_first, move_to_first_spec_vp btree_index btree_cursor).
Definition btree_get_record_spec := 
  (_btree_get_record, get_record_spec_vp btree_index btree_cursor).
Definition btree_create_cursor_spec := 
  (_btree_create_cursor, create_cursor_spec_vp btree_index btree_cursor).
Definition btree_go_to_key_spec := 
  (_btree_go_to_key, go_to_key_spec_vp btree_index btree_cursor).
Definition btree_put_record_spec := 
  (_btree_put_record, put_record_spec_vp btree_index btree_cursor).

Definition attr_list_length_spec :=
  DECLARE _attr_list_length
  WITH p: val, l: list(string * Z)
  PRE [tptr attr_lst]
    PROP()
    PARAMS(p) GLOBALS()
    SEP(attr_lst_rep l p)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (Zlength l))))
    SEP(attr_lst_rep l p).


Fixpoint id_index (lst: list(string*Z)) (id:string) : Z :=
  match lst with
  | [] => 0
  | (s, z) :: t => if eqb id s then ((Zlength lst) - (Zlength t) - 1)
                        else 1 + id_index t id
  end.

Definition lst_is_empty (lst: list(string*Z)) : bool :=
 match lst with
  | [] => true
  | _ => false
 end.

(* covers both the cases when list is empty and when item not in list *)
Definition calc_indx (lst: list(string*Z)) (n: Z) : Z :=
  if (Z.eqb n (Zlength lst)) then -1 else n.

Definition index_of_pk_col_spec :=
  DECLARE _index_of_pk_column
  WITH lst: list(string * Z), p: val, pk: list(string*Z), q: val, id: string
  PRE [tptr attr_lst, tptr attr_lst]
    PROP( pk <> [] /\ (fst (hd (""%string, -1) pk)) = id)
    PARAMS(p; q) GLOBALS()
    SEP(attr_lst_rep lst p; attr_lst_rep pk q)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (calc_indx lst (id_index lst id)))))
    SEP(attr_lst_rep lst p; attr_lst_rep pk q).

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [tptr tschar, tptr tschar ]
    PROP ()
    PARAMS(str1; str2) GLOBALS()
    SEP (cstring Ews s1 str1; cstring Ews s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring Ews s1 str1; cstring Ews s2 str2).

Definition malloc_btree_cursor_spec :=
  DECLARE _malloc_btree_cursor
  WITH r: relation val, gv: globals
  PRE [tptr tvoid]
    PROP()
    PARAMS() GLOBALS(gv)
    SEP(mem_mgr gv)
  POST [tptr tcursor]
    EX cur_ptr,
    PROP()
    LOCAL(temp ret_temp cur_ptr)
    SEP(mem_mgr gv; relation_rep r; cursor_rep (first_cursor (get_root r)) r cur_ptr).

Definition Gprog :=  BtreeIndexASI ++ [exit_spec; malloc_spec; free_spec; strcmp_spec] ++ 
  [btree_create_index_spec; btree_cardinality_spec; btree_cursor_has_next_spec;
   btree_move_to_next_spec; btree_move_to_first_spec; btree_go_to_key_spec; 
   btree_get_record_spec; btree_create_cursor_spec; btree_put_record_spec ] ++ 
  [ attr_list_length_spec; index_of_pk_col_spec; malloc_btree_cursor_spec].


