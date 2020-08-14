Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.db_client.
Require Import indices.db_cursor.
Require Import indices.ordered_interface.
Require Import indices.btree_instance.
Require Import indices.spec_BtreeIndexASI.
Require Import indices.verif_stringlist.
Require Import btrees.btrees_sep.
Require Import btrees.btrees.
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

(* method table *)
Definition ord_index_mtable := Tstruct _OrdIndexMtable noattr.

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

(* ================= ENTRY ARRAY REP ================= *)

Inductive entry_contents :=
 | int_entry: Z -> entry_contents
 | str_entry: string -> entry_contents.

Definition entry_rep (e: entry_contents * reptype entry) : mpred :=
  match e with
  | (int_entry num, inl v) => !! (exists i: Ptrofs.int, v = Vptrofs i /\ Ptrofs.unsigned i = num) && emp
  | (str_entry s, inr v) => malloc_token Ews (tarray tschar (Z.of_nat (length s) + 1)) v * string_rep s v
  | _ => FF
 end.

Definition entry_array_rep (lst: list entry_contents) (p: val) := 
  EX a: list (entry_contents * reptype entry),
  data_at Ews (tarray entry (Zlength lst)) (map snd a) p *
  iter_sepcon entry_rep a.

Definition entry_array_local_facts:
  forall l p, entry_array_rep l p |-- !! (isptr p).
Proof.
  intros l p. unfold entry_array_rep. Intros a.
  rewrite data_at_isptr. entailer!. 
Qed.

(* ================= INDEX ATTR REP ================= *)

Definition index_attr_rep (attr: list (string * Z)) (pk_attr: list (string * Z))(s: val) :=
  EX (p:val) (q:val),
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

    db_cursor_rep := fun cur wrap_ptr =>
        (EX tree_ptr cur_ptr, cursor_repr btree_index cur cur_ptr *
        malloc_token Ews btree_cursor_t wrap_ptr * 
        data_at Ews btree_cursor_t (tree_ptr, cur_ptr) wrap_ptr)%logic;
|}.


(* ================= SPECS  ================= *)

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

(* ================= ORD MTABLE ================= *)

Definition ord_mtable_rep (p: val):=
  EX ci cc c mtn mtf gtk chn pr gr: val, 
  malloc_token Ews ord_index_mtable p *
  data_at Ews ord_index_mtable (ci, (cc, (c, (mtn, (mtf, (gtk, (chn, (pr, gr)))))))) p *
  func_ptr' (snd btree_create_index_spec) ci *
  func_ptr' (snd btree_create_cursor_spec) cc *
  func_ptr' (snd btree_cardinality_spec) c *
  func_ptr' (snd btree_move_to_next_spec) mtn *
  func_ptr' (snd btree_move_to_first_spec) mtf *
  func_ptr' (snd btree_go_to_key_spec) gtk *
  func_ptr' (snd btree_cursor_has_next_spec) chn *
  func_ptr' (snd btree_put_record_spec) pr *
  func_ptr' (snd btree_get_record_spec) gr.

(* ================= HELPER SPECS ================= *)

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

Definition malloc_btree_cursor_spec
  (oi: OrderedIndex.index) (db: db_cursor oi) :=
  DECLARE _malloc_btree_cursor
  WITH u: unit, gv: globals
  PRE []
    PROP()
    PARAMS() GLOBALS(gv)
    SEP(mem_mgr gv; ord_mtable_rep (gv _btree_mtable))
  POST [tptr (db_cursor_type oi db)]
    EX ws_ptr r t_ptr,
    PROP()
    LOCAL(temp ret_temp ws_ptr)
    SEP(mem_mgr gv; ord_mtable_rep (gv _btree_mtable); oi.(t_repr) r t_ptr; 
      (oi.(t_repr) r t_ptr -* (db_cursor_rep oi db) (oi.(create_cursor) r) ws_ptr)).

Fixpoint fill (oi: OrderedIndex.index) 
  (cur: oi.(cursor)) (lst: list (oi.(key) * oi.(value) * val)) (newcur: oi.(cursor)):=
  match lst with
  | [] => (cur = newcur)
  | (k, v, p) :: t => exists cur' : oi.(cursor), (oi.(put_record) cur k v p cur') /\ fill oi cur' t newcur
  end.

(* pk is one column for now. 
    this function calculates the list of pairs (keys and values) to be inserted into the relation
    from a list of entries (cells in the array). 

    for each row i, we have one key and value
    the ptr to the row (value) is just the ptr to the array, plus i * numcols
    numcols = length of schema

    the key is the entry in the row that is at the offset of the pk column *)
Definition calc_insertlst (oi: OrderedIndex.index) (numrows: Z) (schema: list(string*Z))
  (pk: list(string*Z)) (data: list entry_contents) : list (oi.(key) * oi.(value)). Admitted.

Definition fill_relation_spec
  (oi: OrderedIndex.index) (db: db_cursor oi) :=
  DECLARE _fill_relation
  WITH data_ptr: val, ws_ptr: val, numrows: Z, ip: val, 
           data: list entry_contents, cur: oi.(cursor), 
           attrs: list(string*Z), pk_attrs: list(string*Z), gv: globals
  PRE [tptr entry, tptr (db_cursor_type oi db), size_t, tptr index_attr]
    PROP(Zlength(pk_attrs) = 1 /\ exists insertlst, insertlst = calc_insertlst oi numrows attrs pk_attrs data)
    PARAMS(data_ptr; ws_ptr; (Vptrofs (Ptrofs.repr numrows)); ip) GLOBALS(gv)
    SEP(mem_mgr gv; 
          entry_array_rep data data_ptr;
          ord_mtable_rep (gv _btree_mtable);
          index_attr_rep attrs pk_attrs ip;
          (db_cursor_rep oi db) cur ws_ptr)
  POST [tptr (db_cursor_type oi db)]
    EX newcur insertlst, 
    PROP(fill oi cur insertlst newcur)
    LOCAL(temp ret_temp ws_ptr)
    SEP(mem_mgr gv; 
          entry_array_rep data data_ptr;
          ord_mtable_rep (gv _btree_mtable);
          index_attr_rep attrs pk_attrs ip;
          (db_cursor_rep oi db) newcur ws_ptr).

Definition lib_specs :=  [exit_spec; malloc_spec; free_spec; strcmp_spec].
Definition index_specs := [btree_create_index_spec; btree_cardinality_spec; btree_cursor_has_next_spec;
   btree_move_to_next_spec; btree_move_to_first_spec; btree_go_to_key_spec; 
   btree_get_record_spec; btree_create_cursor_spec; btree_put_record_spec ].
Definition client_specs :=   [ attr_list_length_spec; index_of_pk_col_spec; 
   malloc_btree_cursor_spec btree_index btree_cursor; fill_relation_spec btree_index btree_cursor].

Definition Gprog :=  BtreeIndexASI ++ lib_specs ++ index_specs ++ client_specs.

