From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "../../src/db_operations_light.c"%string.
  Definition normalized := true.
End Info.

Definition _Cursor : ident := 28%positive.
Definition _Q : ident := 108%positive.
Definition _RL_CursorIsValid : ident := 100%positive.
Definition _RL_FreeCursor : ident := 99%positive.
Definition _RL_GetRecord : ident := 102%positive.
Definition _RL_IsEmpty : ident := 105%positive.
Definition _RL_MoveToFirst : ident := 103%positive.
Definition _RL_MoveToNext : ident := 104%positive.
Definition _RL_NewCursor : ident := 98%positive.
Definition _RL_NewRelation : ident := 97%positive.
Definition _RL_PutRecord : ident := 101%positive.
Definition _Relation : ident := 19%positive.
Definition ___assert_fail : ident := 96%positive.
Definition ___builtin_ais_annot : ident := 41%positive.
Definition ___builtin_annot : ident := 48%positive.
Definition ___builtin_annot_intval : ident := 49%positive.
Definition ___builtin_bswap : ident := 42%positive.
Definition ___builtin_bswap16 : ident := 44%positive.
Definition ___builtin_bswap32 : ident := 43%positive.
Definition ___builtin_bswap64 : ident := 74%positive.
Definition ___builtin_clz : ident := 75%positive.
Definition ___builtin_clzl : ident := 76%positive.
Definition ___builtin_clzll : ident := 77%positive.
Definition ___builtin_ctz : ident := 78%positive.
Definition ___builtin_ctzl : ident := 79%positive.
Definition ___builtin_ctzll : ident := 80%positive.
Definition ___builtin_debug : ident := 92%positive.
Definition ___builtin_fabs : ident := 45%positive.
Definition ___builtin_fmadd : ident := 83%positive.
Definition ___builtin_fmax : ident := 81%positive.
Definition ___builtin_fmin : ident := 82%positive.
Definition ___builtin_fmsub : ident := 84%positive.
Definition ___builtin_fnmadd : ident := 85%positive.
Definition ___builtin_fnmsub : ident := 86%positive.
Definition ___builtin_fsqrt : ident := 46%positive.
Definition ___builtin_membar : ident := 50%positive.
Definition ___builtin_memcpy_aligned : ident := 47%positive.
Definition ___builtin_nop : ident := 91%positive.
Definition ___builtin_read16_reversed : ident := 87%positive.
Definition ___builtin_read32_reversed : ident := 88%positive.
Definition ___builtin_va_arg : ident := 52%positive.
Definition ___builtin_va_copy : ident := 53%positive.
Definition ___builtin_va_end : ident := 54%positive.
Definition ___builtin_va_start : ident := 51%positive.
Definition ___builtin_write16_reversed : ident := 89%positive.
Definition ___builtin_write32_reversed : ident := 90%positive.
Definition ___compcert_i64_dtos : ident := 59%positive.
Definition ___compcert_i64_dtou : ident := 60%positive.
Definition ___compcert_i64_sar : ident := 71%positive.
Definition ___compcert_i64_sdiv : ident := 65%positive.
Definition ___compcert_i64_shl : ident := 69%positive.
Definition ___compcert_i64_shr : ident := 70%positive.
Definition ___compcert_i64_smod : ident := 67%positive.
Definition ___compcert_i64_smulh : ident := 72%positive.
Definition ___compcert_i64_stod : ident := 61%positive.
Definition ___compcert_i64_stof : ident := 63%positive.
Definition ___compcert_i64_udiv : ident := 66%positive.
Definition ___compcert_i64_umod : ident := 68%positive.
Definition ___compcert_i64_umulh : ident := 73%positive.
Definition ___compcert_i64_utod : ident := 62%positive.
Definition ___compcert_i64_utof : ident := 64%positive.
Definition ___compcert_va_composite : ident := 58%positive.
Definition ___compcert_va_float64 : ident := 57%positive.
Definition ___compcert_va_int32 : ident := 55%positive.
Definition ___compcert_va_int64 : ident := 56%positive.
Definition ___func__ : ident := 169%positive.
Definition ___stringlit_1 : ident := 170%positive.
Definition ___stringlit_2 : ident := 171%positive.
Definition _a : ident := 133%positive.
Definition _attribute_list_length : ident := 127%positive.
Definition _attribute_list_t : ident := 16%positive.
Definition _attrs : ident := 17%positive.
Definition _attrs_all : ident := 146%positive.
Definition _attrs_proj : ident := 151%positive.
Definition _bt : ident := 27%positive.
Definition _build_keypair : ident := 123%positive.
Definition _c : ident := 29%positive.
Definition _close : ident := 23%positive.
Definition _close_iterator : ident := 131%positive.
Definition _current : ident := 152%positive.
Definition _current_inner : ident := 38%positive.
Definition _current_outer : ident := 39%positive.
Definition _current_tuple : ident := 176%positive.
Definition _d : ident := 142%positive.
Definition _data : ident := 1%positive.
Definition _dom : ident := 147%positive.
Definition _domain : ident := 15%positive.
Definition _e : ident := 135%positive.
Definition _elem : ident := 2%positive.
Definition _env : ident := 25%positive.
Definition _exit : ident := 107%positive.
Definition _fifo : ident := 6%positive.
Definition _fifo_empty : ident := 114%positive.
Definition _fifo_get : ident := 116%positive.
Definition _fifo_new : ident := 109%positive.
Definition _fifo_put : ident := 113%positive.
Definition _get_field_address : ident := 150%positive.
Definition _get_next : ident := 130%positive.
Definition _get_offset : ident := 148%positive.
Definition _get_projection : ident := 153%positive.
Definition _get_schema : ident := 145%positive.
Definition _get_schema_aux : ident := 143%positive.
Definition _h : ident := 111%positive.
Definition _head : ident := 4%positive.
Definition _i : ident := 175%positive.
Definition _id : ident := 14%positive.
Definition _ind : ident := 156%positive.
Definition _ind_on_inner : ident := 36%positive.
Definition _ind_on_inner_sch : ident := 37%positive.
Definition _index_data : ident := 178%positive.
Definition _index_insert : ident := 119%positive.
Definition _index_join : ident := 172%positive.
Definition _index_join_close : ident := 167%positive.
Definition _index_join_env : ident := 40%positive.
Definition _index_join_init : ident := 159%positive.
Definition _index_join_iterator_mtable : ident := 168%positive.
Definition _index_join_next : ident := 166%positive.
Definition _index_lookup : ident := 120%positive.
Definition _index_new : ident := 118%positive.
Definition _index_scan : ident := 158%positive.
Definition _init : ident := 22%positive.
Definition _init_iterator : ident := 129%positive.
Definition _inner_attrs : ident := 34%positive.
Definition _inner_join_attrs : ident := 35%positive.
Definition _inner_t : ident := 164%positive.
Definition _inner_t_length : ident := 161%positive.
Definition _inner_t_ofs : ident := 165%positive.
Definition _inthash_schema : ident := 121%positive.
Definition _it : ident := 128%positive.
Definition _iterator_t : ident := 26%positive.
Definition _join_length : ident := 162%positive.
Definition _k : ident := 177%positive.
Definition _l : ident := 125%positive.
Definition _main : ident := 179%positive.
Definition _make_elem : ident := 117%positive.
Definition _malloc : ident := 93%positive.
Definition _materialize : ident := 134%positive.
Definition _memcpy : ident := 94%positive.
Definition _methods : ident := 24%positive.
Definition _mtable : ident := 11%positive.
Definition _n : ident := 115%positive.
Definition _new_t : ident := 163%positive.
Definition _next : ident := 3%positive.
Definition _ofs : ident := 149%positive.
Definition _outer : ident := 31%positive.
Definition _outer_attrs : ident := 32%positive.
Definition _outer_join_attrs : ident := 33%positive.
Definition _outer_t_length : ident := 160%positive.
Definition _p : ident := 110%positive.
Definition _pk_attrs : ident := 18%positive.
Definition _pk_index : ident := 20%positive.
Definition _primary_key : ident := 174%positive.
Definition _proj : ident := 157%positive.
Definition _r : ident := 140%positive.
Definition _rel : ident := 154%positive.
Definition _relation_t : ident := 21%positive.
Definition _res : ident := 132%positive.
Definition _s : ident := 144%positive.
Definition _sch : ident := 155%positive.
Definition _schema_insert : ident := 8%positive.
Definition _schema_lookup : ident := 9%positive.
Definition _schema_methods : ident := 10%positive.
Definition _schema_new : ident := 7%positive.
Definition _schema_private : ident := 12%positive.
Definition _schema_t : ident := 13%positive.
Definition _seq_scan : ident := 141%positive.
Definition _seq_scan_close : ident := 138%positive.
Definition _seq_scan_env : ident := 30%positive.
Definition _seq_scan_init : ident := 136%positive.
Definition _seq_scan_iterator_mtable : ident := 139%positive.
Definition _seq_scan_next : ident := 137%positive.
Definition _strcmp : ident := 95%positive.
Definition _stringlist_schema : ident := 122%positive.
Definition _surely_malloc : ident := 106%positive.
Definition _t : ident := 112%positive.
Definition _tail : ident := 5%positive.
Definition _tuple_count : ident := 173%positive.
Definition _tuple_schema : ident := 124%positive.
Definition _x : ident := 126%positive.
Definition _t'1 : ident := 180%positive.
Definition _t'10 : ident := 189%positive.
Definition _t'11 : ident := 190%positive.
Definition _t'12 : ident := 191%positive.
Definition _t'13 : ident := 192%positive.
Definition _t'14 : ident := 193%positive.
Definition _t'15 : ident := 194%positive.
Definition _t'16 : ident := 195%positive.
Definition _t'17 : ident := 196%positive.
Definition _t'18 : ident := 197%positive.
Definition _t'19 : ident := 198%positive.
Definition _t'2 : ident := 181%positive.
Definition _t'20 : ident := 199%positive.
Definition _t'21 : ident := 200%positive.
Definition _t'22 : ident := 201%positive.
Definition _t'23 : ident := 202%positive.
Definition _t'24 : ident := 203%positive.
Definition _t'25 : ident := 204%positive.
Definition _t'26 : ident := 205%positive.
Definition _t'27 : ident := 206%positive.
Definition _t'28 : ident := 207%positive.
Definition _t'29 : ident := 208%positive.
Definition _t'3 : ident := 182%positive.
Definition _t'30 : ident := 209%positive.
Definition _t'31 : ident := 210%positive.
Definition _t'32 : ident := 211%positive.
Definition _t'33 : ident := 212%positive.
Definition _t'34 : ident := 213%positive.
Definition _t'4 : ident := 183%positive.
Definition _t'5 : ident := 184%positive.
Definition _t'6 : ident := 185%positive.
Definition _t'7 : ident := 186%positive.
Definition _t'8 : ident := 187%positive.
Definition _t'9 : ident := 188%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 83);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fifo_new := {|
  fn_return := (tptr (Tstruct _fifo noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_Q, (tptr (Tstruct _fifo noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _fifo noattr) tuint) :: nil))
    (Sset _Q
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _fifo noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
          (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
            (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _Q (tptr (Tstruct _fifo noattr))))))))
|}.

Definition f_fifo_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) ::
                (_p, (tptr (Tstruct _elem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) ::
               (_t, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _elem noattr)))
        (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _h
      (Efield
        (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
          (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _elem noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
          (Etempvar _p (tptr (Tstruct _elem noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
          (Etempvar _p (tptr (Tstruct _elem noattr)))))
      (Ssequence
        (Sset _t
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _elem noattr)))
                (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr)))
            (Etempvar _p (tptr (Tstruct _elem noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
                (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
            (Etempvar _p (tptr (Tstruct _elem noattr)))))))))
|}.

Definition f_fifo_empty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
        (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
  (Sreturn (Some (Ebinop Oeq (Etempvar _h (tptr (Tstruct _elem noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_fifo_get := {|
  fn_return := (tptr (Tstruct _elem noattr));
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) ::
               (_n, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
        (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _h (tptr (Tstruct _elem noattr)))
          (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
            (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
        (Etempvar _n (tptr (Tstruct _elem noattr))))
      (Sreturn (Some (Etempvar _h (tptr (Tstruct _elem noattr))))))))
|}.

Definition f_make_elem := {|
  fn_return := (tptr (Tstruct _elem noattr));
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _elem noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _elem noattr) tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _elem noattr)))
          (Tstruct _elem noattr)) _data (tptr tvoid))
      (Etempvar _data (tptr tvoid)))
    (Sreturn (Some (Etempvar _p (tptr (Tstruct _elem noattr)))))))
|}.

Definition v_inthash_schema := {|
  gvar_info := (Tstruct _schema_t noattr);
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_stringlist_schema := {|
  gvar_info := (Tstruct _schema_t noattr);
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_attribute_list_length := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_n, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x (Etempvar _l (tptr (Tstruct _attribute_list_t noattr))))
  (Ssequence
    (Sset _n (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Etempvar _x (tptr (Tstruct _attribute_list_t noattr)))
        (Ssequence
          (Sset _x
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _next
              (tptr (Tstruct _attribute_list_t noattr))))
          (Sset _n
            (Ebinop Oadd (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Sreturn (Some (Etempvar _n tuint))))))
|}.

Definition f_init_iterator := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_it, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
               (_t'1, (tptr (Tstruct _methods noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
        (Tstruct _iterator_t noattr)) _mtable
      (tptr (Tstruct _methods noattr))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _t'1 (tptr (Tstruct _methods noattr)))
          (Tstruct _methods noattr)) _init
        (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
            (Tstruct _iterator_t noattr)) _env (tptr tvoid)))
      (Scall None
        (Etempvar _t'2 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default)))
        ((Etempvar _t'3 (tptr tvoid)) :: nil)))))
|}.

Definition f_get_next := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_it, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3,
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                        cc_default))) ::
               (_t'2, (tptr (Tstruct _methods noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
          (Tstruct _iterator_t noattr)) _mtable
        (tptr (Tstruct _methods noattr))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _t'2 (tptr (Tstruct _methods noattr)))
            (Tstruct _methods noattr)) _next
          (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
              (Tstruct _iterator_t noattr)) _env (tptr tvoid)))
        (Scall (Some _t'1)
          (Etempvar _t'3 (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default)))
          ((Etempvar _t'4 (tptr tvoid)) :: nil)))))
  (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
|}.

Definition f_close_iterator := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_it, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
               (_t'1, (tptr (Tstruct _methods noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
        (Tstruct _iterator_t noattr)) _mtable
      (tptr (Tstruct _methods noattr))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _t'1 (tptr (Tstruct _methods noattr)))
          (Tstruct _methods noattr)) _close
        (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
            (Tstruct _iterator_t noattr)) _env (tptr tvoid)))
      (Scall None
        (Etempvar _t'2 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default)))
        ((Etempvar _t'3 (tptr tvoid)) :: nil)))))
|}.

Definition f_materialize := {|
  fn_return := (tptr (Tstruct _fifo noattr));
  fn_callconv := cc_default;
  fn_params := ((_it, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr (Tstruct _fifo noattr))) :: (_a, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _elem noattr))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _fifo_new (Tfunction Tnil (tptr (Tstruct _fifo noattr))
                        cc_default)) nil)
    (Sset _res (Etempvar _t'1 (tptr (Tstruct _fifo noattr)))))
  (Ssequence
    (Scall None
      (Evar _init_iterator (Tfunction
                             (Tcons (tptr (Tstruct _iterator_t noattr)) Tnil)
                             tvoid cc_default))
      ((Etempvar _it (tptr (Tstruct _iterator_t noattr))) :: nil))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _get_next (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _iterator_t noattr))
                                      Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _it (tptr (Tstruct _iterator_t noattr))) :: nil))
                (Sset _t'3 (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tvoid))))
              (Sset _a (Etempvar _t'3 (tptr tvoid))))
            (Sifthenelse (Etempvar _t'3 (tptr tvoid)) Sskip Sbreak))
          (Ssequence
            (Scall (Some _t'4)
              (Evar _make_elem (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr (Tstruct _elem noattr)) cc_default))
              ((Etempvar _a (tptr tvoid)) :: nil))
            (Scall None
              (Evar _fifo_put (Tfunction
                                (Tcons (tptr (Tstruct _fifo noattr))
                                  (Tcons (tptr (Tstruct _elem noattr)) Tnil))
                                tvoid cc_default))
              ((Etempvar _res (tptr (Tstruct _fifo noattr))) ::
               (Etempvar _t'4 (tptr (Tstruct _elem noattr))) :: nil))))
        Sskip)
      (Sreturn (Some (Etempvar _res (tptr (Tstruct _fifo noattr))))))))
|}.

Definition f_seq_scan_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_e, (tptr (Tstruct _seq_scan_env noattr))) ::
               (_t'2, (tptr (Tstruct _Cursor noattr))) ::
               (_t'1, (tptr (Tstruct _Cursor noattr))) ::
               (_t'4, (tptr (Tstruct _Relation noattr))) ::
               (_t'3, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _e
    (Ecast (Etempvar _env (tptr tvoid))
      (tptr (Tstruct _seq_scan_env noattr))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _seq_scan_env noattr)))
                  (Tstruct _seq_scan_env noattr)) _bt
                (tptr (Tstruct _Relation noattr))))
            (Scall (Some _t'1)
              (Evar _RL_NewCursor (Tfunction
                                    (Tcons (tptr (Tstruct _Relation noattr))
                                      Tnil) (tptr (Tstruct _Cursor noattr))
                                    cc_default))
              ((Etempvar _t'4 (tptr (Tstruct _Relation noattr))) :: nil)))
          (Sset _t'2
            (Ecast (Etempvar _t'1 (tptr (Tstruct _Cursor noattr)))
              (tptr (Tstruct _Cursor noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _e (tptr (Tstruct _seq_scan_env noattr)))
              (Tstruct _seq_scan_env noattr)) _c
            (tptr (Tstruct _Cursor noattr)))
          (Etempvar _t'2 (tptr (Tstruct _Cursor noattr)))))
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _t'2 (tptr (Tstruct _Cursor noattr))) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _e (tptr (Tstruct _seq_scan_env noattr)))
            (Tstruct _seq_scan_env noattr)) _c
          (tptr (Tstruct _Cursor noattr))))
      (Scall None
        (Evar _RL_MoveToFirst (Tfunction
                                (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                tint cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _Cursor noattr))) :: nil)))))
|}.

Definition f_seq_scan_next := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _Cursor noattr))) ::
               (_res, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Efield
      (Ederef
        (Ecast (Etempvar _env (tptr tvoid))
          (tptr (Tstruct _seq_scan_env noattr)))
        (Tstruct _seq_scan_env noattr)) _c (tptr (Tstruct _Cursor noattr))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _RL_IsEmpty (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tint cc_default))
          ((Etempvar _c (tptr (Tstruct _Cursor noattr))) :: nil))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _RL_CursorIsValid (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil) tint cc_default))
              ((Etempvar _c (tptr (Tstruct _Cursor noattr))) :: nil))
            (Sset _t'2
              (Ecast (Eunop Onotbool (Etempvar _t'3 tint) tint) tbool)))))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _RL_GetRecord (Tfunction
                                (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                (tptr tvoid) cc_default))
          ((Etempvar _c (tptr (Tstruct _Cursor noattr))) :: nil))
        (Sset _res (Etempvar _t'4 (tptr tvoid))))
      (Ssequence
        (Scall None
          (Evar _RL_MoveToNext (Tfunction
                                 (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                 tvoid cc_default))
          ((Etempvar _c (tptr (Tstruct _Cursor noattr))) :: nil))
        (Sreturn (Some (Etempvar _res (tptr tvoid))))))))
|}.

Definition f_seq_scan_close := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Efield
      (Ederef
        (Ecast (Etempvar _env (tptr tvoid))
          (tptr (Tstruct _seq_scan_env noattr)))
        (Tstruct _seq_scan_env noattr)) _c (tptr (Tstruct _Cursor noattr))))
  (Scall None
    (Evar _RL_FreeCursor (Tfunction
                           (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid
                           cc_default))
    ((Etempvar _c (tptr (Tstruct _Cursor noattr))) :: nil)))
|}.

Definition v_seq_scan_iterator_mtable := {|
  gvar_info := (Tstruct _methods noattr);
  gvar_init := (Init_addrof _seq_scan_init (Ptrofs.repr 0) ::
                Init_addrof _seq_scan_next (Ptrofs.repr 0) ::
                Init_addrof _seq_scan_close (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_seq_scan := {|
  fn_return := (tptr (Tstruct _iterator_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (Tstruct _relation_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_it, (tptr (Tstruct _iterator_t noattr))) ::
               (_env, (tptr (Tstruct _seq_scan_env noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _iterator_t noattr) tuint) :: nil))
    (Sset _it (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _it (tptr (Tstruct _iterator_t noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
            (Tstruct _iterator_t noattr)) _mtable
          (tptr (Tstruct _methods noattr)))
        (Eaddrof (Evar _seq_scan_iterator_mtable (Tstruct _methods noattr))
          (tptr (Tstruct _methods noattr))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Esizeof (Tstruct _seq_scan_env noattr) tuint) :: nil))
          (Sset _env (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _env (tptr (Tstruct _seq_scan_env noattr)))
                         tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _r (tptr (Tstruct _relation_t noattr)))
                    (Tstruct _relation_t noattr)) _pk_index
                  (tptr (Tstruct _Relation noattr))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _env (tptr (Tstruct _seq_scan_env noattr)))
                    (Tstruct _seq_scan_env noattr)) _bt
                  (tptr (Tstruct _Relation noattr)))
                (Etempvar _t'3 (tptr (Tstruct _Relation noattr)))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _env (tptr (Tstruct _seq_scan_env noattr)))
                    (Tstruct _seq_scan_env noattr)) _c
                  (tptr (Tstruct _Cursor noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
                      (Tstruct _iterator_t noattr)) _env (tptr tvoid))
                  (Ecast
                    (Etempvar _env (tptr (Tstruct _seq_scan_env noattr)))
                    (tptr tvoid)))
                (Sreturn (Some (Ecast
                                 (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
                                 (tptr (Tstruct _iterator_t noattr)))))))))))))
|}.

Definition f_get_schema_aux := {|
  fn_return := (tptr (Tstruct _schema_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_d, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _d tint)
  (LScons (Some 0)
    (Sreturn (Some (Eaddrof (Evar _inthash_schema (Tstruct _schema_t noattr))
                     (tptr (Tstruct _schema_t noattr)))))
    (LScons (Some 1)
      (Sreturn (Some (Eaddrof
                       (Evar _stringlist_schema (Tstruct _schema_t noattr))
                       (tptr (Tstruct _schema_t noattr)))))
      (LScons None
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        LSnil))))
|}.

Definition f_get_schema := {|
  fn_return := (tptr (Tstruct _schema_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_attrs, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr (Tstruct _schema_t noattr))) ::
               (_t'3, (tptr (Tstruct _schema_t noattr))) ::
               (_t'2, (tptr (Tstruct _schema_t noattr))) ::
               (_t'1, (tptr (Tstruct _schema_t noattr))) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'4, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr)))
                 tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef
              (Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr)))
              (Tstruct _attribute_list_t noattr)) _domain tint))
        (Scall (Some _t'1)
          (Evar _get_schema_aux (Tfunction (Tcons tint Tnil)
                                  (tptr (Tstruct _schema_t noattr))
                                  cc_default)) ((Etempvar _t'6 tint) :: nil)))
      (Sset _s (Etempvar _t'1 (tptr (Tstruct _schema_t noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef
              (Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr)))
              (Tstruct _attribute_list_t noattr)) _next
            (tptr (Tstruct _attribute_list_t noattr))))
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _t'5 (tptr (Tstruct _attribute_list_t noattr)))
                       tint)
          (Sreturn (Some (Etempvar _s (tptr (Tstruct _schema_t noattr)))))
          Sskip))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr)))
                  (Tstruct _attribute_list_t noattr)) _next
                (tptr (Tstruct _attribute_list_t noattr))))
            (Scall (Some _t'2)
              (Evar _get_schema (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _attribute_list_t noattr))
                                    Tnil) (tptr (Tstruct _schema_t noattr))
                                  cc_default))
              ((Etempvar _t'4 (tptr (Tstruct _attribute_list_t noattr))) ::
               nil)))
          (Scall (Some _t'3)
            (Evar _tuple_schema (Tfunction
                                  (Tcons (tptr (Tstruct _schema_t noattr))
                                    (Tcons (tptr (Tstruct _schema_t noattr))
                                      Tnil))
                                  (tptr (Tstruct _schema_t noattr))
                                  cc_default))
            ((Etempvar _s (tptr (Tstruct _schema_t noattr))) ::
             (Etempvar _t'2 (tptr (Tstruct _schema_t noattr))) :: nil)))
        (Sreturn (Some (Etempvar _t'3 (tptr (Tstruct _schema_t noattr)))))))))
|}.

Definition f_get_offset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_attrs_all, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_id, (tptr tschar)) :: (_dom, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_res, tuint) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'5, (tptr tschar)) :: (_t'4, tint) ::
               (_t'3, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _attrs_all (tptr (Tstruct _attribute_list_t noattr)))
                 tint)
    (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 1) tint) :: nil))
    Sskip)
  (Ssequence
    (Sset _x (Etempvar _attrs_all (tptr (Tstruct _attribute_list_t noattr))))
    (Ssequence
      (Sset _res (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _x (tptr (Tstruct _attribute_list_t noattr)))
                      (Tstruct _attribute_list_t noattr)) _id (tptr tschar)))
                (Scall (Some _t'2)
                  (Evar _strcmp (Tfunction
                                  (Tcons (tptr tschar)
                                    (Tcons (tptr tschar) Tnil)) tint
                                  cc_default))
                  ((Etempvar _id (tptr tschar)) ::
                   (Etempvar _t'5 (tptr tschar)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _x (tptr (Tstruct _attribute_list_t noattr)))
                        (Tstruct _attribute_list_t noattr)) _domain tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _dom tint)
                                 (Etempvar _t'4 tint) tint)
                    (Sreturn (Some (Etempvar _res tuint)))
                    (Scall None
                      (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                    cc_default))
                      ((Econst_int (Int.repr 1) tint) :: nil))))
                Sskip))
            (Sset _res
              (Ebinop Oadd (Etempvar _res tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _x (tptr (Tstruct _attribute_list_t noattr)))
                      (Tstruct _attribute_list_t noattr)) _next
                    (tptr (Tstruct _attribute_list_t noattr))))
                (Sset _t'1
                  (Ecast
                    (Etempvar _t'3 (tptr (Tstruct _attribute_list_t noattr)))
                    (tptr (Tstruct _attribute_list_t noattr)))))
              (Sset _x
                (Etempvar _t'1 (tptr (Tstruct _attribute_list_t noattr)))))
            (Sifthenelse (Etempvar _t'1 (tptr (Tstruct _attribute_list_t noattr)))
              Sskip
              Sbreak)))
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))))))
|}.

Definition f_get_field_address := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_attrs_all, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_id, (tptr tschar)) :: (_dom, tint) :: (_t, (tptr tvoid)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_offset (Tfunction
                          (Tcons (tptr (Tstruct _attribute_list_t noattr))
                            (Tcons (tptr tschar) (Tcons tint Tnil))) tint
                          cc_default))
      ((Etempvar _attrs_all (tptr (Tstruct _attribute_list_t noattr))) ::
       (Etempvar _id (tptr tschar)) :: (Etempvar _dom tint) :: nil))
    (Sset _ofs (Etempvar _t'1 tint)))
  (Sreturn (Some (Ecast
                   (Ebinop Oadd
                     (Ecast (Etempvar _t (tptr tvoid)) (tptr tuint))
                     (Etempvar _ofs tuint) (tptr tuint)) (tptr tvoid)))))
|}.

Definition f_get_projection := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_attrs_all, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_t, (tptr tvoid)) ::
                (_attrs_proj, (tptr (Tstruct _attribute_list_t noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tuint) :: (_current, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tint) :: (_t'8, tint) :: (_t'7, (tptr tschar)) ::
               (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'4, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _attrs_proj (tptr (Tstruct _attribute_list_t noattr)))
                 tint)
    (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 1) tint) :: nil))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef
              (Etempvar _attrs_proj (tptr (Tstruct _attribute_list_t noattr)))
              (Tstruct _attribute_list_t noattr)) _id (tptr tschar)))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef
                (Etempvar _attrs_proj (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _domain tint))
          (Scall (Some _t'1)
            (Evar _get_offset (Tfunction
                                (Tcons
                                  (tptr (Tstruct _attribute_list_t noattr))
                                  (Tcons (tptr tschar) (Tcons tint Tnil)))
                                tint cc_default))
            ((Etempvar _attrs_all (tptr (Tstruct _attribute_list_t noattr))) ::
             (Etempvar _t'7 (tptr tschar)) :: (Etempvar _t'8 tint) :: nil))))
      (Sset _ofs (Etempvar _t'1 tint)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t (tptr tvoid)) (tptr tuint))
              (Etempvar _ofs tuint) (tptr tuint)) tuint))
        (Sset _current (Ecast (Etempvar _t'6 tuint) (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Etempvar _attrs_proj (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _next
              (tptr (Tstruct _attribute_list_t noattr))))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _t'5 (tptr (Tstruct _attribute_list_t noattr)))
                         tint)
            (Sreturn (Some (Etempvar _current (tptr tvoid))))
            Sskip))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _attrs_proj (tptr (Tstruct _attribute_list_t noattr)))
                    (Tstruct _attribute_list_t noattr)) _next
                  (tptr (Tstruct _attribute_list_t noattr))))
              (Scall (Some _t'2)
                (Evar _get_projection (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _attribute_list_t noattr))
                                          (Tcons (tptr tvoid)
                                            (Tcons
                                              (tptr (Tstruct _attribute_list_t noattr))
                                              Tnil))) (tptr tvoid)
                                        cc_default))
                ((Etempvar _attrs_all (tptr (Tstruct _attribute_list_t noattr))) ::
                 (Etempvar _t (tptr tvoid)) ::
                 (Etempvar _t'4 (tptr (Tstruct _attribute_list_t noattr))) ::
                 nil)))
            (Scall (Some _t'3)
              (Evar _build_keypair (Tfunction
                                     (Tcons (tptr tvoid)
                                       (Tcons (tptr tvoid) Tnil))
                                     (tptr tvoid) cc_default))
              ((Etempvar _current (tptr tvoid)) ::
               (Etempvar _t'2 (tptr tvoid)) :: nil)))
          (Sreturn (Some (Etempvar _t'3 (tptr tvoid)))))))))
|}.

Definition f_index_scan := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_rel, (tptr (Tstruct _relation_t noattr))) ::
                (_attrs, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_sch, (tptr (Tstruct _schema_t noattr))) ::
               (_ind, (tptr tvoid)) ::
               (_it, (tptr (Tstruct _iterator_t noattr))) ::
               (_t, (tptr tvoid)) :: (_proj, (tptr tvoid)) ::
               (_l, (tptr (Tstruct _fifo noattr))) ::
               (_t'9, (tptr (Tstruct _elem noattr))) ::
               (_t'8, (tptr (Tstruct _fifo noattr))) ::
               (_t'7, (tptr tvoid)) :: (_t'6, (tptr tvoid)) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _iterator_t noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _schema_t noattr))) ::
               (_t'10, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_schema (Tfunction
                          (Tcons (tptr (Tstruct _attribute_list_t noattr))
                            Tnil) (tptr (Tstruct _schema_t noattr))
                          cc_default))
      ((Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr))) :: nil))
    (Sset _sch (Etempvar _t'1 (tptr (Tstruct _schema_t noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _index_new (Tfunction
                           (Tcons (tptr (Tstruct _schema_t noattr)) Tnil)
                           (tptr tvoid) cc_default))
        ((Etempvar _sch (tptr (Tstruct _schema_t noattr))) :: nil))
      (Sset _ind (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _seq_scan (Tfunction
                            (Tcons (tptr (Tstruct _relation_t noattr)) Tnil)
                            (tptr (Tstruct _iterator_t noattr)) cc_default))
          ((Etempvar _rel (tptr (Tstruct _relation_t noattr))) :: nil))
        (Sset _it (Etempvar _t'3 (tptr (Tstruct _iterator_t noattr)))))
      (Ssequence
        (Scall None
          (Evar _init_iterator (Tfunction
                                 (Tcons (tptr (Tstruct _iterator_t noattr))
                                   Tnil) tvoid cc_default))
          ((Etempvar _it (tptr (Tstruct _iterator_t noattr))) :: nil))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _get_next (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _iterator_t noattr))
                                          Tnil) (tptr tvoid) cc_default))
                      ((Etempvar _it (tptr (Tstruct _iterator_t noattr))) ::
                       nil))
                    (Sset _t'5
                      (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tvoid))))
                  (Sset _t (Etempvar _t'5 (tptr tvoid))))
                (Sifthenelse (Etempvar _t'5 (tptr tvoid)) Sskip Sbreak))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _rel (tptr (Tstruct _relation_t noattr)))
                          (Tstruct _relation_t noattr)) _attrs
                        (tptr (Tstruct _attribute_list_t noattr))))
                    (Scall (Some _t'6)
                      (Evar _get_projection (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _attribute_list_t noattr))
                                                (Tcons (tptr tvoid)
                                                  (Tcons
                                                    (tptr (Tstruct _attribute_list_t noattr))
                                                    Tnil))) (tptr tvoid)
                                              cc_default))
                      ((Etempvar _t'10 (tptr (Tstruct _attribute_list_t noattr))) ::
                       (Etempvar _t (tptr tvoid)) ::
                       (Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr))) ::
                       nil)))
                  (Sset _proj (Etempvar _t'6 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _index_lookup (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _schema_t noattr))
                                              (Tcons (tptr tvoid)
                                                (Tcons (tptr tvoid) Tnil)))
                                            (tptr tvoid) cc_default))
                      ((Etempvar _sch (tptr (Tstruct _schema_t noattr))) ::
                       (Etempvar _ind (tptr tvoid)) ::
                       (Etempvar _proj (tptr tvoid)) :: nil))
                    (Sset _l
                      (Ecast (Etempvar _t'7 (tptr tvoid))
                        (tptr (Tstruct _fifo noattr)))))
                  (Ssequence
                    (Sifthenelse (Eunop Onotbool
                                   (Etempvar _l (tptr (Tstruct _fifo noattr)))
                                   tint)
                      (Ssequence
                        (Scall (Some _t'8)
                          (Evar _fifo_new (Tfunction Tnil
                                            (tptr (Tstruct _fifo noattr))
                                            cc_default)) nil)
                        (Sset _l
                          (Etempvar _t'8 (tptr (Tstruct _fifo noattr)))))
                      Sskip)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _make_elem (Tfunction
                                             (Tcons (tptr tvoid) Tnil)
                                             (tptr (Tstruct _elem noattr))
                                             cc_default))
                          ((Etempvar _t (tptr tvoid)) :: nil))
                        (Scall None
                          (Evar _fifo_put (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _fifo noattr))
                                              (Tcons
                                                (tptr (Tstruct _elem noattr))
                                                Tnil)) tvoid cc_default))
                          ((Etempvar _l (tptr (Tstruct _fifo noattr))) ::
                           (Etempvar _t'9 (tptr (Tstruct _elem noattr))) ::
                           nil)))
                      (Scall None
                        (Evar _index_insert (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _schema_t noattr))
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid)
                                                    (Tcons (tptr tvoid) Tnil))))
                                              (tptr tvoid) cc_default))
                        ((Etempvar _sch (tptr (Tstruct _schema_t noattr))) ::
                         (Etempvar _ind (tptr tvoid)) ::
                         (Etempvar _proj (tptr tvoid)) ::
                         (Etempvar _l (tptr (Tstruct _fifo noattr))) :: nil)))))))
            Sskip)
          (Sreturn (Some (Etempvar _ind (tptr tvoid)))))))))
|}.

Definition f_index_join_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_e, (tptr (Tstruct _index_join_env noattr))) ::
               (_t'1, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _e
    (Ecast (Etempvar _env (tptr tvoid))
      (tptr (Tstruct _index_join_env noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
            (Tstruct _index_join_env noattr)) _outer
          (tptr (Tstruct _iterator_t noattr))))
      (Scall None
        (Evar _init_iterator (Tfunction
                               (Tcons (tptr (Tstruct _iterator_t noattr))
                                 Tnil) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _iterator_t noattr))) :: nil)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
            (Tstruct _index_join_env noattr)) _current_inner
          (tptr (Tstruct _fifo noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sassign
        (Efield
          (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
            (Tstruct _index_join_env noattr)) _current_outer (tptr tvoid))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
|}.

Definition f_index_join_next := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_e, (tptr (Tstruct _index_join_env noattr))) ::
               (_proj, (tptr tvoid)) :: (_outer_t_length, tuint) ::
               (_inner_t_length, tuint) :: (_join_length, tuint) ::
               (_new_t, (tptr tvoid)) :: (_inner_t, (tptr tvoid)) ::
               (_l, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_n, tuint) :: (_inner_t_ofs, tuint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, (tptr (Tstruct _elem noattr))) ::
               (_t'11, (tptr tvoid)) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'34, (tptr (Tstruct _fifo noattr))) ::
               (_t'33, (tptr (Tstruct _fifo noattr))) ::
               (_t'32, (tptr (Tstruct _iterator_t noattr))) ::
               (_t'31, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'30, (tptr tvoid)) ::
               (_t'29, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'28, (tptr tvoid)) ::
               (_t'27, (tptr (Tstruct _schema_t noattr))) ::
               (_t'26, (tptr tvoid)) ::
               (_t'25, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'24, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'23, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'22, (tptr tvoid)) ::
               (_t'21, (tptr (Tstruct _fifo noattr))) :: (_t'20, tint) ::
               (_t'19, (tptr tschar)) ::
               (_t'18, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'17, tint) :: (_t'16, (tptr tschar)) ::
               (_t'15, (tptr (Tstruct _attribute_list_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _e
    (Ecast (Etempvar _env (tptr tvoid))
      (tptr (Tstruct _index_join_env noattr))))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'33
                (Efield
                  (Ederef
                    (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                    (Tstruct _index_join_env noattr)) _current_inner
                  (tptr (Tstruct _fifo noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'33 (tptr (Tstruct _fifo noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'1 (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Ssequence
                    (Sset _t'34
                      (Efield
                        (Ederef
                          (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                          (Tstruct _index_join_env noattr)) _current_inner
                        (tptr (Tstruct _fifo noattr))))
                    (Scall (Some _t'2)
                      (Evar _fifo_empty (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _fifo noattr))
                                            Tnil) tint cc_default))
                      ((Etempvar _t'34 (tptr (Tstruct _fifo noattr))) :: nil)))
                  (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))))
            (Sifthenelse (Etempvar _t'1 tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'32
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                            (Tstruct _index_join_env noattr)) _outer
                          (tptr (Tstruct _iterator_t noattr))))
                      (Scall (Some _t'4)
                        (Evar _get_next (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _iterator_t noattr))
                                            Tnil) (tptr tvoid) cc_default))
                        ((Etempvar _t'32 (tptr (Tstruct _iterator_t noattr))) ::
                         nil)))
                    (Sset _t'5
                      (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tvoid))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                        (Tstruct _index_join_env noattr)) _current_outer
                      (tptr tvoid)) (Etempvar _t'5 (tptr tvoid))))
                (Sset _t'3 (Ecast (Etempvar _t'5 (tptr tvoid)) tbool)))
              (Sset _t'3 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'3 tint) Sskip Sbreak))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'29
                (Efield
                  (Ederef
                    (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                    (Tstruct _index_join_env noattr)) _outer_attrs
                  (tptr (Tstruct _attribute_list_t noattr))))
              (Ssequence
                (Sset _t'30
                  (Efield
                    (Ederef
                      (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                      (Tstruct _index_join_env noattr)) _current_outer
                    (tptr tvoid)))
                (Ssequence
                  (Sset _t'31
                    (Efield
                      (Ederef
                        (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                        (Tstruct _index_join_env noattr)) _outer_join_attrs
                      (tptr (Tstruct _attribute_list_t noattr))))
                  (Scall (Some _t'6)
                    (Evar _get_projection (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _attribute_list_t noattr))
                                              (Tcons (tptr tvoid)
                                                (Tcons
                                                  (tptr (Tstruct _attribute_list_t noattr))
                                                  Tnil))) (tptr tvoid)
                                            cc_default))
                    ((Etempvar _t'29 (tptr (Tstruct _attribute_list_t noattr))) ::
                     (Etempvar _t'30 (tptr tvoid)) ::
                     (Etempvar _t'31 (tptr (Tstruct _attribute_list_t noattr))) ::
                     nil)))))
            (Sset _proj (Etempvar _t'6 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Sset _t'27
                (Efield
                  (Ederef
                    (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                    (Tstruct _index_join_env noattr)) _ind_on_inner_sch
                  (tptr (Tstruct _schema_t noattr))))
              (Ssequence
                (Sset _t'28
                  (Efield
                    (Ederef
                      (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                      (Tstruct _index_join_env noattr)) _ind_on_inner
                    (tptr tvoid)))
                (Scall (Some _t'7)
                  (Evar _index_lookup (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _schema_t noattr))
                                          (Tcons (tptr tvoid)
                                            (Tcons (tptr tvoid) Tnil)))
                                        (tptr tvoid) cc_default))
                  ((Etempvar _t'27 (tptr (Tstruct _schema_t noattr))) ::
                   (Etempvar _t'28 (tptr tvoid)) ::
                   (Etempvar _proj (tptr tvoid)) :: nil))))
            (Sassign
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                  (Tstruct _index_join_env noattr)) _current_inner
                (tptr (Tstruct _fifo noattr)))
              (Ecast (Etempvar _t'7 (tptr tvoid))
                (tptr (Tstruct _fifo noattr)))))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'26
          (Efield
            (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
              (Tstruct _index_join_env noattr)) _current_outer (tptr tvoid)))
        (Sifthenelse (Eunop Onotbool (Etempvar _t'26 (tptr tvoid)) tint)
          (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
          Sskip))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'25
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                  (Tstruct _index_join_env noattr)) _outer_attrs
                (tptr (Tstruct _attribute_list_t noattr))))
            (Scall (Some _t'8)
              (Evar _attribute_list_length (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _attribute_list_t noattr))
                                               Tnil) tuint cc_default))
              ((Etempvar _t'25 (tptr (Tstruct _attribute_list_t noattr))) ::
               nil)))
          (Sset _outer_t_length (Etempvar _t'8 tuint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'24
                (Efield
                  (Ederef
                    (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                    (Tstruct _index_join_env noattr)) _inner_attrs
                  (tptr (Tstruct _attribute_list_t noattr))))
              (Scall (Some _t'9)
                (Evar _attribute_list_length (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _attribute_list_t noattr))
                                                 Tnil) tuint cc_default))
                ((Etempvar _t'24 (tptr (Tstruct _attribute_list_t noattr))) ::
                 nil)))
            (Sset _inner_t_length (Etempvar _t'9 tuint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'23
                  (Efield
                    (Ederef
                      (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                      (Tstruct _index_join_env noattr)) _inner_join_attrs
                    (tptr (Tstruct _attribute_list_t noattr))))
                (Scall (Some _t'10)
                  (Evar _attribute_list_length (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _attribute_list_t noattr))
                                                   Tnil) tuint cc_default))
                  ((Etempvar _t'23 (tptr (Tstruct _attribute_list_t noattr))) ::
                   nil)))
              (Sset _join_length (Etempvar _t'10 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'11)
                  (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                  cc_default))
                  ((Ebinop Omul (Esizeof (tptr tvoid) tuint)
                     (Ebinop Oadd
                       (Ebinop Osub
                         (Ebinop Oadd (Etempvar _outer_t_length tuint)
                           (Etempvar _inner_t_length tuint) tuint)
                         (Etempvar _join_length tuint) tuint)
                       (Econst_int (Int.repr 1) tint) tuint) tuint) :: nil))
                (Sset _new_t (Etempvar _t'11 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Sset _t'22
                    (Efield
                      (Ederef
                        (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                        (Tstruct _index_join_env noattr)) _current_outer
                      (tptr tvoid)))
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Etempvar _new_t (tptr tvoid)) ::
                     (Etempvar _t'22 (tptr tvoid)) ::
                     (Ebinop Omul (Esizeof (tptr tvoid) tuint)
                       (Etempvar _outer_t_length tuint) tuint) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'21
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                            (Tstruct _index_join_env noattr)) _current_inner
                          (tptr (Tstruct _fifo noattr))))
                      (Scall (Some _t'12)
                        (Evar _fifo_get (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _fifo noattr))
                                            Tnil)
                                          (tptr (Tstruct _elem noattr))
                                          cc_default))
                        ((Etempvar _t'21 (tptr (Tstruct _fifo noattr))) ::
                         nil)))
                    (Sset _inner_t
                      (Efield
                        (Ederef
                          (Etempvar _t'12 (tptr (Tstruct _elem noattr)))
                          (Tstruct _elem noattr)) _data (tptr tvoid))))
                  (Ssequence
                    (Sset _l
                      (Efield
                        (Ederef
                          (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                          (Tstruct _index_join_env noattr)) _inner_attrs
                        (tptr (Tstruct _attribute_list_t noattr))))
                    (Ssequence
                      (Sset _n (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop One
                                           (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'18
                                    (Efield
                                      (Ederef
                                        (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                                        (Tstruct _index_join_env noattr))
                                      _inner_attrs
                                      (tptr (Tstruct _attribute_list_t noattr))))
                                  (Ssequence
                                    (Sset _t'19
                                      (Efield
                                        (Ederef
                                          (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                          (Tstruct _attribute_list_t noattr))
                                        _id (tptr tschar)))
                                    (Ssequence
                                      (Sset _t'20
                                        (Efield
                                          (Ederef
                                            (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                            (Tstruct _attribute_list_t noattr))
                                          _domain tint))
                                      (Scall (Some _t'13)
                                        (Evar _get_offset (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _attribute_list_t noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tint
                                                                  Tnil)))
                                                            tint cc_default))
                                        ((Etempvar _t'18 (tptr (Tstruct _attribute_list_t noattr))) ::
                                         (Etempvar _t'19 (tptr tschar)) ::
                                         (Etempvar _t'20 tint) :: nil)))))
                                (Sset _inner_t_ofs (Etempvar _t'13 tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'15
                                    (Efield
                                      (Ederef
                                        (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
                                        (Tstruct _index_join_env noattr))
                                      _inner_join_attrs
                                      (tptr (Tstruct _attribute_list_t noattr))))
                                  (Ssequence
                                    (Sset _t'16
                                      (Efield
                                        (Ederef
                                          (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                          (Tstruct _attribute_list_t noattr))
                                        _id (tptr tschar)))
                                    (Ssequence
                                      (Sset _t'17
                                        (Efield
                                          (Ederef
                                            (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                            (Tstruct _attribute_list_t noattr))
                                          _domain tint))
                                      (Scall (Some _t'14)
                                        (Evar _get_offset (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _attribute_list_t noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tint
                                                                  Tnil)))
                                                            tint cc_default))
                                        ((Etempvar _t'15 (tptr (Tstruct _attribute_list_t noattr))) ::
                                         (Etempvar _t'16 (tptr tschar)) ::
                                         (Etempvar _t'17 tint) :: nil)))))
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _t'14 tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _memcpy (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        (Tcons (tptr tvoid)
                                                          (Tcons tuint Tnil)))
                                                      (tptr tvoid)
                                                      cc_default))
                                      ((Ecast
                                         (Ebinop Oadd
                                           (Ebinop Oadd
                                             (Ecast
                                               (Etempvar _new_t (tptr tvoid))
                                               (tptr tuint))
                                             (Etempvar _outer_t_length tuint)
                                             (tptr tuint))
                                           (Etempvar _n tuint) (tptr tuint))
                                         (tptr tvoid)) ::
                                       (Ecast
                                         (Ebinop Oadd
                                           (Ecast
                                             (Etempvar _inner_t (tptr tvoid))
                                             (tptr tuint))
                                           (Etempvar _inner_t_ofs tuint)
                                           (tptr tuint)) (tptr tvoid)) ::
                                       (Esizeof tuint tuint) :: nil))
                                    (Sset _n
                                      (Ebinop Oadd (Etempvar _n tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))
                                  Sskip))))
                          (Sset _l
                            (Efield
                              (Ederef
                                (Etempvar _l (tptr (Tstruct _attribute_list_t noattr)))
                                (Tstruct _attribute_list_t noattr)) _next
                              (tptr (Tstruct _attribute_list_t noattr)))))
                        (Sreturn (Some (Etempvar _new_t (tptr tvoid))))))))))))))))
|}.

Definition f_index_join_close := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_env, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_e, (tptr (Tstruct _index_join_env noattr))) ::
               (_t'1, (tptr (Tstruct _iterator_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _e
    (Ecast (Etempvar _env (tptr tvoid))
      (tptr (Tstruct _index_join_env noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _e (tptr (Tstruct _index_join_env noattr)))
            (Tstruct _index_join_env noattr)) _outer
          (tptr (Tstruct _iterator_t noattr))))
      (Scall None
        (Evar _close_iterator (Tfunction
                                (Tcons (tptr (Tstruct _iterator_t noattr))
                                  Tnil) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _iterator_t noattr))) :: nil)))
    (Sreturn None)))
|}.

Definition v_index_join_iterator_mtable := {|
  gvar_info := (Tstruct _methods noattr);
  gvar_init := (Init_addrof _index_join_init (Ptrofs.repr 0) ::
                Init_addrof _index_join_next (Ptrofs.repr 0) ::
                Init_addrof _index_join_close (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_index_join := {|
  fn_return := (tptr (Tstruct _iterator_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_outer_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_inner_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_outer_join_attrs,
                 (tptr (Tstruct _attribute_list_t noattr))) ::
                (_inner_join_attrs,
                 (tptr (Tstruct _attribute_list_t noattr))) ::
                (_outer, (tptr (Tstruct _iterator_t noattr))) ::
                (_ind_on_inner, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_env, (tptr (Tstruct _index_join_env noattr))) ::
               (_it, (tptr (Tstruct _iterator_t noattr))) ::
               (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _schema_t noattr))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _attribute_list_length (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _attribute_list_t noattr))
                                         Tnil) tuint cc_default))
        ((Etempvar _outer_join_attrs (tptr (Tstruct _attribute_list_t noattr))) ::
         nil))
      (Scall (Some _t'2)
        (Evar _attribute_list_length (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _attribute_list_t noattr))
                                         Tnil) tuint cc_default))
        ((Etempvar _inner_join_attrs (tptr (Tstruct _attribute_list_t noattr))) ::
         nil)))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                   tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_2 (tarray tschar 83)) ::
         (Evar ___stringlit_1 (tarray tschar 32)) ::
         (Econst_int (Int.repr 264) tint) ::
         (Evar ___func__ (tarray tschar 11)) :: nil))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _index_join_env noattr) tuint) :: nil))
      (Sset _env (Etempvar _t'3 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                     tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
              (Tstruct _index_join_env noattr)) _outer
            (tptr (Tstruct _iterator_t noattr)))
          (Etempvar _outer (tptr (Tstruct _iterator_t noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                (Tstruct _index_join_env noattr)) _ind_on_inner (tptr tvoid))
            (Etempvar _ind_on_inner (tptr tvoid)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                  (Tstruct _index_join_env noattr)) _outer_attrs
                (tptr (Tstruct _attribute_list_t noattr)))
              (Etempvar _outer_attrs (tptr (Tstruct _attribute_list_t noattr))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                    (Tstruct _index_join_env noattr)) _inner_attrs
                  (tptr (Tstruct _attribute_list_t noattr)))
                (Etempvar _inner_attrs (tptr (Tstruct _attribute_list_t noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                      (Tstruct _index_join_env noattr)) _outer_join_attrs
                    (tptr (Tstruct _attribute_list_t noattr)))
                  (Etempvar _outer_join_attrs (tptr (Tstruct _attribute_list_t noattr))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                        (Tstruct _index_join_env noattr)) _inner_join_attrs
                      (tptr (Tstruct _attribute_list_t noattr)))
                    (Etempvar _inner_join_attrs (tptr (Tstruct _attribute_list_t noattr))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _get_schema (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _attribute_list_t noattr))
                                              Tnil)
                                            (tptr (Tstruct _schema_t noattr))
                                            cc_default))
                        ((Etempvar _inner_join_attrs (tptr (Tstruct _attribute_list_t noattr))) ::
                         nil))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                            (Tstruct _index_join_env noattr))
                          _ind_on_inner_sch
                          (tptr (Tstruct _schema_t noattr)))
                        (Etempvar _t'4 (tptr (Tstruct _schema_t noattr)))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                          (tptr tvoid) cc_default))
                          ((Esizeof (Tstruct _iterator_t noattr) tuint) ::
                           nil))
                        (Sset _it (Etempvar _t'5 (tptr tvoid))))
                      (Ssequence
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
                                       tint)
                          (Scall None
                            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                          cc_default))
                            ((Econst_int (Int.repr 1) tint) :: nil))
                          Sskip)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
                                (Tstruct _iterator_t noattr)) _mtable
                              (tptr (Tstruct _methods noattr)))
                            (Eaddrof
                              (Evar _index_join_iterator_mtable (Tstruct _methods noattr))
                              (tptr (Tstruct _methods noattr))))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _it (tptr (Tstruct _iterator_t noattr)))
                                  (Tstruct _iterator_t noattr)) _env
                                (tptr tvoid))
                              (Ecast
                                (Etempvar _env (tptr (Tstruct _index_join_env noattr)))
                                (tptr tvoid)))
                            (Sreturn (Some (Etempvar _it (tptr (Tstruct _iterator_t noattr)))))))))))))))))))
|}.

Definition f_index_data := {|
  fn_return := (tptr (Tstruct _Relation noattr));
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr (tptr (tptr tvoid)))) ::
                (_tuple_count, tint) ::
                (_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
                (_primary_key, (tptr (Tstruct _attribute_list_t noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tuint) :: (_bt, (tptr (Tstruct _Relation noattr))) ::
               (_c, (tptr (Tstruct _Cursor noattr))) :: (_i, tint) ::
               (_current_tuple, (tptr tuint)) :: (_k, tuint) ::
               (_t'5, (tptr (Tstruct _Cursor noattr))) ::
               (_t'4, (tptr (Tstruct _Relation noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'10, (tptr (Tstruct _attribute_list_t noattr))) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, (tptr tschar)) ::
               (_t'6, (tptr (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _primary_key (tptr (Tstruct _attribute_list_t noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef
                (Etempvar _primary_key (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _next
              (tptr (Tstruct _attribute_list_t noattr))))
          (Sset _t'1
            (Ecast
              (Ebinop One
                (Etempvar _t'10 (tptr (Tstruct _attribute_list_t noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              tbool))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef
                (Etempvar _primary_key (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _domain tint))
          (Sset _t'2
            (Ecast
              (Ebinop One (Etempvar _t'9 tint) (Econst_int (Int.repr 0) tint)
                tint) tbool)))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef
              (Etempvar _primary_key (tptr (Tstruct _attribute_list_t noattr)))
              (Tstruct _attribute_list_t noattr)) _id (tptr tschar)))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef
                (Etempvar _primary_key (tptr (Tstruct _attribute_list_t noattr)))
                (Tstruct _attribute_list_t noattr)) _domain tint))
          (Scall (Some _t'3)
            (Evar _get_offset (Tfunction
                                (Tcons
                                  (tptr (Tstruct _attribute_list_t noattr))
                                  (Tcons (tptr tschar) (Tcons tint Tnil)))
                                tint cc_default))
            ((Etempvar _attrs (tptr (Tstruct _attribute_list_t noattr))) ::
             (Etempvar _t'7 (tptr tschar)) :: (Etempvar _t'8 tint) :: nil))))
      (Sset _ofs (Etempvar _t'3 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _RL_NewRelation (Tfunction Tnil
                                  (tptr (Tstruct _Relation noattr))
                                  cc_default)) nil)
        (Sset _bt (Etempvar _t'4 (tptr (Tstruct _Relation noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'5)
            (Evar _RL_NewCursor (Tfunction
                                  (Tcons (tptr (Tstruct _Relation noattr))
                                    Tnil) (tptr (Tstruct _Cursor noattr))
                                  cc_default))
            ((Etempvar _bt (tptr (Tstruct _Relation noattr))) :: nil))
          (Sset _c (Etempvar _t'5 (tptr (Tstruct _Cursor noattr)))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _tuple_count tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _data (tptr (tptr (tptr tvoid))))
                          (Etempvar _i tint) (tptr (tptr (tptr tvoid))))
                        (tptr (tptr tvoid))))
                    (Sset _current_tuple
                      (Ecast (Etempvar _t'6 (tptr (tptr tvoid)))
                        (tptr tuint))))
                  (Ssequence
                    (Sset _k
                      (Ederef
                        (Ebinop Oadd (Etempvar _current_tuple (tptr tuint))
                          (Etempvar _ofs tuint) (tptr tuint)) tuint))
                    (Scall None
                      (Evar _RL_PutRecord (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _Cursor noattr))
                                              (Tcons tuint
                                                (Tcons (tptr tvoid) Tnil)))
                                            tvoid cc_default))
                      ((Etempvar _c (tptr (Tstruct _Cursor noattr))) ::
                       (Etempvar _k tuint) ::
                       (Ecast (Etempvar _current_tuple (tptr tuint))
                         (tptr tvoid)) :: nil)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Sreturn (Some (Etempvar _bt (tptr (Tstruct _Relation noattr))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _elem Struct
   ((_data, (tptr tvoid)) :: (_next, (tptr (Tstruct _elem noattr))) :: nil)
   noattr ::
 Composite _fifo Struct
   ((_head, (tptr (Tstruct _elem noattr))) ::
    (_tail, (tptr (Tstruct _elem noattr))) :: nil)
   noattr ::
 Composite _schema_methods Struct
   ((_schema_new,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))) ::
    (_schema_insert,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr tvoid)
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))))
             (tptr tvoid) cc_default))) ::
    (_schema_lookup,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) (tptr tvoid)
             cc_default))) :: nil)
   noattr ::
 Composite _schema_t Struct
   ((_mtable, (tptr (Tstruct _schema_methods noattr))) ::
    (_schema_private, (tptr tvoid)) :: nil)
   noattr ::
 Composite _attribute_list_t Struct
   ((_id, (tptr tschar)) :: (_domain, tint) ::
    (_next, (tptr (Tstruct _attribute_list_t noattr))) :: nil)
   noattr ::
 Composite _relation_t Struct
   ((_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_pk_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_pk_index, (tptr (Tstruct _Relation noattr))) :: nil)
   noattr ::
 Composite _methods Struct
   ((_init, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_next,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))) ::
    (_close, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    nil)
   noattr ::
 Composite _iterator_t Struct
   ((_mtable, (tptr (Tstruct _methods noattr))) :: (_env, (tptr tvoid)) ::
    nil)
   noattr ::
 Composite _seq_scan_env Struct
   ((_bt, (tptr (Tstruct _Relation noattr))) ::
    (_c, (tptr (Tstruct _Cursor noattr))) :: nil)
   noattr ::
 Composite _index_join_env Struct
   ((_outer, (tptr (Tstruct _iterator_t noattr))) ::
    (_outer_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_outer_join_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_inner_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_inner_join_attrs, (tptr (Tstruct _attribute_list_t noattr))) ::
    (_ind_on_inner, (tptr tvoid)) ::
    (_ind_on_inner_sch, (tptr (Tstruct _schema_t noattr))) ::
    (_current_inner, (tptr (Tstruct _fifo noattr))) ::
    (_current_outer, (tptr tvoid)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_strcmp,
   Gfun(External (EF_external "strcmp"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) tint cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_RL_NewRelation,
   Gfun(External (EF_external "RL_NewRelation"
                   (mksignature nil (Some AST.Tint) cc_default)) Tnil
     (tptr (Tstruct _Relation noattr)) cc_default)) ::
 (_RL_NewCursor,
   Gfun(External (EF_external "RL_NewCursor"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Relation noattr)) Tnil)
     (tptr (Tstruct _Cursor noattr)) cc_default)) ::
 (_RL_FreeCursor,
   Gfun(External (EF_external "RL_FreeCursor"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid cc_default)) ::
 (_RL_CursorIsValid,
   Gfun(External (EF_external "RL_CursorIsValid"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint cc_default)) ::
 (_RL_PutRecord,
   Gfun(External (EF_external "RL_PutRecord"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr))
       (Tcons tuint (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_RL_GetRecord,
   Gfun(External (EF_external "RL_GetRecord"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_RL_MoveToFirst,
   Gfun(External (EF_external "RL_MoveToFirst"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint cc_default)) ::
 (_RL_MoveToNext,
   Gfun(External (EF_external "RL_MoveToNext"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid cc_default)) ::
 (_RL_IsEmpty,
   Gfun(External (EF_external "RL_IsEmpty"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_fifo_new, Gfun(Internal f_fifo_new)) ::
 (_fifo_put, Gfun(Internal f_fifo_put)) ::
 (_fifo_empty, Gfun(Internal f_fifo_empty)) ::
 (_fifo_get, Gfun(Internal f_fifo_get)) ::
 (_make_elem, Gfun(Internal f_make_elem)) ::
 (_index_new,
   Gfun(External (EF_external "index_new"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _schema_t noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_index_insert,
   Gfun(External (EF_external "index_insert"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _schema_t noattr))
       (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))))
     (tptr tvoid) cc_default)) ::
 (_index_lookup,
   Gfun(External (EF_external "index_lookup"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _schema_t noattr))
       (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) (tptr tvoid)
     cc_default)) :: (_inthash_schema, Gvar v_inthash_schema) ::
 (_stringlist_schema, Gvar v_stringlist_schema) ::
 (_build_keypair,
   Gfun(External (EF_external "build_keypair"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default)) ::
 (_tuple_schema,
   Gfun(External (EF_external "tuple_schema"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (Tstruct _schema_t noattr))
       (Tcons (tptr (Tstruct _schema_t noattr)) Tnil))
     (tptr (Tstruct _schema_t noattr)) cc_default)) ::
 (_attribute_list_length, Gfun(Internal f_attribute_list_length)) ::
 (_init_iterator, Gfun(Internal f_init_iterator)) ::
 (_get_next, Gfun(Internal f_get_next)) ::
 (_close_iterator, Gfun(Internal f_close_iterator)) ::
 (_materialize, Gfun(Internal f_materialize)) ::
 (_seq_scan_init, Gfun(Internal f_seq_scan_init)) ::
 (_seq_scan_next, Gfun(Internal f_seq_scan_next)) ::
 (_seq_scan_close, Gfun(Internal f_seq_scan_close)) ::
 (_seq_scan_iterator_mtable, Gvar v_seq_scan_iterator_mtable) ::
 (_seq_scan, Gfun(Internal f_seq_scan)) ::
 (_get_schema_aux, Gfun(Internal f_get_schema_aux)) ::
 (_get_schema, Gfun(Internal f_get_schema)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_get_field_address, Gfun(Internal f_get_field_address)) ::
 (_get_projection, Gfun(Internal f_get_projection)) ::
 (_index_scan, Gfun(Internal f_index_scan)) ::
 (_index_join_init, Gfun(Internal f_index_join_init)) ::
 (_index_join_next, Gfun(Internal f_index_join_next)) ::
 (_index_join_close, Gfun(Internal f_index_join_close)) ::
 (_index_join_iterator_mtable, Gvar v_index_join_iterator_mtable) ::
 (___func__, Gvar v___func__) ::
 (_index_join, Gfun(Internal f_index_join)) ::
 (_index_data, Gfun(Internal f_index_data)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _index_data :: _index_join :: _index_join_iterator_mtable ::
 _index_join_close :: _index_join_next :: _index_join_init :: _index_scan ::
 _get_projection :: _get_field_address :: _get_offset :: _get_schema ::
 _get_schema_aux :: _seq_scan :: _seq_scan_iterator_mtable ::
 _seq_scan_close :: _seq_scan_next :: _seq_scan_init :: _materialize ::
 _close_iterator :: _get_next :: _init_iterator :: _attribute_list_length ::
 _tuple_schema :: _build_keypair :: _stringlist_schema :: _inthash_schema ::
 _index_lookup :: _index_insert :: _index_new :: _make_elem :: _fifo_get ::
 _fifo_empty :: _fifo_put :: _fifo_new :: _exit :: _surely_malloc ::
 _RL_IsEmpty :: _RL_MoveToNext :: _RL_MoveToFirst :: _RL_GetRecord ::
 _RL_PutRecord :: _RL_CursorIsValid :: _RL_FreeCursor :: _RL_NewCursor ::
 _RL_NewRelation :: ___assert_fail :: _strcmp :: _memcpy :: _malloc ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


