From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.7".
  Definition build_number := "".
  Definition build_tag := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "index_string.c".
  Definition normalized := false.
End Info.

Definition _BN_CompareSuffix : ident := $"BN_CompareSuffix".
Definition _BN_ExportSuffixValue : ident := $"BN_ExportSuffixValue".
Definition _BN_FreeBorderNode : ident := $"BN_FreeBorderNode".
Definition _BN_GetLink : ident := $"BN_GetLink".
Definition _BN_GetPrefixValue : ident := $"BN_GetPrefixValue".
Definition _BN_GetSuffixValue : ident := $"BN_GetSuffixValue".
Definition _BN_HasSuffix : ident := $"BN_HasSuffix".
Definition _BN_NewBorderNode : ident := $"BN_NewBorderNode".
Definition _BN_SetLink : ident := $"BN_SetLink".
Definition _BN_SetPrefixValue : ident := $"BN_SetPrefixValue".
Definition _BN_SetSuffixValue : ident := $"BN_SetSuffixValue".
Definition _BN_SetValue : ident := $"BN_SetValue".
Definition _BN_TestSuffix : ident := $"BN_TestSuffix".
Definition _BorderNode : ident := $"BorderNode".
Definition _CursorSlice_T : ident := $"CursorSlice_T".
Definition _Cursor_T : ident := $"Cursor_T".
Definition _Iempty : ident := $"Iempty".
Definition _Ifirst_cursor : ident := $"Ifirst_cursor".
Definition _Ifree_cursor : ident := $"Ifree_cursor".
Definition _Iget_key : ident := $"Iget_key".
Definition _Iget_value : ident := $"Iget_value".
Definition _Imake_cursor : ident := $"Imake_cursor".
Definition _Inext_cursor : ident := $"Inext_cursor".
Definition _Iput : ident := $"Iput".
Definition _Key_T : ident := $"Key_T".
Definition _Sempty : ident := $"Sempty".
Definition _Sget_value : ident := $"Sget_value".
Definition _Smake_cursor : ident := $"Smake_cursor".
Definition _Trie_T : ident := $"Trie_T".
Definition _UTIL_GetNextKeySlice : ident := $"UTIL_GetNextKeySlice".
Definition _UTIL_StrEqual : ident := $"UTIL_StrEqual".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _bn : ident := $"bn".
Definition _bnode : ident := $"bnode".
Definition _bnode1 : ident := $"bnode1".
Definition _bnode2 : ident := $"bnode2".
Definition _bnode__1 : ident := $"bnode__1".
Definition _bnode_cursor : ident := $"bnode_cursor".
Definition _bordernode : ident := $"bordernode".
Definition _bordernode_next_cursor : ident := $"bordernode_next_cursor".
Definition _capacity : ident := $"capacity".
Definition _clearFlag : ident := $"clearFlag".
Definition _content : ident := $"content".
Definition _create_pair : ident := $"create_pair".
Definition _cs : ident := $"cs".
Definition _cursor : ident := $"cursor".
Definition _exit : ident := $"exit".
Definition _flags : ident := $"flags".
Definition _free : ident := $"free".
Definition _free_key : ident := $"free_key".
Definition _i : ident := $"i".
Definition _index : ident := $"index".
Definition _index__1 : ident := $"index__1".
Definition _index__2 : ident := $"index__2".
Definition _k : ident := $"k".
Definition _k1 : ident := $"k1".
Definition _k1__1 : ident := $"k1__1".
Definition _k2 : ident := $"k2".
Definition _k2__1 : ident := $"k2__1".
Definition _k__1 : ident := $"k__1".
Definition _key : ident := $"key".
Definition _key1 : ident := $"key1".
Definition _key2 : ident := $"key2".
Definition _keySuffix : ident := $"keySuffix".
Definition _keySuffixLength : ident := $"keySuffixLength".
Definition _keyslice : ident := $"keyslice".
Definition _keyslice1 : ident := $"keyslice1".
Definition _keyslice2 : ident := $"keyslice2".
Definition _len : ident := $"len".
Definition _len1 : ident := $"len1".
Definition _len2 : ident := $"len2".
Definition _lenA : ident := $"lenA".
Definition _lenB : ident := $"lenB".
Definition _main : ident := $"main".
Definition _make_cursor : ident := $"make_cursor".
Definition _malloc : ident := $"malloc".
Definition _move_key : ident := $"move_key".
Definition _n : ident := $"n".
Definition _newKey : ident := $"newKey".
Definition _newStr : ident := $"newStr".
Definition _new_addr : ident := $"new_addr".
Definition _new_cursor : ident := $"new_cursor".
Definition _new_index : ident := $"new_index".
Definition _new_key : ident := $"new_key".
Definition _next_bnode : ident := $"next_bnode".
Definition _next_bnode_cursor : ident := $"next_bnode_cursor".
Definition _next_cursor : ident := $"next_cursor".
Definition _node : ident := $"node".
Definition _node_cursor : ident := $"node_cursor".
Definition _normalize_cursor : ident := $"normalize_cursor".
Definition _obtained_keyslice : ident := $"obtained_keyslice".
Definition _p : ident := $"p".
Definition _pop_cursor : ident := $"pop_cursor".
Definition _prefixFlags : ident := $"prefixFlags".
Definition _prefixLinks : ident := $"prefixLinks".
Definition _push_cursor : ident := $"push_cursor".
Definition _put : ident := $"put".
Definition _readFlag : ident := $"readFlag".
Definition _res : ident := $"res".
Definition _ret_value : ident := $"ret_value".
Definition _root : ident := $"root".
Definition _setFlag : ident := $"setFlag".
Definition _size : ident := $"size".
Definition _str : ident := $"str".
Definition _strict_first_cursor : ident := $"strict_first_cursor".
Definition _subindex : ident := $"subindex".
Definition _subindex__1 : ident := $"subindex__1".
Definition _subkey : ident := $"subkey".
Definition _success : ident := $"success".
Definition _success__1 : ident := $"success__1".
Definition _suf : ident := $"suf".
Definition _suffix : ident := $"suffix".
Definition _suffixLink : ident := $"suffixLink".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _temp_cursor : ident := $"temp_cursor".
Definition _temp_cursor__1 : ident := $"temp_cursor__1".
Definition _temp_cursor__2 : ident := $"temp_cursor__2".
Definition _top_cursor : ident := $"top_cursor".
Definition _v : ident := $"v".
Definition _v1 : ident := $"v1".
Definition _v2 : ident := $"v2".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_push_cursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr tvoid)) :: (_node_cursor, (tptr tvoid)) ::
                (_bnode_cursor, tulong) ::
                (_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_addr, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_i, tulong) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef
                     (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                     (Tstruct _Cursor_T noattr)) _capacity tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _CursorSlice_T noattr) tulong) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _content
          (tptr (Tstruct _CursorSlice_T noattr)))
        (Etempvar _t'1 (tptr tvoid))))
    (Sifthenelse (Ebinop Ole
                   (Efield
                     (Ederef
                       (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                       (Tstruct _Cursor_T noattr)) _capacity tulong)
                   (Efield
                     (Ederef
                       (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                       (Tstruct _Cursor_T noattr)) _size tulong) tint)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _capacity tulong)
          (Ebinop Omul
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _capacity tulong)
            (Econst_int (Int.repr 2) tint) tulong))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
              ((Ebinop Omul (Esizeof (Tstruct _CursorSlice_T noattr) tulong)
                 (Efield
                   (Ederef
                     (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                     (Tstruct _Cursor_T noattr)) _capacity tulong) tulong) ::
               nil))
            (Sset _new_addr (Etempvar _t'2 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                 (Efield
                                   (Ederef
                                     (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                     (Tstruct _Cursor_T noattr)) _size
                                   tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr)))
                            (Etempvar _i tulong)
                            (tptr (Tstruct _CursorSlice_T noattr)))
                          (Tstruct _CursorSlice_T noattr)) _node_cursor
                        (tptr tvoid))
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                (Tstruct _Cursor_T noattr)) _content
                              (tptr (Tstruct _CursorSlice_T noattr)))
                            (Etempvar _i tulong)
                            (tptr (Tstruct _CursorSlice_T noattr)))
                          (Tstruct _CursorSlice_T noattr)) _node_cursor
                        (tptr tvoid)))
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr)))
                            (Etempvar _i tulong)
                            (tptr (Tstruct _CursorSlice_T noattr)))
                          (Tstruct _CursorSlice_T noattr)) _bnode_cursor
                        tuint)
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                (Tstruct _Cursor_T noattr)) _content
                              (tptr (Tstruct _CursorSlice_T noattr)))
                            (Etempvar _i tulong)
                            (tptr (Tstruct _CursorSlice_T noattr)))
                          (Tstruct _CursorSlice_T noattr)) _bnode_cursor
                        tuint))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Efield
                   (Ederef
                     (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                     (Tstruct _Cursor_T noattr)) _content
                   (tptr (Tstruct _CursorSlice_T noattr))) :: nil))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                    (Tstruct _Cursor_T noattr)) _content
                  (tptr (Tstruct _CursorSlice_T noattr)))
                (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr))))))))
      Sskip))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _content
              (tptr (Tstruct _CursorSlice_T noattr)))
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _size tulong)
            (tptr (Tstruct _CursorSlice_T noattr)))
          (Tstruct _CursorSlice_T noattr)) _node (tptr tvoid))
      (Etempvar _node (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                  (Tstruct _Cursor_T noattr)) _content
                (tptr (Tstruct _CursorSlice_T noattr)))
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                  (Tstruct _Cursor_T noattr)) _size tulong)
              (tptr (Tstruct _CursorSlice_T noattr)))
            (Tstruct _CursorSlice_T noattr)) _node_cursor (tptr tvoid))
        (Etempvar _node_cursor (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                    (Tstruct _Cursor_T noattr)) _content
                  (tptr (Tstruct _CursorSlice_T noattr)))
                (Efield
                  (Ederef
                    (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                    (Tstruct _Cursor_T noattr)) _size tulong)
                (tptr (Tstruct _CursorSlice_T noattr)))
              (Tstruct _CursorSlice_T noattr)) _bnode_cursor tuint)
          (Etempvar _bnode_cursor tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tulong)
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _size tulong)
            (Econst_int (Int.repr 1) tint) tulong))))))
|}.

Definition f_pop_cursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop One
               (Efield
                 (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                   (Tstruct _Cursor_T noattr)) _size tulong)
               (Econst_int (Int.repr 0) tint) tint)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
          (Tstruct _Cursor_T noattr)) _size tulong)
      (Ebinop Osub
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _size tulong)
        (Econst_int (Int.repr 1) tint) tulong))
    (Scall None
      (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
      ((Efield
         (Ederef
           (Ebinop Oadd
             (Efield
               (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                 (Tstruct _Cursor_T noattr)) _content
               (tptr (Tstruct _CursorSlice_T noattr)))
             (Efield
               (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                 (Tstruct _Cursor_T noattr)) _size tulong)
             (tptr (Tstruct _CursorSlice_T noattr)))
           (Tstruct _CursorSlice_T noattr)) _node_cursor (tptr tvoid)) ::
       nil)))
  Sskip)
|}.

Definition f_top_cursor := {|
  fn_return := (tptr (Tstruct _CursorSlice_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop One
               (Efield
                 (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                   (Tstruct _Cursor_T noattr)) _size tulong)
               (Econst_int (Int.repr 0) tint) tint)
  (Sreturn (Some (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                       (Tstruct _Cursor_T noattr)) _content
                     (tptr (Tstruct _CursorSlice_T noattr)))
                   (Ebinop Osub
                     (Efield
                       (Ederef
                         (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                         (Tstruct _Cursor_T noattr)) _size tulong)
                     (Econst_int (Int.repr 1) tint) tulong)
                   (tptr (Tstruct _CursorSlice_T noattr)))))
  (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|}.

Definition f_new_cursor := {|
  fn_return := (tptr (Tstruct _Cursor_T noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) ::
               (_t'2, tulong) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr (Tstruct _Cursor_T noattr)) tulong) :: nil))
    (Sset _cursor (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tulong)
          (Etempvar _t'2 tulong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _capacity tulong)
        (Etempvar _t'2 tulong)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _content
          (tptr (Tstruct _CursorSlice_T noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))))))))
|}.

Definition f_UTIL_GetNextKeySlice := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tulong) :: (_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tulong) (Ecast (Esizeof tulong tulong) tint)
          tint)
        (Ssequence
          (Sset _res
            (Ebinop Oshl (Etempvar _res tulong)
              (Econst_int (Int.repr 8) tint) tulong))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _len tulong) tint)
              (Ssequence
                (Sset _res
                  (Ebinop Oor (Etempvar _res tulong)
                    (Ebinop Oand
                      (Ecast (Ederef (Etempvar _str (tptr tschar)) tschar)
                        tulong) (Econst_int (Int.repr 255) tint) tulong)
                    tulong))
                (Sset _str
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Econst_int (Int.repr 1) tint) (tptr tschar))))
              Sskip)
            (Sset _i
              (Ebinop Oadd (Etempvar _i tulong)
                (Econst_int (Int.repr 1) tint) tulong)))))
      (Sreturn (Some (Etempvar _res tulong))))))
|}.

Definition f_UTIL_StrEqual := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_lenA, tulong) ::
                (_b, (tptr tschar)) :: (_lenB, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _lenA tulong) (Etempvar _lenB tulong)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Etempvar _lenA tulong) tint)
            Sskip
            Sbreak)
          (Sifthenelse (Ebinop One
                         (Ederef
                           (Ebinop Oadd (Etempvar _a (tptr tschar))
                             (Etempvar _i tulong) (tptr tschar)) tschar)
                         (Ederef
                           (Ebinop Oadd (Etempvar _b (tptr tschar))
                             (Etempvar _i tulong) (tptr tschar)) tschar)
                         tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_new_key := {|
  fn_return := (tptr (Tstruct _Key_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_newKey, (tptr (Tstruct _Key_T noattr))) ::
               (_newStr, (tptr tschar)) :: (_i, tulong) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _newKey
    (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
      (tptr (Tstruct _Key_T noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof tschar tulong) (Etempvar _len tulong) tulong) ::
         nil))
      (Sset _newStr (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _len tulong) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _newStr (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar)
              (Ederef
                (Ebinop Oadd (Etempvar _str (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                   cc_default))
            ((Esizeof (Tstruct _Key_T noattr) tulong) :: nil))
          (Sset _newKey
            (Ecast (Etempvar _t'2 (tptr tvoid))
              (tptr (Tstruct _Key_T noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))
                (Tstruct _Key_T noattr)) _content (tptr tschar))
            (Etempvar _newStr (tptr tschar)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))
                  (Tstruct _Key_T noattr)) _len tulong)
              (Etempvar _len tulong))
            (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))))))))))
|}.

Definition f_move_key := {|
  fn_return := (tptr (Tstruct _Key_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_newKey, (tptr (Tstruct _Key_T noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _newKey
    (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
      (tptr (Tstruct _Key_T noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _Key_T noattr) tulong) :: nil))
      (Sset _newKey
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Key_T noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))
            (Tstruct _Key_T noattr)) _content (tptr tschar))
        (Etempvar _str (tptr tschar)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))
              (Tstruct _Key_T noattr)) _len tulong) (Etempvar _len tulong))
        (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))))))))
|}.

Definition f_free_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _Key_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
         (Tstruct _Key_T noattr)) _content (tptr tschar)) :: nil))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _key (tptr (Tstruct _Key_T noattr))) :: nil)))
|}.

Definition f_setFlag := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_flags, tulong) :: (_index, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor (Etempvar _flags tulong)
                 (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                   (Etempvar _index tulong) tint) tulong)))
|}.

Definition f_clearFlag := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_flags, tulong) :: (_index, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oand (Etempvar _flags tulong)
                 (Eunop Onotint
                   (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                     (Etempvar _index tulong) tint) tint) tulong)))
|}.

Definition f_readFlag := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_flags, tulong) :: (_index, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oand (Etempvar _flags tulong)
               (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                 (Etempvar _index tulong) tint) tulong)
  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_BN_NewBorderNode := {|
  fn_return := (tptr (Tstruct _BorderNode noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_bordernode, (tptr (Tstruct _BorderNode noattr))) ::
               (_i, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _BorderNode noattr) tulong) :: nil))
    (Sset _bordernode
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _BorderNode noattr)))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _prefixLinks
                  (tarray (tptr tvoid) 9)) (Etempvar _i tint)
                (tptr (tptr tvoid))) (tptr tvoid))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _prefixFlags tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _keySuffixLength tulong)
              (Econst_int (Int.repr 0) tint))
            (Sreturn (Some (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))))))))))
|}.

Definition f_BN_FreeBorderNode := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bordernode, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Efield
                     (Ederef
                       (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                       (Tstruct _BorderNode noattr)) _keySuffix
                     (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
             (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) :: nil))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _bordernode (tptr (Tstruct _BorderNode noattr))) :: nil))
      (Sreturn None))))
|}.

Definition f_BN_SetPrefixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _setFlag (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong
                       cc_default))
      ((Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _prefixFlags tulong) ::
       (Etempvar _i tint) :: nil))
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _prefixFlags tulong)
      (Etempvar _t'1 tulong)))
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _prefixLinks
          (tarray (tptr tvoid) 9)) (Etempvar _i tint) (tptr (tptr tvoid)))
      (tptr tvoid)) (Etempvar _val (tptr tvoid))))
|}.

Definition f_BN_GetPrefixValue := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                (_val, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Ederef (Etempvar _val (tptr (tptr tvoid))) (tptr tvoid))
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _prefixLinks
          (tarray (tptr tvoid) 9)) (Etempvar _i tint) (tptr (tptr tvoid)))
      (tptr tvoid)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _readFlag (Tfunction (Tcons tulong (Tcons tulong Tnil)) tint
                        cc_default))
      ((Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _prefixFlags tulong) ::
       (Etempvar _i tint) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_BN_SetSuffixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suffix, (tptr tschar)) :: (_len, tulong) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                     (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) :: nil))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof tschar tulong) (Etempvar _len tulong) tulong) ::
         nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _len tulong) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                      (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar)
              (Ederef
                (Ebinop Oadd (Etempvar _suffix (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tulong)
          (Etempvar _len tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
          (Etempvar _val (tptr tvoid)))))))
|}.

Definition f_BN_TestSuffix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (Tstruct _Key_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One
               (Efield
                 (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                   (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _UTIL_StrEqual (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons tulong
                                 (Tcons (tptr tschar) (Tcons tulong Tnil))))
                             tint cc_default))
      ((Ebinop Oadd
         (Efield
           (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
             (Tstruct _Key_T noattr)) _content (tptr tschar))
         (Ecast (Esizeof tulong tulong) tint) (tptr tschar)) ::
       (Ebinop Osub
         (Efield
           (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
             (Tstruct _Key_T noattr)) _len tulong)
         (Ecast (Esizeof tulong tulong) tint) tulong) ::
       (Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) ::
       (Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffixLength tulong) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_BN_GetSuffixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suf, (tptr tschar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                     (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _UTIL_StrEqual (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons tulong
                                 (Tcons (tptr tschar) (Tcons tulong Tnil))))
                             tint cc_default))
      ((Etempvar _suf (tptr tschar)) :: (Etempvar _len tulong) ::
       (Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) ::
       (Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffixLength tulong) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Efield
                       (Ederef
                         (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                         (Tstruct _BorderNode noattr)) _suffixLink
                       (tptr tvoid))))
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
|}.

Definition f_BN_ExportSuffixValue := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (tptr (Tstruct _Key_T noattr)))) ::
                (_val, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _Key_T noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One
               (Efield
                 (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                   (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _move_key (Tfunction (Tcons (tptr tschar) (Tcons tulong Tnil))
                          (tptr (Tstruct _Key_T noattr)) cc_default))
        ((Efield
           (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
             (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) ::
         (Efield
           (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
             (Tstruct _BorderNode noattr)) _keySuffixLength tulong) :: nil))
      (Sassign
        (Ederef (Etempvar _key (tptr (tptr (Tstruct _Key_T noattr))))
          (tptr (Tstruct _Key_T noattr)))
        (Etempvar _t'1 (tptr (Tstruct _Key_T noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tulong)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign (Ederef (Etempvar _val (tptr (tptr tvoid))) (tptr tvoid))
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_BN_HasSuffix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                     (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
|}.

Definition f_BN_SetLink := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                     (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
           (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)) :: nil))
    Sskip)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffixLength tulong)
        (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Etempvar _val (tptr tvoid))))))
|}.

Definition f_BN_GetLink := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_val, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                     (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _t'1 (Econst_int (Int.repr 1) tint))
    (Sset _t'1
      (Ecast
        (Ebinop Oeq
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint) tbool)))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    (Ssequence
      (Sassign (Ederef (Etempvar _val (tptr (tptr tvoid))) (tptr tvoid))
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_BN_SetValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (Tstruct _Key_T noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ogt
               (Efield
                 (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                   (Tstruct _Key_T noattr)) _len tulong)
               (Ecast (Esizeof tulong tulong) tint) tint)
  (Scall None
    (Evar _BN_SetSuffixValue (Tfunction
                               (Tcons (tptr (Tstruct _BorderNode noattr))
                                 (Tcons (tptr tschar)
                                   (Tcons tulong (Tcons (tptr tvoid) Tnil))))
                               tvoid cc_default))
    ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
     (Ebinop Oadd
       (Efield
         (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
           (Tstruct _Key_T noattr)) _content (tptr tschar))
       (Ecast (Esizeof tulong tulong) tint) (tptr tschar)) ::
     (Ebinop Osub
       (Efield
         (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
           (Tstruct _Key_T noattr)) _len tulong)
       (Ecast (Esizeof tulong tulong) tint) tulong) ::
     (Etempvar _val (tptr tvoid)) :: nil))
  (Scall None
    (Evar _BN_SetPrefixValue (Tfunction
                               (Tcons (tptr (Tstruct _BorderNode noattr))
                                 (Tcons tint (Tcons (tptr tvoid) Tnil)))
                               tvoid cc_default))
    ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
     (Efield
       (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
         (Tstruct _Key_T noattr)) _len tulong) ::
     (Etempvar _val (tptr tvoid)) :: nil)))
|}.

Definition f_bordernode_next_cursor := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_bnode_cursor, tulong) ::
                (_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Etempvar _bnode_cursor tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _i tulong)
                       (Ecast (Esizeof tulong tulong) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Scall (Some _t'1)
            (Evar _readFlag (Tfunction (Tcons tulong (Tcons tulong Tnil))
                              tint cc_default))
            ((Efield
               (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                 (Tstruct _BorderNode noattr)) _prefixFlags tulong) ::
             (Etempvar _i tulong) :: nil))
          (Sifthenelse (Etempvar _t'1 tint)
            (Sreturn (Some (Etempvar _i tulong)))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _bnode_cursor tulong)
                   (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                     (Econst_int (Int.repr 1) tint) tint) tint)
      (Sifthenelse (Ebinop One
                     (Efield
                       (Ederef
                         (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                         (Tstruct _BorderNode noattr)) _keySuffix
                       (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'2 (Ecast (Econst_int (Int.repr 1) tint) tbool))
        (Ssequence
          (Sset _t'2
            (Ecast
              (Ebinop One
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              tbool))
          (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool))))
      (Sset _t'2 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                       (Econst_int (Int.repr 1) tint) tint)))
      (Sreturn (Some (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                       (Econst_int (Int.repr 2) tint) tint))))))
|}.

Definition f_Sempty := {|
  fn_return := (tptr (Tstruct _Trie_T noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_new_index, (tptr (Tstruct _Trie_T noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr (Tstruct _Trie_T noattr)) tulong) :: nil))
    (Sset _new_index (Etempvar _t'1 (tptr tvoid))))
  (Sreturn (Some (Etempvar _new_index (tptr (Tstruct _Trie_T noattr))))))
|}.

Definition f_make_cursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _Key_T noattr))) ::
                (_index, (tptr tvoid)) ::
                (_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := ((_obtained_keyslice, tulong) :: (_ret_value, (tptr tvoid)) ::
              (_subindex, (tptr tvoid)) :: nil);
  fn_temps := ((_keyslice, tulong) :: (_node_cursor, (tptr tvoid)) ::
               (_success, tint) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_subkey, (tptr (Tstruct _Key_T noattr))) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, (tptr (Tstruct _Key_T noattr))) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _UTIL_GetNextKeySlice (Tfunction
                                    (Tcons (tptr tschar) (Tcons tulong Tnil))
                                    tulong cc_default))
      ((Efield
         (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
           (Tstruct _Key_T noattr)) _content (tptr tschar)) ::
       (Efield
         (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
           (Tstruct _Key_T noattr)) _len tulong) :: nil))
    (Sset _keyslice (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Imake_cursor (Tfunction
                              (Tcons tulong (Tcons (tptr tvoid) Tnil))
                              (tptr tvoid) cc_default))
        ((Etempvar _keyslice tulong) :: (Etempvar _index (tptr tvoid)) ::
         nil))
      (Sset _node_cursor (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _Iget_key (Tfunction
                            (Tcons (tptr tvoid) (Tcons (tptr tulong) Tnil))
                            tint cc_default))
          ((Etempvar _node_cursor (tptr tvoid)) ::
           (Eaddrof (Evar _obtained_keyslice tulong) (tptr tulong)) :: nil))
        (Sset _success (Etempvar _t'3 tint)))
      (Ssequence
        (Sifthenelse (Etempvar _success tint)
          (Sset _t'8
            (Ecast
              (Ebinop Oeq (Etempvar _keyslice tulong)
                (Evar _obtained_keyslice tulong) tint) tbool))
          (Sset _t'8 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'8 tint)
          (Sifthenelse (Ebinop Ole
                         (Efield
                           (Ederef
                             (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                             (Tstruct _Key_T noattr)) _len tulong)
                         (Ecast (Esizeof tulong tulong) tint) tint)
            (Scall None
              (Evar _push_cursor (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons (tptr tvoid)
                                       (Tcons tulong
                                         (Tcons
                                           (tptr (Tstruct _Cursor_T noattr))
                                           Tnil)))) tvoid cc_default))
              ((Etempvar _index (tptr tvoid)) ::
               (Etempvar _node_cursor (tptr tvoid)) ::
               (Efield
                 (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                   (Tstruct _Key_T noattr)) _len tulong) ::
               (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _Iget_value (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr (tptr tvoid)) Tnil)) tint
                                    cc_default))
                ((Etempvar _node_cursor (tptr tvoid)) ::
                 (Eaddrof (Evar _ret_value (tptr tvoid)) (tptr (tptr tvoid))) ::
                 nil))
              (Ssequence
                (Sset _bnode
                  (Ecast (Evar _ret_value (tptr tvoid))
                    (tptr (Tstruct _BorderNode noattr))))
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _BN_HasSuffix (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _BorderNode noattr))
                                            Tnil) tint cc_default))
                    ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                     nil))
                  (Sifthenelse (Etempvar _t'7 tint)
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _BN_CompareSuffix (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _BorderNode noattr))
                                                    (Tcons
                                                      (tptr (Tstruct _Key_T noattr))
                                                      Tnil)) tint cc_default))
                        ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                         (Etempvar _key (tptr (Tstruct _Key_T noattr))) ::
                         nil))
                      (Sifthenelse (Etempvar _t'4 tint)
                        (Scall None
                          (Evar _push_cursor (Tfunction
                                               (Tcons (tptr tvoid)
                                                 (Tcons (tptr tvoid)
                                                   (Tcons tulong
                                                     (Tcons
                                                       (tptr (Tstruct _Cursor_T noattr))
                                                       Tnil)))) tvoid
                                               cc_default))
                          ((Etempvar _index (tptr tvoid)) ::
                           (Etempvar _node_cursor (tptr tvoid)) ::
                           (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                             (Econst_int (Int.repr 1) tint) tint) ::
                           (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                           nil))
                        (Scall None
                          (Evar _push_cursor (Tfunction
                                               (Tcons (tptr tvoid)
                                                 (Tcons (tptr tvoid)
                                                   (Tcons tulong
                                                     (Tcons
                                                       (tptr (Tstruct _Cursor_T noattr))
                                                       Tnil)))) tvoid
                                               cc_default))
                          ((Etempvar _index (tptr tvoid)) ::
                           (Etempvar _node_cursor (tptr tvoid)) ::
                           (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                             (Econst_int (Int.repr 2) tint) tint) ::
                           (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                           nil))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _BN_GetLink (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _BorderNode noattr))
                                                (Tcons (tptr (tptr tvoid))
                                                  Tnil)) tint cc_default))
                          ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                           (Eaddrof (Evar _subindex (tptr tvoid))
                             (tptr (tptr tvoid))) :: nil))
                        (Sset _success (Etempvar _t'5 tint)))
                      (Sifthenelse (Etempvar _success tint)
                        (Ssequence
                          (Scall None
                            (Evar _push_cursor (Tfunction
                                                 (Tcons (tptr tvoid)
                                                   (Tcons (tptr tvoid)
                                                     (Tcons tulong
                                                       (Tcons
                                                         (tptr (Tstruct _Cursor_T noattr))
                                                         Tnil)))) tvoid
                                                 cc_default))
                            ((Etempvar _index (tptr tvoid)) ::
                             (Etempvar _node_cursor (tptr tvoid)) ::
                             (Ebinop Oadd
                               (Ecast (Esizeof tulong tulong) tint)
                               (Econst_int (Int.repr 1) tint) tint) ::
                             (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar _new_key (Tfunction
                                                 (Tcons (tptr tschar)
                                                   (Tcons tulong Tnil))
                                                 (tptr (Tstruct _Key_T noattr))
                                                 cc_default))
                                ((Ebinop Oadd
                                   (Efield
                                     (Ederef
                                       (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                       (Tstruct _Key_T noattr)) _content
                                     (tptr tschar))
                                   (Ecast (Esizeof tulong tulong) tint)
                                   (tptr tschar)) ::
                                 (Ebinop Osub
                                   (Efield
                                     (Ederef
                                       (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                       (Tstruct _Key_T noattr)) _len tulong)
                                   (Ecast (Esizeof tulong tulong) tint)
                                   tulong) :: nil))
                              (Sset _subkey
                                (Etempvar _t'6 (tptr (Tstruct _Key_T noattr)))))
                            (Ssequence
                              (Scall None
                                (Evar _make_cursor (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _Key_T noattr))
                                                       (Tcons (tptr tvoid)
                                                         (Tcons
                                                           (tptr (Tstruct _Cursor_T noattr))
                                                           Tnil))) tvoid
                                                     cc_default))
                                ((Etempvar _subkey (tptr (Tstruct _Key_T noattr))) ::
                                 (Evar _subindex (tptr tvoid)) ::
                                 (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                                 nil))
                              (Scall None
                                (Evar _free_key (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Key_T noattr))
                                                    Tnil) tvoid cc_default))
                                ((Etempvar _subkey (tptr (Tstruct _Key_T noattr))) ::
                                 nil)))))
                        (Scall None
                          (Evar _push_cursor (Tfunction
                                               (Tcons (tptr tvoid)
                                                 (Tcons (tptr tvoid)
                                                   (Tcons tulong
                                                     (Tcons
                                                       (tptr (Tstruct _Cursor_T noattr))
                                                       Tnil)))) tvoid
                                               cc_default))
                          ((Etempvar _index (tptr tvoid)) ::
                           (Etempvar _node_cursor (tptr tvoid)) ::
                           (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                             (Econst_int (Int.repr 2) tint) tint) ::
                           (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                           nil)))))))))
          (Scall None
            (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
            ((Etempvar _node_cursor (tptr tvoid)) :: nil)))))))
|}.

Definition f_Smake_cursor := {|
  fn_return := (tptr (Tstruct _Cursor_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _Key_T noattr))) ::
                (_index, (tptr (Tstruct _Trie_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) ::
               (_t'2, (tptr (Tstruct _Cursor_T noattr))) ::
               (_t'1, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _new_cursor (Tfunction Tnil (tptr (Tstruct _Cursor_T noattr))
                          cc_default)) nil)
    (Sset _cursor (Etempvar _t'1 (tptr (Tstruct _Cursor_T noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _new_cursor (Tfunction Tnil (tptr (Tstruct _Cursor_T noattr))
                            cc_default)) nil)
      (Scall None
        (Evar _make_cursor (Tfunction
                             (Tcons (tptr (Tstruct _Key_T noattr))
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr (Tstruct _Cursor_T noattr))
                                   Tnil))) tvoid cc_default))
        ((Etempvar _key (tptr (Tstruct _Key_T noattr))) ::
         (Efield
           (Ederef (Etempvar _index (tptr (Tstruct _Trie_T noattr)))
             (Tstruct _Trie_T noattr)) _root (tptr tvoid)) ::
         (Etempvar _t'2 (tptr (Tstruct _Cursor_T noattr))) :: nil)))
    (Sreturn (Some (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))))))
|}.

Definition f_strict_first_cursor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_index, (tptr tvoid)) ::
                (_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := ((_ret_value, (tptr tvoid)) :: (_subindex, (tptr tvoid)) :: nil);
  fn_temps := ((_node_cursor, (tptr tvoid)) :: (_success, tint) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_bnode_cursor, tulong) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tulong) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _Ifirst_cursor (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                             cc_default))
      ((Etempvar _index (tptr tvoid)) :: nil))
    (Sset _node_cursor (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Iget_value (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr (tptr tvoid)) Tnil)) tint
                            cc_default))
        ((Etempvar _node_cursor (tptr tvoid)) ::
         (Eaddrof (Evar _ret_value (tptr tvoid)) (tptr (tptr tvoid))) :: nil))
      (Sset _success (Etempvar _t'2 tint)))
    (Sifthenelse (Etempvar _success tint)
      (Ssequence
        (Sset _bnode
          (Ecast (Evar _ret_value (tptr tvoid))
            (tptr (Tstruct _BorderNode noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _bordernode_next_cursor (Tfunction
                                              (Tcons tulong
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  Tnil)) tulong cc_default))
              ((Econst_int (Int.repr 1) tint) ::
               (Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) :: nil))
            (Sset _bnode_cursor (Etempvar _t'3 tulong)))
          (Sifthenelse (Ebinop Ole (Etempvar _bnode_cursor tulong)
                         (Ecast (Esizeof tulong tulong) tint) tint)
            (Ssequence
              (Scall None
                (Evar _push_cursor (Tfunction
                                     (Tcons (tptr tvoid)
                                       (Tcons (tptr tvoid)
                                         (Tcons tulong
                                           (Tcons
                                             (tptr (Tstruct _Cursor_T noattr))
                                             Tnil)))) tvoid cc_default))
                ((Etempvar _index (tptr tvoid)) ::
                 (Etempvar _node_cursor (tptr tvoid)) ::
                 (Etempvar _bnode_cursor tulong) ::
                 (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))
            (Sifthenelse (Ebinop Oeq (Etempvar _bnode_cursor tulong)
                           (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                             (Econst_int (Int.repr 1) tint) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _push_cursor (Tfunction
                                       (Tcons (tptr tvoid)
                                         (Tcons (tptr tvoid)
                                           (Tcons tulong
                                             (Tcons
                                               (tptr (Tstruct _Cursor_T noattr))
                                               Tnil)))) tvoid cc_default))
                  ((Etempvar _index (tptr tvoid)) ::
                   (Etempvar _node_cursor (tptr tvoid)) ::
                   (Etempvar _bnode_cursor tulong) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                   nil))
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _BN_HasSuffix (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _BorderNode noattr))
                                            Tnil) tint cc_default))
                    ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                     nil))
                  (Sifthenelse (Etempvar _t'6 tint)
                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _BN_GetLink (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _BorderNode noattr))
                                                (Tcons (tptr (tptr tvoid))
                                                  Tnil)) tint cc_default))
                          ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                           (Eaddrof (Evar _subindex (tptr tvoid))
                             (tptr (tptr tvoid))) :: nil))
                        (Sset _success (Etempvar _t'4 tint)))
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _strict_first_cursor (Tfunction
                                                       (Tcons (tptr tvoid)
                                                         (Tcons
                                                           (tptr (Tstruct _Cursor_T noattr))
                                                           Tnil)) tint
                                                       cc_default))
                          ((Evar _subindex (tptr tvoid)) ::
                           (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                           nil))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                          (Ssequence
                            (Scall None
                              (Evar _pop_cursor (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor_T noattr))
                                                    Tnil) tvoid cc_default))
                              ((Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                               nil))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
              (Ssequence
                (Scall None
                  (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                  ((Etempvar _node_cursor (tptr tvoid)) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
      (Ssequence
        (Scall None
          (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
          ((Etempvar _node_cursor (tptr tvoid)) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_normalize_cursor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := ((_ret_value, (tptr tvoid)) :: (_subindex, (tptr tvoid)) ::
              (_subindex__1, (tptr tvoid)) :: nil);
  fn_temps := ((_cs, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_next_bnode_cursor, tulong) :: (_success, tint) ::
               (_next_cursor, (tptr tvoid)) :: (_success__1, tint) ::
               (_next_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_bnode_cursor, tulong) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tulong) :: (_t'6, tint) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tulong) ::
               (_t'1, (tptr (Tstruct _CursorSlice_T noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _top_cursor (Tfunction
                          (Tcons (tptr (Tstruct _Cursor_T noattr)) Tnil)
                          (tptr (Tstruct _CursorSlice_T noattr)) cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) :: nil))
    (Sset _cs (Etempvar _t'1 (tptr (Tstruct _CursorSlice_T noattr)))))
  (Sifthenelse (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
    (Ssequence
      (Scall None
        (Evar _Iget_value (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr (tptr tvoid)) Tnil)) tint
                            cc_default))
        ((Efield
           (Ederef (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
             (Tstruct _CursorSlice_T noattr)) _node_cursor (tptr tvoid)) ::
         (Eaddrof (Evar _ret_value (tptr tvoid)) (tptr (tptr tvoid))) :: nil))
      (Ssequence
        (Sset _bnode (Evar _ret_value (tptr tvoid)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _bordernode_next_cursor (Tfunction
                                              (Tcons tulong
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  Tnil)) tulong cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                   (Tstruct _CursorSlice_T noattr)) _bnode_cursor tuint) ::
               (Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) :: nil))
            (Sset _next_bnode_cursor (Etempvar _t'2 tulong)))
          (Sifthenelse (Ebinop Ole (Etempvar _next_bnode_cursor tulong)
                         (Ecast (Esizeof tulong tulong) tint) tint)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                    (Tstruct _CursorSlice_T noattr)) _bnode_cursor tuint)
                (Etempvar _next_bnode_cursor tulong))
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))
            (Sifthenelse (Ebinop Oeq (Etempvar _next_bnode_cursor tulong)
                           (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                             (Econst_int (Int.repr 1) tint) tint) tint)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                      (Tstruct _CursorSlice_T noattr)) _bnode_cursor tuint)
                  (Ebinop Oadd (Ecast (Esizeof tulong tulong) tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _BN_HasSuffix (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _BorderNode noattr))
                                              Tnil) tint cc_default))
                      ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                       nil))
                    (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tint) tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Evar _BN_GetLink (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  (Tcons (tptr (tptr tvoid))
                                                    Tnil)) tint cc_default))
                            ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                             (Eaddrof (Evar _subindex (tptr tvoid))
                               (tptr (tptr tvoid))) :: nil))
                          (Sset _success (Etempvar _t'3 tint)))
                        (Scall None
                          (Evar _strict_first_cursor (Tfunction
                                                       (Tcons (tptr tvoid)
                                                         (Tcons
                                                           (tptr (Tstruct _Cursor_T noattr))
                                                           Tnil)) tint
                                                       cc_default))
                          ((Evar _subindex (tptr tvoid)) ::
                           (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                           nil)))
                      Sskip))
                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _Inext_cursor (Tfunction (Tcons (tptr tvoid) Tnil)
                                          (tptr tvoid) cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                         (Tstruct _CursorSlice_T noattr)) _node_cursor
                       (tptr tvoid)) :: nil))
                  (Sset _next_cursor (Etempvar _t'5 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'6)
                      (Evar _Iget_value (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons (tptr (tptr tvoid)) Tnil))
                                          tint cc_default))
                      ((Etempvar _next_cursor (tptr tvoid)) ::
                       (Eaddrof (Evar _ret_value (tptr tvoid))
                         (tptr (tptr tvoid))) :: nil))
                    (Sset _success__1 (Etempvar _t'6 tint)))
                  (Sifthenelse (Etempvar _success__1 tint)
                    (Ssequence
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                             (Tstruct _CursorSlice_T noattr)) _node_cursor
                           (tptr tvoid)) :: nil))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                              (Tstruct _CursorSlice_T noattr)) _node_cursor
                            (tptr tvoid))
                          (Etempvar _next_cursor (tptr tvoid)))
                        (Ssequence
                          (Sset _next_bnode (Evar _ret_value (tptr tvoid)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'7)
                                (Evar _bordernode_next_cursor (Tfunction
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr (Tstruct _BorderNode noattr))
                                                                    Tnil))
                                                                tulong
                                                                cc_default))
                                ((Econst_int (Int.repr 1) tint) ::
                                 (Etempvar _next_bnode (tptr (Tstruct _BorderNode noattr))) ::
                                 nil))
                              (Sset _bnode_cursor (Etempvar _t'7 tulong)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _cs (tptr (Tstruct _CursorSlice_T noattr)))
                                    (Tstruct _CursorSlice_T noattr))
                                  _bnode_cursor tuint)
                                (Etempvar _bnode_cursor tulong))
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _next_bnode_cursor tulong)
                                                 (Ebinop Oadd
                                                   (Ecast
                                                     (Esizeof tulong tulong)
                                                     tint)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint) tint)
                                    (Ssequence
                                      (Scall (Some _t'10)
                                        (Evar _BN_HasSuffix (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                Tnil) tint
                                                              cc_default))
                                        ((Etempvar _next_bnode (tptr (Tstruct _BorderNode noattr))) ::
                                         nil))
                                      (Sset _t'9
                                        (Ecast
                                          (Eunop Onotbool
                                            (Etempvar _t'10 tint) tint)
                                          tbool)))
                                    (Sset _t'9
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _t'9 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'8)
                                          (Evar _BN_GetLink (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                (Tcons
                                                                  (tptr (tptr tvoid))
                                                                  Tnil)) tint
                                                              cc_default))
                                          ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                                           (Eaddrof
                                             (Evar _subindex__1 (tptr tvoid))
                                             (tptr (tptr tvoid))) :: nil))
                                        (Sset _success__1
                                          (Etempvar _t'8 tint)))
                                      (Scall None
                                        (Evar _strict_first_cursor (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (Tstruct _Cursor_T noattr))
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                        ((Evar _subindex__1 (tptr tvoid)) ::
                                         (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                                         nil)))
                                    Sskip))
                                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))
                    (Ssequence
                      (Scall None
                        (Evar _Ifree_cursor (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                        ((Etempvar _next_cursor (tptr tvoid)) :: nil))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
    (Ssequence
      (Scall None
        (Evar _pop_cursor (Tfunction
                            (Tcons (tptr (Tstruct _Cursor_T noattr)) Tnil)
                            tvoid cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) :: nil))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_Sget_value := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) ::
                (_index, (tptr (Tstruct _Trie_T noattr))) ::
                (_value, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_create_pair := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_key1, (tptr tschar)) :: (_len1, tulong) ::
                (_key2, (tptr tschar)) :: (_len2, tulong) ::
                (_v1, (tptr tvoid)) :: (_v2, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_keyslice1, tulong) :: (_keyslice2, tulong) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_k1, (tptr (Tstruct _Key_T noattr))) ::
               (_k2, (tptr (Tstruct _Key_T noattr))) ::
               (_index, (tptr tvoid)) :: (_temp_cursor, (tptr tvoid)) ::
               (_bnode__1, (tptr (Tstruct _BorderNode noattr))) ::
               (_index__1, (tptr tvoid)) ::
               (_temp_cursor__1, (tptr tvoid)) ::
               (_bnode1, (tptr (Tstruct _BorderNode noattr))) ::
               (_k1__1, (tptr (Tstruct _Key_T noattr))) ::
               (_bnode2, (tptr (Tstruct _BorderNode noattr))) ::
               (_k2__1, (tptr (Tstruct _Key_T noattr))) ::
               (_index__2, (tptr tvoid)) ::
               (_temp_cursor__2, (tptr tvoid)) :: (_t'19, (tptr tvoid)) ::
               (_t'18, (tptr tvoid)) :: (_t'17, (tptr tvoid)) ::
               (_t'16, (tptr (Tstruct _Key_T noattr))) ::
               (_t'15, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'14, (tptr (Tstruct _Key_T noattr))) ::
               (_t'13, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'12, tint) :: (_t'11, (tptr tvoid)) ::
               (_t'10, (tptr tvoid)) :: (_t'9, (tptr tvoid)) ::
               (_t'8, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'7, (tptr tvoid)) :: (_t'6, (tptr tvoid)) ::
               (_t'5, (tptr (Tstruct _Key_T noattr))) ::
               (_t'4, (tptr (Tstruct _Key_T noattr))) ::
               (_t'3, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _UTIL_GetNextKeySlice (Tfunction
                                    (Tcons (tptr tschar) (Tcons tulong Tnil))
                                    tulong cc_default))
      ((Etempvar _key1 (tptr tschar)) :: (Etempvar _len1 tulong) :: nil))
    (Sset _keyslice1 (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _UTIL_GetNextKeySlice (Tfunction
                                      (Tcons (tptr tschar)
                                        (Tcons tulong Tnil)) tulong
                                      cc_default))
        ((Etempvar _key2 (tptr tschar)) :: (Etempvar _len2 tulong) :: nil))
      (Sset _keyslice2 (Etempvar _t'2 tulong)))
    (Sifthenelse (Ebinop Oeq (Etempvar _keyslice1 tulong)
                   (Etempvar _keyslice2 tulong) tint)
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _len1 tulong)
                       (Ecast (Esizeof tulong tulong) tint) tint)
          (Sset _t'12 (Econst_int (Int.repr 1) tint))
          (Sset _t'12
            (Ecast
              (Ebinop Ole (Etempvar _len2 tulong)
                (Ecast (Esizeof tulong tulong) tint) tint) tbool)))
        (Sifthenelse (Etempvar _t'12 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _BN_NewBorderNode (Tfunction Tnil
                                          (tptr (Tstruct _BorderNode noattr))
                                          cc_default)) nil)
              (Sset _bnode
                (Etempvar _t'3 (tptr (Tstruct _BorderNode noattr)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _new_key (Tfunction
                                   (Tcons (tptr tschar) (Tcons tulong Tnil))
                                   (tptr (Tstruct _Key_T noattr)) cc_default))
                  ((Etempvar _key1 (tptr tschar)) ::
                   (Etempvar _len1 tulong) :: nil))
                (Sset _k1 (Etempvar _t'4 (tptr (Tstruct _Key_T noattr)))))
              (Ssequence
                (Scall None
                  (Evar _BN_SetValue (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _BorderNode noattr))
                                         (Tcons
                                           (tptr (Tstruct _Key_T noattr))
                                           (Tcons (tptr tvoid) Tnil))) tvoid
                                       cc_default))
                  ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                   (Etempvar _k1 (tptr (Tstruct _Key_T noattr))) ::
                   (Etempvar _v1 (tptr tvoid)) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _new_key (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons tulong Tnil))
                                       (tptr (Tstruct _Key_T noattr))
                                       cc_default))
                      ((Etempvar _key2 (tptr tschar)) ::
                       (Etempvar _len2 tulong) :: nil))
                    (Sset _k2 (Etempvar _t'5 (tptr (Tstruct _Key_T noattr)))))
                  (Ssequence
                    (Scall None
                      (Evar _BN_SetValue (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _BorderNode noattr))
                                             (Tcons
                                               (tptr (Tstruct _Key_T noattr))
                                               (Tcons (tptr tvoid) Tnil)))
                                           tvoid cc_default))
                      ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                       (Etempvar _k2 (tptr (Tstruct _Key_T noattr))) ::
                       (Etempvar _v2 (tptr tvoid)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _free_key (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Key_T noattr))
                                            Tnil) tvoid cc_default))
                        ((Etempvar _k1 (tptr (Tstruct _Key_T noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _free_key (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _Key_T noattr))
                                              Tnil) tvoid cc_default))
                          ((Etempvar _k2 (tptr (Tstruct _Key_T noattr))) ::
                           nil))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'6)
                              (Evar _Iempty (Tfunction Tnil (tptr tvoid)
                                              cc_default)) nil)
                            (Sset _index (Etempvar _t'6 (tptr tvoid))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'7)
                                (Evar _Ifirst_cursor (Tfunction
                                                       (Tcons (tptr tvoid)
                                                         Tnil) (tptr tvoid)
                                                       cc_default))
                                ((Etempvar _index (tptr tvoid)) :: nil))
                              (Sset _temp_cursor
                                (Etempvar _t'7 (tptr tvoid))))
                            (Ssequence
                              (Scall None
                                (Evar _Iput (Tfunction
                                              (Tcons tulong
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tvoid cc_default))
                                ((Etempvar _keyslice1 tulong) ::
                                 (Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                                 (Etempvar _temp_cursor (tptr tvoid)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _Ifree_cursor (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                  ((Etempvar _temp_cursor (tptr tvoid)) ::
                                   nil))
                                (Sreturn (Some (Etempvar _index (tptr tvoid)))))))))))))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'8)
                (Evar _BN_NewBorderNode (Tfunction Tnil
                                          (tptr (Tstruct _BorderNode noattr))
                                          cc_default)) nil)
              (Sset _bnode__1
                (Etempvar _t'8 (tptr (Tstruct _BorderNode noattr)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _create_pair (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons tulong
                                           (Tcons (tptr tschar)
                                             (Tcons tulong
                                               (Tcons (tptr tvoid)
                                                 (Tcons (tptr tvoid) Tnil))))))
                                       (tptr tvoid) cc_default))
                  ((Ebinop Oadd (Etempvar _key1 (tptr tschar))
                     (Ecast (Esizeof tulong tulong) tint) (tptr tschar)) ::
                   (Ebinop Osub (Etempvar _len1 tulong)
                     (Ecast (Esizeof tulong tulong) tint) tulong) ::
                   (Ebinop Oadd (Etempvar _key2 (tptr tschar))
                     (Ecast (Esizeof tulong tulong) tint) (tptr tschar)) ::
                   (Ebinop Osub (Etempvar _len2 tulong)
                     (Ecast (Esizeof tulong tulong) tint) tulong) ::
                   (Etempvar _v1 (tptr tvoid)) ::
                   (Etempvar _v2 (tptr tvoid)) :: nil))
                (Scall None
                  (Evar _BN_SetLink (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _BorderNode noattr))
                                        (Tcons (tptr tvoid) Tnil)) tvoid
                                      cc_default))
                  ((Etempvar _bnode__1 (tptr (Tstruct _BorderNode noattr))) ::
                   (Etempvar _t'9 (tptr tvoid)) :: nil)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'10)
                    (Evar _Iempty (Tfunction Tnil (tptr tvoid) cc_default))
                    nil)
                  (Sset _index__1 (Etempvar _t'10 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'11)
                      (Evar _Ifirst_cursor (Tfunction
                                             (Tcons (tptr tvoid) Tnil)
                                             (tptr tvoid) cc_default))
                      ((Etempvar _index__1 (tptr tvoid)) :: nil))
                    (Sset _temp_cursor__1 (Etempvar _t'11 (tptr tvoid))))
                  (Ssequence
                    (Scall None
                      (Evar _Iput (Tfunction
                                    (Tcons tulong
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid) Tnil))) tvoid
                                    cc_default))
                      ((Etempvar _keyslice1 tulong) ::
                       (Etempvar _bnode__1 (tptr (Tstruct _BorderNode noattr))) ::
                       (Etempvar _temp_cursor__1 (tptr tvoid)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _Ifree_cursor (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                        ((Etempvar _temp_cursor__1 (tptr tvoid)) :: nil))
                      (Sreturn (Some (Etempvar _index__1 (tptr tvoid))))))))))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'13)
            (Evar _BN_NewBorderNode (Tfunction Tnil
                                      (tptr (Tstruct _BorderNode noattr))
                                      cc_default)) nil)
          (Sset _bnode1 (Etempvar _t'13 (tptr (Tstruct _BorderNode noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'14)
              (Evar _new_key (Tfunction
                               (Tcons (tptr tschar) (Tcons tulong Tnil))
                               (tptr (Tstruct _Key_T noattr)) cc_default))
              ((Etempvar _key1 (tptr tschar)) :: (Etempvar _len1 tulong) ::
               nil))
            (Sset _k1__1 (Etempvar _t'14 (tptr (Tstruct _Key_T noattr)))))
          (Ssequence
            (Scall None
              (Evar _BN_SetValue (Tfunction
                                   (Tcons (tptr (Tstruct _BorderNode noattr))
                                     (Tcons (tptr (Tstruct _Key_T noattr))
                                       (Tcons (tptr tvoid) Tnil))) tvoid
                                   cc_default))
              ((Etempvar _bnode1 (tptr (Tstruct _BorderNode noattr))) ::
               (Etempvar _k1__1 (tptr (Tstruct _Key_T noattr))) ::
               (Etempvar _v1 (tptr tvoid)) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'15)
                  (Evar _BN_NewBorderNode (Tfunction Tnil
                                            (tptr (Tstruct _BorderNode noattr))
                                            cc_default)) nil)
                (Sset _bnode2
                  (Etempvar _t'15 (tptr (Tstruct _BorderNode noattr)))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'16)
                    (Evar _new_key (Tfunction
                                     (Tcons (tptr tschar)
                                       (Tcons tulong Tnil))
                                     (tptr (Tstruct _Key_T noattr))
                                     cc_default))
                    ((Etempvar _key2 (tptr tschar)) ::
                     (Etempvar _len2 tulong) :: nil))
                  (Sset _k2__1
                    (Etempvar _t'16 (tptr (Tstruct _Key_T noattr)))))
                (Ssequence
                  (Scall None
                    (Evar _BN_SetValue (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BorderNode noattr))
                                           (Tcons
                                             (tptr (Tstruct _Key_T noattr))
                                             (Tcons (tptr tvoid) Tnil)))
                                         tvoid cc_default))
                    ((Etempvar _bnode2 (tptr (Tstruct _BorderNode noattr))) ::
                     (Etempvar _k2__1 (tptr (Tstruct _Key_T noattr))) ::
                     (Etempvar _v2 (tptr tvoid)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _free_key (Tfunction
                                        (Tcons (tptr (Tstruct _Key_T noattr))
                                          Tnil) tvoid cc_default))
                      ((Etempvar _k1__1 (tptr (Tstruct _Key_T noattr))) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _free_key (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Key_T noattr))
                                            Tnil) tvoid cc_default))
                        ((Etempvar _k2__1 (tptr (Tstruct _Key_T noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'17)
                            (Evar _Iempty (Tfunction Tnil (tptr tvoid)
                                            cc_default)) nil)
                          (Sset _index__2 (Etempvar _t'17 (tptr tvoid))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'18)
                              (Evar _Ifirst_cursor (Tfunction
                                                     (Tcons (tptr tvoid)
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                              ((Etempvar _index__2 (tptr tvoid)) :: nil))
                            (Sset _temp_cursor__2
                              (Etempvar _t'18 (tptr tvoid))))
                          (Ssequence
                            (Scall None
                              (Evar _Iput (Tfunction
                                            (Tcons tulong
                                              (Tcons (tptr tvoid)
                                                (Tcons (tptr tvoid) Tnil)))
                                            tvoid cc_default))
                              ((Etempvar _keyslice2 tulong) ::
                               (Etempvar _bnode2 (tptr (Tstruct _BorderNode noattr))) ::
                               (Etempvar _temp_cursor__2 (tptr tvoid)) ::
                               nil))
                            (Ssequence
                              (Scall None
                                (Evar _Ifree_cursor (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                ((Etempvar _temp_cursor__2 (tptr tvoid)) ::
                                 nil))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'19)
                                    (Evar _Ifirst_cursor (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil)
                                                           (tptr tvoid)
                                                           cc_default))
                                    ((Etempvar _index__2 (tptr tvoid)) ::
                                     nil))
                                  (Sset _temp_cursor__2
                                    (Etempvar _t'19 (tptr tvoid))))
                                (Ssequence
                                  (Scall None
                                    (Evar _Iput (Tfunction
                                                  (Tcons tulong
                                                    (Tcons (tptr tvoid)
                                                      (Tcons (tptr tvoid)
                                                        Tnil))) tvoid
                                                  cc_default))
                                    ((Etempvar _keyslice1 tulong) ::
                                     (Etempvar _bnode1 (tptr (Tstruct _BorderNode noattr))) ::
                                     (Etempvar _temp_cursor__2 (tptr tvoid)) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _Ifree_cursor (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                      ((Etempvar _temp_cursor__2 (tptr tvoid)) ::
                                       nil))
                                    (Sreturn (Some (Etempvar _index__2 (tptr tvoid))))))))))))))))))))))
|}.

Definition f_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tschar)) :: (_len, tulong) ::
                (_v, (tptr tvoid)) :: (_index, (tptr tvoid)) :: nil);
  fn_vars := ((_obtained_keyslice, tulong) :: (_ret_value, (tptr tvoid)) ::
              (_k2, (tptr (Tstruct _Key_T noattr))) :: (_v2, (tptr tvoid)) ::
              (_subindex__1, (tptr tvoid)) :: nil);
  fn_temps := ((_keyslice, tulong) :: (_node_cursor, (tptr tvoid)) ::
               (_success, tint) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_k, (tptr (Tstruct _Key_T noattr))) ::
               (_subindex, (tptr tvoid)) ::
               (_bnode__1, (tptr (Tstruct _BorderNode noattr))) ::
               (_k__1, (tptr (Tstruct _Key_T noattr))) :: (_t'11, tint) ::
               (_t'10, (tptr (Tstruct _Key_T noattr))) ::
               (_t'9, (tptr (Tstruct _BorderNode noattr))) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _Key_T noattr))) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _UTIL_GetNextKeySlice (Tfunction
                                    (Tcons (tptr tschar) (Tcons tulong Tnil))
                                    tulong cc_default))
      ((Etempvar _key (tptr tschar)) :: (Etempvar _len tulong) :: nil))
    (Sset _keyslice (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Imake_cursor (Tfunction
                              (Tcons tulong (Tcons (tptr tvoid) Tnil))
                              (tptr tvoid) cc_default))
        ((Etempvar _keyslice tulong) :: (Etempvar _index (tptr tvoid)) ::
         nil))
      (Sset _node_cursor (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _Iget_key (Tfunction
                            (Tcons (tptr tvoid) (Tcons (tptr tulong) Tnil))
                            tint cc_default))
          ((Etempvar _node_cursor (tptr tvoid)) ::
           (Eaddrof (Evar _obtained_keyslice tulong) (tptr tulong)) :: nil))
        (Sset _success (Etempvar _t'3 tint)))
      (Ssequence
        (Sifthenelse (Etempvar _success tint)
          (Sset _t'11
            (Ecast
              (Ebinop Oeq (Evar _obtained_keyslice tulong)
                (Etempvar _keyslice tulong) tint) tbool))
          (Sset _t'11 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'11 tint)
          (Ssequence
            (Scall None
              (Evar _Iget_value (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr (tptr tvoid)) Tnil)) tint
                                  cc_default))
              ((Etempvar _node_cursor (tptr tvoid)) ::
               (Eaddrof (Evar _ret_value (tptr tvoid)) (tptr (tptr tvoid))) ::
               nil))
            (Ssequence
              (Sset _bnode (Evar _ret_value (tptr tvoid)))
              (Ssequence
                (Scall None
                  (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                  ((Etempvar _node_cursor (tptr tvoid)) :: nil))
                (Sifthenelse (Ebinop Ole (Etempvar _len tulong)
                               (Ecast (Esizeof tulong tulong) tint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _BN_SetPrefixValue (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _BorderNode noattr))
                                                   (Tcons tint
                                                     (Tcons (tptr tvoid)
                                                       Tnil))) tvoid
                                                 cc_default))
                      ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                       (Etempvar _len tulong) ::
                       (Etempvar _v (tptr tvoid)) :: nil))
                    (Sreturn None))
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _BN_HasSuffix (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _BorderNode noattr))
                                              Tnil) tint cc_default))
                      ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                       nil))
                    (Sifthenelse (Etempvar _t'8 tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _new_key (Tfunction
                                             (Tcons (tptr tschar)
                                               (Tcons tulong Tnil))
                                             (tptr (Tstruct _Key_T noattr))
                                             cc_default))
                            ((Etempvar _key (tptr tschar)) ::
                             (Etempvar _len tulong) :: nil))
                          (Sset _k
                            (Etempvar _t'4 (tptr (Tstruct _Key_T noattr)))))
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _BN_TestSuffix (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _BorderNode noattr))
                                                     (Tcons
                                                       (tptr (Tstruct _Key_T noattr))
                                                       Tnil)) tint
                                                   cc_default))
                            ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                             (Etempvar _k (tptr (Tstruct _Key_T noattr))) ::
                             nil))
                          (Sifthenelse (Etempvar _t'6 tint)
                            (Ssequence
                              (Scall None
                                (Evar _free_key (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Key_T noattr))
                                                    Tnil) tvoid cc_default))
                                ((Etempvar _k (tptr (Tstruct _Key_T noattr))) ::
                                 nil))
                              (Ssequence
                                (Scall None
                                  (Evar _BN_SetSuffixValue (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _BorderNode noattr))
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 (Tcons
                                                                   tulong
                                                                   (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))))
                                                             tvoid
                                                             cc_default))
                                  ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                                   (Ebinop Oadd (Etempvar _key (tptr tschar))
                                     (Ecast (Esizeof tulong tulong) tint)
                                     (tptr tschar)) ::
                                   (Ebinop Osub (Etempvar _len tulong)
                                     (Ecast (Esizeof tulong tulong) tint)
                                     tulong) :: (Etempvar _v (tptr tvoid)) ::
                                   nil))
                                (Sreturn None)))
                            (Ssequence
                              (Scall None
                                (Evar _free_key (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Key_T noattr))
                                                    Tnil) tvoid cc_default))
                                ((Etempvar _k (tptr (Tstruct _Key_T noattr))) ::
                                 nil))
                              (Ssequence
                                (Scall None
                                  (Evar _BN_ExportSuffixValue (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _BorderNode noattr))
                                                                  (Tcons
                                                                    (tptr (tptr (Tstruct _Key_T noattr)))
                                                                    (Tcons
                                                                    (tptr (tptr tvoid))
                                                                    Tnil)))
                                                                tint
                                                                cc_default))
                                  ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                                   (Eaddrof
                                     (Evar _k2 (tptr (Tstruct _Key_T noattr)))
                                     (tptr (tptr (Tstruct _Key_T noattr)))) ::
                                   (Eaddrof (Evar _v2 (tptr tvoid))
                                     (tptr (tptr tvoid))) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'5)
                                      (Evar _create_pair (Tfunction
                                                           (Tcons
                                                             (tptr tschar)
                                                             (Tcons tulong
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 (Tcons
                                                                   tulong
                                                                   (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))))))
                                                           (tptr tvoid)
                                                           cc_default))
                                      ((Ebinop Oadd
                                         (Etempvar _key (tptr tschar))
                                         (Ecast (Esizeof tulong tulong) tint)
                                         (tptr tschar)) ::
                                       (Ebinop Osub (Etempvar _len tulong)
                                         (Ecast (Esizeof tulong tulong) tint)
                                         tulong) ::
                                       (Efield
                                         (Ederef
                                           (Evar _k2 (tptr (Tstruct _Key_T noattr)))
                                           (Tstruct _Key_T noattr)) _content
                                         (tptr tschar)) ::
                                       (Efield
                                         (Ederef
                                           (Evar _k2 (tptr (Tstruct _Key_T noattr)))
                                           (Tstruct _Key_T noattr)) _len
                                         tulong) ::
                                       (Etempvar _v (tptr tvoid)) ::
                                       (Evar _v2 (tptr tvoid)) :: nil))
                                    (Sset _subindex
                                      (Etempvar _t'5 (tptr tvoid))))
                                  (Ssequence
                                    (Scall None
                                      (Evar _BN_SetLink (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _BorderNode noattr))
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil)) tvoid
                                                          cc_default))
                                      ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                                       (Etempvar _subindex (tptr tvoid)) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _free_key (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _Key_T noattr))
                                                            Tnil) tvoid
                                                          cc_default))
                                        ((Evar _k2 (tptr (Tstruct _Key_T noattr))) ::
                                         nil))
                                      (Sreturn None)))))))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _BN_GetLink (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  (Tcons (tptr (tptr tvoid))
                                                    Tnil)) tint cc_default))
                            ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                             (Eaddrof (Evar _subindex__1 (tptr tvoid))
                               (tptr (tptr tvoid))) :: nil))
                          (Sset _success (Etempvar _t'7 tint)))
                        (Sifthenelse (Etempvar _success tint)
                          (Ssequence
                            (Scall None
                              (Evar _put (Tfunction
                                           (Tcons (tptr tschar)
                                             (Tcons tulong
                                               (Tcons (tptr tvoid)
                                                 (Tcons (tptr tvoid) Tnil))))
                                           tvoid cc_default))
                              ((Ebinop Oadd (Etempvar _key (tptr tschar))
                                 (Ecast (Esizeof tulong tulong) tint)
                                 (tptr tschar)) ::
                               (Ebinop Osub (Etempvar _len tulong)
                                 (Ecast (Esizeof tulong tulong) tint) tulong) ::
                               (Etempvar _v (tptr tvoid)) ::
                               (Evar _subindex__1 (tptr tvoid)) :: nil))
                            (Sreturn None))
                          (Ssequence
                            (Scall None
                              (Evar _BN_SetSuffixValue (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _BorderNode noattr))
                                                           (Tcons
                                                             (tptr tschar)
                                                             (Tcons tulong
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil))))
                                                         tvoid cc_default))
                              ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                               (Ebinop Oadd (Etempvar _key (tptr tschar))
                                 (Ecast (Esizeof tulong tulong) tint)
                                 (tptr tschar)) ::
                               (Ebinop Osub (Etempvar _len tulong)
                                 (Ecast (Esizeof tulong tulong) tint) tulong) ::
                               (Etempvar _v (tptr tvoid)) :: nil))
                            (Sreturn None))))))))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'9)
                (Evar _BN_NewBorderNode (Tfunction Tnil
                                          (tptr (Tstruct _BorderNode noattr))
                                          cc_default)) nil)
              (Sset _bnode__1
                (Etempvar _t'9 (tptr (Tstruct _BorderNode noattr)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'10)
                  (Evar _new_key (Tfunction
                                   (Tcons (tptr tschar) (Tcons tulong Tnil))
                                   (tptr (Tstruct _Key_T noattr)) cc_default))
                  ((Etempvar _key (tptr tschar)) :: (Etempvar _len tulong) ::
                   nil))
                (Sset _k__1 (Etempvar _t'10 (tptr (Tstruct _Key_T noattr)))))
              (Ssequence
                (Scall None
                  (Evar _BN_SetValue (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _BorderNode noattr))
                                         (Tcons
                                           (tptr (Tstruct _Key_T noattr))
                                           (Tcons (tptr tvoid) Tnil))) tvoid
                                       cc_default))
                  ((Etempvar _bnode__1 (tptr (Tstruct _BorderNode noattr))) ::
                   (Etempvar _k__1 (tptr (Tstruct _Key_T noattr))) ::
                   (Etempvar _v (tptr tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _free_key (Tfunction
                                      (Tcons (tptr (Tstruct _Key_T noattr))
                                        Tnil) tvoid cc_default))
                    ((Etempvar _k__1 (tptr (Tstruct _Key_T noattr))) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _Iput (Tfunction
                                    (Tcons tulong
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid) Tnil))) tvoid
                                    cc_default))
                      ((Etempvar _keyslice tulong) ::
                       (Etempvar _bnode__1 (tptr (Tstruct _BorderNode noattr))) ::
                       (Etempvar _node_cursor (tptr tvoid)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _Ifree_cursor (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                        ((Etempvar _node_cursor (tptr tvoid)) :: nil))
                      (Sreturn None))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _Key_T Struct
   ((_content, (tptr tschar)) :: (_len, tulong) :: nil)
   noattr ::
 Composite _CursorSlice_T Struct
   ((_node, (tptr tvoid)) :: (_node_cursor, (tptr tvoid)) ::
    (_bnode_cursor, tuint) :: nil)
   noattr ::
 Composite _Cursor_T Struct
   ((_capacity, tulong) :: (_size, tulong) ::
    (_content, (tptr (Tstruct _CursorSlice_T noattr))) :: nil)
   noattr ::
 Composite _Trie_T Struct
   ((_root, (tptr tvoid)) :: (_size, tulong) :: nil)
   noattr ::
 Composite _BorderNode Struct
   ((_prefixFlags, tulong) :: (_prefixLinks, (tarray (tptr tvoid) 9)) ::
    (_suffixLink, (tptr tvoid)) :: (_keySuffix, (tptr tschar)) ::
    (_keySuffixLength, tulong) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_Iempty,
   Gfun(External (EF_external "Iempty"
                   (mksignature nil AST.Tlong cc_default)) Tnil (tptr tvoid)
     cc_default)) ::
 (_Imake_cursor,
   Gfun(External (EF_external "Imake_cursor"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons (tptr tvoid) Tnil))
     (tptr tvoid) cc_default)) ::
 (_Ifirst_cursor,
   Gfun(External (EF_external "Ifirst_cursor"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default)) ::
 (_Inext_cursor,
   Gfun(External (EF_external "Inext_cursor"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default)) ::
 (_Ifree_cursor,
   Gfun(External (EF_external "Ifree_cursor"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_Iget_key,
   Gfun(External (EF_external "Iget_key"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tulong) Tnil)) tint cc_default)) ::
 (_Iget_value,
   Gfun(External (EF_external "Iget_value"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr (tptr tvoid)) Tnil)) tint cc_default)) ::
 (_Iput,
   Gfun(External (EF_external "Iput"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons tulong (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tvoid
     cc_default)) :: (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_push_cursor, Gfun(Internal f_push_cursor)) ::
 (_pop_cursor, Gfun(Internal f_pop_cursor)) ::
 (_top_cursor, Gfun(Internal f_top_cursor)) ::
 (_new_cursor, Gfun(Internal f_new_cursor)) ::
 (_UTIL_GetNextKeySlice, Gfun(Internal f_UTIL_GetNextKeySlice)) ::
 (_UTIL_StrEqual, Gfun(Internal f_UTIL_StrEqual)) ::
 (_new_key, Gfun(Internal f_new_key)) ::
 (_move_key, Gfun(Internal f_move_key)) ::
 (_free_key, Gfun(Internal f_free_key)) ::
 (_setFlag, Gfun(Internal f_setFlag)) ::
 (_clearFlag, Gfun(Internal f_clearFlag)) ::
 (_readFlag, Gfun(Internal f_readFlag)) ::
 (_BN_NewBorderNode, Gfun(Internal f_BN_NewBorderNode)) ::
 (_BN_FreeBorderNode, Gfun(Internal f_BN_FreeBorderNode)) ::
 (_BN_SetPrefixValue, Gfun(Internal f_BN_SetPrefixValue)) ::
 (_BN_GetPrefixValue, Gfun(Internal f_BN_GetPrefixValue)) ::
 (_BN_SetSuffixValue, Gfun(Internal f_BN_SetSuffixValue)) ::
 (_BN_TestSuffix, Gfun(Internal f_BN_TestSuffix)) ::
 (_BN_GetSuffixValue, Gfun(Internal f_BN_GetSuffixValue)) ::
 (_BN_ExportSuffixValue, Gfun(Internal f_BN_ExportSuffixValue)) ::
 (_BN_HasSuffix, Gfun(Internal f_BN_HasSuffix)) ::
 (_BN_SetLink, Gfun(Internal f_BN_SetLink)) ::
 (_BN_GetLink, Gfun(Internal f_BN_GetLink)) ::
 (_BN_SetValue, Gfun(Internal f_BN_SetValue)) ::
 (_BN_CompareSuffix,
   Gfun(External (EF_external "BN_CompareSuffix"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _BorderNode noattr))
       (Tcons (tptr (Tstruct _Key_T noattr)) Tnil)) tint cc_default)) ::
 (_bordernode_next_cursor, Gfun(Internal f_bordernode_next_cursor)) ::
 (_Sempty, Gfun(Internal f_Sempty)) ::
 (_make_cursor, Gfun(Internal f_make_cursor)) ::
 (_Smake_cursor, Gfun(Internal f_Smake_cursor)) ::
 (_strict_first_cursor, Gfun(Internal f_strict_first_cursor)) ::
 (_normalize_cursor, Gfun(Internal f_normalize_cursor)) ::
 (_Sget_value, Gfun(Internal f_Sget_value)) ::
 (_create_pair, Gfun(Internal f_create_pair)) ::
 (_put, Gfun(Internal f_put)) :: nil).

Definition public_idents : list ident :=
(_put :: _create_pair :: _Sget_value :: _normalize_cursor ::
 _strict_first_cursor :: _Smake_cursor :: _Sempty :: _BN_CompareSuffix ::
 _BN_SetValue :: _BN_GetLink :: _BN_SetLink :: _BN_HasSuffix ::
 _BN_ExportSuffixValue :: _BN_GetSuffixValue :: _BN_TestSuffix ::
 _BN_SetSuffixValue :: _BN_GetPrefixValue :: _BN_SetPrefixValue ::
 _BN_FreeBorderNode :: _BN_NewBorderNode :: _readFlag :: _clearFlag ::
 _setFlag :: _free_key :: _move_key :: _new_key :: _UTIL_StrEqual ::
 _UTIL_GetNextKeySlice :: _new_cursor :: _top_cursor :: _pop_cursor ::
 _push_cursor :: _surely_malloc :: _Iput :: _Iget_value :: _Iget_key ::
 _Ifree_cursor :: _Inext_cursor :: _Ifirst_cursor :: _Imake_cursor ::
 _Iempty :: _exit :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


