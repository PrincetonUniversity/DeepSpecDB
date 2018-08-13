From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _BN_CompareSuffix : ident := 114%positive.
Definition _BN_ExportSuffixValue : ident := 109%positive.
Definition _BN_FreeBorderNode : ident := 97%positive.
Definition _BN_GetLink : ident := 111%positive.
Definition _BN_GetPrefixValue : ident := 101%positive.
Definition _BN_GetSuffixValue : ident := 107%positive.
Definition _BN_HasSuffix : ident := 112%positive.
Definition _BN_NewBorderNode : ident := 96%positive.
Definition _BN_SetLink : ident := 110%positive.
Definition _BN_SetPrefixValue : ident := 100%positive.
Definition _BN_SetSuffixValue : ident := 103%positive.
Definition _BN_SetValue : ident := 113%positive.
Definition _BN_TestSuffix : ident := 105%positive.
Definition _BorderNode : ident := 14%positive.
Definition _CursorSlice_T : ident := 6%positive.
Definition _Cursor_T : ident := 9%positive.
Definition _Ifree_cursor : ident := 71%positive.
Definition _Iget_key : ident := 72%positive.
Definition _Iget_value : ident := 73%positive.
Definition _Imake_cursor : ident := 70%positive.
Definition _Key_T : ident := 3%positive.
Definition _Sempty : ident := 116%positive.
Definition _Sget_value : ident := 129%positive.
Definition _Smake_cursor : ident := 127%positive.
Definition _UTIL_GetNextKeySlice : ident := 85%positive.
Definition _UTIL_StrEqual : ident := 90%positive.
Definition ___builtin_ais_annot : ident := 15%positive.
Definition ___builtin_annot : ident := 22%positive.
Definition ___builtin_annot_intval : ident := 23%positive.
Definition ___builtin_bswap : ident := 16%positive.
Definition ___builtin_bswap16 : ident := 18%positive.
Definition ___builtin_bswap32 : ident := 17%positive.
Definition ___builtin_bswap64 : ident := 48%positive.
Definition ___builtin_clz : ident := 49%positive.
Definition ___builtin_clzl : ident := 50%positive.
Definition ___builtin_clzll : ident := 51%positive.
Definition ___builtin_ctz : ident := 52%positive.
Definition ___builtin_ctzl : ident := 53%positive.
Definition ___builtin_ctzll : ident := 54%positive.
Definition ___builtin_debug : ident := 66%positive.
Definition ___builtin_fabs : ident := 19%positive.
Definition ___builtin_fmadd : ident := 57%positive.
Definition ___builtin_fmax : ident := 55%positive.
Definition ___builtin_fmin : ident := 56%positive.
Definition ___builtin_fmsub : ident := 58%positive.
Definition ___builtin_fnmadd : ident := 59%positive.
Definition ___builtin_fnmsub : ident := 60%positive.
Definition ___builtin_fsqrt : ident := 20%positive.
Definition ___builtin_membar : ident := 24%positive.
Definition ___builtin_memcpy_aligned : ident := 21%positive.
Definition ___builtin_nop : ident := 65%positive.
Definition ___builtin_read16_reversed : ident := 61%positive.
Definition ___builtin_read32_reversed : ident := 62%positive.
Definition ___builtin_va_arg : ident := 26%positive.
Definition ___builtin_va_copy : ident := 27%positive.
Definition ___builtin_va_end : ident := 28%positive.
Definition ___builtin_va_start : ident := 25%positive.
Definition ___builtin_write16_reversed : ident := 63%positive.
Definition ___builtin_write32_reversed : ident := 64%positive.
Definition ___compcert_i64_dtos : ident := 33%positive.
Definition ___compcert_i64_dtou : ident := 34%positive.
Definition ___compcert_i64_sar : ident := 45%positive.
Definition ___compcert_i64_sdiv : ident := 39%positive.
Definition ___compcert_i64_shl : ident := 43%positive.
Definition ___compcert_i64_shr : ident := 44%positive.
Definition ___compcert_i64_smod : ident := 41%positive.
Definition ___compcert_i64_smulh : ident := 46%positive.
Definition ___compcert_i64_stod : ident := 35%positive.
Definition ___compcert_i64_stof : ident := 37%positive.
Definition ___compcert_i64_udiv : ident := 40%positive.
Definition ___compcert_i64_umod : ident := 42%positive.
Definition ___compcert_i64_umulh : ident := 47%positive.
Definition ___compcert_i64_utod : ident := 36%positive.
Definition ___compcert_i64_utof : ident := 38%positive.
Definition ___compcert_va_composite : ident := 32%positive.
Definition ___compcert_va_float64 : ident := 31%positive.
Definition ___compcert_va_int32 : ident := 29%positive.
Definition ___compcert_va_int64 : ident := 30%positive.
Definition __make_cursor : ident := 126%positive.
Definition _a : ident := 86%positive.
Definition _b : ident := 88%positive.
Definition _bn : ident := 98%positive.
Definition _bnode : ident := 122%positive.
Definition _bnode_cursor : ident := 5%positive.
Definition _bordernode : ident := 95%positive.
Definition _capacity : ident := 7%positive.
Definition _content : ident := 1%positive.
Definition _cursor : ident := 77%positive.
Definition _exit : ident := 69%positive.
Definition _free : ident := 68%positive.
Definition _i : ident := 79%positive.
Definition _index : ident := 117%positive.
Definition _key : ident := 104%positive.
Definition _keySuffix : ident := 12%positive.
Definition _keySuffixLength : ident := 13%positive.
Definition _keyslice : ident := 118%positive.
Definition _len : ident := 2%positive.
Definition _lenA : ident := 87%positive.
Definition _lenB : ident := 89%positive.
Definition _main : ident := 130%positive.
Definition _malloc : ident := 67%positive.
Definition _move_key : ident := 94%positive.
Definition _n : ident := 74%positive.
Definition _newKey : ident := 91%positive.
Definition _newStr : ident := 92%positive.
Definition _new_addr : ident := 78%positive.
Definition _new_cursor : ident := 82%positive.
Definition _new_index : ident := 115%positive.
Definition _new_key : ident := 93%positive.
Definition _node_cursor : ident := 4%positive.
Definition _obtained_keyslice : ident := 119%positive.
Definition _p : ident := 75%positive.
Definition _pop_cursor : ident := 81%positive.
Definition _prefixLinks : ident := 10%positive.
Definition _push_cursor : ident := 80%positive.
Definition _res : ident := 84%positive.
Definition _ret_temp : ident := 108%positive.
Definition _ret_value : ident := 121%positive.
Definition _size : ident := 8%positive.
Definition _str : ident := 83%positive.
Definition _subindex : ident := 124%positive.
Definition _subkey : ident := 123%positive.
Definition _subkey__1 : ident := 125%positive.
Definition _success : ident := 120%positive.
Definition _suf : ident := 106%positive.
Definition _suffix : ident := 102%positive.
Definition _suffixLink : ident := 11%positive.
Definition _surely_malloc : ident := 76%positive.
Definition _val : ident := 99%positive.
Definition _value : ident := 128%positive.
Definition _t'1 : ident := 131%positive.
Definition _t'10 : ident := 140%positive.
Definition _t'11 : ident := 141%positive.
Definition _t'12 : ident := 142%positive.
Definition _t'13 : ident := 143%positive.
Definition _t'14 : ident := 144%positive.
Definition _t'15 : ident := 145%positive.
Definition _t'16 : ident := 146%positive.
Definition _t'17 : ident := 147%positive.
Definition _t'18 : ident := 148%positive.
Definition _t'19 : ident := 149%positive.
Definition _t'2 : ident := 132%positive.
Definition _t'3 : ident := 133%positive.
Definition _t'4 : ident := 134%positive.
Definition _t'5 : ident := 135%positive.
Definition _t'6 : ident := 136%positive.
Definition _t'7 : ident := 137%positive.
Definition _t'8 : ident := 138%positive.
Definition _t'9 : ident := 139%positive.

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
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
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
  fn_params := ((_node_cursor, (tptr tvoid)) :: (_bnode_cursor, tuint) ::
                (_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_addr, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_i, tuint) :: (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, (tptr tvoid)) ::
               (_t'14, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_t'13, tuint) ::
               (_t'12, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_t'11, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) ::
               (_t'6, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _CursorSlice_T noattr))) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
          (Tstruct _Cursor_T noattr)) _capacity tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _CursorSlice_T noattr) tuint) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _content
            (tptr (Tstruct _CursorSlice_T noattr)))
          (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sset _t'9
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _capacity tuint))
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _size tuint))
          (Sifthenelse (Ebinop Ole (Etempvar _t'9 tuint)
                         (Etempvar _t'10 tuint) tint)
            (Ssequence
              (Ssequence
                (Sset _t'18
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                      (Tstruct _Cursor_T noattr)) _capacity tuint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                      (Tstruct _Cursor_T noattr)) _capacity tuint)
                  (Ebinop Omul (Etempvar _t'18 tuint)
                    (Econst_int (Int.repr 2) tint) tuint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'17
                      (Efield
                        (Ederef
                          (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                          (Tstruct _Cursor_T noattr)) _capacity tuint))
                    (Scall (Some _t'2)
                      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                             (tptr tvoid) cc_default))
                      ((Ebinop Omul
                         (Esizeof (Tstruct _CursorSlice_T noattr) tuint)
                         (Etempvar _t'17 tuint) tuint) :: nil)))
                  (Sset _new_addr (Etempvar _t'2 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Sset _t'16
                            (Efield
                              (Ederef
                                (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                (Tstruct _Cursor_T noattr)) _size tuint))
                          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                         (Etempvar _t'16 tuint) tint)
                            Sskip
                            Sbreak))
                        (Ssequence
                          (Ssequence
                            (Sset _t'14
                              (Efield
                                (Ederef
                                  (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                  (Tstruct _Cursor_T noattr)) _content
                                (tptr (Tstruct _CursorSlice_T noattr))))
                            (Ssequence
                              (Sset _t'15
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _t'14 (tptr (Tstruct _CursorSlice_T noattr)))
                                      (Etempvar _i tuint)
                                      (tptr (Tstruct _CursorSlice_T noattr)))
                                    (Tstruct _CursorSlice_T noattr))
                                  _node_cursor (tptr tvoid)))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr)))
                                      (Etempvar _i tuint)
                                      (tptr (Tstruct _CursorSlice_T noattr)))
                                    (Tstruct _CursorSlice_T noattr))
                                  _node_cursor (tptr tvoid))
                                (Etempvar _t'15 (tptr tvoid)))))
                          (Ssequence
                            (Sset _t'12
                              (Efield
                                (Ederef
                                  (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                                  (Tstruct _Cursor_T noattr)) _content
                                (tptr (Tstruct _CursorSlice_T noattr))))
                            (Ssequence
                              (Sset _t'13
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _t'12 (tptr (Tstruct _CursorSlice_T noattr)))
                                      (Etempvar _i tuint)
                                      (tptr (Tstruct _CursorSlice_T noattr)))
                                    (Tstruct _CursorSlice_T noattr))
                                  _bnode_cursor tuint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr)))
                                      (Etempvar _i tuint)
                                      (tptr (Tstruct _CursorSlice_T noattr)))
                                    (Tstruct _CursorSlice_T noattr))
                                  _bnode_cursor tuint)
                                (Etempvar _t'13 tuint))))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'11
                        (Efield
                          (Ederef
                            (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                            (Tstruct _Cursor_T noattr)) _content
                          (tptr (Tstruct _CursorSlice_T noattr))))
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _t'11 (tptr (Tstruct _CursorSlice_T noattr))) ::
                         nil)))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                          (Tstruct _Cursor_T noattr)) _content
                        (tptr (Tstruct _CursorSlice_T noattr)))
                      (Etempvar _new_addr (tptr (Tstruct _CursorSlice_T noattr))))))))
            Sskip)))))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _content
          (tptr (Tstruct _CursorSlice_T noattr))))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tuint))
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Etempvar _t'6 (tptr (Tstruct _CursorSlice_T noattr)))
                (Etempvar _t'7 tuint) (tptr (Tstruct _CursorSlice_T noattr)))
              (Tstruct _CursorSlice_T noattr)) _node_cursor (tptr tvoid))
          (Etempvar _node_cursor (tptr tvoid)))))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _content
            (tptr (Tstruct _CursorSlice_T noattr))))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
                (Tstruct _Cursor_T noattr)) _size tuint))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Etempvar _t'4 (tptr (Tstruct _CursorSlice_T noattr)))
                  (Etempvar _t'5 tuint)
                  (tptr (Tstruct _CursorSlice_T noattr)))
                (Tstruct _CursorSlice_T noattr)) _bnode_cursor tuint)
            (Etempvar _bnode_cursor tuint))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tuint)
          (Ebinop Oadd (Etempvar _t'3 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))))
|}.

Definition f_pop_cursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
        (Tstruct _Cursor_T noattr)) _size tuint))
  (Sifthenelse (Ebinop One (Etempvar _t'1 tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _size tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _size tuint)
        (Ebinop Osub (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    Sskip))
|}.

Definition f_new_cursor := {|
  fn_return := (tptr (Tstruct _Cursor_T noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) ::
               (_t'2, tuint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr (Tstruct _Cursor_T noattr)) tuint) :: nil))
    (Sset _cursor (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
              (Tstruct _Cursor_T noattr)) _size tuint) (Etempvar _t'2 tuint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _capacity tuint)
        (Etempvar _t'2 tuint)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))
            (Tstruct _Cursor_T noattr)) _content
          (tptr (Tstruct _CursorSlice_T noattr)))
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))))))))
|}.

Definition f_UTIL_GetNextKeySlice := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_i, tuint) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tuint) (Ecast (Esizeof tuint tuint) tint)
          tint)
        (Ssequence
          (Sset _res
            (Ebinop Oshl (Etempvar _res tuint) (Econst_int (Int.repr 8) tint)
              tuint))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Ederef (Etempvar _str (tptr tschar)) tschar))
                  (Sset _res
                    (Ebinop Oor (Etempvar _res tuint)
                      (Ebinop Oand (Ecast (Etempvar _t'1 tschar) tuint)
                        (Econst_int (Int.repr 255) tint) tuint) tuint)))
                (Sset _str
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Econst_int (Int.repr 1) tint) (tptr tschar))))
              Sskip)
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint)))))
      (Sreturn (Some (Etempvar _res tuint))))))
|}.

Definition f_UTIL_StrEqual := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_lenA, tuint) ::
                (_b, (tptr tschar)) :: (_lenB, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _lenA tuint) (Etempvar _lenB tuint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _lenA tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tschar)) (Etempvar _i tuint)
                  (tptr tschar)) tschar))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar))
              (Sifthenelse (Ebinop One (Etempvar _t'1 tschar)
                             (Etempvar _t'2 tschar) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_new_key := {|
  fn_return := (tptr (Tstruct _Key_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_newKey, (tptr (Tstruct _Key_T noattr))) ::
               (_newStr, (tptr tschar)) :: (_i, tuint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'3, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _newKey
    (Ecast (Econst_int (Int.repr 0) tint) (tptr (Tstruct _Key_T noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof tschar tuint) (Etempvar _len tuint) tuint) ::
         nil))
      (Sset _newStr (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _newStr (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar)
                (Etempvar _t'3 tschar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                   cc_default))
            ((Esizeof (Tstruct _Key_T noattr) tuint) :: nil))
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
                  (Tstruct _Key_T noattr)) _len tuint) (Etempvar _len tuint))
            (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))))))))))
|}.

Definition f_move_key := {|
  fn_return := (tptr (Tstruct _Key_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_newKey, (tptr (Tstruct _Key_T noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _newKey
    (Ecast (Econst_int (Int.repr 0) tint) (tptr (Tstruct _Key_T noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _Key_T noattr) tuint) :: nil))
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
              (Tstruct _Key_T noattr)) _len tuint) (Etempvar _len tuint))
        (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _Key_T noattr)))))))))
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
      ((Esizeof (Tstruct _BorderNode noattr) tuint) :: nil))
    (Sset _bordernode
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _BorderNode noattr)))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 4) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _prefixLinks
                  (tarray (tptr tvoid) 4)) (Etempvar _i tint)
                (tptr (tptr tvoid))) (tptr tvoid))
            (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr))))))))))
|}.

Definition f_BN_FreeBorderNode := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bordernode, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
      (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _t'2 (tptr tschar)) :: nil)))
        Sskip))
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
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _prefixLinks (tarray (tptr tvoid) 4))
      (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)
      (tptr (tptr tvoid))) (tptr tvoid)) (Etempvar _val (tptr tvoid)))
|}.

Definition f_BN_GetPrefixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _prefixLinks
          (tarray (tptr tvoid) 4))
        (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)
        (tptr (tptr tvoid))) (tptr tvoid)))
  (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
|}.

Definition f_BN_SetSuffixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suffix, (tptr tschar)) :: (_len, tuint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr tschar)) :: (_t'4, (tptr tschar)) ::
               (_t'3, tschar) :: (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'4 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _t'5 (tptr tschar)) :: nil)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof tschar tuint) (Etempvar _len tuint) tuint) ::
         nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _suffix (tptr tschar))
                      (Etempvar _i tuint) (tptr tschar)) tschar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'2 (tptr tschar))
                      (Etempvar _i tuint) (tptr tschar)) tschar)
                  (Etempvar _t'3 tschar)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
          (Etempvar _len tuint))
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
  fn_temps := ((_t'1, tint) :: (_t'6, tuint) :: (_t'5, (tptr tschar)) ::
               (_t'4, tuint) :: (_t'3, (tptr tschar)) ::
               (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
        (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
  (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
              (Tstruct _Key_T noattr)) _content (tptr tschar)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                (Tstruct _Key_T noattr)) _len tuint))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
              (Scall (Some _t'1)
                (Evar _UTIL_StrEqual (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons tuint
                                           (Tcons (tptr tschar)
                                             (Tcons tuint Tnil)))) tint
                                       cc_default))
                ((Ebinop Oadd (Etempvar _t'3 (tptr tschar))
                   (Ecast (Esizeof tuint tuint) tint) (tptr tschar)) ::
                 (Ebinop Osub (Etempvar _t'4 tuint)
                   (Ecast (Esizeof tuint tuint) tint) tuint) ::
                 (Etempvar _t'5 (tptr tschar)) :: (Etempvar _t'6 tuint) ::
                 nil))))))
      (Sreturn (Some (Etempvar _t'1 tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_BN_GetSuffixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suf, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'5, (tptr tschar)) :: (_t'4, tuint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'5 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
        (Scall (Some _t'1)
          (Evar _UTIL_StrEqual (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons tuint
                                     (Tcons (tptr tschar) (Tcons tuint Tnil))))
                                 tint cc_default))
          ((Etempvar _suf (tptr tschar)) :: (Etempvar _len tuint) ::
           (Etempvar _t'3 (tptr tschar)) :: (Etempvar _t'4 tuint) :: nil))))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
        (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_BN_ExportSuffixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (tptr (Tstruct _Key_T noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret_temp, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _Key_T noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
              (Scall (Some _t'1)
                (Evar _move_key (Tfunction
                                  (Tcons (tptr tschar) (Tcons tuint Tnil))
                                  (tptr (Tstruct _Key_T noattr)) cc_default))
                ((Etempvar _t'3 (tptr tschar)) :: (Etempvar _t'4 tuint) ::
                 nil))))
          (Sassign
            (Ederef (Etempvar _key (tptr (tptr (Tstruct _Key_T noattr))))
              (tptr (Tstruct _Key_T noattr)))
            (Etempvar _t'1 (tptr (Tstruct _Key_T noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
            (Econst_int (Int.repr 0) tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
            (Econst_int (Int.repr 0) tint))))
      (Sassign
        (Ederef (Etempvar _key (tptr (tptr (Tstruct _Key_T noattr))))
          (tptr (Tstruct _Key_T noattr))) (Econst_int (Int.repr 0) tint))))
  (Ssequence
    (Sset _ret_temp
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _ret_temp (tptr tvoid)))))))
|}.

Definition f_BN_SetLink := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _t'2 (tptr tschar)) :: nil)))
      Sskip))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
        (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Etempvar _val (tptr tvoid))))))
|}.

Definition f_BN_GetLink := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_BN_HasSuffix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
        (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
  (Sreturn (Some (Ebinop One (Etempvar _t'1 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_BN_SetValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (Tstruct _Key_T noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuint) :: (_t'3, (tptr tschar)) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
        (Tstruct _Key_T noattr)) _len tuint))
  (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tuint)
                 (Ecast (Esizeof tuint tuint) tint) tint)
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
            (Tstruct _Key_T noattr)) _content (tptr tschar)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
              (Tstruct _Key_T noattr)) _len tuint))
        (Scall None
          (Evar _BN_SetSuffixValue (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _BorderNode noattr))
                                       (Tcons (tptr tschar)
                                         (Tcons tuint
                                           (Tcons (tptr tvoid) Tnil)))) tvoid
                                     cc_default))
          ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
           (Ebinop Oadd (Etempvar _t'3 (tptr tschar))
             (Ecast (Esizeof tuint tuint) tint) (tptr tschar)) ::
           (Ebinop Osub (Etempvar _t'4 tuint)
             (Ecast (Esizeof tuint tuint) tint) tuint) ::
           (Etempvar _val (tptr tvoid)) :: nil))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
            (Tstruct _Key_T noattr)) _len tuint))
      (Scall None
        (Evar _BN_SetPrefixValue (Tfunction
                                   (Tcons (tptr (Tstruct _BorderNode noattr))
                                     (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                   tvoid cc_default))
        ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
         (Etempvar _t'2 tuint) :: (Etempvar _val (tptr tvoid)) :: nil)))))
|}.

Definition f_Sempty := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_new_index, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr tvoid) tuint) :: nil))
    (Sset _new_index (Etempvar _t'1 (tptr tvoid))))
  (Sreturn (Some (Etempvar _new_index (tptr tvoid)))))
|}.

Definition f__make_cursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _Key_T noattr))) ::
                (_index, (tptr tvoid)) ::
                (_cursor, (tptr (Tstruct _Cursor_T noattr))) :: nil);
  fn_vars := ((_obtained_keyslice, tuint) :: (_ret_value, (tptr tvoid)) ::
              nil);
  fn_temps := ((_keyslice, tuint) :: (_node_cursor, (tptr tvoid)) ::
               (_success, tint) ::
               (_bnode, (tptr (Tstruct _BorderNode noattr))) ::
               (_subkey, (tptr (Tstruct _Key_T noattr))) ::
               (_subindex, (tptr tvoid)) ::
               (_subkey__1, (tptr (Tstruct _Key_T noattr))) ::
               (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _Key_T noattr))) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _Key_T noattr))) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: (_t'19, tuint) ::
               (_t'18, (tptr tschar)) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, (tptr tvoid)) :: (_t'14, tuint) ::
               (_t'13, (tptr tschar)) :: (_t'12, tuint) ::
               (_t'11, (tptr tschar)) :: (_t'10, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'18
        (Efield
          (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
            (Tstruct _Key_T noattr)) _content (tptr tschar)))
      (Ssequence
        (Sset _t'19
          (Efield
            (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
              (Tstruct _Key_T noattr)) _len tuint))
        (Scall (Some _t'1)
          (Evar _UTIL_GetNextKeySlice (Tfunction
                                        (Tcons (tptr tschar)
                                          (Tcons tuint Tnil)) tuint
                                        cc_default))
          ((Etempvar _t'18 (tptr tschar)) :: (Etempvar _t'19 tuint) :: nil))))
    (Sset _keyslice (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Imake_cursor (Tfunction
                              (Tcons tuint (Tcons (tptr tvoid) Tnil))
                              (tptr tvoid) cc_default))
        ((Etempvar _keyslice tuint) :: (Etempvar _index (tptr tvoid)) :: nil))
      (Sset _node_cursor (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _Iget_key (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr tvoid) (Tcons (tptr tuint) Tnil)))
                            tint cc_default))
          ((Etempvar _node_cursor (tptr tvoid)) ::
           (Etempvar _index (tptr tvoid)) ::
           (Eaddrof (Evar _obtained_keyslice tuint) (tptr tuint)) :: nil))
        (Sset _success (Etempvar _t'3 tint)))
      (Ssequence
        (Sifthenelse (Etempvar _success tint)
          (Ssequence
            (Sset _t'17 (Evar _obtained_keyslice tuint))
            (Sset _t'9
              (Ecast
                (Ebinop Oeq (Etempvar _keyslice tuint) (Etempvar _t'17 tuint)
                  tint) tbool)))
          (Sset _t'9 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'9 tint)
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                  (Tstruct _Key_T noattr)) _len tuint))
            (Sifthenelse (Ebinop Ole (Etempvar _t'10 tuint)
                           (Ecast (Esizeof tuint tuint) tint) tint)
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                      (Tstruct _Key_T noattr)) _len tuint))
                (Scall None
                  (Evar _push_cursor (Tfunction
                                       (Tcons (tptr tvoid)
                                         (Tcons tuint
                                           (Tcons
                                             (tptr (Tstruct _Cursor_T noattr))
                                             Tnil))) tvoid cc_default))
                  ((Etempvar _node_cursor (tptr tvoid)) ::
                   (Etempvar _t'16 tuint) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                   nil)))
              (Ssequence
                (Scall None
                  (Evar _Iget_value (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons (tptr (tptr tvoid)) Tnil)))
                                      tint cc_default))
                  ((Etempvar _node_cursor (tptr tvoid)) ::
                   (Etempvar _index (tptr tvoid)) ::
                   (Eaddrof (Evar _ret_value (tptr tvoid))
                     (tptr (tptr tvoid))) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'15 (Evar _ret_value (tptr tvoid)))
                    (Sset _bnode
                      (Ecast (Etempvar _t'15 (tptr tvoid))
                        (tptr (Tstruct _BorderNode noattr)))))
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
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                  (Tstruct _Key_T noattr)) _content
                                (tptr tschar)))
                            (Ssequence
                              (Sset _t'14
                                (Efield
                                  (Ederef
                                    (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                    (Tstruct _Key_T noattr)) _len tuint))
                              (Scall (Some _t'4)
                                (Evar _new_key (Tfunction
                                                 (Tcons (tptr tschar)
                                                   (Tcons tuint Tnil))
                                                 (tptr (Tstruct _Key_T noattr))
                                                 cc_default))
                                ((Ebinop Oadd (Etempvar _t'13 (tptr tschar))
                                   (Ecast (Esizeof tuint tuint) tint)
                                   (tptr tschar)) ::
                                 (Ebinop Osub (Etempvar _t'14 tuint)
                                   (Ecast (Esizeof tuint tuint) tint) tuint) ::
                                 nil))))
                          (Sset _subkey
                            (Etempvar _t'4 (tptr (Tstruct _Key_T noattr)))))
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _BN_CompareSuffix (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _Key_T noattr))
                                                          Tnil)) tint
                                                      cc_default))
                            ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                             (Etempvar _subkey (tptr (Tstruct _Key_T noattr))) ::
                             nil))
                          (Sifthenelse (Etempvar _t'5 tint)
                            (Scall None
                              (Evar _push_cursor (Tfunction
                                                   (Tcons (tptr tvoid)
                                                     (Tcons tuint
                                                       (Tcons
                                                         (tptr (Tstruct _Cursor_T noattr))
                                                         Tnil))) tvoid
                                                   cc_default))
                              ((Etempvar _node_cursor (tptr tvoid)) ::
                               (Ebinop Oadd
                                 (Ecast (Esizeof tuint tuint) tint)
                                 (Econst_int (Int.repr 1) tint) tint) ::
                               (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                               nil))
                            (Scall None
                              (Evar _push_cursor (Tfunction
                                                   (Tcons (tptr tvoid)
                                                     (Tcons tuint
                                                       (Tcons
                                                         (tptr (Tstruct _Cursor_T noattr))
                                                         Tnil))) tvoid
                                                   cc_default))
                              ((Etempvar _node_cursor (tptr tvoid)) ::
                               (Ebinop Oadd
                                 (Ecast (Esizeof tuint tuint) tint)
                                 (Econst_int (Int.repr 2) tint) tint) ::
                               (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                               nil)))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _BN_GetLink (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  Tnil) (tptr tvoid)
                                                cc_default))
                            ((Etempvar _bnode (tptr (Tstruct _BorderNode noattr))) ::
                             nil))
                          (Sset _subindex (Etempvar _t'6 (tptr tvoid))))
                        (Sifthenelse (Ebinop One
                                       (Etempvar _subindex (tptr tvoid))
                                       (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid)) tint)
                          (Ssequence
                            (Scall None
                              (Evar _push_cursor (Tfunction
                                                   (Tcons (tptr tvoid)
                                                     (Tcons tuint
                                                       (Tcons
                                                         (tptr (Tstruct _Cursor_T noattr))
                                                         Tnil))) tvoid
                                                   cc_default))
                              ((Etempvar _node_cursor (tptr tvoid)) ::
                               (Ebinop Oadd
                                 (Ecast (Esizeof tuint tuint) tint)
                                 (Econst_int (Int.repr 1) tint) tint) ::
                               (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                               nil))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                        (Tstruct _Key_T noattr)) _content
                                      (tptr tschar)))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _key (tptr (Tstruct _Key_T noattr)))
                                          (Tstruct _Key_T noattr)) _len
                                        tuint))
                                    (Scall (Some _t'7)
                                      (Evar _new_key (Tfunction
                                                       (Tcons (tptr tschar)
                                                         (Tcons tuint Tnil))
                                                       (tptr (Tstruct _Key_T noattr))
                                                       cc_default))
                                      ((Ebinop Oadd
                                         (Etempvar _t'11 (tptr tschar))
                                         (Ecast (Esizeof tuint tuint) tint)
                                         (tptr tschar)) ::
                                       (Ebinop Osub (Etempvar _t'12 tuint)
                                         (Ecast (Esizeof tuint tuint) tint)
                                         tuint) :: nil))))
                                (Sset _subkey__1
                                  (Etempvar _t'7 (tptr (Tstruct _Key_T noattr)))))
                              (Scall None
                                (Evar __make_cursor (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Key_T noattr))
                                                        (Tcons (tptr tvoid)
                                                          (Tcons
                                                            (tptr (Tstruct _Cursor_T noattr))
                                                            Tnil))) tvoid
                                                      cc_default))
                                ((Etempvar _subkey__1 (tptr (Tstruct _Key_T noattr))) ::
                                 (Etempvar _subindex (tptr tvoid)) ::
                                 (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                                 nil))))
                          (Scall None
                            (Evar _push_cursor (Tfunction
                                                 (Tcons (tptr tvoid)
                                                   (Tcons tuint
                                                     (Tcons
                                                       (tptr (Tstruct _Cursor_T noattr))
                                                       Tnil))) tvoid
                                                 cc_default))
                            ((Etempvar _node_cursor (tptr tvoid)) ::
                             (Ebinop Oadd (Ecast (Esizeof tuint tuint) tint)
                               (Econst_int (Int.repr 2) tint) tint) ::
                             (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr))) ::
                             nil))))))))))
          (Scall None
            (Evar _Ifree_cursor (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
            ((Etempvar _node_cursor (tptr tvoid)) :: nil)))))))
|}.

Definition f_Smake_cursor := {|
  fn_return := (tptr (Tstruct _Cursor_T noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _Key_T noattr))) ::
                (_index, (tptr tvoid)) :: nil);
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
        (Evar __make_cursor (Tfunction
                              (Tcons (tptr (Tstruct _Key_T noattr))
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr (Tstruct _Cursor_T noattr))
                                    Tnil))) tvoid cc_default))
        ((Etempvar _key (tptr (Tstruct _Key_T noattr))) ::
         (Etempvar _index (tptr tvoid)) ::
         (Etempvar _t'2 (tptr (Tstruct _Cursor_T noattr))) :: nil)))
    (Sreturn (Some (Etempvar _cursor (tptr (Tstruct _Cursor_T noattr)))))))
|}.

Definition f_Sget_value := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor_T noattr))) ::
                (_index, (tptr tvoid)) :: (_value, (tptr (tptr tvoid))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition composites : list composite_definition :=
(Composite _Key_T Struct
   ((_content, (tptr tschar)) :: (_len, tuint) :: nil)
   noattr ::
 Composite _CursorSlice_T Struct
   ((_node_cursor, (tptr tvoid)) :: (_bnode_cursor, tuint) :: nil)
   noattr ::
 Composite _Cursor_T Struct
   ((_capacity, tuint) :: (_size, tuint) ::
    (_content, (tptr (Tstruct _CursorSlice_T noattr))) :: nil)
   noattr ::
 Composite _BorderNode Struct
   ((_prefixLinks, (tarray (tptr tvoid) 4)) :: (_suffixLink, (tptr tvoid)) ::
    (_keySuffix, (tptr tschar)) :: (_keySuffixLength, tuint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_Imake_cursor,
   Gfun(External (EF_external "Imake_cursor"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tuint (Tcons (tptr tvoid) Tnil))
     (tptr tvoid) cc_default)) ::
 (_Ifree_cursor,
   Gfun(External (EF_external "Ifree_cursor"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_Iget_key,
   Gfun(External (EF_external "Iget_key"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons (tptr tuint) Tnil))) tint
     cc_default)) ::
 (_Iget_value,
   Gfun(External (EF_external "Iget_value"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons (tptr (tptr tvoid)) Tnil))) tint
     cc_default)) :: (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_push_cursor, Gfun(Internal f_push_cursor)) ::
 (_pop_cursor, Gfun(Internal f_pop_cursor)) ::
 (_new_cursor, Gfun(Internal f_new_cursor)) ::
 (_UTIL_GetNextKeySlice, Gfun(Internal f_UTIL_GetNextKeySlice)) ::
 (_UTIL_StrEqual, Gfun(Internal f_UTIL_StrEqual)) ::
 (_new_key, Gfun(Internal f_new_key)) ::
 (_move_key, Gfun(Internal f_move_key)) ::
 (_BN_NewBorderNode, Gfun(Internal f_BN_NewBorderNode)) ::
 (_BN_FreeBorderNode, Gfun(Internal f_BN_FreeBorderNode)) ::
 (_BN_SetPrefixValue, Gfun(Internal f_BN_SetPrefixValue)) ::
 (_BN_GetPrefixValue, Gfun(Internal f_BN_GetPrefixValue)) ::
 (_BN_SetSuffixValue, Gfun(Internal f_BN_SetSuffixValue)) ::
 (_BN_TestSuffix, Gfun(Internal f_BN_TestSuffix)) ::
 (_BN_GetSuffixValue, Gfun(Internal f_BN_GetSuffixValue)) ::
 (_BN_ExportSuffixValue, Gfun(Internal f_BN_ExportSuffixValue)) ::
 (_BN_SetLink, Gfun(Internal f_BN_SetLink)) ::
 (_BN_GetLink, Gfun(Internal f_BN_GetLink)) ::
 (_BN_HasSuffix, Gfun(Internal f_BN_HasSuffix)) ::
 (_BN_SetValue, Gfun(Internal f_BN_SetValue)) ::
 (_BN_CompareSuffix,
   Gfun(External (EF_external "BN_CompareSuffix"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (Tstruct _BorderNode noattr))
       (Tcons (tptr (Tstruct _Key_T noattr)) Tnil)) tint cc_default)) ::
 (_Sempty, Gfun(Internal f_Sempty)) ::
 (__make_cursor, Gfun(Internal f__make_cursor)) ::
 (_Smake_cursor, Gfun(Internal f_Smake_cursor)) ::
 (_Sget_value, Gfun(Internal f_Sget_value)) :: nil).

Definition public_idents : list ident :=
(_Sget_value :: _Smake_cursor :: __make_cursor :: _Sempty ::
 _BN_CompareSuffix :: _BN_SetValue :: _BN_HasSuffix :: _BN_GetLink ::
 _BN_SetLink :: _BN_ExportSuffixValue :: _BN_GetSuffixValue ::
 _BN_TestSuffix :: _BN_SetSuffixValue :: _BN_GetPrefixValue ::
 _BN_SetPrefixValue :: _BN_FreeBorderNode :: _BN_NewBorderNode ::
 _move_key :: _new_key :: _UTIL_StrEqual :: _UTIL_GetNextKeySlice ::
 _new_cursor :: _pop_cursor :: _push_cursor :: _surely_malloc ::
 _Iget_value :: _Iget_key :: _Ifree_cursor :: _Imake_cursor :: _exit ::
 _free :: _malloc :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


