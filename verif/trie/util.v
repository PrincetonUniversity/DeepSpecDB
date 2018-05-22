From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _UTIL_BinarySearch : ident := 63%positive.
Definition _UTIL_GetNextKeySlice : ident := 87%positive.
Definition _UTIL_KeySliceToStr : ident := 90%positive.
Definition _UTIL_Min : ident := 79%positive.
Definition _UTIL_ResizeArray : ident := 71%positive.
Definition _UTIL_Shuffle : ident := 95%positive.
Definition _UTIL_StrEqual : ident := 82%positive.
Definition _UTIL_StrToUl : ident := 75%positive.
Definition _UTIL_UlToStr : ident := 77%positive.
Definition ___assert_fail : ident := 53%positive.
Definition ___builtin_ais_annot : ident := 1%positive.
Definition ___builtin_annot : ident := 8%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 34%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 52%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 43%positive.
Definition ___builtin_fmax : ident := 41%positive.
Definition ___builtin_fmin : ident := 42%positive.
Definition ___builtin_fmsub : ident := 44%positive.
Definition ___builtin_fnmadd : ident := 45%positive.
Definition ___builtin_fnmsub : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 6%positive.
Definition ___builtin_membar : ident := 10%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_nop : ident := 51%positive.
Definition ___builtin_read16_reversed : ident := 47%positive.
Definition ___builtin_read32_reversed : ident := 48%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition ___builtin_write16_reversed : ident := 49%positive.
Definition ___builtin_write32_reversed : ident := 50%positive.
Definition ___compcert_i64_dtos : ident := 19%positive.
Definition ___compcert_i64_dtou : ident := 20%positive.
Definition ___compcert_i64_sar : ident := 31%positive.
Definition ___compcert_i64_sdiv : ident := 25%positive.
Definition ___compcert_i64_shl : ident := 29%positive.
Definition ___compcert_i64_shr : ident := 30%positive.
Definition ___compcert_i64_smod : ident := 27%positive.
Definition ___compcert_i64_smulh : ident := 32%positive.
Definition ___compcert_i64_stod : ident := 21%positive.
Definition ___compcert_i64_stof : ident := 23%positive.
Definition ___compcert_i64_udiv : ident := 26%positive.
Definition ___compcert_i64_umod : ident := 28%positive.
Definition ___compcert_i64_umulh : ident := 33%positive.
Definition ___compcert_i64_utod : ident := 22%positive.
Definition ___compcert_i64_utof : ident := 24%positive.
Definition ___compcert_va_composite : ident := 18%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition ___func__ : ident := 64%positive.
Definition ___func____1 : ident := 83%positive.
Definition ___func____2 : ident := 88%positive.
Definition ___stringlit_1 : ident := 68%positive.
Definition ___stringlit_2 : ident := 69%positive.
Definition ___stringlit_3 : ident := 70%positive.
Definition ___stringlit_4 : ident := 85%positive.
Definition ___stringlit_5 : ident := 86%positive.
Definition _a : ident := 57%positive.
Definition _arr : ident := 92%positive.
Definition _array : ident := 65%positive.
Definition _b : ident := 78%positive.
Definition _calloc : ident := 54%positive.
Definition _currLength : ident := 66%positive.
Definition _desiredLength : ident := 67%positive.
Definition _hi : ident := 60%positive.
Definition _i : ident := 73%positive.
Definition _keySlice : ident := 89%positive.
Definition _len : ident := 84%positive.
Definition _lenA : ident := 80%positive.
Definition _lenB : ident := 81%positive.
Definition _lo : ident := 59%positive.
Definition _main : ident := 96%positive.
Definition _memcmp : ident := 56%positive.
Definition _mid : ident := 61%positive.
Definition _r : ident := 93%positive.
Definition _random : ident := 91%positive.
Definition _realloc : ident := 55%positive.
Definition _res : ident := 74%positive.
Definition _str : ident := 72%positive.
Definition _temp : ident := 94%positive.
Definition _tgt : ident := 58%positive.
Definition _ul : ident := 76%positive.
Definition _val : ident := 62%positive.
Definition _t'1 : ident := 97%positive.
Definition _t'2 : ident := 98%positive.
Definition _t'3 : ident := 99%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 35);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_UTIL_BinarySearch := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tint)) :: (_tgt, tint) :: (_lo, tint) ::
                (_hi, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_mid, tint) :: (_val, tint) :: nil);
  fn_body :=
(Ssequence
  (Swhile
    (Ebinop Olt (Etempvar _lo tint) (Etempvar _hi tint) tint)
    (Ssequence
      (Sset _mid
        (Ebinop Oshr
          (Ebinop Oadd (Etempvar _lo tint) (Etempvar _hi tint) tint)
          (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sset _val
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _mid tint)
              (tptr tint)) tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _val tint) (Etempvar _tgt tint)
                       tint)
          (Sreturn (Some (Etempvar _mid tint)))
          (Sifthenelse (Ebinop Olt (Etempvar _val tint) (Etempvar _tgt tint)
                         tint)
            (Sset _lo
              (Ebinop Oadd (Etempvar _mid tint)
                (Econst_int (Int.repr 1) tint) tint))
            (Sset _hi (Etempvar _mid tint)))))))
  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_UTIL_ResizeArray := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_array, (tptr tvoid)) :: (_currLength, tuint) ::
                (_desiredLength, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _array (tptr tvoid))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 11)) ::
       (Evar ___stringlit_1 (tarray tschar 7)) ::
       (Econst_int (Int.repr 40) tint) ::
       (Evar ___func__ (tarray tschar 17)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _currLength tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_3 (tarray tschar 16)) ::
         (Evar ___stringlit_1 (tarray tschar 7)) ::
         (Econst_int (Int.repr 41) tint) ::
         (Evar ___func__ (tarray tschar 17)) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _realloc (Tfunction (Tcons (tptr tvoid) (Tcons tuint Tnil))
                           (tptr tvoid) cc_default))
          ((Etempvar _array (tptr tvoid)) ::
           (Ebinop Omul (Etempvar _desiredLength tuint)
             (Esizeof (tptr tvoid) tuint) tuint) :: nil))
        (Sset _array
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (tptr tvoid)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _array (tptr tvoid))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)
        (Sreturn (Some (Etempvar _array (tptr tvoid))))))))
|}.

Definition f_UTIL_StrToUl := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_res, tuint) :: (_t'1, tint) ::
               (_t'3, tschar) :: (_t'2, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _res (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'3 (Ederef (Etempvar _str (tptr tschar)) tschar))
              (Sifthenelse (Ebinop One (Etempvar _t'3 tschar)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt (Etempvar _i tint)
                      (Ecast (Esizeof tuint tuint) tint) tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
          (Ssequence
            (Sset _res
              (Ebinop Oshl (Etempvar _res tuint)
                (Econst_int (Int.repr 8) tint) tuint))
            (Ssequence
              (Ssequence
                (Sset _t'2 (Ederef (Etempvar _str (tptr tschar)) tschar))
                (Sset _res
                  (Ebinop Oor (Etempvar _res tuint)
                    (Ecast
                      (Ebinop Oand (Etempvar _t'2 tschar)
                        (Econst_int (Int.repr 255) tint) tint) tuint) tuint)))
              (Ssequence
                (Sset _str
                  (Ebinop Oadd (Etempvar _str (tptr tschar))
                    (Econst_int (Int.repr 1) tint) (tptr tschar)))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
        Sskip)
      (Ssequence
        (Swhile
          (Ebinop Olt (Etempvar _i tint) (Ecast (Esizeof tuint tuint) tint)
            tint)
          (Ssequence
            (Sset _res
              (Ebinop Oshl (Etempvar _res tuint)
                (Econst_int (Int.repr 8) tint) tuint))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _res tuint)))))))
|}.

Definition f_UTIL_UlToStr := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_ul, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr tschar)) :: (_i, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _calloc (Tfunction (Tcons tuint (Tcons tuint Tnil)) (tptr tvoid)
                      cc_default))
      ((Econst_int (Int.repr 9) tint) :: (Esizeof tschar tuint) :: nil))
    (Sset _res (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 7) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _res (tptr tschar)) (Etempvar _i tint)
                  (tptr tschar)) tschar) (Etempvar _ul tuint))
            (Sset _ul
              (Ebinop Oshr (Etempvar _ul tuint)
                (Econst_int (Int.repr 8) tint) tuint))))
        (Sset _i
          (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _res (tptr tschar))))))
|}.

Definition f_UTIL_Min := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_a, tuint) :: (_b, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ole (Etempvar _a tuint) (Etempvar _b tuint) tint)
  (Sreturn (Some (Etempvar _a tuint)))
  (Sreturn (Some (Etempvar _b tuint))))
|}.

Definition f_UTIL_StrEqual := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_lenA, tuint) ::
                (_b, (tptr tschar)) :: (_lenB, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _lenA tuint) (Etempvar _lenB tuint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _memcmp (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                        cc_default))
        ((Etempvar _a (tptr tschar)) :: (Etempvar _b (tptr tschar)) ::
         (Etempvar _lenA tuint) :: nil))
      (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_UTIL_GetNextKeySlice := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_i, tint) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _len tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_4 (tarray tschar 9)) ::
           (Evar ___stringlit_1 (tarray tschar 7)) ::
           (Econst_int (Int.repr 104) tint) ::
           (Evar ___func____1 (tarray tschar 21)) :: nil)))
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _len tint)
                       (Ecast (Esizeof tuint tuint) tint) tint)
          Sskip
          (Scall None
            (Evar ___assert_fail (Tfunction
                                   (Tcons (tptr tschar)
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tschar) Tnil)))) tvoid
                                   cc_default))
            ((Evar ___stringlit_5 (tarray tschar 35)) ::
             (Evar ___stringlit_1 (tarray tschar 7)) ::
             (Econst_int (Int.repr 105) tint) ::
             (Evar ___func____1 (tarray tschar 21)) :: nil)))
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tint) (Etempvar _len tint) tint)
            (Ssequence
              (Sset _res
                (Ebinop Oshl (Etempvar _res tuint)
                  (Econst_int (Int.repr 8) tint) tuint))
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Ederef (Etempvar _str (tptr tschar)) tschar))
                  (Sset _res
                    (Ebinop Oor (Etempvar _res tuint)
                      (Ebinop Oand (Ecast (Etempvar _t'1 tschar) tuint)
                        (Econst_int (Int.repr 255) tint) tuint) tuint)))
                (Ssequence
                  (Sset _str
                    (Ebinop Oadd (Etempvar _str (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar)))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))))
          (Ssequence
            (Swhile
              (Ebinop Olt (Etempvar _i tint)
                (Ecast (Esizeof tuint tuint) tint) tint)
              (Ssequence
                (Sset _res
                  (Ebinop Oshl (Etempvar _res tuint)
                    (Econst_int (Int.repr 8) tint) tuint))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Etempvar _res tuint)))))))))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_UTIL_KeySliceToStr := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_keySlice, tuint) :: (_len, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr tschar)) :: (_i, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _calloc (Tfunction (Tcons tuint (Tcons tuint Tnil)) (tptr tvoid)
                      cc_default))
      ((Etempvar _len tint) :: (Esizeof tschar tuint) :: nil))
    (Sset _res (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _len tint)
                   (Econst_int (Int.repr 0) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_4 (tarray tschar 9)) ::
         (Evar ___stringlit_1 (tarray tschar 7)) ::
         (Econst_int (Int.repr 126) tint) ::
         (Evar ___func____2 (tarray tschar 19)) :: nil)))
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _len tint)
                     (Ecast (Esizeof tuint tuint) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_5 (tarray tschar 35)) ::
           (Evar ___stringlit_1 (tarray tschar 7)) ::
           (Econst_int (Int.repr 127) tint) ::
           (Evar ___func____2 (tarray tschar 19)) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 7) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                             (Econst_int (Int.repr 0) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _len tint) tint)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _res (tptr tschar))
                        (Etempvar _i tint) (tptr tschar)) tschar)
                    (Etempvar _keySlice tuint))
                  Sskip)
                (Sset _keySlice
                  (Ebinop Oshr (Etempvar _keySlice tuint)
                    (Econst_int (Int.repr 8) tint) tuint))))
            (Sset _i
              (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _res (tptr tschar))))))))
|}.

Definition f_UTIL_Shuffle := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_arr, (tptr tint)) :: (_len, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_r, tint) :: (_temp, tint) :: (_t'1, tint) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _len tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _random (Tfunction Tnil tint
                            {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
            nil)
          (Sset _r (Etempvar _t'1 tint)))
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _r
              (Ebinop Omul (Etempvar _r tint)
                (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))
            Sskip)
          (Ssequence
            (Sset _r
              (Ebinop Omod (Etempvar _r tint)
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint) tint))
            (Ssequence
              (Sset _temp
                (Ederef
                  (Ebinop Oadd (Etempvar _arr (tptr tint)) (Etempvar _i tint)
                    (tptr tint)) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _arr (tptr tint))
                        (Etempvar _r tint) (tptr tint)) tint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _arr (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint)
                    (Etempvar _t'2 tint)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _arr (tptr tint))
                      (Etempvar _r tint) (tptr tint)) tint)
                  (Etempvar _temp tint))))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
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
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tuint (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (_realloc,
   Gfun(External (EF_external "realloc"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
     cc_default)) ::
 (_UTIL_BinarySearch, Gfun(Internal f_UTIL_BinarySearch)) ::
 (___func__, Gvar v___func__) ::
 (_UTIL_ResizeArray, Gfun(Internal f_UTIL_ResizeArray)) ::
 (_UTIL_StrToUl, Gfun(Internal f_UTIL_StrToUl)) ::
 (_UTIL_UlToStr, Gfun(Internal f_UTIL_UlToStr)) ::
 (_UTIL_Min, Gfun(Internal f_UTIL_Min)) ::
 (_UTIL_StrEqual, Gfun(Internal f_UTIL_StrEqual)) ::
 (___func____1, Gvar v___func____1) ::
 (_UTIL_GetNextKeySlice, Gfun(Internal f_UTIL_GetNextKeySlice)) ::
 (___func____2, Gvar v___func____2) ::
 (_UTIL_KeySliceToStr, Gfun(Internal f_UTIL_KeySliceToStr)) ::
 (_random,
   Gfun(External (EF_external "random"
                   (mksignature nil (Some AST.Tint)
                     {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|})) ::
 (_UTIL_Shuffle, Gfun(Internal f_UTIL_Shuffle)) :: nil).

Definition public_idents : list ident :=
(_UTIL_Shuffle :: _random :: _UTIL_KeySliceToStr :: _UTIL_GetNextKeySlice ::
 _UTIL_StrEqual :: _UTIL_Min :: _UTIL_UlToStr :: _UTIL_StrToUl ::
 _UTIL_ResizeArray :: _UTIL_BinarySearch :: _memcmp :: _realloc :: _calloc ::
 ___assert_fail :: ___builtin_debug :: ___builtin_nop ::
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


