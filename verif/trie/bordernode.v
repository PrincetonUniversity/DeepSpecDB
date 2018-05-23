From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _BN_FreeBorderNode : ident := 65%positive.
Definition _BN_GetPrefixValue : ident := 74%positive.
Definition _BN_GetSuffixValue : ident := 79%positive.
Definition _BN_HasSuffix : ident := 78%positive.
Definition _BN_NewBorderNode : ident := 64%positive.
Definition _BN_SetPrefixValue : ident := 72%positive.
Definition _BN_SetSuffixValue : ident := 77%positive.
Definition _BorderNode : ident := 5%positive.
Definition _UTIL_StrEqual : ident := 60%positive.
Definition ___assert_fail : ident := 59%positive.
Definition ___builtin_ais_annot : ident := 6%positive.
Definition ___builtin_annot : ident := 13%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 39%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 57%positive.
Definition ___builtin_fabs : ident := 10%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fsqrt : ident := 11%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_nop : ident := 56%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_write16_reversed : ident := 54%positive.
Definition ___builtin_write32_reversed : ident := 55%positive.
Definition ___compcert_i64_dtos : ident := 24%positive.
Definition ___compcert_i64_dtou : ident := 25%positive.
Definition ___compcert_i64_sar : ident := 36%positive.
Definition ___compcert_i64_sdiv : ident := 30%positive.
Definition ___compcert_i64_shl : ident := 34%positive.
Definition ___compcert_i64_shr : ident := 35%positive.
Definition ___compcert_i64_smod : ident := 32%positive.
Definition ___compcert_i64_smulh : ident := 37%positive.
Definition ___compcert_i64_stod : ident := 26%positive.
Definition ___compcert_i64_stof : ident := 28%positive.
Definition ___compcert_i64_udiv : ident := 31%positive.
Definition ___compcert_i64_umod : ident := 33%positive.
Definition ___compcert_i64_umulh : ident := 38%positive.
Definition ___compcert_i64_utod : ident := 27%positive.
Definition ___compcert_i64_utof : ident := 29%positive.
Definition ___compcert_va_composite : ident := 23%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___compcert_va_int32 : ident := 20%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition ___func__ : ident := 66%positive.
Definition ___func____1 : ident := 73%positive.
Definition ___stringlit_1 : ident := 69%positive.
Definition ___stringlit_2 : ident := 70%positive.
Definition ___stringlit_3 : ident := 71%positive.
Definition _bn : ident := 67%positive.
Definition _bordernode : ident := 62%positive.
Definition _free : ident := 58%positive.
Definition _i : ident := 63%positive.
Definition _keySuffix : ident := 3%positive.
Definition _keySuffixLength : ident := 4%positive.
Definition _len : ident := 76%positive.
Definition _main : ident := 80%positive.
Definition _prefixLinks : ident := 1%positive.
Definition _suf : ident := 75%positive.
Definition _suffixLink : ident := 2%positive.
Definition _surely_malloc : ident := 61%positive.
Definition _val : ident := 68%positive.
Definition _t'1 : ident := 81%positive.
Definition _t'2 : ident := 82%positive.
Definition _t'3 : ident := 83%positive.
Definition _t'4 : ident := 84%positive.
Definition _t'5 : ident := 85%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
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
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _bordernode (tptr (Tstruct _BorderNode noattr))) :: nil))
    (Sreturn None)))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_BN_SetPrefixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oge (Etempvar _i tint) (Econst_int (Int.repr 0) tint)
                 tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 7)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 80) tint) ::
       (Evar ___func__ (tarray tschar 18)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Econst_int (Int.repr 4) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_3 (tarray tschar 16)) ::
         (Evar ___stringlit_1 (tarray tschar 13)) ::
         (Econst_int (Int.repr 81) tint) ::
         (Evar ___func__ (tarray tschar 18)) :: nil)))
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _prefixLinks
            (tarray (tptr tvoid) 4)) (Etempvar _i tint) (tptr (tptr tvoid)))
        (tptr tvoid)) (Etempvar _val (tptr tvoid)))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
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
  (Sifthenelse (Ebinop Oge (Etempvar _i tint) (Econst_int (Int.repr 0) tint)
                 tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 7)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 86) tint) ::
       (Evar ___func____1 (tarray tschar 18)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Econst_int (Int.repr 4) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_3 (tarray tschar 16)) ::
         (Evar ___stringlit_1 (tarray tschar 13)) ::
         (Econst_int (Int.repr 87) tint) ::
         (Evar ___func____1 (tarray tschar 18)) :: nil)))
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _prefixLinks
              (tarray (tptr tvoid) 4)) (Etempvar _i tint)
            (tptr (tptr tvoid))) (tptr tvoid)))
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))
|}.

Definition f_BN_SetSuffixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suf, (tptr tschar)) :: (_len, tuint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
        (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
    (Etempvar _suf (tptr tschar)))
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
      (Etempvar _val (tptr tvoid)))))
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

Definition composites : list composite_definition :=
(Composite _BorderNode Struct
   ((_prefixLinks, (tarray (tptr tvoid) 4)) :: (_suffixLink, (tptr tvoid)) ::
    (_keySuffix, (tptr tschar)) :: (_keySuffixLength, tuint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_UTIL_StrEqual,
   Gfun(External (EF_external "UTIL_StrEqual"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar)
       (Tcons tuint (Tcons (tptr tschar) (Tcons tuint Tnil)))) tint
     cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_BN_NewBorderNode, Gfun(Internal f_BN_NewBorderNode)) ::
 (_BN_FreeBorderNode, Gfun(Internal f_BN_FreeBorderNode)) ::
 (___func__, Gvar v___func__) ::
 (_BN_SetPrefixValue, Gfun(Internal f_BN_SetPrefixValue)) ::
 (___func____1, Gvar v___func____1) ::
 (_BN_GetPrefixValue, Gfun(Internal f_BN_GetPrefixValue)) ::
 (_BN_SetSuffixValue, Gfun(Internal f_BN_SetSuffixValue)) ::
 (_BN_HasSuffix, Gfun(Internal f_BN_HasSuffix)) ::
 (_BN_GetSuffixValue, Gfun(Internal f_BN_GetSuffixValue)) :: nil).

Definition public_idents : list ident :=
(_BN_GetSuffixValue :: _BN_HasSuffix :: _BN_SetSuffixValue ::
 _BN_GetPrefixValue :: _BN_SetPrefixValue :: _BN_FreeBorderNode ::
 _BN_NewBorderNode :: _surely_malloc :: _UTIL_StrEqual :: ___assert_fail ::
 _free :: ___builtin_debug :: ___builtin_nop ::
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


