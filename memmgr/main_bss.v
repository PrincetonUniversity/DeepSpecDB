From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "main_bss.c"%string.
  Definition normalized := true.
End Info.

Definition _Nblocks : ident := 70%positive.
Definition ___builtin_annot : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 8%positive.
Definition ___builtin_bswap : ident := 1%positive.
Definition ___builtin_bswap16 : ident := 3%positive.
Definition ___builtin_bswap32 : ident := 2%positive.
Definition ___builtin_bswap64 : ident := 33%positive.
Definition ___builtin_clz : ident := 34%positive.
Definition ___builtin_clzl : ident := 35%positive.
Definition ___builtin_clzll : ident := 36%positive.
Definition ___builtin_ctz : ident := 37%positive.
Definition ___builtin_ctzl : ident := 38%positive.
Definition ___builtin_ctzll : ident := 39%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 4%positive.
Definition ___builtin_fmadd : ident := 42%positive.
Definition ___builtin_fmax : ident := 40%positive.
Definition ___builtin_fmin : ident := 41%positive.
Definition ___builtin_fmsub : ident := 43%positive.
Definition ___builtin_fnmadd : ident := 44%positive.
Definition ___builtin_fnmsub : ident := 45%positive.
Definition ___builtin_fsqrt : ident := 5%positive.
Definition ___builtin_membar : ident := 9%positive.
Definition ___builtin_memcpy_aligned : ident := 6%positive.
Definition ___builtin_nop : ident := 50%positive.
Definition ___builtin_read16_reversed : ident := 46%positive.
Definition ___builtin_read32_reversed : ident := 47%positive.
Definition ___builtin_va_arg : ident := 11%positive.
Definition ___builtin_va_copy : ident := 12%positive.
Definition ___builtin_va_end : ident := 13%positive.
Definition ___builtin_va_start : ident := 10%positive.
Definition ___builtin_write16_reversed : ident := 48%positive.
Definition ___builtin_write32_reversed : ident := 49%positive.
Definition ___compcert_i64_dtos : ident := 18%positive.
Definition ___compcert_i64_dtou : ident := 19%positive.
Definition ___compcert_i64_sar : ident := 30%positive.
Definition ___compcert_i64_sdiv : ident := 24%positive.
Definition ___compcert_i64_shl : ident := 28%positive.
Definition ___compcert_i64_shr : ident := 29%positive.
Definition ___compcert_i64_smod : ident := 26%positive.
Definition ___compcert_i64_smulh : ident := 31%positive.
Definition ___compcert_i64_stod : ident := 20%positive.
Definition ___compcert_i64_stof : ident := 22%positive.
Definition ___compcert_i64_udiv : ident := 25%positive.
Definition ___compcert_i64_umod : ident := 27%positive.
Definition ___compcert_i64_umulh : ident := 32%positive.
Definition ___compcert_i64_utod : ident := 21%positive.
Definition ___compcert_i64_utof : ident := 23%positive.
Definition ___compcert_va_composite : ident := 17%positive.
Definition ___compcert_va_float64 : ident := 16%positive.
Definition ___compcert_va_int32 : ident := 14%positive.
Definition ___compcert_va_int64 : ident := 15%positive.
Definition ___stringlit_1 : ident := 92%positive.
Definition ___stringlit_2 : ident := 93%positive.
Definition ___stringlit_3 : ident := 94%positive.
Definition _abort : ident := 88%positive.
Definition _addr : ident := 54%positive.
Definition _b : ident := 64%positive.
Definition _bb : ident := 91%positive.
Definition _bin : ident := 68%positive.
Definition _bin2size : ident := 65%positive.
Definition _chunks : ident := 78%positive.
Definition _fildes : ident := 58%positive.
Definition _fill_bin : ident := 80%positive.
Definition _flags : ident := 57%positive.
Definition _free : ident := 86%positive.
Definition _free_large : ident := 85%positive.
Definition _free_small : ident := 84%positive.
Definition _ful : ident := 77%positive.
Definition _heap : ident := 90%positive.
Definition _j : ident := 72%positive.
Definition _len : ident := 55%positive.
Definition _list_from_block : ident := 73%positive.
Definition _main : ident := 63%positive.
Definition _malloc : ident := 87%positive.
Definition _malloc_large : ident := 83%positive.
Definition _malloc_small : ident := 82%positive.
Definition _mmap : ident := 52%positive.
Definition _mmap0 : ident := 61%positive.
Definition _munmap : ident := 53%positive.
Definition _n : ident := 74%positive.
Definition _nbytes : ident := 81%positive.
Definition _off : ident := 59%positive.
Definition _p : ident := 60%positive.
Definition _placeholder : ident := 62%positive.
Definition _pre_fill : ident := 75%positive.
Definition _printf : ident := 89%positive.
Definition _prot : ident := 56%positive.
Definition _q : ident := 71%positive.
Definition _req : ident := 76%positive.
Definition _s : ident := 66%positive.
Definition _size2bin : ident := 67%positive.
Definition _tl : ident := 69%positive.
Definition _try_pre_fill : ident := 79%positive.
Definition _t'1 : ident := 95%positive.
Definition _t'2 : ident := 96%positive.
Definition _t'3 : ident := 97%positive.
Definition _t'4 : ident := 98%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 34);
  gvar_init := (Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_heap := {|
  gvar_info := (tarray tschar 524296);
  gvar_init := (Init_space 524296 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_bb, (tptr tschar)) :: (_p, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tvoid) :: (_t'2, tint) ::
               (_t'1, tvoid) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _bb (Evar _heap (tarray tschar 524296)))
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Ebinop Omod (Ecast (Etempvar _bb (tptr tschar)) tuint)
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                         (Econst_int (Int.repr 2) tint) tint) tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _bb
          (Ecast
            (Ebinop Osub
              (Ebinop Oadd (Etempvar _bb (tptr tschar))
                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                  (Econst_int (Int.repr 2) tint) tint) (tptr tschar))
              (Ebinop Omod (Ecast (Etempvar _bb (tptr tschar)) tuint)
                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                  (Econst_int (Int.repr 2) tint) tint) tuint) (tptr tschar))
            (tptr tvoid)))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Ebinop Omod
                         (Ecast (Etempvar _bb (tptr tschar)) tuint)
                         (Ebinop Omul (Econst_int (Int.repr 4) tint)
                           (Econst_int (Int.repr 2) tint) tint) tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'1
            (Ecast (Ecast (Econst_int (Int.repr 0) tint) tvoid) tvoid))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_3 (tarray tschar 30)) ::
                 (Evar ___stringlit_2 (tarray tschar 11)) ::
                 (Econst_int (Int.repr 16) tint) ::
                 (Evar ___stringlit_1 (tarray tschar 34)) :: nil))
              (Scall (Some _t'3)
                (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
            (Sset _t'1 (Ecast (Etempvar _t'3 tvoid) tvoid))))
        (Ssequence
          (Scall None
            (Evar _pre_fill (Tfunction
                              (Tcons tuint (Tcons (tptr tvoid) Tnil)) tvoid
                              cc_default))
            ((Econst_int (Int.repr 100) tint) ::
             (Etempvar _bb (tptr tschar)) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default))
                ((Econst_int (Int.repr 100) tint) :: nil))
              (Sset _p (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _p (tptr tvoid)) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
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
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil None cc_default)) Tnil
     tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_pre_fill,
   Gfun(External (EF_external "pre_fill"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons tuint (Tcons (tptr tvoid) Tnil))
     tvoid cc_default)) :: (_heap, Gvar v_heap) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _pre_fill :: _free :: _malloc :: _printf :: _abort ::
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
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


