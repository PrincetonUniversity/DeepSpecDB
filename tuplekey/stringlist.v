From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.3"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "stringlist.c"%string.
  Definition normalized := true.
End Info.

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
Definition _buckets : ident := 5%positive.
Definition _copy_string : ident := 81%positive.
Definition _exit : ident := 59%positive.
Definition _i : ident := 60%positive.
Definition _icell : ident := 3%positive.
Definition _inthash : ident := 6%positive.
Definition _inthash_insert : ident := 70%positive.
Definition _inthash_insert_list : ident := 68%positive.
Definition _inthash_lookup : ident := 65%positive.
Definition _inthash_new : ident := 62%positive.
Definition _key : ident := 1%positive.
Definition _main : ident := 71%positive.
Definition _malloc : ident := 58%positive.
Definition _n : ident := 80%positive.
Definition _new_icell : ident := 63%positive.
Definition _new_scell : ident := 82%positive.
Definition _next : ident := 4%positive.
Definition _old : ident := 69%positive.
Definition _p : ident := 61%positive.
Definition _q : ident := 64%positive.
Definition _r : ident := 67%positive.
Definition _r0 : ident := 66%positive.
Definition _root : ident := 73%positive.
Definition _s : ident := 79%positive.
Definition _scell : ident := 72%positive.
Definition _strcmp : ident := 77%positive.
Definition _strcpy : ident := 76%positive.
Definition _stringlist : ident := 74%positive.
Definition _stringlist_insert : ident := 83%positive.
Definition _stringlist_lookup : ident := 84%positive.
Definition _stringlist_new : ident := 78%positive.
Definition _strlen : ident := 75%positive.
Definition _value : ident := 2%positive.
Definition _t'1 : ident := 85%positive.
Definition _t'2 : ident := 86%positive.
Definition _t'3 : ident := 87%positive.

Definition f_stringlist_new := {|
  fn_return := (tptr (Tstruct _stringlist noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _stringlist noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _stringlist noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _stringlist noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _stringlist noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
            (Tstruct _stringlist noattr)) _root
          (tptr (Tstruct _scell noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _p (tptr (Tstruct _stringlist noattr))))))))
|}.

Definition f_copy_string := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_n, tint) :: (_p, (tptr tschar)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _n
      (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
        tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Etempvar _n tint) :: nil))
      (Sset _p (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tschar)) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _strcpy (Tfunction
                          (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                          (tptr tschar) cc_default))
          ((Etempvar _p (tptr tschar)) :: (Etempvar _s (tptr tschar)) :: nil))
        (Sreturn (Some (Etempvar _p (tptr tschar))))))))
|}.

Definition f_new_scell := {|
  fn_return := (tptr (Tstruct _scell noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tschar)) :: (_value, (tptr tvoid)) ::
                (_next, (tptr (Tstruct _scell noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _scell noattr))) ::
               (_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _scell noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _scell noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _scell noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copy_string (Tfunction (Tcons (tptr tschar) Tnil)
                               (tptr tschar) cc_default))
          ((Etempvar _key (tptr tschar)) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
              (Tstruct _scell noattr)) _key (tptr tschar))
          (Etempvar _t'2 (tptr tschar))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
              (Tstruct _scell noattr)) _value (tptr tvoid))
          (Etempvar _value (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
                (Tstruct _scell noattr)) _next
              (tptr (Tstruct _scell noattr)))
            (Etempvar _next (tptr (Tstruct _scell noattr))))
          (Sreturn (Some (Etempvar _p (tptr (Tstruct _scell noattr))))))))))
|}.

Definition f_stringlist_insert := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) ::
                (_key, (tptr tschar)) :: (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) ::
               (_r, (tptr (tptr (Tstruct _scell noattr)))) ::
               (_old, (tptr tvoid)) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _scell noattr))) ::
               (_t'3, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Eaddrof
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
          (Tstruct _stringlist noattr)) _root (tptr (Tstruct _scell noattr)))
      (tptr (tptr (Tstruct _scell noattr)))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _q
          (Ederef (Etempvar _r (tptr (tptr (Tstruct _scell noattr))))
            (tptr (Tstruct _scell noattr))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _q (tptr (Tstruct _scell noattr))) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _new_scell (Tfunction
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tvoid)
                                         (Tcons
                                           (tptr (Tstruct _scell noattr))
                                           Tnil)))
                                     (tptr (Tstruct _scell noattr))
                                     cc_default))
                  ((Etempvar _key (tptr tschar)) ::
                   (Etempvar _value (tptr tvoid)) ::
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                   nil))
                (Sassign
                  (Ederef (Etempvar _r (tptr (tptr (Tstruct _scell noattr))))
                    (tptr (Tstruct _scell noattr)))
                  (Etempvar _t'1 (tptr (Tstruct _scell noattr)))))
              (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)))))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                    (Tstruct _scell noattr)) _key (tptr tschar)))
              (Scall (Some _t'2)
                (Evar _strcmp (Tfunction
                                (Tcons (tptr tschar)
                                  (Tcons (tptr tschar) Tnil)) tint
                                cc_default))
                ((Etempvar _t'3 (tptr tschar)) ::
                 (Etempvar _key (tptr tschar)) :: nil)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _old
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                      (Tstruct _scell noattr)) _value (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                        (Tstruct _scell noattr)) _value (tptr tvoid))
                    (Etempvar _value (tptr tvoid)))
                  (Sreturn (Some (Etempvar _old (tptr tvoid))))))
              Sskip)))))
    (Sset _r
      (Eaddrof
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
            (Tstruct _scell noattr)) _next (tptr (Tstruct _scell noattr)))
        (tptr (tptr (Tstruct _scell noattr)))))))
|}.

Definition f_stringlist_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) ::
                (_key, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) :: (_t'1, tint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _q
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
          (Tstruct _stringlist noattr)) _root (tptr (Tstruct _scell noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _q (tptr (Tstruct _scell noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                  (Tstruct _scell noattr)) _key (tptr tschar)))
            (Scall (Some _t'1)
              (Evar _strcmp (Tfunction
                              (Tcons (tptr tschar)
                                (Tcons (tptr tschar) Tnil)) tint cc_default))
              ((Etempvar _t'3 (tptr tschar)) ::
               (Etempvar _key (tptr tschar)) :: nil)))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                    (Tstruct _scell noattr)) _value (tptr tvoid)))
              (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))
            Sskip)))
      (Sset _q
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
            (Tstruct _scell noattr)) _next (tptr (Tstruct _scell noattr))))))
  (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|}.

Definition composites : list composite_definition :=
(Composite _scell Struct
   ((_key, (tptr tschar)) :: (_value, (tptr tvoid)) ::
    (_next, (tptr (Tstruct _scell noattr))) :: nil)
   noattr ::
 Composite _stringlist Struct
   ((_root, (tptr (Tstruct _scell noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) Tnil) tuint cc_default)) ::
 (_strcpy,
   Gfun(External (EF_external "strcpy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) (tptr tschar)
     cc_default)) ::
 (_strcmp,
   Gfun(External (EF_external "strcmp"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) tint cc_default)) ::
 (_stringlist_new, Gfun(Internal f_stringlist_new)) ::
 (_copy_string, Gfun(Internal f_copy_string)) ::
 (_new_scell, Gfun(Internal f_new_scell)) ::
 (_stringlist_insert, Gfun(Internal f_stringlist_insert)) ::
 (_stringlist_lookup, Gfun(Internal f_stringlist_lookup)) :: nil).

Definition public_idents : list ident :=
(_stringlist_lookup :: _stringlist_insert :: _new_scell :: _copy_string ::
 _stringlist_new :: _strcmp :: _strcpy :: _strlen :: _exit :: _malloc ::
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


