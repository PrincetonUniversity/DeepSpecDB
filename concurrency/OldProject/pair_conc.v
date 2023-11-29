From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "pair_conc.c".
  Definition normalized := true.
End Info.

Definition _Pair : ident := $"Pair".
Definition _PairImpl : ident := $"PairImpl".
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
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
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
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
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
Definition _acquire : ident := $"acquire".
Definition _argc : ident := $"argc".
Definition _args : ident := $"args".
Definition _argv : ident := $"argv".
Definition _b : ident := $"b".
Definition _da : ident := $"da".
Definition _data : ident := $"data".
Definition _db : ident := $"db".
Definition _exit : ident := $"exit".
Definition _free : ident := $"free".
Definition _freelock : ident := $"freelock".
Definition _freelock2 : ident := $"freelock2".
Definition _fst : ident := $"fst".
Definition _l : ident := $"l".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _p : ident := $"p".
Definition _pa : ident := $"pa".
Definition _pair : ident := $"pair".
Definition _pair_free : ident := $"pair_free".
Definition _pair_new : ident := $"pair_new".
Definition _pb : ident := $"pb".
Definition _read_pair : ident := $"read_pair".
Definition _release : ident := $"release".
Definition _release2 : ident := $"release2".
Definition _result : ident := $"result".
Definition _snd : ident := $"snd".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t_lock : ident := $"t_lock".
Definition _thread_func : ident := $"thread_func".
Definition _thread_lock : ident := $"thread_lock".
Definition _va : ident := $"va".
Definition _va2 : ident := $"va2".
Definition _val : ident := $"val".
Definition _version : ident := $"version".
Definition _write : ident := $"write".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.

Definition v_pa := {|
  gvar_info := (tptr (Tstruct _PairImpl noattr));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_pb := {|
  gvar_info := (tptr (Tstruct _PairImpl noattr));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_thread_lock := {|
  gvar_info := (tarray (tptr tvoid) 2);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tulong) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _PairImpl noattr))) :: (_val, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _PairImpl noattr)))
        (Tstruct _PairImpl noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _PairImpl noattr)))
            (Tstruct _PairImpl noattr)) _data tint) (Etempvar _val tint))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _PairImpl noattr)))
                (Tstruct _PairImpl noattr)) _version tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _PairImpl noattr)))
                (Tstruct _PairImpl noattr)) _version tuint)
            (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Scall None
          (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                           cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))))))
|}.

Definition f_pair_new := {|
  fn_return := (tptr (Tstruct _PairImpl noattr));
  fn_callconv := cc_default;
  fn_params := ((_val, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pair, (tptr (Tstruct _PairImpl noattr))) ::
               (_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _PairImpl noattr) tulong) :: nil))
    (Sset _pair
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _PairImpl noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (tarray (tptr tvoid) 2) tulong) :: nil))
      (Sset _l
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (tarray (tptr tvoid) 2)))))
    (Ssequence
      (Scall None
        (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
        ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _pair (tptr (Tstruct _PairImpl noattr)))
              (Tstruct _PairImpl noattr)) _lock
            (tptr (tarray (tptr tvoid) 2)))
          (Etempvar _l (tptr (tarray (tptr tvoid) 2))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _pair (tptr (Tstruct _PairImpl noattr)))
                (Tstruct _PairImpl noattr)) _data tint) (Etempvar _val tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _pair (tptr (Tstruct _PairImpl noattr)))
                  (Tstruct _PairImpl noattr)) _version tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Scall None
                (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default))
                ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
              (Sreturn (Some (Etempvar _pair (tptr (Tstruct _PairImpl noattr))))))))))))
|}.

Definition f_pair_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _PairImpl noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _PairImpl noattr)))
        (Tstruct _PairImpl noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Scall None
        (Evar _freelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _l (tptr tvoid)) :: nil))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _p (tptr (Tstruct _PairImpl noattr))) :: nil))))))
|}.

Definition f_read_pair := {|
  fn_return := (tptr (Tstruct _Pair noattr));
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _PairImpl noattr))) ::
                (_b, (tptr (Tstruct _PairImpl noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_da, tint) :: (_db, tint) :: (_va, tuint) :: (_va2, tuint) ::
               (_result, (tptr (Tstruct _Pair noattr))) ::
               (_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _Pair noattr) tulong) :: nil))
    (Sset _result
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Pair noattr)))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _l
          (Efield
            (Ederef (Etempvar _a (tptr (Tstruct _PairImpl noattr)))
              (Tstruct _PairImpl noattr)) _lock
            (tptr (tarray (tptr tvoid) 2))))
        (Ssequence
          (Scall None
            (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                             cc_default))
            ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
          (Ssequence
            (Sset _da
              (Efield
                (Ederef (Etempvar _a (tptr (Tstruct _PairImpl noattr)))
                  (Tstruct _PairImpl noattr)) _data tint))
            (Ssequence
              (Sset _va
                (Efield
                  (Ederef (Etempvar _a (tptr (Tstruct _PairImpl noattr)))
                    (Tstruct _PairImpl noattr)) _version tuint))
              (Ssequence
                (Scall None
                  (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                (Ssequence
                  (Sset _l
                    (Efield
                      (Ederef (Etempvar _b (tptr (Tstruct _PairImpl noattr)))
                        (Tstruct _PairImpl noattr)) _lock
                      (tptr (tarray (tptr tvoid) 2))))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                    (Ssequence
                      (Sset _db
                        (Efield
                          (Ederef
                            (Etempvar _b (tptr (Tstruct _PairImpl noattr)))
                            (Tstruct _PairImpl noattr)) _data tint))
                      (Ssequence
                        (Scall None
                          (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
                          ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) ::
                           nil))
                        (Ssequence
                          (Sset _l
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct _PairImpl noattr)))
                                (Tstruct _PairImpl noattr)) _lock
                              (tptr (tarray (tptr tvoid) 2))))
                          (Ssequence
                            (Scall None
                              (Evar _acquire (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                              ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) ::
                               nil))
                            (Ssequence
                              (Sset _va2
                                (Efield
                                  (Ederef
                                    (Etempvar _a (tptr (Tstruct _PairImpl noattr)))
                                    (Tstruct _PairImpl noattr)) _version
                                  tuint))
                              (Ssequence
                                (Scall None
                                  (Evar _release (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   tvoid cc_default))
                                  ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) ::
                                   nil))
                                (Sifthenelse (Ebinop Oeq (Etempvar _va tuint)
                                               (Etempvar _va2 tuint) tint)
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _result (tptr (Tstruct _Pair noattr)))
                                          (Tstruct _Pair noattr)) _fst tint)
                                      (Etempvar _da tint))
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _result (tptr (Tstruct _Pair noattr)))
                                            (Tstruct _Pair noattr)) _snd
                                          tint) (Etempvar _db tint))
                                      (Sreturn (Some (Etempvar _result (tptr (Tstruct _Pair noattr)))))))
                                  Sskip)))))))))))))))
    Sskip))
|}.

Definition f_thread_func := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr (Tstruct _PairImpl noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
      (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Evar _pa (tptr (Tstruct _PairImpl noattr))))
      (Scall None
        (Evar _write (Tfunction
                       (Tcons (tptr (Tstruct _PairImpl noattr))
                         (Tcons tint Tnil)) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _PairImpl noattr))) ::
         (Econst_int (Int.repr 2) tint) :: nil)))
    (Ssequence
      (Scall None
        (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
        ((Ecast (Etempvar _l (tptr (tarray (tptr tvoid) 2))) (tptr tvoid)) ::
         nil))
      (Sreturn (Some (Ecast
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       (tptr tvoid)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_argc, tint) :: (_argv, (tptr (tptr tschar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t_lock, (tptr (tarray (tptr tvoid) 2))) ::
               (_result, (tptr (Tstruct _Pair noattr))) ::
               (_t'3, (tptr (Tstruct _Pair noattr))) ::
               (_t'2, (tptr (Tstruct _PairImpl noattr))) ::
               (_t'1, (tptr (Tstruct _PairImpl noattr))) ::
               (_t'7, (tptr (Tstruct _PairImpl noattr))) ::
               (_t'6, (tptr (Tstruct _PairImpl noattr))) ::
               (_t'5, (tptr (Tstruct _PairImpl noattr))) ::
               (_t'4, (tptr (Tstruct _PairImpl noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _pair_new (Tfunction (Tcons tint Tnil)
                          (tptr (Tstruct _PairImpl noattr)) cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      (Sassign (Evar _pa (tptr (Tstruct _PairImpl noattr)))
        (Etempvar _t'1 (tptr (Tstruct _PairImpl noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _pair_new (Tfunction (Tcons tint Tnil)
                            (tptr (Tstruct _PairImpl noattr)) cc_default))
          ((Econst_int (Int.repr 2) tint) :: nil))
        (Sassign (Evar _pb (tptr (Tstruct _PairImpl noattr)))
          (Etempvar _t'2 (tptr (Tstruct _PairImpl noattr)))))
      (Ssequence
        (Sset _t_lock
          (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
            (tptr (tarray (tptr tvoid) 2))))
        (Ssequence
          (Scall None
            (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
            ((Ecast (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
               (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _spawn (Tfunction
                             (Tcons
                               (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                       (tptr tvoid) cc_default))
                               (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
              ((Ecast
                 (Eaddrof
                   (Evar _thread_func (Tfunction (Tcons (tptr tvoid) Tnil)
                                        (tptr tvoid) cc_default))
                   (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                           cc_default))) (tptr tvoid)) ::
               (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                 (tptr tvoid)) :: nil))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'6 (Evar _pa (tptr (Tstruct _PairImpl noattr))))
                  (Ssequence
                    (Sset _t'7 (Evar _pb (tptr (Tstruct _PairImpl noattr))))
                    (Scall (Some _t'3)
                      (Evar _read_pair (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _PairImpl noattr))
                                           (Tcons
                                             (tptr (Tstruct _PairImpl noattr))
                                             Tnil))
                                         (tptr (Tstruct _Pair noattr))
                                         cc_default))
                      ((Etempvar _t'6 (tptr (Tstruct _PairImpl noattr))) ::
                       (Etempvar _t'7 (tptr (Tstruct _PairImpl noattr))) ::
                       nil))))
                (Sset _result (Etempvar _t'3 (tptr (Tstruct _Pair noattr)))))
              (Ssequence
                (Scall None
                  (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Ecast (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                     (tptr tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                    ((Ecast (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                       (tptr tvoid)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Evar _pa (tptr (Tstruct _PairImpl noattr))))
                      (Scall None
                        (Evar _pair_free (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _PairImpl noattr))
                                             Tnil) tvoid cc_default))
                        ((Etempvar _t'5 (tptr (Tstruct _PairImpl noattr))) ::
                         nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'4
                          (Evar _pb (tptr (Tstruct _PairImpl noattr))))
                        (Scall None
                          (Evar _pair_free (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _PairImpl noattr))
                                               Tnil) tvoid cc_default))
                          ((Etempvar _t'4 (tptr (Tstruct _PairImpl noattr))) ::
                           nil)))
                      (Ssequence
                        (Scall None
                          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                          ((Etempvar _result (tptr (Tstruct _Pair noattr))) ::
                           nil))
                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _Pair Struct
   (Member_plain _fst tint :: Member_plain _snd tint :: nil)
   noattr ::
 Composite _PairImpl Struct
   (Member_plain _lock (tptr (tarray (tptr tvoid) 2)) ::
    Member_plain _data tint :: Member_plain _version tuint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
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
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
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
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
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
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock2,
   Gfun(External (EF_external "freelock2"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release2,
   Gfun(External (EF_external "release2"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons
       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) :: (_pa, Gvar v_pa) ::
 (_pb, Gvar v_pb) :: (_thread_lock, Gvar v_thread_lock) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_write, Gfun(Internal f_write)) ::
 (_pair_new, Gfun(Internal f_pair_new)) ::
 (_pair_free, Gfun(Internal f_pair_free)) ::
 (_read_pair, Gfun(Internal f_read_pair)) ::
 (_thread_func, Gfun(Internal f_thread_func)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func :: _read_pair :: _pair_free :: _pair_new :: _write ::
 _surely_malloc :: _thread_lock :: _pb :: _pa :: _spawn :: _release2 ::
 _freelock2 :: _release :: _acquire :: _freelock :: _makelock :: _exit ::
 _free :: _malloc :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


