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
  Definition source_file := "kvnode.c".
  Definition normalized := true.
End Info.

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
Definition _acquire : ident := $"acquire".
Definition _argc : ident := $"argc".
Definition _args : ident := $"args".
Definition _argv : ident := $"argv".
Definition _data : ident := $"data".
Definition _dlock : ident := $"dlock".
Definition _dlocks : ident := $"dlocks".
Definition _exit : ident := $"exit".
Definition _first : ident := $"first".
Definition _free : ident := $"free".
Definition _freelock : ident := $"freelock".
Definition _freelock2 : ident := $"freelock2".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _l : ident := $"l".
Definition _ll : ident := $"ll".
Definition _locks : ident := $"locks".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _node : ident := $"node".
Definition _node_free : ident := $"node_free".
Definition _node_new : ident := $"node_new".
Definition _one_node : ident := $"one_node".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _read : ident := $"read".
Definition _release : ident := $"release".
Definition _release2 : ident := $"release2".
Definition _result : ident := $"result".
Definition _second : ident := $"second".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t_lock : ident := $"t_lock".
Definition _thread_func : ident := $"thread_func".
Definition _thread_lock : ident := $"thread_lock".
Definition _v : ident := $"v".
Definition _values : ident := $"values".
Definition _ver : ident := $"ver".
Definition _version : ident := $"version".
Definition _vlock : ident := $"vlock".
Definition _write : ident := $"write".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
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

Definition v_one_node := {|
  gvar_info := (tptr (Tstruct _node noattr));
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

Definition v_first := {|
  gvar_info := (tptr tint);
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_second := {|
  gvar_info := (tptr tint);
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_node_new := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_values, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _node noattr))) ::
               (_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_locks, (tptr (tarray (tptr tvoid) 2))) ::
               (_data, (tptr tint)) :: (_i, tint) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _node noattr) tulong) :: nil))
    (Sset _result
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
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
        (Ssequence
          (Scall (Some _t'3)
            (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                   cc_default))
            ((Ebinop Omul (Econst_int (Int.repr 8) tint)
               (Esizeof (tarray (tptr tvoid) 2) tulong) tulong) :: nil))
          (Sset _locks
            (Ecast (Etempvar _t'3 (tptr tvoid))
              (tptr (tarray (tptr tvoid) 2)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                     (tptr tvoid) cc_default))
              ((Ebinop Omul (Econst_int (Int.repr 8) tint)
                 (Esizeof tint tulong) tulong) :: nil))
            (Sset _data (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Scall None
                      (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                      ((Ebinop Oadd
                         (Etempvar _locks (tptr (tarray (tptr tvoid) 2)))
                         (Etempvar _i tint) (tptr (tarray (tptr tvoid) 2))) ::
                       nil))
                    (Ssequence
                      (Ssequence
                        (Sset _t'5
                          (Ederef
                            (Ebinop Oadd (Etempvar _values (tptr tint))
                              (Etempvar _i tint) (tptr tint)) tint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _data (tptr tint))
                              (Etempvar _i tint) (tptr tint)) tint)
                          (Etempvar _t'5 tint)))
                      (Scall None
                        (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Ebinop Oadd
                           (Etempvar _locks (tptr (tarray (tptr tvoid) 2)))
                           (Etempvar _i tint) (tptr (tarray (tptr tvoid) 2))) ::
                         nil)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _result (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _vlock
                  (tptr (tarray (tptr tvoid) 2)))
                (Etempvar _l (tptr (tarray (tptr tvoid) 2))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _result (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _version tint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _dlocks
                      (tptr (tarray (tptr tvoid) 2)))
                    (Etempvar _locks (tptr (tarray (tptr tvoid) 2))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _data (tptr tint))
                      (Etempvar _data (tptr tint)))
                    (Ssequence
                      (Scall None
                        (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                      (Sreturn (Some (Etempvar _result (tptr (Tstruct _node noattr))))))))))))))))
|}.

Definition f_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_out, (tptr tint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_ver, tint) ::
               (_i, tint) :: (_dlock, (tptr (tarray (tptr tvoid) 2))) ::
               (_v, tint) :: (_t'3, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'2, tint) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _l
        (Efield
          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _vlock (tptr (tarray (tptr tvoid) 2))))
      (Ssequence
        (Scall None
          (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                           cc_default))
          ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
        (Ssequence
          (Sset _ver
            (Efield
              (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _version tint))
          (Ssequence
            (Scall None
              (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default))
              ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Oand (Etempvar _ver tint)
                               (Econst_int (Int.repr 1) tint) tint)
                             (Econst_int (Int.repr 1) tint) tint)
                Scontinue
                Sskip)
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 8) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'3
                            (Efield
                              (Ederef
                                (Etempvar _n (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _dlocks
                              (tptr (tarray (tptr tvoid) 2))))
                          (Sset _dlock
                            (Ebinop Oadd
                              (Etempvar _t'3 (tptr (tarray (tptr tvoid) 2)))
                              (Etempvar _i tint)
                              (tptr (tarray (tptr tvoid) 2)))))
                        (Ssequence
                          (Scall None
                            (Evar _acquire (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                            ((Etempvar _dlock (tptr (tarray (tptr tvoid) 2))) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'1
                                (Efield
                                  (Ederef
                                    (Etempvar _n (tptr (Tstruct _node noattr)))
                                    (Tstruct _node noattr)) _data
                                  (tptr tint)))
                              (Ssequence
                                (Sset _t'2
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                                      (Etempvar _i tint) (tptr tint)) tint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _out (tptr tint))
                                      (Etempvar _i tint) (tptr tint)) tint)
                                  (Etempvar _t'2 tint))))
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                              ((Etempvar _dlock (tptr (tarray (tptr tvoid) 2))) ::
                               nil))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall None
                    (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                     cc_default))
                    ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                  (Ssequence
                    (Sset _v
                      (Efield
                        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _version tint))
                    (Ssequence
                      (Scall None
                        (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _v tint)
                                     (Etempvar _ver tint) tint)
                        (Sreturn None)
                        Sskip)))))))))))
  Sskip)
|}.

Definition f_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_in, (tptr tint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_ver, tint) ::
               (_i, tint) :: (_dlock, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'3, (tptr (tarray (tptr tvoid) 2))) :: (_t'2, tint) ::
               (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _vlock (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
    (Ssequence
      (Sset _ver
        (Efield
          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _version tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _version tint)
          (Ebinop Oadd (Etempvar _ver tint) (Econst_int (Int.repr 1) tint)
            tint))
        (Ssequence
          (Scall None
            (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                             cc_default))
            ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _dlocks
                          (tptr (tarray (tptr tvoid) 2))))
                      (Sset _dlock
                        (Ebinop Oadd
                          (Etempvar _t'3 (tptr (tarray (tptr tvoid) 2)))
                          (Etempvar _i tint) (tptr (tarray (tptr tvoid) 2)))))
                    (Ssequence
                      (Scall None
                        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _dlock (tptr (tarray (tptr tvoid) 2))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'1
                            (Efield
                              (Ederef
                                (Etempvar _n (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _data (tptr tint)))
                          (Ssequence
                            (Sset _t'2
                              (Ederef
                                (Ebinop Oadd (Etempvar _in (tptr tint))
                                  (Etempvar _i tint) (tptr tint)) tint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                                  (Etempvar _i tint) (tptr tint)) tint)
                              (Etempvar _t'2 tint))))
                        (Scall None
                          (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
                          ((Etempvar _dlock (tptr (tarray (tptr tvoid) 2))) ::
                           nil))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Scall None
                (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default))
                ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _version tint)
                  (Ebinop Oadd (Etempvar _ver tint)
                    (Econst_int (Int.repr 2) tint) tint))
                (Scall None
                  (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))))))))))
|}.

Definition f_node_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_i, tint) ::
               (_ll, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'3, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'2, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _vlock (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
    (Ssequence
      (Scall None
        (Evar _freelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
        ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 8) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _dlocks
                        (tptr (tarray (tptr tvoid) 2))))
                    (Sset _ll
                      (Ebinop Oadd
                        (Etempvar _t'3 (tptr (tarray (tptr tvoid) 2)))
                        (Etempvar _i tint) (tptr (tarray (tptr tvoid) 2)))))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Etempvar _ll (tptr (tarray (tptr tvoid) 2))) :: nil))
                    (Scall None
                      (Evar _freelock (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                      ((Etempvar _ll (tptr (tarray (tptr tvoid) 2))) :: nil)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _dlocks
                  (tptr (tarray (tptr tvoid) 2))))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _t'2 (tptr (tarray (tptr tvoid) 2))) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _data (tptr tint)))
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _t'1 (tptr tint)) :: nil)))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _n (tptr (Tstruct _node noattr))) :: nil)))))))))
|}.

Definition f_thread_func := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_t'2, (tptr tint)) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
      (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Evar _one_node (tptr (Tstruct _node noattr))))
      (Ssequence
        (Sset _t'2 (Evar _second (tptr tint)))
        (Scall None
          (Evar _write (Tfunction
                         (Tcons (tptr (Tstruct _node noattr))
                           (Tcons (tptr tint) Tnil)) tvoid cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _node noattr))) ::
           (Etempvar _t'2 (tptr tint)) :: nil))))
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
  fn_temps := ((_i, tint) :: (_t_lock, (tptr (tarray (tptr tvoid) 2))) ::
               (_result, (tptr tint)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'11, (tptr tint)) :: (_t'10, (tptr tint)) ::
               (_t'9, (tptr tint)) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr tint)) :: (_t'5, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Econst_int (Int.repr 8) tint) (Esizeof tint tulong)
           tulong) :: nil))
      (Sassign (Evar _first (tptr tint))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                 cc_default))
          ((Ebinop Omul (Econst_int (Int.repr 8) tint) (Esizeof tint tulong)
             tulong) :: nil))
        (Sassign (Evar _second (tptr tint))
          (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'11 (Evar _first (tptr tint)))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'11 (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint)
                    (Etempvar _i tint)))
                (Ssequence
                  (Sset _t'10 (Evar _second (tptr tint)))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'10 (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint)
                    (Ebinop Osub (Econst_int (Int.repr 8) tint)
                      (Etempvar _i tint) tint)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'9 (Evar _first (tptr tint)))
              (Scall (Some _t'3)
                (Evar _node_new (Tfunction (Tcons (tptr tint) Tnil)
                                  (tptr (Tstruct _node noattr)) cc_default))
                ((Etempvar _t'9 (tptr tint)) :: nil)))
            (Sassign (Evar _one_node (tptr (Tstruct _node noattr)))
              (Etempvar _t'3 (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Sset _t_lock
              (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
                (tptr (tarray (tptr tvoid) 2))))
            (Ssequence
              (Scall None
                (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Etempvar _t_lock (tptr (tarray (tptr tvoid) 2))) :: nil))
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
                                     (tptr (Tfunction
                                             (Tcons (tptr tvoid) Tnil)
                                             (tptr tvoid) cc_default))
                                     (Tcons (tptr tvoid) Tnil)) tvoid
                                   cc_default))
                    ((Ecast
                       (Eaddrof
                         (Evar _thread_func (Tfunction
                                              (Tcons (tptr tvoid) Tnil)
                                              (tptr tvoid) cc_default))
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default))) (tptr tvoid)) ::
                     (Ecast
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       (tptr tvoid)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                               (tptr tvoid) cc_default))
                        ((Ebinop Omul (Econst_int (Int.repr 8) tint)
                           (Esizeof tint tulong) tulong) :: nil))
                      (Sset _result
                        (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tint))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Evar _one_node (tptr (Tstruct _node noattr))))
                        (Scall None
                          (Evar _read (Tfunction
                                        (Tcons (tptr (Tstruct _node noattr))
                                          (Tcons (tptr tint) Tnil)) tvoid
                                        cc_default))
                          ((Etempvar _t'8 (tptr (Tstruct _node noattr))) ::
                           (Etempvar _result (tptr tint)) :: nil)))
                      (Ssequence
                        (Scall None
                          (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
                          ((Ecast
                             (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                             (tptr tvoid)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _freelock2 (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                            ((Ecast
                               (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                               (tptr tvoid)) :: nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'7
                                (Evar _one_node (tptr (Tstruct _node noattr))))
                              (Scall None
                                (Evar _node_free (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _node noattr))
                                                     Tnil) tvoid cc_default))
                                ((Etempvar _t'7 (tptr (Tstruct _node noattr))) ::
                                 nil)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'6 (Evar _first (tptr tint)))
                                (Scall None
                                  (Evar _free (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                                  ((Etempvar _t'6 (tptr tint)) :: nil)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5 (Evar _second (tptr tint)))
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _t'5 (tptr tint)) :: nil)))
                                (Ssequence
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _result (tptr tint)) :: nil))
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   (Member_plain _vlock (tptr (tarray (tptr tvoid) 2)) ::
    Member_plain _version tint ::
    Member_plain _dlocks (tptr (tarray (tptr tvoid) 2)) ::
    Member_plain _data (tptr tint) :: nil)
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
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_one_node, Gvar v_one_node) :: (_thread_lock, Gvar v_thread_lock) ::
 (_first, Gvar v_first) :: (_second, Gvar v_second) ::
 (_node_new, Gfun(Internal f_node_new)) :: (_read, Gfun(Internal f_read)) ::
 (_write, Gfun(Internal f_write)) ::
 (_node_free, Gfun(Internal f_node_free)) ::
 (_thread_func, Gfun(Internal f_thread_func)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func :: _node_free :: _write :: _read :: _node_new ::
 _second :: _first :: _thread_lock :: _one_node :: _surely_malloc ::
 _spawn :: _release2 :: _freelock2 :: _release :: _acquire :: _freelock ::
 _makelock :: _exit :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


