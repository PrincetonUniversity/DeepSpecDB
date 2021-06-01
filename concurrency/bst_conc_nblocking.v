From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "macos".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "bst_conc_nblocking.c".
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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition _acquire : ident := $"acquire".
Definition _ap : ident := $"ap".
Definition _args : ident := $"args".
Definition _at : ident := $"at".
Definition _atom_ptr : ident := $"atom_ptr".
Definition _atomic_CAS_ptr : ident := $"atomic_CAS_ptr".
Definition _atomic_load_ptr : ident := $"atomic_load_ptr".
Definition _atomic_store_ptr : ident := $"atomic_store_ptr".
Definition _b : ident := $"b".
Definition _exit : ident := $"exit".
Definition _free : ident := $"free".
Definition _free_atomic_ptr : ident := $"free_atomic_ptr".
Definition _freelock2 : ident := $"freelock2".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _i__2 : ident := $"i__2".
Definition _insert : ident := $"insert".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _l__1 : ident := $"l__1".
Definition _l__2 : ident := $"l__2".
Definition _left : ident := $"left".
Definition _lookup : ident := $"lookup".
Definition _main : ident := $"main".
Definition _make_atomic_ptr : ident := $"make_atomic_ptr".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _p : ident := $"p".
Definition _ref : ident := $"ref".
Definition _release2 : ident := $"release2".
Definition _result : ident := $"result".
Definition _right : ident := $"right".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tb : ident := $"tb".
Definition _temp : ident := $"temp".
Definition _thread_func_insert : ident := $"thread_func_insert".
Definition _thread_func_lookup : ident := $"thread_func_lookup".
Definition _thread_lock : ident := $"thread_lock".
Definition _tp : ident := $"tp".
Definition _tree : ident := $"tree".
Definition _treebox_free : ident := $"treebox_free".
Definition _treebox_new : ident := $"treebox_new".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_tb := {|
  gvar_info := (tptr (Tstruct _atom_ptr noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_thread_lock := {|
  gvar_info := (tarray (tarray (tptr tvoid) 2) 10);
  gvar_init := (Init_space 80 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

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

Definition f_treebox_new := {|
  fn_return := (tptr (Tstruct _atom_ptr noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'1, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _make_atomic_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                               (tptr (Tstruct _atom_ptr noattr)) cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr (Tstruct _atom_ptr noattr)))))
  (Sreturn (Some (Etempvar _p (tptr (Tstruct _atom_ptr noattr))))))
|}.

Definition f_treebox_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_at, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t, (tptr (Tstruct _tree noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'3, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'2, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _at (Etempvar _b (tptr (Tstruct _atom_ptr noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _atomic_load_ptr (Tfunction
                                 (Tcons (tptr (Tstruct _atom_ptr noattr))
                                   Tnil) (tptr tvoid) cc_default))
        ((Etempvar _at (tptr (Tstruct _atom_ptr noattr))) :: nil))
      (Sset _t (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _t (tptr (Tstruct _tree noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _atom_ptr noattr))))
            (Scall None
              (Evar _treebox_free (Tfunction
                                    (Tcons (tptr (Tstruct _atom_ptr noattr))
                                      Tnil) tvoid cc_default))
              ((Etempvar _t'4 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _atom_ptr noattr))))
              (Scall None
                (Evar _treebox_free (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atom_ptr noattr))
                                        Tnil) tvoid cc_default))
                ((Etempvar _t'3 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef (Etempvar _t (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall None
                  (Evar _free_atomic_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) tvoid cc_default))
                  ((Etempvar _t'2 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _t (tptr (Tstruct _tree noattr))) :: nil)))))
        Sskip)
      (Scall None
        (Evar _free_atomic_ptr (Tfunction
                                 (Tcons (tptr (Tstruct _atom_ptr noattr))
                                   Tnil) tvoid cc_default))
        ((Etempvar _at (tptr (Tstruct _atom_ptr noattr))) :: nil)))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _atom_ptr noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_temp, (tptr (Tstruct _atom_ptr noattr))) ::
               (_tp, (tptr (Tstruct _tree noattr))) ::
               (_ref, (tptr (tptr tvoid))) ::
               (_p, (tptr (Tstruct _tree noattr))) ::
               (_val, (tptr (Tstruct _atom_ptr noattr))) ::
               (_left, (tptr (Tstruct _atom_ptr noattr))) ::
               (_right, (tptr (Tstruct _atom_ptr noattr))) ::
               (_result, tint) :: (_y, tint) :: (_t'7, tint) ::
               (_t'6, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'5, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'4, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) ::
               (_t'8, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp (Etempvar _t (tptr (Tstruct _atom_ptr noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (tptr tvoid) tuint) :: nil))
      (Sset _ref (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (tptr tvoid)))))
    (Ssequence
      (Sassign (Ederef (Etempvar _ref (tptr (tptr tvoid))) (tptr tvoid))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _atomic_load_ptr (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_ptr noattr))
                                           Tnil) (tptr tvoid) cc_default))
                ((Etempvar _temp (tptr (Tstruct _atom_ptr noattr))) :: nil))
              (Sset _tp (Etempvar _t'2 (tptr tvoid))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _tp (tptr (Tstruct _tree noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
                  (Sset _p
                    (Ecast (Etempvar _t'3 (tptr tvoid))
                      (tptr (Tstruct _tree noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint)
                    (Etempvar _x tint))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _make_atomic_ptr (Tfunction
                                                 (Tcons (tptr tvoid) Tnil)
                                                 (tptr (Tstruct _atom_ptr noattr))
                                                 cc_default))
                        ((Etempvar _value (tptr tvoid)) :: nil))
                      (Sset _val
                        (Etempvar _t'4 (tptr (Tstruct _atom_ptr noattr)))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value
                          (tptr (Tstruct _atom_ptr noattr)))
                        (Etempvar _val (tptr (Tstruct _atom_ptr noattr))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _make_atomic_ptr (Tfunction
                                                     (Tcons (tptr tvoid)
                                                       Tnil)
                                                     (tptr (Tstruct _atom_ptr noattr))
                                                     cc_default))
                            ((Econst_int (Int.repr 0) tint) :: nil))
                          (Sset _left
                            (Etempvar _t'5 (tptr (Tstruct _atom_ptr noattr)))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _atom_ptr noattr)))
                            (Etempvar _left (tptr (Tstruct _atom_ptr noattr))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar _make_atomic_ptr (Tfunction
                                                         (Tcons (tptr tvoid)
                                                           Tnil)
                                                         (tptr (Tstruct _atom_ptr noattr))
                                                         cc_default))
                                ((Econst_int (Int.repr 0) tint) :: nil))
                              (Sset _right
                                (Etempvar _t'6 (tptr (Tstruct _atom_ptr noattr)))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _atom_ptr noattr)))
                                (Etempvar _right (tptr (Tstruct _atom_ptr noattr))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _atomic_CAS_ptr (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _atom_ptr noattr))
                                                              (Tcons
                                                                (tptr (tptr tvoid))
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil)))
                                                            tint cc_default))
                                    ((Etempvar _temp (tptr (Tstruct _atom_ptr noattr))) ::
                                     (Etempvar _ref (tptr (tptr tvoid))) ::
                                     (Etempvar _p (tptr (Tstruct _tree noattr))) ::
                                     nil))
                                  (Sset _result (Etempvar _t'7 tint)))
                                (Ssequence
                                  (Sifthenelse (Eunop Onotbool
                                                 (Etempvar _result tint)
                                                 tint)
                                    (Ssequence
                                      (Scall None
                                        (Evar _free_atomic_ptr (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _atom_ptr noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                        ((Etempvar _val (tptr (Tstruct _atom_ptr noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _free_atomic_ptr (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _left (tptr (Tstruct _atom_ptr noattr))) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _free_atomic_ptr (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                            ((Etempvar _right (tptr (Tstruct _atom_ptr noattr))) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _free (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                              ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
                                               nil))
                                            Scontinue))))
                                    Sskip)
                                  (Ssequence
                                    (Scall None
                                      (Evar _free (Tfunction
                                                    (Tcons (tptr tvoid) Tnil)
                                                    tvoid cc_default))
                                      ((Etempvar _ref (tptr (tptr tvoid))) ::
                                       nil))
                                    (Sreturn None))))))))))))
              (Ssequence
                (Sset _y
                  (Efield
                    (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _key tint))
                (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                               (Etempvar _y tint) tint)
                  (Sset _temp
                    (Efield
                      (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _left
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Sifthenelse (Ebinop Olt (Etempvar _y tint)
                                 (Etempvar _x tint) tint)
                    (Sset _temp
                      (Efield
                        (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _right
                        (tptr (Tstruct _atom_ptr noattr))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef
                              (Etempvar _tp (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _value
                            (tptr (Tstruct _atom_ptr noattr))))
                        (Scall None
                          (Evar _atomic_store_ptr (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _atom_ptr noattr))
                                                      (Tcons (tptr tvoid)
                                                        Tnil)) tvoid
                                                    cc_default))
                          ((Etempvar _t'8 (tptr (Tstruct _atom_ptr noattr))) ::
                           (Etempvar _value (tptr tvoid)) :: nil)))
                      (Ssequence
                        (Scall None
                          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                          ((Etempvar _ref (tptr (tptr tvoid))) :: nil))
                        (Sreturn None)))))))))
        Sskip))))
|}.

Definition f_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _atom_ptr noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ap, (tptr (Tstruct _atom_ptr noattr))) ::
               (_p, (tptr (Tstruct _tree noattr))) :: (_v, (tptr tvoid)) ::
               (_y, tint) :: (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'7, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'6, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'5, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _ap (Etempvar _t (tptr (Tstruct _atom_ptr noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _atomic_load_ptr (Tfunction
                                 (Tcons (tptr (Tstruct _atom_ptr noattr))
                                   Tnil) (tptr tvoid) cc_default))
        ((Etempvar _ap (tptr (Tstruct _atom_ptr noattr))) :: nil))
      (Sset _p (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Swhile
        (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
        (Ssequence
          (Sset _y
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _key tint))
          (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint)
                         tint)
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _left
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall (Some _t'2)
                  (Evar _atomic_load_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _t'7 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Sset _p (Etempvar _t'2 (tptr tvoid))))
            (Sifthenelse (Ebinop Olt (Etempvar _y tint) (Etempvar _x tint)
                           tint)
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _right
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Scall (Some _t'3)
                    (Evar _atomic_load_ptr (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_ptr noattr))
                                               Tnil) (tptr tvoid) cc_default))
                    ((Etempvar _t'6 (tptr (Tstruct _atom_ptr noattr))) ::
                     nil)))
                (Sset _p (Etempvar _t'3 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _value
                        (tptr (Tstruct _atom_ptr noattr))))
                    (Scall (Some _t'4)
                      (Evar _atomic_load_ptr (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _atom_ptr noattr))
                                                 Tnil) (tptr tvoid)
                                               cc_default))
                      ((Etempvar _t'5 (tptr (Tstruct _atom_ptr noattr))) ::
                       nil)))
                  (Sset _v (Etempvar _t'4 (tptr tvoid))))
                (Sreturn (Some (Etempvar _v (tptr tvoid)))))))))
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
|}.

Definition f_thread_func_insert := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_i, tint) ::
               (_t'1, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Ecast (Etempvar _args (tptr tvoid)) (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 1) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                         (Econst_int (Int.repr 10) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1 (Evar _tb (tptr (Tstruct _atom_ptr noattr))))
            (Scall None
              (Evar _insert (Tfunction
                              (Tcons (tptr (Tstruct _atom_ptr noattr))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                              cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _atom_ptr noattr))) ::
               (Etempvar _i tint) ::
               (Evar ___stringlit_1 (tarray tschar 6)) :: nil))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
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

Definition f_thread_func_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_i, tint) ::
               (_v, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Ecast (Etempvar _args (tptr tvoid)) (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 10) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                         (Econst_int (Int.repr 1) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'2 (Evar _tb (tptr (Tstruct _atom_ptr noattr))))
              (Scall (Some _t'1)
                (Evar _lookup (Tfunction
                                (Tcons (tptr (Tstruct _atom_ptr noattr))
                                  (Tcons tint Tnil)) (tptr tvoid) cc_default))
                ((Etempvar _t'2 (tptr (Tstruct _atom_ptr noattr))) ::
                 (Etempvar _i tint) :: nil)))
            (Sset _v (Etempvar _t'1 (tptr tvoid)))))
        (Sset _i
          (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
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
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_i__1, tint) :: (_l__1, (tptr (tarray (tptr tvoid) 2))) ::
               (_i__2, tint) :: (_l__2, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'2, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _treebox_new (Tfunction Tnil (tptr (Tstruct _atom_ptr noattr))
                             cc_default)) nil)
      (Sassign (Evar _tb (tptr (Tstruct _atom_ptr noattr)))
        (Etempvar _t'1 (tptr (Tstruct _atom_ptr noattr)))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 5) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 10) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _l
                (Ebinop Oadd
                  (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 10))
                  (Etempvar _i tint) (tptr (tarray (tptr tvoid) 2))))
              (Ssequence
                (Scall None
                  (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                  ((Ecast (Etempvar _l (tptr (tarray (tptr tvoid) 2)))
                     (tptr tvoid)) :: nil))
                (Scall None
                  (Evar _spawn (Tfunction
                                 (Tcons
                                   (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (tptr tvoid) cc_default))
                                   (Tcons (tptr tvoid) Tnil)) tvoid
                                 cc_default))
                  ((Ecast
                     (Eaddrof
                       (Evar _thread_func_lookup (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   (tptr tvoid) cc_default))
                       (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                               (tptr tvoid) cc_default))) (tptr tvoid)) ::
                   (Ecast (Etempvar _l (tptr (tarray (tptr tvoid) 2)))
                     (tptr tvoid)) :: nil)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _i__1 (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                             (Econst_int (Int.repr 5) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _l__1
                  (Ebinop Oadd
                    (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 10))
                    (Etempvar _i__1 tint) (tptr (tarray (tptr tvoid) 2))))
                (Ssequence
                  (Scall None
                    (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                    ((Ecast (Etempvar _l__1 (tptr (tarray (tptr tvoid) 2)))
                       (tptr tvoid)) :: nil))
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
                         (Evar _thread_func_insert (Tfunction
                                                     (Tcons (tptr tvoid)
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default))) (tptr tvoid)) ::
                     (Ecast (Etempvar _l__1 (tptr (tarray (tptr tvoid) 2)))
                       (tptr tvoid)) :: nil)))))
            (Sset _i__1
              (Ebinop Oadd (Etempvar _i__1 tint)
                (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Ssequence
            (Sset _i__2 (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i__2 tint)
                               (Econst_int (Int.repr 10) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _l__2
                    (Ebinop Oadd
                      (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 10))
                      (Etempvar _i__2 tint) (tptr (tarray (tptr tvoid) 2))))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Ecast (Etempvar _l__2 (tptr (tarray (tptr tvoid) 2)))
                         (tptr tvoid)) :: nil))
                    (Scall None
                      (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                      ((Ecast (Etempvar _l__2 (tptr (tarray (tptr tvoid) 2)))
                         (tptr tvoid)) :: nil)))))
              (Sset _i__2
                (Ebinop Oadd (Etempvar _i__2 tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'2 (Evar _tb (tptr (Tstruct _atom_ptr noattr))))
              (Scall None
                (Evar _treebox_free (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atom_ptr noattr))
                                        Tnil) tvoid cc_default))
                ((Etempvar _t'2 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   ((_key, tint) :: (_value, (tptr (Tstruct _atom_ptr noattr))) ::
    (_left, (tptr (Tstruct _atom_ptr noattr))) ::
    (_right, (tptr (Tstruct _atom_ptr noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock2,
   Gfun(External (EF_external "freelock2"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release2,
   Gfun(External (EF_external "release2"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons
       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_make_atomic_ptr,
   Gfun(External (EF_external "make_atomic_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr (Tstruct _atom_ptr noattr)) cc_default)) ::
 (_atomic_load_ptr,
   Gfun(External (EF_external "atomic_load_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_atomic_store_ptr,
   Gfun(External (EF_external "atomic_store_ptr"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr)) (Tcons (tptr tvoid) Tnil))
     tvoid cc_default)) ::
 (_atomic_CAS_ptr,
   Gfun(External (EF_external "atomic_CAS_ptr"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr))
       (Tcons (tptr (tptr tvoid)) (Tcons (tptr tvoid) Tnil))) tint
     cc_default)) ::
 (_free_atomic_ptr,
   Gfun(External (EF_external "free_atomic_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr)) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) :: (_tb, Gvar v_tb) ::
 (_thread_lock, Gvar v_thread_lock) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_treebox_new, Gfun(Internal f_treebox_new)) ::
 (_treebox_free, Gfun(Internal f_treebox_free)) ::
 (_insert, Gfun(Internal f_insert)) :: (_lookup, Gfun(Internal f_lookup)) ::
 (_thread_func_insert, Gfun(Internal f_thread_func_insert)) ::
 (_thread_func_lookup, Gfun(Internal f_thread_func_lookup)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func_lookup :: _thread_func_insert :: _lookup :: _insert ::
 _treebox_free :: _treebox_new :: _surely_malloc :: _thread_lock :: _tb ::
 _exit :: _free :: _malloc :: _free_atomic_ptr :: _atomic_CAS_ptr ::
 _atomic_store_ptr :: _atomic_load_ptr :: _make_atomic_ptr :: _spawn ::
 _release2 :: _freelock2 :: _acquire :: _makelock :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


