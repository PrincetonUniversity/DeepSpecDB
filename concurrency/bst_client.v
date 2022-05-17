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
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "bst_client.c".
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
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _d : ident := $"d".
Definition _insert : ident := $"insert".
Definition _insert_int : ident := $"insert_int".
Definition _key : ident := $"key".
Definition _left : ident := $"left".
Definition _lock : ident := $"lock".
Definition _lookup : ident := $"lookup".
Definition _main : ident := $"main".
Definition _p_value : ident := $"p_value".
Definition _result : ident := $"result".
Definition _retVal : ident := $"retVal".
Definition _retrieve_value : ident := $"retrieve_value".
Definition _right : ident := $"right".
Definition _searchResult : ident := $"searchResult".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tb : ident := $"tb".
Definition _thread_lock : ident := $"thread_lock".
Definition _tree : ident := $"tree".
Definition _tree_t : ident := $"tree_t".
Definition _treebox_free : ident := $"treebox_free".
Definition _treebox_new : ident := $"treebox_new".
Definition _update_tree : ident := $"update_tree".
Definition _value : ident := $"value".
Definition _y : ident := $"y".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition v_thread_lock := {|
  gvar_info := (tarray (tptr tvoid) 2);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_tb := {|
  gvar_info := (tptr (tptr (Tstruct _tree_t noattr)));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_a := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_b := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_c := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_d := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_insert_int := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) ::
                (_key, tint) :: (_value, tint) :: nil);
  fn_vars := ((_value, tint) :: nil);
  fn_temps := ((_p_value, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _value tint) (Etempvar _value tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default)) ((Esizeof tint tulong) :: nil))
      (Sset _p_value (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Sset _t'2 (Evar _value tint))
        (Sassign
          (Ederef (Ecast (Etempvar _p_value (tptr tvoid)) (tptr tint)) tint)
          (Etempvar _t'2 tint)))
      (Scall None
        (Evar _insert (Tfunction
                        (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                          (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                        cc_default))
        ((Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) ::
         (Etempvar _key tint) ::
         (Ecast (Eaddrof (Evar _value tint) (tptr tint)) (tptr tvoid)) ::
         nil)))))
|}.

Definition f_update_tree := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _a tint) (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign (Evar _b tint) (Econst_int (Int.repr 2) tint))
    (Ssequence
      (Sassign (Evar _c tint) (Econst_int (Int.repr 3) tint))
      (Ssequence
        (Sassign (Evar _d tint) (Econst_int (Int.repr 4) tint))
        (Ssequence
          (Scall None
            (Evar _insert (Tfunction
                            (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                              (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                            cc_default))
            ((Etempvar _t (tptr tvoid)) :: (Econst_int (Int.repr 1) tint) ::
             (Eaddrof (Evar _a tint) (tptr tint)) :: nil))
          (Ssequence
            (Scall None
              (Evar _insert (Tfunction
                              (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                              cc_default))
              ((Etempvar _t (tptr tvoid)) ::
               (Econst_int (Int.repr 2) tint) ::
               (Eaddrof (Evar _b tint) (tptr tint)) :: nil))
            (Ssequence
              (Scall None
                (Evar _insert (Tfunction
                                (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                                  (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                tvoid cc_default))
                ((Etempvar _t (tptr tvoid)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Eaddrof (Evar _c tint) (tptr tint)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _insert (Tfunction
                                  (Tcons
                                    (tptr (tptr (Tstruct _tree_t noattr)))
                                    (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                  tvoid cc_default))
                  ((Etempvar _t (tptr tvoid)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Eaddrof (Evar _d tint) (tptr tint)) :: nil))
                (Sreturn (Some (Ecast
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) (tptr tvoid))))))))))))
|}.

Definition f_retrieve_value := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_searchResult, (tptr tvoid)) :: (_y, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _y (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _lookup (Tfunction
                            (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                              (Tcons tint Tnil)) (tptr tvoid) cc_default))
            ((Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) ::
             (Econst_int (Int.repr 2) tint) :: nil))
          (Sset _searchResult (Etempvar _t'1 (tptr tvoid))))
        (Sifthenelse (Ebinop One (Etempvar _searchResult (tptr tvoid))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sset _y
            (Ederef (Ecast (Etempvar _searchResult (tptr tvoid)) (tptr tint))
              tint))
          Sskip))
      (Sifthenelse (Ebinop One (Etempvar _y tint)
                     (Econst_int (Int.repr 4) tint) tint)
        Sskip
        Sbreak))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _lookup (Tfunction
                          (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                            (Tcons tint Tnil)) (tptr tvoid) cc_default))
          ((Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset _searchResult (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Sset _t'3
          (Ederef (Ecast (Etempvar _searchResult (tptr tvoid)) (tptr tint))
            tint))
        (Sreturn (Some (Etempvar _t'3 tint)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_result, (tptr tint)) :: (_retVal, tint) :: (_t'2, tint) ::
               (_t'1, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _treebox_new (Tfunction Tnil
                             (tptr (tptr (Tstruct _tree_t noattr)))
                             cc_default)) nil)
      (Sset _t (Etempvar _t'1 (tptr (tptr (Tstruct _tree_t noattr))))))
    (Ssequence
      (Scall None
        (Evar _spawn (Tfunction
                       (Tcons
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default))
                         (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
        ((Ecast
           (Eaddrof
             (Evar _update_tree (Tfunction (Tcons (tptr tvoid) Tnil)
                                  (tptr tvoid) cc_default))
             (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                     cc_default))) (tptr tvoid)) ::
         (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _retrieve_value (Tfunction
                                    (Tcons
                                      (tptr (tptr (Tstruct _tree_t noattr)))
                                      Tnil) tint cc_default))
            ((Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) :: nil))
          (Sset _retVal (Etempvar _t'2 tint)))
        (Ssequence
          (Scall None
            (Evar _treebox_free (Tfunction
                                  (Tcons
                                    (tptr (tptr (Tstruct _tree_t noattr)))
                                    Tnil) tvoid cc_default))
            ((Etempvar _t (tptr (tptr (Tstruct _tree_t noattr)))) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   (Member_plain _key tint :: Member_plain _value (tptr tvoid) ::
    Member_plain _left (tptr (Tstruct _tree_t noattr)) ::
    Member_plain _right (tptr (Tstruct _tree_t noattr)) :: nil)
   noattr ::
 Composite _tree_t Struct
   (Member_plain _t (tptr (Tstruct _tree noattr)) ::
    Member_plain _lock (tptr (tarray (tptr tvoid) 2)) :: nil)
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
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons
       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_thread_lock, Gvar v_thread_lock) :: (_tb, Gvar v_tb) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_treebox_new,
   Gfun(External (EF_external "treebox_new"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (tptr (Tstruct _tree_t noattr))) cc_default)) ::
 (_treebox_free,
   Gfun(External (EF_external "treebox_free"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (tptr (Tstruct _tree_t noattr))) Tnil) tvoid cc_default)) ::
 (_insert,
   Gfun(External (EF_external "insert"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
       (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_lookup,
   Gfun(External (EF_external "lookup"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default))
     (Tcons (tptr (tptr (Tstruct _tree_t noattr))) (Tcons tint Tnil))
     (tptr tvoid) cc_default)) :: (_a, Gvar v_a) :: (_b, Gvar v_b) ::
 (_c, Gvar v_c) :: (_d, Gvar v_d) ::
 (_insert_int, Gfun(Internal f_insert_int)) ::
 (_update_tree, Gfun(Internal f_update_tree)) ::
 (_retrieve_value, Gfun(Internal f_retrieve_value)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _retrieve_value :: _update_tree :: _insert_int :: _d :: _c :: _b ::
 _a :: _lookup :: _insert :: _treebox_free :: _treebox_new ::
 _surely_malloc :: _tb :: _thread_lock :: _spawn :: ___builtin_debug ::
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


