From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.12".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "bst.c".
  Definition normalized := true.
End Info.

Definition _Inorder : ident := $"Inorder".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
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
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
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
Definition _changeValue : ident := $"changeValue".
Definition _exit : ident := $"exit".
Definition _findNext : ident := $"findNext".
Definition _free : ident := $"free".
Definition _freeDS : ident := $"freeDS".
Definition _freelock2 : ident := $"freelock2".
Definition _getValue : ident := $"getValue".
Definition _inRange : ident := $"inRange".
Definition _insertOp : ident := $"insertOp".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _l1 : ident := $"l1".
Definition _l2 : ident := $"l2".
Definition _left : ident := $"left".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _max : ident := $"max".
Definition _min : ident := $"min".
Definition _n : ident := $"n".
Definition _n_tree : ident := $"n_tree".
Definition _node : ident := $"node".
Definition _node_t : ident := $"node_t".
Definition _p : ident := $"p".
Definition _p1 : ident := $"p1".
Definition _p2 : ident := $"p2".
Definition _p_tree : ident := $"p_tree".
Definition _pa : ident := $"pa".
Definition _pb : ident := $"pb".
Definition _pn : ident := $"pn".
Definition _pn__2 : ident := $"pn__2".
Definition _printDS : ident := $"printDS".
Definition _printf : ident := $"printf".
Definition _release : ident := $"release".
Definition _right : ident := $"right".
Definition _status : ident := $"status".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tgp : ident := $"tgp".
Definition _tgt : ident := $"tgt".
Definition _thread_lock : ident := $"thread_lock".
Definition _traverse : ident := $"traverse".
Definition _tree_t : ident := $"tree_t".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
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

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_thread_lock := {|
  gvar_info := (tarray (tptr tvoid) 8);
  gvar_init := (Init_space 64 :: nil);
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

Definition f_findNext := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p_tree, (tptr tvoid)) :: (_n_tree, (tptr (tptr tvoid))) ::
                (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree_t noattr))) ::
               (_n, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_y, tint) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _tree_t noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _tree_t noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ecast (Etempvar _p_tree (tptr tvoid)) (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _n
      (Ecast (Etempvar _n_tree (tptr (tptr tvoid)))
        (tptr (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
        (Sset _y
          (Efield
            (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _key tint)))
      (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                  (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _left
                  (tptr (Tstruct _tree_t noattr))))
              (Sassign
                (Ederef (Etempvar _n (tptr (tptr (Tstruct _tree_t noattr))))
                  (tptr (Tstruct _tree_t noattr)))
                (Ecast (Etempvar _t'4 (tptr (Tstruct _tree_t noattr)))
                  (tptr (Tstruct _tree_t noattr))))))
          (Sreturn (Some (Econst_int (Int.repr 2) tint))))
        (Sifthenelse (Ebinop Ogt (Etempvar _x tint) (Etempvar _y tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _t
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef (Etempvar _t'1 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _right
                    (tptr (Tstruct _tree_t noattr))))
                (Sassign
                  (Ederef
                    (Etempvar _n (tptr (tptr (Tstruct _tree_t noattr))))
                    (tptr (Tstruct _tree_t noattr)))
                  (Ecast (Etempvar _t'2 (tptr (Tstruct _tree_t noattr)))
                    (tptr (Tstruct _tree_t noattr))))))
            (Sreturn (Some (Econst_int (Int.repr 2) tint))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_insertOp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p_tree, (tptr tvoid)) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: (_status, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree_t noattr))) ::
               (_p1, (tptr (Tstruct _tree_t noattr))) ::
               (_p2, (tptr (Tstruct _tree_t noattr))) ::
               (_l1, (tptr (tarray (tptr tvoid) 8))) ::
               (_l2, (tptr (tarray (tptr tvoid) 8))) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) ::
               (_t'11, (tptr (Tstruct _node noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _node noattr))) :: (_t'7, tint) ::
               (_t'6, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ecast (Etempvar _p_tree (tptr tvoid)) (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _tree_t noattr) tulong) :: nil))
      (Sset _p1
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _tree_t noattr) tulong) :: nil))
        (Sset _p2
          (Ecast (Etempvar _t'2 (tptr tvoid))
            (tptr (Tstruct _tree_t noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                       (tptr tvoid) cc_default))
                ((Esizeof (tarray (tptr tvoid) 8) tulong) :: nil))
              (Sset _l1
                (Ecast (Etempvar _t'3 (tptr tvoid))
                  (tptr (tarray (tptr tvoid) 8)))))
            (Ssequence
              (Scall None
                (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Etempvar _l1 (tptr (tarray (tptr tvoid) 8))) :: nil))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
                      (Tstruct _tree_t noattr)) _lock
                    (tptr (tarray (tptr tvoid) 8)))
                  (Etempvar _l1 (tptr (tarray (tptr tvoid) 8))))
                (Ssequence
                  (Scall None
                    (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                     cc_default))
                    ((Etempvar _l1 (tptr (tarray (tptr tvoid) 8))) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                               (tptr tvoid) cc_default))
                        ((Esizeof (tarray (tptr tvoid) 8) tulong) :: nil))
                      (Sset _l2
                        (Ecast (Etempvar _t'4 (tptr tvoid))
                          (tptr (tarray (tptr tvoid) 8)))))
                    (Ssequence
                      (Scall None
                        (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil)
                                          tvoid cc_default))
                        ((Etempvar _l2 (tptr (tarray (tptr tvoid) 8))) ::
                         nil))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                              (Tstruct _tree_t noattr)) _lock
                            (tptr (tarray (tptr tvoid) 8)))
                          (Etempvar _l2 (tptr (tarray (tptr tvoid) 8))))
                        (Ssequence
                          (Scall None
                            (Evar _release (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                            ((Etempvar _l2 (tptr (tarray (tptr tvoid) 8))) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'5)
                                (Evar _surely_malloc (Tfunction
                                                       (Tcons tulong Tnil)
                                                       (tptr tvoid)
                                                       cc_default))
                                ((Esizeof (Tstruct _node noattr) tulong) ::
                                 nil))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                    (Tstruct _tree_t noattr)) _t
                                  (tptr (Tstruct _node noattr)))
                                (Ecast (Etempvar _t'5 (tptr tvoid))
                                  (tptr (Tstruct _node noattr)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'11
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                      (Tstruct _tree_t noattr)) _t
                                    (tptr (Tstruct _node noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'11 (tptr (Tstruct _node noattr)))
                                      (Tstruct _node noattr)) _key tint)
                                  (Etempvar _x tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'10
                                    (Efield
                                      (Ederef
                                        (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                        (Tstruct _tree_t noattr)) _t
                                      (tptr (Tstruct _node noattr))))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'10 (tptr (Tstruct _node noattr)))
                                        (Tstruct _node noattr)) _value
                                      (tptr tvoid))
                                    (Etempvar _value (tptr tvoid))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Efield
                                        (Ederef
                                          (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                          (Tstruct _tree_t noattr)) _t
                                        (tptr (Tstruct _node noattr))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'9 (tptr (Tstruct _node noattr)))
                                          (Tstruct _node noattr)) _left
                                        (tptr (Tstruct _tree_t noattr)))
                                      (Ecast
                                        (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
                                        (tptr (Tstruct _tree_t noattr)))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'8
                                        (Efield
                                          (Ederef
                                            (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                            (Tstruct _tree_t noattr)) _t
                                          (tptr (Tstruct _node noattr))))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                                            (Tstruct _node noattr)) _right
                                          (tptr (Tstruct _tree_t noattr)))
                                        (Ecast
                                          (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                                          (tptr (Tstruct _tree_t noattr)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'7
                                          (Efield
                                            (Ederef
                                              (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                              (Tstruct _tree_t noattr)) _min
                                            tint))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
                                              (Tstruct _tree_t noattr)) _min
                                            tint) (Etempvar _t'7 tint)))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
                                              (Tstruct _tree_t noattr)) _max
                                            tint) (Etempvar _x tint))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                                                (Tstruct _tree_t noattr))
                                              _min tint) (Etempvar _x tint))
                                          (Ssequence
                                            (Sset _t'6
                                              (Efield
                                                (Ederef
                                                  (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                                                  (Tstruct _tree_t noattr))
                                                _max tint))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                                                  (Tstruct _tree_t noattr))
                                                _max tint)
                                              (Etempvar _t'6 tint))))))))))))))))))))))))
|}.

Definition f_changeValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p_tree, (tptr tvoid)) :: (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree_t noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ecast (Etempvar _p_tree (tptr tvoid)) (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
    (Sassign
      (Efield
        (Ederef (Etempvar _t'1 (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _value (tptr tvoid))
      (Etempvar _value (tptr tvoid)))))
|}.

Definition f_getValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p_tree, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree_t noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ecast (Etempvar _p_tree (tptr tvoid)) (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _value (tptr tvoid)))
      (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))))
|}.

Definition f_Inorder := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'9, (tptr (Tstruct _tree_t noattr))) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr (Tstruct _node noattr))) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _tree_t noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
        (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
  (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr (Tstruct _node noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _left
              (tptr (Tstruct _tree_t noattr))))
          (Scall None
            (Evar _Inorder (Tfunction
                             (Tcons (tptr (Tstruct _tree_t noattr)) Tnil)
                             tvoid cc_default))
            ((Etempvar _t'9 (tptr (Tstruct _tree_t noattr))) :: nil))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _key tint))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _t
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _value (tptr tvoid)))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_1 (tarray tschar 11)) ::
                   (Etempvar _t'5 tint) ::
                   (Ecast (Etempvar _t'7 (tptr tvoid)) (tptr tschar)) :: nil))))))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _right
                (tptr (Tstruct _tree_t noattr))))
            (Scall None
              (Evar _Inorder (Tfunction
                               (Tcons (tptr (Tstruct _tree_t noattr)) Tnil)
                               tvoid cc_default))
              ((Etempvar _t'3 (tptr (Tstruct _tree_t noattr))) :: nil))))))
    Sskip))
|}.

Definition f_printDS := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgt, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _tgt (Ederef (Etempvar _t (tptr (tptr tvoid))) (tptr tvoid)))
  (Scall None
    (Evar _Inorder (Tfunction (Tcons (tptr (Tstruct _tree_t noattr)) Tnil)
                     tvoid cc_default))
    ((Etempvar _tgt (tptr (Tstruct _tree_t noattr))) :: nil)))
|}.

Definition f_freeDS := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p_tree, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgp, (tptr (Tstruct _tree_t noattr))) ::
               (_pa, (tptr (Tstruct _tree_t noattr))) ::
               (_pb, (tptr (Tstruct _tree_t noattr))) ::
               (_p, (tptr (Tstruct _node noattr))) :: (_l, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _tgp
    (Ecast (Etempvar _p_tree (tptr tvoid)) (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _l
      (Efield
        (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _lock (tptr (tarray (tptr tvoid) 8))))
    (Ssequence
      (Scall None
        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sifthenelse (Ebinop One
                         (Etempvar _p (tptr (Tstruct _node noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Sset _pa
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _left
                  (tptr (Tstruct _tree_t noattr))))
              (Ssequence
                (Sset _pb
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _right
                    (tptr (Tstruct _tree_t noattr))))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _freeDS (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                      ((Etempvar _pa (tptr (Tstruct _tree_t noattr))) :: nil))
                    (Scall None
                      (Evar _freeDS (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                      ((Etempvar _pb (tptr (Tstruct _tree_t noattr))) :: nil))))))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default))
              ((Etempvar _l (tptr tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _l (tptr tvoid)) :: nil))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _tgp (tptr (Tstruct _tree_t noattr))) :: nil)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   (Member_plain _key tint :: Member_plain _value (tptr tvoid) ::
    Member_plain _left (tptr (Tstruct _tree_t noattr)) ::
    Member_plain _right (tptr (Tstruct _tree_t noattr)) :: nil)
   noattr ::
 Composite _tree_t Struct
   (Member_plain _t (tptr (Tstruct _node noattr)) ::
    Member_plain _lock (tptr (tarray (tptr tvoid) 8)) ::
    Member_plain _min tint :: Member_plain _max tint :: nil)
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
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
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
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
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
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
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
 (_thread_lock, Gvar v_thread_lock) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_findNext, Gfun(Internal f_findNext)) ::
 (_insertOp, Gfun(Internal f_insertOp)) ::
 (_changeValue, Gfun(Internal f_changeValue)) ::
 (_getValue, Gfun(Internal f_getValue)) ::
 (_Inorder, Gfun(Internal f_Inorder)) ::
 (_printDS, Gfun(Internal f_printDS)) ::
 (_freeDS, Gfun(Internal f_freeDS)) :: nil).

Definition public_idents : list ident :=
(_freeDS :: _printDS :: _Inorder :: _getValue :: _changeValue :: _insertOp ::
 _findNext :: _surely_malloc :: _thread_lock :: _freelock2 :: _release ::
 _acquire :: _makelock :: _exit :: _free :: _malloc :: _printf ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
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


