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
  Definition source_file := "giveup_template.c".
  Definition normalized := true.
End Info.

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
Definition _acquire : ident := $"acquire".
Definition _atom_int : ident := $"atom_int".
Definition _changeValue : ident := $"changeValue".
Definition _changeValue_helper : ident := $"changeValue_helper".
Definition _current : ident := $"current".
Definition _exit : ident := $"exit".
Definition _findNext : ident := $"findNext".
Definition _getLeftChild : ident := $"getLeftChild".
Definition _getLock : ident := $"getLock".
Definition _getRightChild : ident := $"getRightChild".
Definition _getValue : ident := $"getValue".
Definition _getValue_helper : ident := $"getValue_helper".
Definition _inRange : ident := $"inRange".
Definition _initStack : ident := $"initStack".
Definition _insertOp : ident := $"insertOp".
Definition _insertOp_bst : ident := $"insertOp_bst".
Definition _insertOp_helper : ident := $"insertOp_helper".
Definition _isEmpty : ident := $"isEmpty".
Definition _item : ident := $"item".
Definition _items : ident := $"items".
Definition _l : ident := $"l".
Definition _l1 : ident := $"l1".
Definition _l2 : ident := $"l2".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _max : ident := $"max".
Definition _min : ident := $"min".
Definition _n : ident := $"n".
Definition _newt : ident := $"newt".
Definition _node : ident := $"node".
Definition _node_t : ident := $"node_t".
Definition _p : ident := $"p".
Definition _p1 : ident := $"p1".
Definition _p2 : ident := $"p2".
Definition _pn : ident := $"pn".
Definition _pn__2 : ident := $"pn__2".
Definition _pop : ident := $"pop".
Definition _printDS_helper : ident := $"printDS_helper".
Definition _printKey : ident := $"printKey".
Definition _push : ident := $"push".
Definition _release : ident := $"release".
Definition _s : ident := $"s".
Definition _stack : ident := $"stack".
Definition _status : ident := $"status".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tb : ident := $"tb".
Definition _tgt : ident := $"tgt".
Definition _thread_lock : ident := $"thread_lock".
Definition _top : ident := $"top".
Definition _traverse : ident := $"traverse".
Definition _treebox_helper : ident := $"treebox_helper".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_thread_lock := {|
  gvar_info := (tptr (Tstruct _atom_int noattr));
  gvar_init := (Init_space 8 :: nil);
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

Definition v_tb := {|
  gvar_info := (tptr (tptr (Tstruct _node_t noattr)));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_initStack := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _stack noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
      (Tstruct _stack noattr)) _top tint)
  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
|}.

Definition f_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _stack noattr))) ::
                (_item, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
            (Tstruct _stack noattr)) _top tint))
      (Sset _t'1
        (Ecast
          (Ebinop Oadd (Etempvar _t'2 tint) (Econst_int (Int.repr 1) tint)
            tint) tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
          (Tstruct _stack noattr)) _top tint) (Etempvar _t'1 tint)))
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
            (Tstruct _stack noattr)) _items
          (tarray (tptr (Tstruct _node_t noattr)) 100)) (Etempvar _t'1 tint)
        (tptr (tptr (Tstruct _node_t noattr))))
      (tptr (Tstruct _node_t noattr)))
    (Etempvar _item (tptr (Tstruct _node_t noattr)))))
|}.

Definition f_isEmpty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _stack noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
        (Tstruct _stack noattr)) _top tint))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tint)
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))))
|}.

Definition f_pop := {|
  fn_return := (tptr (Tstruct _node_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _stack noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) ::
               (_t'3, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'2)
      (Evar _isEmpty (Tfunction (Tcons (tptr (Tstruct _stack noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _s (tptr (Tstruct _stack noattr))) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
                (Tstruct _stack noattr)) _top tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
                (Tstruct _stack noattr)) _top tint)
            (Ebinop Osub (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _stack noattr)))
                    (Tstruct _stack noattr)) _items
                  (tarray (tptr (Tstruct _node_t noattr)) 100))
                (Etempvar _t'1 tint) (tptr (tptr (Tstruct _node_t noattr))))
              (tptr (Tstruct _node_t noattr))))
          (Sreturn (Some (Etempvar _t'3 (tptr (Tstruct _node_t noattr)))))))
      Sskip))
  (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|}.

Definition f_inRange := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _node_t noattr)))
          (Tstruct _node_t noattr)) _min tint))
    (Sifthenelse (Ebinop Ogt (Etempvar _x tint) (Etempvar _t'2 tint) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _node_t noattr)))
              (Tstruct _node_t noattr)) _max tint))
        (Sset _t'1
          (Ecast (Ebinop Olt (Etempvar _x tint) (Etempvar _t'3 tint) tint)
            tbool)))
      (Sset _t'1 (Econst_int (Int.repr 0) tint))))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_traverse := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_status, tint) :: (_p, (tptr tvoid)) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'14, (tptr (Tstruct _atom_int noattr))) ::
               (_t'13, (tptr (Tstruct _node_t noattr))) ::
               (_t'12, (tptr (Tstruct _node_t noattr))) ::
               (_t'11, (tptr (Tstruct _node_t noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node_t noattr))) ::
               (_t'8, (tptr (Tstruct _atom_int noattr))) ::
               (_t'7, (tptr (Tstruct _node_t noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node_t noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _status (Econst_int (Int.repr 2) tint))
  (Ssequence
    (Sset _p
      (Efield
        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
          (Tstruct _pn noattr)) _n (tptr (Tstruct _node_t noattr))))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Ssequence
              (Sset _t'13
                (Efield
                  (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                    (Tstruct _pn noattr)) _n (tptr (Tstruct _node_t noattr))))
              (Ssequence
                (Sset _t'14
                  (Efield
                    (Ederef (Etempvar _t'13 (tptr (Tstruct _node_t noattr)))
                      (Tstruct _node_t noattr)) _lock
                    (tptr (Tstruct _atom_int noattr))))
                (Scall None
                  (Evar _acquire (Tfunction
                                   (Tcons (tptr (Tstruct _atom_int noattr))
                                     Tnil) tvoid cc_default))
                  ((Etempvar _t'14 (tptr (Tstruct _atom_int noattr))) :: nil))))
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                      (Tstruct _pn noattr)) _n
                    (tptr (Tstruct _node_t noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                      (Tstruct _pn noattr)) _p
                    (tptr (Tstruct _node_t noattr)))
                  (Etempvar _t'12 (tptr (Tstruct _node_t noattr)))))
              (Ssequence
                (Ssequence
                  (Sset _t'11
                    (Efield
                      (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                        (Tstruct _pn noattr)) _p
                      (tptr (Tstruct _node_t noattr))))
                  (Scall (Some _t'2)
                    (Evar _inRange (Tfunction
                                     (Tcons (tptr (Tstruct _node_t noattr))
                                       (Tcons tint Tnil)) tint cc_default))
                    ((Etempvar _t'11 (tptr (Tstruct _node_t noattr))) ::
                     (Etempvar _x tint) :: nil)))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                               (Econst_int (Int.repr 1) tint) tint)
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                          (Tstruct _pn noattr)) _p
                        (tptr (Tstruct _node_t noattr))))
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _t'5 (tptr (Tstruct _node_t noattr)))
                            (Tstruct _node_t noattr)) _t
                          (tptr (Tstruct _node noattr))))
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Ssequence
                          (Sset _status (Econst_int (Int.repr 2) tint))
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                    (Tstruct _pn noattr)) _p
                                  (tptr (Tstruct _node_t noattr))))
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'9 (tptr (Tstruct _node_t noattr)))
                                      (Tstruct _node_t noattr)) _t
                                    (tptr (Tstruct _node noattr))))
                                (Scall (Some _t'1)
                                  (Evar _findNext (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _node noattr))
                                                      (Tcons
                                                        (tptr (tptr tvoid))
                                                        (Tcons tint Tnil)))
                                                    tint cc_default))
                                  ((Etempvar _t'10 (tptr (Tstruct _node noattr))) ::
                                   (Ecast
                                     (Eaddrof
                                       (Efield
                                         (Ederef
                                           (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                           (Tstruct _pn noattr)) _n
                                         (tptr (Tstruct _node_t noattr)))
                                       (tptr (tptr (Tstruct _node_t noattr))))
                                     (tptr (tptr tvoid))) ::
                                   (Etempvar _x tint) :: nil))))
                            (Sset _status (Etempvar _t'1 tint)))
                          (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Sset _status (Econst_int (Int.repr 0) tint))
                              Sbreak)
                            (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sset _status (Econst_int (Int.repr 1) tint))
                                Sbreak)
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                      (Tstruct _pn noattr)) _p
                                    (tptr (Tstruct _node_t noattr))))
                                (Ssequence
                                  (Sset _t'8
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'7 (tptr (Tstruct _node_t noattr)))
                                        (Tstruct _node_t noattr)) _lock
                                      (tptr (Tstruct _atom_int noattr))))
                                  (Scall None
                                    (Evar _release (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _atom_int noattr))
                                                       Tnil) tvoid
                                                     cc_default))
                                    ((Etempvar _t'8 (tptr (Tstruct _atom_int noattr))) ::
                                     nil))))))))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                            (Tstruct _pn noattr)) _p
                          (tptr (Tstruct _node_t noattr))))
                      (Ssequence
                        (Sset _t'4
                          (Efield
                            (Ederef
                              (Etempvar _t'3 (tptr (Tstruct _node_t noattr)))
                              (Tstruct _node_t noattr)) _lock
                            (tptr (Tstruct _atom_int noattr))))
                        (Scall None
                          (Evar _release (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_int noattr))
                                             Tnil) tvoid cc_default))
                          ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) ::
                           nil))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                          (Tstruct _pn noattr)) _n
                        (tptr (Tstruct _node_t noattr)))
                      (Etempvar _p (tptr tvoid)))))))))
        Sskip)
      (Sreturn (Some (Etempvar _status tint))))))
|}.

Definition f_insertOp_bst := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: (_status, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p1, (tptr (Tstruct _node_t noattr))) ::
               (_p2, (tptr (Tstruct _node_t noattr))) ::
               (_l1, (tptr (Tstruct _atom_int noattr))) ::
               (_l2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'6, tint) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _node_t noattr) tulong) :: nil))
    (Sset _p1
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node_t noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _node_t noattr) tulong) :: nil))
      (Sset _p2
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _node_t noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p1 (tptr (Tstruct _node_t noattr)))
            (Tstruct _node_t noattr)) _t (tptr (Tstruct _node noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p2 (tptr (Tstruct _node_t noattr)))
              (Tstruct _node_t noattr)) _t (tptr (Tstruct _node noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _makelock (Tfunction Tnil
                                (tptr (Tstruct _atom_int noattr)) cc_default))
              nil)
            (Sset _l1 (Etempvar _t'3 (tptr (Tstruct _atom_int noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _p1 (tptr (Tstruct _node_t noattr)))
                  (Tstruct _node_t noattr)) _lock
                (tptr (Tstruct _atom_int noattr)))
              (Etempvar _l1 (tptr (Tstruct _atom_int noattr))))
            (Ssequence
              (Scall None
                (Evar _release (Tfunction
                                 (Tcons (tptr (Tstruct _atom_int noattr))
                                   Tnil) tvoid cc_default))
                ((Etempvar _l1 (tptr (Tstruct _atom_int noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _makelock (Tfunction Tnil
                                      (tptr (Tstruct _atom_int noattr))
                                      cc_default)) nil)
                  (Sset _l2
                    (Etempvar _t'4 (tptr (Tstruct _atom_int noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p2 (tptr (Tstruct _node_t noattr)))
                        (Tstruct _node_t noattr)) _lock
                      (tptr (Tstruct _atom_int noattr)))
                    (Etempvar _l2 (tptr (Tstruct _atom_int noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _release (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_int noattr))
                                         Tnil) tvoid cc_default))
                      ((Etempvar _l2 (tptr (Tstruct _atom_int noattr))) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _insertOp (Tfunction
                                          (Tcons
                                            (tptr (tptr (Tstruct _node noattr)))
                                            (Tcons tint
                                              (Tcons (tptr tvoid)
                                                (Tcons tint
                                                  (Tcons (tptr tvoid)
                                                    (Tcons (tptr tvoid) Tnil))))))
                                          tvoid cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _p (tptr (Tstruct _node_t noattr)))
                               (Tstruct _node_t noattr)) _t
                             (tptr (Tstruct _node noattr)))
                           (tptr (tptr (Tstruct _node noattr)))) ::
                         (Etempvar _x tint) ::
                         (Etempvar _value (tptr tvoid)) ::
                         (Etempvar _status tint) ::
                         (Etempvar _p1 (tptr (Tstruct _node_t noattr))) ::
                         (Etempvar _p2 (tptr (Tstruct _node_t noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'6
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _node_t noattr)))
                                (Tstruct _node_t noattr)) _min tint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p1 (tptr (Tstruct _node_t noattr)))
                                (Tstruct _node_t noattr)) _min tint)
                            (Etempvar _t'6 tint)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p1 (tptr (Tstruct _node_t noattr)))
                                (Tstruct _node_t noattr)) _max tint)
                            (Etempvar _x tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p2 (tptr (Tstruct _node_t noattr)))
                                  (Tstruct _node_t noattr)) _min tint)
                              (Etempvar _x tint))
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tstruct _node_t noattr)))
                                    (Tstruct _node_t noattr)) _max tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _p2 (tptr (Tstruct _node_t noattr)))
                                    (Tstruct _node_t noattr)) _max tint)
                                (Etempvar _t'5 tint)))))))))))))))))
|}.

Definition f_insertOp_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: (_status, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _insertOp_bst (Tfunction
                        (Tcons (tptr (Tstruct _node_t noattr))
                          (Tcons tint (Tcons (tptr tvoid) (Tcons tint Tnil))))
                        tvoid cc_default))
  ((Etempvar _p (tptr (Tstruct _node_t noattr))) :: (Etempvar _x tint) ::
   (Etempvar _value (tptr tvoid)) :: (Etempvar _status tint) :: nil))
|}.

Definition f_treebox_helper := {|
  fn_return := (tptr (Tstruct _node_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_newt, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _node_t noattr) tulong) :: nil))
    (Sset _newt
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node_t noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _makelock (Tfunction Tnil (tptr (Tstruct _atom_int noattr))
                          cc_default)) nil)
      (Sset _l (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _newt (tptr (Tstruct _node_t noattr)))
            (Tstruct _node_t noattr)) _lock
          (tptr (Tstruct _atom_int noattr)))
        (Etempvar _l (tptr (Tstruct _atom_int noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _newt (tptr (Tstruct _node_t noattr)))
              (Tstruct _node_t noattr)) _t (tptr (Tstruct _node noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _newt (tptr (Tstruct _node_t noattr)))
                (Tstruct _node_t noattr)) _min tint)
            (Ebinop Osub
              (Eunop Oneg (Econst_int (Int.repr 2147483647) tint) tint)
              (Econst_int (Int.repr 1) tint) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _newt (tptr (Tstruct _node_t noattr)))
                  (Tstruct _node_t noattr)) _max tint)
              (Econst_int (Int.repr 2147483647) tint))
            (Ssequence
              (Scall None
                (Evar _release (Tfunction
                                 (Tcons (tptr (Tstruct _atom_int noattr))
                                   Tnil) tvoid cc_default))
                ((Etempvar _l (tptr (Tstruct _atom_int noattr))) :: nil))
              (Sreturn (Some (Etempvar _newt (tptr (Tstruct _node_t noattr))))))))))))
|}.

Definition f_getLock := {|
  fn_return := (tptr (Tstruct _atom_int noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _node_t noattr)))
        (Tstruct _node_t noattr)) _lock (tptr (Tstruct _atom_int noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _atom_int noattr))))))
|}.

Definition f_changeValue_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _node_t noattr)))
        (Tstruct _node_t noattr)) _t (tptr (Tstruct _node noattr))))
  (Scall None
    (Evar _changeValue (Tfunction
                         (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid
                         cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _node noattr))) ::
     (Etempvar _value (tptr tvoid)) :: nil)))
|}.

Definition f_getValue_helper := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _node_t noattr)))
          (Tstruct _node_t noattr)) _t (tptr (Tstruct _node noattr))))
    (Scall (Some _t'1)
      (Evar _getValue (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                        cc_default))
      ((Etempvar _t'2 (tptr (Tstruct _node noattr))) :: nil)))
  (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
|}.

Definition f_printDS_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr tvoid))) :: nil);
  fn_vars := ((_s, (Tstruct _stack noattr)) :: nil);
  fn_temps := ((_tgt, (tptr (Tstruct _node_t noattr))) ::
               (_current, (tptr (Tstruct _node_t noattr))) ::
               (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _node_t noattr))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _tgt (Ederef (Etempvar _t (tptr (tptr tvoid))) (tptr tvoid)))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _tgt (tptr (Tstruct _node_t noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn None)
      Sskip)
    (Ssequence
      (Scall None
        (Evar _initStack (Tfunction
                           (Tcons (tptr (Tstruct _stack noattr)) Tnil) tvoid
                           cc_default))
        ((Eaddrof (Evar _s (Tstruct _stack noattr))
           (tptr (Tstruct _stack noattr))) :: nil))
      (Ssequence
        (Sset _current (Etempvar _tgt (tptr (Tstruct _node_t noattr))))
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _current (tptr (Tstruct _node_t noattr)))
                      (Tstruct _node_t noattr)) _t
                    (tptr (Tstruct _node noattr))))
                (Sifthenelse (Ebinop One
                               (Etempvar _t'10 (tptr (Tstruct _node noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sset _t'1 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _isEmpty (Tfunction
                                       (Tcons (tptr (Tstruct _stack noattr))
                                         Tnil) tint cc_default))
                      ((Eaddrof (Evar _s (Tstruct _stack noattr))
                         (tptr (Tstruct _stack noattr))) :: nil))
                    (Sset _t'1
                      (Ecast (Eunop Onotbool (Etempvar _t'2 tint) tint)
                        tbool)))))
              (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef
                          (Etempvar _current (tptr (Tstruct _node_t noattr)))
                          (Tstruct _node_t noattr)) _t
                        (tptr (Tstruct _node noattr))))
                    (Sifthenelse (Ebinop One
                                   (Etempvar _t'9 (tptr (Tstruct _node noattr)))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Scall None
                      (Evar _push (Tfunction
                                    (Tcons (tptr (Tstruct _stack noattr))
                                      (Tcons (tptr (Tstruct _node_t noattr))
                                        Tnil)) tvoid cc_default))
                      ((Eaddrof (Evar _s (Tstruct _stack noattr))
                         (tptr (Tstruct _stack noattr))) ::
                       (Etempvar _current (tptr (Tstruct _node_t noattr))) ::
                       nil))
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef
                              (Etempvar _current (tptr (Tstruct _node_t noattr)))
                              (Tstruct _node_t noattr)) _t
                            (tptr (Tstruct _node noattr))))
                        (Scall (Some _t'3)
                          (Evar _getLeftChild (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _node noattr))
                                                  Tnil) (tptr tvoid)
                                                cc_default))
                          ((Etempvar _t'8 (tptr (Tstruct _node noattr))) ::
                           nil)))
                      (Sset _current
                        (Ecast (Etempvar _t'3 (tptr tvoid))
                          (tptr (Tstruct _node_t noattr)))))))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _pop (Tfunction
                                 (Tcons (tptr (Tstruct _stack noattr)) Tnil)
                                 (tptr (Tstruct _node_t noattr)) cc_default))
                    ((Eaddrof (Evar _s (Tstruct _stack noattr))
                       (tptr (Tstruct _stack noattr))) :: nil))
                  (Sset _current
                    (Etempvar _t'4 (tptr (Tstruct _node_t noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef
                          (Etempvar _current (tptr (Tstruct _node_t noattr)))
                          (Tstruct _node_t noattr)) _t
                        (tptr (Tstruct _node noattr))))
                    (Scall None
                      (Evar _printKey (Tfunction
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil) tvoid cc_default))
                      ((Etempvar _t'7 (tptr (Tstruct _node noattr))) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _current (tptr (Tstruct _node_t noattr)))
                            (Tstruct _node_t noattr)) _t
                          (tptr (Tstruct _node noattr))))
                      (Scall (Some _t'5)
                        (Evar _getRightChild (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _node noattr))
                                                 Tnil) (tptr tvoid)
                                               cc_default))
                        ((Etempvar _t'6 (tptr (Tstruct _node noattr))) ::
                         nil)))
                    (Sset _current
                      (Ecast (Etempvar _t'5 (tptr tvoid))
                        (tptr (Tstruct _node_t noattr)))))))))
          Sskip)))))
|}.

Definition composites : list composite_definition :=
(Composite _pn Struct
   (Member_plain _p (tptr (Tstruct _node_t noattr)) ::
    Member_plain _n (tptr (Tstruct _node_t noattr)) :: nil)
   noattr ::
 Composite _node_t Struct
   (Member_plain _t (tptr (Tstruct _node noattr)) ::
    Member_plain _lock (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _min tint :: Member_plain _max tint :: nil)
   noattr ::
 Composite _stack Struct
   (Member_plain _items (tarray (tptr (Tstruct _node_t noattr)) 100) ::
    Member_plain _top tint :: nil)
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_thread_lock, Gvar v_thread_lock) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_findNext,
   Gfun(External (EF_external "findNext"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _node noattr))
       (Tcons (tptr (tptr tvoid)) (Tcons tint Tnil))) tint cc_default)) ::
 (_insertOp,
   Gfun(External (EF_external "insertOp"
                   (mksignature
                     (AST.Tlong :: AST.Tint :: AST.Tlong :: AST.Tint ::
                      AST.Tlong :: AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (tptr (Tstruct _node noattr)))
       (Tcons tint
         (Tcons (tptr tvoid)
           (Tcons tint (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))))))
     tvoid cc_default)) ::
 (_getValue,
   Gfun(External (EF_external "getValue"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default)) ::
 (_getLeftChild,
   Gfun(External (EF_external "getLeftChild"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _node noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_getRightChild,
   Gfun(External (EF_external "getRightChild"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _node noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_printKey,
   Gfun(External (EF_external "printKey"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _node noattr)) Tnil) tvoid cc_default)) ::
 (_tb, Gvar v_tb) ::
 (_changeValue,
   Gfun(External (EF_external "changeValue"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_initStack, Gfun(Internal f_initStack)) ::
 (_push, Gfun(Internal f_push)) :: (_isEmpty, Gfun(Internal f_isEmpty)) ::
 (_pop, Gfun(Internal f_pop)) :: (_inRange, Gfun(Internal f_inRange)) ::
 (_traverse, Gfun(Internal f_traverse)) ::
 (_insertOp_bst, Gfun(Internal f_insertOp_bst)) ::
 (_insertOp_helper, Gfun(Internal f_insertOp_helper)) ::
 (_treebox_helper, Gfun(Internal f_treebox_helper)) ::
 (_getLock, Gfun(Internal f_getLock)) ::
 (_changeValue_helper, Gfun(Internal f_changeValue_helper)) ::
 (_getValue_helper, Gfun(Internal f_getValue_helper)) ::
 (_printDS_helper, Gfun(Internal f_printDS_helper)) :: nil).

Definition public_idents : list ident :=
(_printDS_helper :: _getValue_helper :: _changeValue_helper :: _getLock ::
 _treebox_helper :: _insertOp_helper :: _insertOp_bst :: _traverse ::
 _inRange :: _pop :: _isEmpty :: _push :: _initStack :: _changeValue ::
 _tb :: _printKey :: _getRightChild :: _getLeftChild :: _getValue ::
 _insertOp :: _findNext :: _thread_lock :: _release :: _acquire ::
 _makelock :: _exit :: _malloc :: ___builtin_debug :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_clsll ::
 ___builtin_clsl :: ___builtin_cls :: ___builtin_fence ::
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


