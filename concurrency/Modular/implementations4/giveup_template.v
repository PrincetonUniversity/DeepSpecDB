From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.13".
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
Definition ___sFILE : ident := $"__sFILE".
Definition ___sFILEX : ident := $"__sFILEX".
Definition ___sbuf : ident := $"__sbuf".
Definition ___stdoutp : ident := $"__stdoutp".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __extra : ident := $"_extra".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __nbuf : ident := $"_nbuf".
Definition __offset : ident := $"_offset".
Definition __p : ident := $"_p".
Definition __r : ident := $"_r".
Definition __read : ident := $"_read".
Definition __seek : ident := $"_seek".
Definition __size : ident := $"_size".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __write : ident := $"_write".
Definition _acquire : ident := $"acquire".
Definition _atom_int : ident := $"atom_int".
Definition _c : ident := $"c".
Definition _change_value : ident := $"change_value".
Definition _change_value_helper : ident := $"change_value_helper".
Definition _css : ident := $"css".
Definition _exit : ident := $"exit".
Definition _fflush : ident := $"fflush".
Definition _findNext : ident := $"findNext".
Definition _get_lock : ident := $"get_lock".
Definition _get_root : ident := $"get_root".
Definition _get_value : ident := $"get_value".
Definition _get_value_helper : ident := $"get_value_helper".
Definition _hash : ident := $"hash".
Definition _inRange : ident := $"inRange".
Definition _insertOp_giveup : ident := $"insertOp_giveup".
Definition _insertOp_helper : ident := $"insertOp_helper".
Definition _lock : ident := $"lock".
Definition _lookup_md : ident := $"lookup_md".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _make_css : ident := $"make_css".
Definition _malloc : ident := $"malloc".
Definition _max : ident := $"max".
Definition _md : ident := $"md".
Definition _md_entry : ident := $"md_entry".
Definition _metadata : ident := $"metadata".
Definition _min : ident := $"min".
Definition _n : ident := $"n".
Definition _new_css : ident := $"new_css".
Definition _node : ident := $"node".
Definition _p : ident := $"p".
Definition _pn : ident := $"pn".
Definition _pn__2 : ident := $"pn__2".
Definition _printDS_giveup : ident := $"printDS_giveup".
Definition _printDS_helper : ident := $"printDS_helper".
Definition _ptr_value : ident := $"ptr_value".
Definition _release : ident := $"release".
Definition _root : ident := $"root".
Definition _status : ident := $"status".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _traverse : ident := $"traverse".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
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

Definition v___stdoutp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
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

Definition f_hash := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr_value, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _ptr_value
    (Ecast (Etempvar _p (tptr (Tstruct _node noattr))) tulong))
  (Sreturn (Some (Ecast
                   (Ebinop Omod
                     (Ebinop Omul (Etempvar _ptr_value tulong)
                       (Econst_long (Int64.repr 654435761) tulong) tulong)
                     (Econst_int (Int.repr 16384) tint) tulong) tint))))
|}.

Definition f_inRange := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _md_entry noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _m (tptr (Tstruct _md_entry noattr)))
          (Tstruct _md_entry noattr)) _min tint))
    (Sifthenelse (Ebinop Ogt (Etempvar _x tint) (Etempvar _t'2 tint) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _m (tptr (Tstruct _md_entry noattr)))
              (Tstruct _md_entry noattr)) _max tint))
        (Sset _t'1
          (Ecast (Ebinop Olt (Etempvar _x tint) (Etempvar _t'3 tint) tint)
            tbool)))
      (Sset _t'1 (Econst_int (Int.repr 0) tint))))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_lookup_md := {|
  fn_return := (tptr (Tstruct _md_entry noattr));
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr (Tstruct _md_entry noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _hash (Tfunction (Tcons (tptr (Tstruct _node noattr)) Tnil) tint
                  cc_default))
    ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
              (Tstruct _css noattr)) _metadata
            (tarray (tptr (Tstruct _md_entry noattr)) 16384))
          (Etempvar _t'1 tint) (tptr (tptr (Tstruct _md_entry noattr))))
        (tptr (Tstruct _md_entry noattr))))
    (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _md_entry noattr)))))))
|}.

Definition f_traverse := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_status, tint) :: (_p, (tptr (Tstruct _node noattr))) ::
               (_md, (tptr (Tstruct _md_entry noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _md_entry noattr))) ::
               (_t'11, (tptr (Tstruct _node noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _atom_int noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _status (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
            (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _t'11 (tptr (Tstruct _node noattr))) tint)
        (Sreturn (Some (Econst_int (Int.repr 2) tint)))
        Sskip))
    (Ssequence
      (Sset _p
        (Efield
          (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
            (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
      (Ssequence
        (Sloop
          (Ssequence
            Sskip
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                      (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
                (Sifthenelse (Eunop Onotbool
                               (Etempvar _t'10 (tptr (Tstruct _node noattr)))
                               tint)
                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                          (Tstruct _pn noattr)) _n
                        (tptr (Tstruct _node noattr))))
                    (Scall (Some _t'1)
                      (Evar _lookup_md (Tfunction
                                         (Tcons (tptr (Tstruct _css noattr))
                                           (Tcons
                                             (tptr (Tstruct _node noattr))
                                             Tnil))
                                         (tptr (Tstruct _md_entry noattr))
                                         cc_default))
                      ((Etempvar _c (tptr (Tstruct _css noattr))) ::
                       (Etempvar _t'9 (tptr (Tstruct _node noattr))) :: nil)))
                  (Sset _md
                    (Etempvar _t'1 (tptr (Tstruct _md_entry noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                          (Tstruct _md_entry noattr)) _lock
                        (tptr (Tstruct _atom_int noattr))))
                    (Scall None
                      (Evar _acquire (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_int noattr))
                                         Tnil) tvoid cc_default))
                      ((Etempvar _t'8 (tptr (Tstruct _atom_int noattr))) ::
                       nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                            (Tstruct _pn noattr)) _n
                          (tptr (Tstruct _node noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                            (Tstruct _pn noattr)) _p
                          (tptr (Tstruct _node noattr)))
                        (Etempvar _t'7 (tptr (Tstruct _node noattr)))))
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _inRange (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _md_entry noattr))
                                           (Tcons tint Tnil)) tint
                                         cc_default))
                        ((Etempvar _md (tptr (Tstruct _md_entry noattr))) ::
                         (Etempvar _x tint) :: nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'6
                                (Efield
                                  (Ederef
                                    (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                    (Tstruct _pn noattr)) _p
                                  (tptr (Tstruct _node noattr))))
                              (Scall (Some _t'2)
                                (Evar _findNext (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _node noattr))
                                                    (Tcons
                                                      (tptr (tptr tvoid))
                                                      (Tcons tint Tnil)))
                                                  tint cc_default))
                                ((Etempvar _t'6 (tptr (Tstruct _node noattr))) ::
                                 (Ecast
                                   (Eaddrof
                                     (Efield
                                       (Ederef
                                         (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                         (Tstruct _pn noattr)) _n
                                       (tptr (Tstruct _node noattr)))
                                     (tptr (tptr (Tstruct _node noattr))))
                                   (tptr (tptr tvoid))) ::
                                 (Etempvar _x tint) :: nil)))
                            (Sset _status (Etempvar _t'2 tint)))
                          (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            Sbreak
                            (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              Sbreak
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Ederef
                                      (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                                      (Tstruct _md_entry noattr)) _lock
                                    (tptr (Tstruct _atom_int noattr))))
                                (Scall None
                                  (Evar _release (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _atom_int noattr))
                                                     Tnil) tvoid cc_default))
                                  ((Etempvar _t'5 (tptr (Tstruct _atom_int noattr))) ::
                                   nil))))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'4
                              (Efield
                                (Ederef
                                  (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                                  (Tstruct _md_entry noattr)) _lock
                                (tptr (Tstruct _atom_int noattr))))
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _atom_int noattr))
                                                 Tnil) tvoid cc_default))
                              ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) ::
                               nil)))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                (Tstruct _pn noattr)) _n
                              (tptr (Tstruct _node noattr)))
                            (Etempvar _p (tptr (Tstruct _node noattr))))))))))))
          Sskip)
        (Sreturn (Some (Etempvar _status tint)))))))
|}.

Definition f_insertOp_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: (_status, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _insertOp_giveup (Tfunction
                           (Tcons (tptr (Tstruct _css noattr))
                             (Tcons (tptr (Tstruct _node noattr))
                               (Tcons tint
                                 (Tcons (tptr tvoid) (Tcons tint Tnil)))))
                           tvoid cc_default))
  ((Etempvar _c (tptr (Tstruct _css noattr))) ::
   (Etempvar _p (tptr (Tstruct _node noattr))) :: (Etempvar _x tint) ::
   (Etempvar _value (tptr tvoid)) :: (Etempvar _status tint) :: nil))
|}.

Definition f_make_css := {|
  fn_return := (tptr (Tstruct _css noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_new_css, (tptr (Tstruct _css noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _css noattr) tulong) :: nil))
    (Sset _new_css
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _css noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _new_css (tptr (Tstruct _css noattr)))
          (Tstruct _css noattr)) _root (tptr (Tstruct _node noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Sreturn (Some (Etempvar _new_css (tptr (Tstruct _css noattr)))))))
|}.

Definition f_get_lock := {|
  fn_return := (tptr (Tstruct _atom_int noattr));
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_m, (tptr (Tstruct _md_entry noattr))) ::
               (_t'1, (tptr (Tstruct _md_entry noattr))) ::
               (_t'3, (tptr (Tstruct ___sFILE noattr))) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _lookup_md (Tfunction
                         (Tcons (tptr (Tstruct _css noattr))
                           (Tcons (tptr (Tstruct _node noattr)) Tnil))
                         (tptr (Tstruct _md_entry noattr)) cc_default))
      ((Etempvar _c (tptr (Tstruct _css noattr))) ::
       (Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
    (Sset _m (Etempvar _t'1 (tptr (Tstruct _md_entry noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'3 (Evar ___stdoutp (tptr (Tstruct ___sFILE noattr))))
      (Scall None
        (Evar _fflush (Tfunction
                        (Tcons (tptr (Tstruct ___sFILE noattr)) Tnil) tint
                        cc_default))
        ((Etempvar _t'3 (tptr (Tstruct ___sFILE noattr))) :: nil)))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _m (tptr (Tstruct _md_entry noattr)))
            (Tstruct _md_entry noattr)) _lock
          (tptr (Tstruct _atom_int noattr))))
      (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _atom_int noattr))))))))
|}.

Definition f_get_root := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _css noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _t (tptr (Tstruct _css noattr)))
        (Tstruct _css noattr)) _root (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_change_value_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _change_value (Tfunction
                        (Tcons (tptr (Tstruct _node noattr))
                          (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
  ((Etempvar _p (tptr (Tstruct _node noattr))) ::
   (Etempvar _value (tptr tvoid)) :: nil))
|}.

Definition f_get_value_helper := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _get_value (Tfunction (Tcons (tptr (Tstruct _node noattr)) Tnil)
                       (tptr tvoid) cc_default))
    ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
  (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
|}.

Definition f_printDS_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _css noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _printDS_giveup (Tfunction (Tcons (tptr (Tstruct _css noattr)) Tnil)
                          tvoid cc_default))
  ((Etempvar _t (tptr (Tstruct _css noattr))) :: nil))
|}.

Definition composites : list composite_definition :=
(Composite ___sbuf Struct
   (Member_plain __base (tptr tuchar) :: Member_plain __size tint :: nil)
   noattr ::
 Composite ___sFILE Struct
   (Member_plain __p (tptr tuchar) :: Member_plain __r tint ::
    Member_plain __w tint :: Member_plain __flags tshort ::
    Member_plain __file tshort ::
    Member_plain __bf (Tstruct ___sbuf noattr) ::
    Member_plain __lbfsize tint :: Member_plain __cookie (tptr tvoid) ::
    Member_plain __close
      (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default)) ::
    Member_plain __read
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __seek
      (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))
              tlong cc_default)) ::
    Member_plain __write
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __ub (Tstruct ___sbuf noattr) ::
    Member_plain __extra (tptr (Tstruct ___sFILEX noattr)) ::
    Member_plain __ur tint :: Member_plain __ubuf (tarray tuchar 3) ::
    Member_plain __nbuf (tarray tuchar 1) ::
    Member_plain __lb (Tstruct ___sbuf noattr) ::
    Member_plain __blksize tint :: Member_plain __offset tlong :: nil)
   noattr ::
 Composite _pn Struct
   (Member_plain _p (tptr (Tstruct _node noattr)) ::
    Member_plain _n (tptr (Tstruct _node noattr)) :: nil)
   noattr ::
 Composite _md_entry Struct
   (Member_plain _lock (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _min tint :: Member_plain _max tint :: nil)
   noattr ::
 Composite _css Struct
   (Member_plain _root (tptr (Tstruct _node noattr)) ::
    Member_plain _metadata (tarray (tptr (Tstruct _md_entry noattr)) 16384) ::
    nil)
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
 (___stdoutp, Gvar v___stdoutp) ::
 (_fflush,
   Gfun(External (EF_external "fflush"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct ___sFILE noattr)) Tnil) tint cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_findNext,
   Gfun(External (EF_external "findNext"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _node noattr))
       (Tcons (tptr (tptr tvoid)) (Tcons tint Tnil))) tint cc_default)) ::
 (_change_value,
   Gfun(External (EF_external "change_value"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _node noattr)) (Tcons (tptr tvoid) Tnil)) tvoid
     cc_default)) ::
 (_get_value,
   Gfun(External (EF_external "get_value"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _node noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_insertOp_giveup,
   Gfun(External (EF_external "insertOp_giveup"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong ::
                      AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _css noattr))
       (Tcons (tptr (Tstruct _node noattr))
         (Tcons tint (Tcons (tptr tvoid) (Tcons tint Tnil))))) tvoid
     cc_default)) ::
 (_printDS_giveup,
   Gfun(External (EF_external "printDS_giveup"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _css noattr)) Tnil) tvoid cc_default)) ::
 (_hash, Gfun(Internal f_hash)) :: (_inRange, Gfun(Internal f_inRange)) ::
 (_lookup_md, Gfun(Internal f_lookup_md)) ::
 (_traverse, Gfun(Internal f_traverse)) ::
 (_insertOp_helper, Gfun(Internal f_insertOp_helper)) ::
 (_make_css, Gfun(Internal f_make_css)) ::
 (_get_lock, Gfun(Internal f_get_lock)) ::
 (_get_root, Gfun(Internal f_get_root)) ::
 (_change_value_helper, Gfun(Internal f_change_value_helper)) ::
 (_get_value_helper, Gfun(Internal f_get_value_helper)) ::
 (_printDS_helper, Gfun(Internal f_printDS_helper)) :: nil).

Definition public_idents : list ident :=
(_printDS_helper :: _get_value_helper :: _change_value_helper :: _get_root ::
 _get_lock :: _make_css :: _insertOp_helper :: _traverse :: _lookup_md ::
 _inRange :: _hash :: _printDS_giveup :: _insertOp_giveup :: _get_value ::
 _change_value :: _findNext :: _release :: _acquire :: _exit :: _malloc ::
 _fflush :: ___stdoutp :: ___builtin_debug :: ___builtin_fmin ::
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


