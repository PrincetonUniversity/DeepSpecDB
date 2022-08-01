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
  Definition source_file := "bst_template.c".
  Definition normalized := true.
End Info.

Definition _Inorder : ident := $"Inorder".
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
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition _acquire : ident := $"acquire".
Definition _args : ident := $"args".
Definition _atom_int : ident := $"atom_int".
Definition _b : ident := $"b".
Definition _exit : ident := $"exit".
Definition _findnext : ident := $"findnext".
Definition _flag : ident := $"flag".
Definition _free : ident := $"free".
Definition _freelock : ident := $"freelock".
Definition _insert : ident := $"insert".
Definition _insertOp : ident := $"insertOp".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _l1 : ident := $"l1".
Definition _l2 : ident := $"l2".
Definition _l_old : ident := $"l_old".
Definition _l_old__1 : ident := $"l_old__1".
Definition _left : ident := $"left".
Definition _lock : ident := $"lock".
Definition _lookup : ident := $"lookup".
Definition _lookup2 : ident := $"lookup2".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _newt : ident := $"newt".
Definition _p : ident := $"p".
Definition _p1 : ident := $"p1".
Definition _p2 : ident := $"p2".
Definition _pa : ident := $"pa".
Definition _pb : ident := $"pb".
Definition _pn : ident := $"pn".
Definition _pn__2 : ident := $"pn__2".
Definition _printf : ident := $"printf".
Definition _release : ident := $"release".
Definition _right : ident := $"right".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _t_lock : ident := $"t_lock".
Definition _tb : ident := $"tb".
Definition _tgp : ident := $"tgp".
Definition _tgt : ident := $"tgt".
Definition _thread_func : ident := $"thread_func".
Definition _traverse : ident := $"traverse".
Definition _traverseInorder : ident := $"traverseInorder".
Definition _tree : ident := $"tree".
Definition _tree_free : ident := $"tree_free".
Definition _tree_t : ident := $"tree_t".
Definition _treebox_free : ident := $"treebox_free".
Definition _treebox_new : ident := $"treebox_new".
Definition _v : ident := $"v".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
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

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_tb := {|
  gvar_info := (tptr (tptr (Tstruct _tree_t noattr)));
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

Definition f_treebox_new := {|
  fn_return := (tptr (tptr (Tstruct _tree_t noattr)));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_newt, (tptr (Tstruct _tree_t noattr))) ::
               (_l, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr (Tstruct _tree_t noattr)) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (tptr (Tstruct _tree_t noattr))))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _tree_t noattr) tulong) :: nil))
      (Sset _newt
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Sassign
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _tree_t noattr))))
          (tptr (Tstruct _tree_t noattr)))
        (Etempvar _newt (tptr (Tstruct _tree_t noattr))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _makelock (Tfunction Tnil (tptr (Tstruct _atom_int noattr))
                              cc_default)) nil)
          (Sset _l (Etempvar _t'3 (tptr (Tstruct _atom_int noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _newt (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _lock
              (tptr (Tstruct _atom_int noattr)))
            (Etempvar _l (tptr (Tstruct _atom_int noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _newt (tptr (Tstruct _tree_t noattr)))
                  (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Scall None
                (Evar _release (Tfunction
                                 (Tcons (tptr (Tstruct _atom_int noattr))
                                   Tnil) tvoid cc_default))
                ((Etempvar _l (tptr (Tstruct _atom_int noattr))) :: nil))
              (Sreturn (Some (Etempvar _p (tptr (tptr (Tstruct _tree_t noattr)))))))))))))
|}.

Definition f_tree_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tgp, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, (tptr (Tstruct _tree_t noattr))) ::
               (_pb, (tptr (Tstruct _tree_t noattr))) ::
               (_p, (tptr (Tstruct _tree noattr))) :: (_l, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
        (Tstruct _tree_t noattr)) _lock (tptr (Tstruct _atom_int noattr))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction
                       (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid
                       cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Sset _p
        (Efield
          (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
            (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _pa
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree_t noattr))))
            (Ssequence
              (Sset _pb
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _right
                  (tptr (Tstruct _tree_t noattr))))
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _tree_free (Tfunction
                                       (Tcons (tptr (Tstruct _tree_t noattr))
                                         Tnil) tvoid cc_default))
                    ((Etempvar _pa (tptr (Tstruct _tree_t noattr))) :: nil))
                  (Scall None
                    (Evar _tree_free (Tfunction
                                       (Tcons (tptr (Tstruct _tree_t noattr))
                                         Tnil) tvoid cc_default))
                    ((Etempvar _pb (tptr (Tstruct _tree_t noattr))) :: nil))))))
          Sskip)
        (Ssequence
          (Scall None
            (Evar _freelock (Tfunction
                              (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                              tvoid cc_default))
            ((Etempvar _l (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _tgp (tptr (Tstruct _tree_t noattr))) :: nil))))))))
|}.

Definition f_treebox_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t
    (Ederef (Etempvar _b (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Scall None
      (Evar _tree_free (Tfunction
                         (Tcons (tptr (Tstruct _tree_t noattr)) Tnil) tvoid
                         cc_default))
      ((Etempvar _t (tptr (Tstruct _tree_t noattr))) :: nil))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _b (tptr (tptr (Tstruct _tree_t noattr)))) :: nil))))
|}.

Definition f_findnext := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_y, tint) :: (_t'8, (tptr (Tstruct _tree noattr))) ::
               (_t'7, (tptr (Tstruct _tree_t noattr))) ::
               (_t'6, (tptr (Tstruct _tree_t noattr))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree_t noattr))) ::
               (_t'3, (tptr (Tstruct _tree_t noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'7
      (Efield
        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
          (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _t'7 (tptr (Tstruct _tree_t noattr)))
            (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
      (Sset _y
        (Efield
          (Ederef (Etempvar _t'8 (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _key tint))))
  (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
              (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _t'4 (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _t'5 (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree_t noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr)))
              (Etempvar _t'6 (tptr (Tstruct _tree_t noattr)))))))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
    (Sifthenelse (Ebinop Ogt (Etempvar _x tint) (Etempvar _y tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _t'1 (tptr (Tstruct _tree_t noattr)))
                  (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _t'2 (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _right
                  (tptr (Tstruct _tree_t noattr))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                    (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr)))
                (Etempvar _t'3 (tptr (Tstruct _tree_t noattr)))))))
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_traverse := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_flag, tint) :: (_b, tint) :: (_t'1, tint) ::
               (_t'8, (tptr (Tstruct _tree_t noattr))) ::
               (_t'7, (tptr (Tstruct _atom_int noattr))) ::
               (_t'6, (tptr (Tstruct _tree_t noattr))) ::
               (_t'5, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr (Tstruct _tree_t noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _flag (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr)))
              (Etempvar _t'8 (tptr (Tstruct _tree_t noattr)))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _t'2 (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _t
                  (tptr (Tstruct _tree noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'3 (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                Sbreak
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _findnext (Tfunction
                                        (Tcons (tptr (Tstruct _pn noattr))
                                          (Tcons tint
                                            (Tcons (tptr tvoid) Tnil))) tint
                                        cc_default))
                      ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) ::
                       (Etempvar _x tint) ::
                       (Etempvar _value (tptr tvoid)) :: nil))
                    (Sset _b (Etempvar _t'1 tint)))
                  (Sifthenelse (Ebinop Oeq (Etempvar _b tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sset _flag (Econst_int (Int.repr 0) tint))
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                              (Tstruct _pn noattr)) _n
                            (tptr (Tstruct _tree_t noattr))))
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _t'6 (tptr (Tstruct _tree_t noattr)))
                                (Tstruct _tree_t noattr)) _lock
                              (tptr (Tstruct _atom_int noattr))))
                          (Scall None
                            (Evar _acquire (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_int noattr))
                                               Tnil) tvoid cc_default))
                            ((Etempvar _t'7 (tptr (Tstruct _atom_int noattr))) ::
                             nil))))
                      (Ssequence
                        (Sset _t'4
                          (Efield
                            (Ederef
                              (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                              (Tstruct _pn noattr)) _p
                            (tptr (Tstruct _tree_t noattr))))
                        (Ssequence
                          (Sset _t'5
                            (Efield
                              (Ederef
                                (Etempvar _t'4 (tptr (Tstruct _tree_t noattr)))
                                (Tstruct _tree_t noattr)) _lock
                              (tptr (Tstruct _atom_int noattr))))
                          (Scall None
                            (Evar _release (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_int noattr))
                                               Tnil) tvoid cc_default))
                            ((Etempvar _t'5 (tptr (Tstruct _atom_int noattr))) ::
                             nil))))))))))))
      Sskip)
    (Sreturn (Some (Etempvar _flag tint)))))
|}.

Definition f_insertOp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p1, (tptr (Tstruct _tree_t noattr))) ::
               (_p2, (tptr (Tstruct _tree_t noattr))) ::
               (_l1, (tptr (Tstruct _atom_int noattr))) ::
               (_l2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'14, (tptr (Tstruct _tree_t noattr))) ::
               (_t'13, (tptr (Tstruct _tree noattr))) ::
               (_t'12, (tptr (Tstruct _tree_t noattr))) ::
               (_t'11, (tptr (Tstruct _tree noattr))) ::
               (_t'10, (tptr (Tstruct _tree_t noattr))) ::
               (_t'9, (tptr (Tstruct _tree noattr))) ::
               (_t'8, (tptr (Tstruct _tree_t noattr))) ::
               (_t'7, (tptr (Tstruct _tree noattr))) ::
               (_t'6, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
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
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
            (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr)))
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
                (Ederef (Etempvar _p1 (tptr (Tstruct _tree_t noattr)))
                  (Tstruct _tree_t noattr)) _lock
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
                      (Ederef (Etempvar _p2 (tptr (Tstruct _tree_t noattr)))
                        (Tstruct _tree_t noattr)) _lock
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
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                                 (tptr tvoid) cc_default))
                          ((Esizeof (Tstruct _tree noattr) tulong) :: nil))
                        (Ssequence
                          (Sset _t'14
                            (Efield
                              (Ederef
                                (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                (Tstruct _pn noattr)) _p
                              (tptr (Tstruct _tree_t noattr))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _t'14 (tptr (Tstruct _tree_t noattr)))
                                (Tstruct _tree_t noattr)) _t
                              (tptr (Tstruct _tree noattr)))
                            (Ecast (Etempvar _t'5 (tptr tvoid))
                              (tptr (Tstruct _tree noattr))))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'12
                            (Efield
                              (Ederef
                                (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                (Tstruct _pn noattr)) _p
                              (tptr (Tstruct _tree_t noattr))))
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _t'12 (tptr (Tstruct _tree_t noattr)))
                                  (Tstruct _tree_t noattr)) _t
                                (tptr (Tstruct _tree noattr))))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'13 (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _key tint)
                              (Etempvar _x tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'10
                              (Efield
                                (Ederef
                                  (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                  (Tstruct _pn noattr)) _p
                                (tptr (Tstruct _tree_t noattr))))
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _t'10 (tptr (Tstruct _tree_t noattr)))
                                    (Tstruct _tree_t noattr)) _t
                                  (tptr (Tstruct _tree noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'11 (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _value
                                  (tptr tvoid))
                                (Etempvar _value (tptr tvoid)))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                    (Tstruct _pn noattr)) _p
                                  (tptr (Tstruct _tree_t noattr))))
                              (Ssequence
                                (Sset _t'9
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'8 (tptr (Tstruct _tree_t noattr)))
                                      (Tstruct _tree_t noattr)) _t
                                    (tptr (Tstruct _tree noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'9 (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _left
                                    (tptr (Tstruct _tree_t noattr)))
                                  (Etempvar _p1 (tptr (Tstruct _tree_t noattr))))))
                            (Ssequence
                              (Sset _t'6
                                (Efield
                                  (Ederef
                                    (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                    (Tstruct _pn noattr)) _p
                                  (tptr (Tstruct _tree_t noattr))))
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'6 (tptr (Tstruct _tree_t noattr)))
                                      (Tstruct _tree_t noattr)) _t
                                    (tptr (Tstruct _tree noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'7 (tptr (Tstruct _tree noattr)))
                                      (Tstruct _tree noattr)) _right
                                    (tptr (Tstruct _tree_t noattr)))
                                  (Etempvar _p2 (tptr (Tstruct _tree_t noattr))))))))))))))))))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) ::
               (_t'9, (tptr (Tstruct _tree_t noattr))) ::
               (_t'8, (tptr (Tstruct _atom_int noattr))) ::
               (_t'7, (tptr (Tstruct _tree_t noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree_t noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _pn noattr) tulong) :: nil))
    (Sset _pn__2
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _pn noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
          (tptr (Tstruct _tree_t noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
            (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr)))
        (Etempvar _t'9 (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
              (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr))))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _t'7 (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _lock
              (tptr (Tstruct _atom_int noattr))))
          (Scall None
            (Evar _acquire (Tfunction
                             (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                             tvoid cc_default))
            ((Etempvar _t'8 (tptr (Tstruct _atom_int noattr))) :: nil))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _traverse (Tfunction
                              (Tcons (tptr (Tstruct _pn noattr))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tint
                              cc_default))
            ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) ::
             (Etempvar _x tint) :: (Etempvar _value (tptr tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                    (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _t'5 (tptr (Tstruct _tree_t noattr)))
                      (Tstruct _tree_t noattr)) _t
                    (tptr (Tstruct _tree noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'6 (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value (tptr tvoid))
                  (Etempvar _value (tptr tvoid)))))
            (Scall None
              (Evar _insertOp (Tfunction
                                (Tcons (tptr (Tstruct _pn noattr))
                                  (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                tvoid cc_default))
              ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) ::
               (Etempvar _x tint) :: (Etempvar _value (tptr tvoid)) :: nil))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _t'3 (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _lock
                  (tptr (Tstruct _atom_int noattr))))
              (Scall None
                (Evar _release (Tfunction
                                 (Tcons (tptr (Tstruct _atom_int noattr))
                                   Tnil) tvoid cc_default))
                ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) :: nil))))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) :: nil)))))))
|}.

Definition f_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_pn__2, (tptr (Tstruct _pn noattr))) :: (_v, (tptr tvoid)) ::
               (_t'2, tint) :: (_t'1, (tptr tvoid)) ::
               (_t'9, (tptr (Tstruct _tree_t noattr))) ::
               (_t'8, (tptr (Tstruct _atom_int noattr))) ::
               (_t'7, (tptr (Tstruct _tree_t noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _tree_t noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _pn noattr) tulong) :: nil))
    (Sset _pn__2
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _pn noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
          (tptr (Tstruct _tree_t noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
            (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr)))
        (Etempvar _t'9 (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
              (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr))))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _t'7 (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _lock
              (tptr (Tstruct _atom_int noattr))))
          (Scall None
            (Evar _acquire (Tfunction
                             (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                             tvoid cc_default))
            ((Etempvar _t'8 (tptr (Tstruct _atom_int noattr))) :: nil))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _traverse (Tfunction
                              (Tcons (tptr (Tstruct _pn noattr))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tint
                              cc_default))
            ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) ::
             (Etempvar _x tint) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                    (Tstruct _pn noattr)) _p (tptr (Tstruct _tree_t noattr))))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _t'5 (tptr (Tstruct _tree_t noattr)))
                      (Tstruct _tree_t noattr)) _t
                    (tptr (Tstruct _tree noattr))))
                (Sset _v
                  (Efield
                    (Ederef (Etempvar _t'6 (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value (tptr tvoid)))))
            (Sset _v (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                  (Tstruct _pn noattr)) _n (tptr (Tstruct _tree_t noattr))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _t'3 (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _lock
                  (tptr (Tstruct _atom_int noattr))))
              (Scall None
                (Evar _release (Tfunction
                                 (Tcons (tptr (Tstruct _atom_int noattr))
                                   Tnil) tvoid cc_default))
                ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) :: nil))))
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _pn__2 (tptr (Tstruct _pn noattr))) :: nil))
            (Sreturn (Some (Etempvar _v (tptr tvoid))))))))))
|}.

Definition f_Inorder := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'9, (tptr (Tstruct _tree_t noattr))) ::
               (_t'8, (tptr (Tstruct _tree noattr))) ::
               (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr (Tstruct _tree noattr))) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree_t noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) ::
               (_t'1, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
        (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr (Tstruct _tree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _t'8 (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _left
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
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _key tint))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _t
                  (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _t'6 (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value (tptr tvoid)))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_1 (tarray tschar 19)) ::
                   (Etempvar _t'5 tint) :: (Etempvar _t'7 (tptr tvoid)) ::
                   nil))))))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree_t noattr)))
                (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _t'2 (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree_t noattr))))
            (Scall None
              (Evar _Inorder (Tfunction
                               (Tcons (tptr (Tstruct _tree_t noattr)) Tnil)
                               tvoid cc_default))
              ((Etempvar _t'3 (tptr (Tstruct _tree_t noattr))) :: nil))))))
    Sskip))
|}.

Definition f_traverseInorder := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgt, (tptr (Tstruct _tree_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _tgt
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Scall None
    (Evar _Inorder (Tfunction (Tcons (tptr (Tstruct _tree_t noattr)) Tnil)
                     tvoid cc_default))
    ((Etempvar _tgt (tptr (Tstruct _tree_t noattr))) :: nil)))
|}.

Definition f_lookup2 := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: (_v, (tptr tvoid)) ::
               (_tgt, (tptr (Tstruct _tree_t noattr))) ::
               (_l, (tptr tvoid)) :: (_y, tint) :: (_l_old, (tptr tvoid)) ::
               (_l_old__1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _tgt
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _l
      (Efield
        (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _lock (tptr (Tstruct _atom_int noattr))))
    (Ssequence
      (Scall None
        (Evar _acquire (Tfunction
                         (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid
                         cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
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
                  (Sset _tgt
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _left
                      (tptr (Tstruct _tree_t noattr))))
                  (Ssequence
                    (Sset _l_old (Etempvar _l (tptr tvoid)))
                    (Ssequence
                      (Sset _l
                        (Efield
                          (Ederef
                            (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
                            (Tstruct _tree_t noattr)) _lock
                          (tptr (Tstruct _atom_int noattr))))
                      (Ssequence
                        (Scall None
                          (Evar _acquire (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_int noattr))
                                             Tnil) tvoid cc_default))
                          ((Etempvar _l (tptr tvoid)) :: nil))
                        (Ssequence
                          (Sset _p
                            (Efield
                              (Ederef
                                (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
                                (Tstruct _tree_t noattr)) _t
                              (tptr (Tstruct _tree noattr))))
                          (Scall None
                            (Evar _release (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_int noattr))
                                               Tnil) tvoid cc_default))
                            ((Etempvar _l_old (tptr tvoid)) :: nil)))))))
                (Sifthenelse (Ebinop Olt (Etempvar _y tint)
                               (Etempvar _x tint) tint)
                  (Ssequence
                    (Sset _tgt
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _right
                        (tptr (Tstruct _tree_t noattr))))
                    (Ssequence
                      (Sset _l_old__1 (Etempvar _l (tptr tvoid)))
                      (Ssequence
                        (Sset _l
                          (Efield
                            (Ederef
                              (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
                              (Tstruct _tree_t noattr)) _lock
                            (tptr (Tstruct _atom_int noattr))))
                        (Ssequence
                          (Scall None
                            (Evar _acquire (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_int noattr))
                                               Tnil) tvoid cc_default))
                            ((Etempvar _l (tptr tvoid)) :: nil))
                          (Ssequence
                            (Sset _p
                              (Efield
                                (Ederef
                                  (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
                                  (Tstruct _tree_t noattr)) _t
                                (tptr (Tstruct _tree noattr))))
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _atom_int noattr))
                                                 Tnil) tvoid cc_default))
                              ((Etempvar _l_old__1 (tptr tvoid)) :: nil)))))))
                  (Ssequence
                    (Sset _v
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _value (tptr tvoid)))
                    (Ssequence
                      (Scall None
                        (Evar _release (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_int noattr))
                                           Tnil) tvoid cc_default))
                        ((Etempvar _l (tptr tvoid)) :: nil))
                      (Sreturn (Some (Etempvar _v (tptr tvoid))))))))))
          (Ssequence
            (Scall None
              (Evar _release (Tfunction
                               (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                               tvoid cc_default))
              ((Etempvar _l (tptr tvoid)) :: nil))
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))))))))
|}.

Definition f_thread_func := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'1, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Ecast (Etempvar _args (tptr tvoid)) (tptr (Tstruct _atom_int noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
      (Scall None
        (Evar _insert (Tfunction
                        (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                          (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                        cc_default))
        ((Etempvar _t'2 (tptr (tptr (Tstruct _tree_t noattr)))) ::
         (Econst_int (Int.repr 6) tint) ::
         (Evar ___stringlit_2 (tarray tschar 16)) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
        (Scall None
          (Evar _insert (Tfunction
                          (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                            (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                          cc_default))
          ((Etempvar _t'1 (tptr (tptr (Tstruct _tree_t noattr)))) ::
           (Econst_int (Int.repr 4) tint) ::
           (Evar ___stringlit_3 (tarray tschar 5)) :: nil)))
      (Ssequence
        (Scall None
          (Evar _release (Tfunction
                           (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                           tvoid cc_default))
          ((Ecast (Etempvar _l (tptr (Tstruct _atom_int noattr)))
             (tptr tvoid)) :: nil))
        (Sreturn (Some (Ecast
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         (tptr tvoid))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t_lock, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'9, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'8, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'7, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'6, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'5, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'4, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _treebox_new (Tfunction Tnil
                             (tptr (tptr (Tstruct _tree_t noattr)))
                             cc_default)) nil)
      (Sassign (Evar _tb (tptr (tptr (Tstruct _tree_t noattr))))
        (Etempvar _t'1 (tptr (tptr (Tstruct _tree_t noattr))))))
    (Ssequence
      (Ssequence
        (Sset _t'9 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
        (Scall None
          (Evar _insert (Tfunction
                          (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                            (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                          cc_default))
          ((Etempvar _t'9 (tptr (tptr (Tstruct _tree_t noattr)))) ::
           (Econst_int (Int.repr 3) tint) ::
           (Evar ___stringlit_4 (tarray tschar 6)) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _t'8 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
          (Scall None
            (Evar _insert (Tfunction
                            (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                              (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                            cc_default))
            ((Etempvar _t'8 (tptr (tptr (Tstruct _tree_t noattr)))) ::
             (Econst_int (Int.repr 1) tint) ::
             (Evar ___stringlit_5 (tarray tschar 4)) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _t'7 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
            (Scall None
              (Evar _insert (Tfunction
                              (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                              cc_default))
              ((Etempvar _t'7 (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (Econst_int (Int.repr 4) tint) ::
               (Evar ___stringlit_6 (tarray tschar 5)) :: nil)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _makelock (Tfunction Tnil
                                  (tptr (Tstruct _atom_int noattr))
                                  cc_default)) nil)
              (Sset _t_lock
                (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
            (Ssequence
              (Scall None
                (Evar _spawn (Tfunction
                               (Tcons
                                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tint cc_default))
                                 (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                ((Ecast
                   (Eaddrof
                     (Evar _thread_func (Tfunction (Tcons (tptr tvoid) Tnil)
                                          (tptr tvoid) cc_default))
                     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                             cc_default))) (tptr tvoid)) ::
                 (Ecast (Etempvar _t_lock (tptr (Tstruct _atom_int noattr)))
                   (tptr tvoid)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _acquire (Tfunction
                                   (Tcons (tptr (Tstruct _atom_int noattr))
                                     Tnil) tvoid cc_default))
                  ((Ecast
                     (Etempvar _t_lock (tptr (Tstruct _atom_int noattr)))
                     (tptr tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _freelock (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atom_int noattr))
                                        Tnil) tvoid cc_default))
                    ((Ecast
                       (Etempvar _t_lock (tptr (Tstruct _atom_int noattr)))
                       (tptr tvoid)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
                        (Scall (Some _t'3)
                          (Evar _lookup (Tfunction
                                          (Tcons
                                            (tptr (tptr (Tstruct _tree_t noattr)))
                                            (Tcons tint Tnil)) (tptr tvoid)
                                          cc_default))
                          ((Etempvar _t'6 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                           (Econst_int (Int.repr 4) tint) :: nil)))
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_7 (tarray tschar 4)) ::
                         (Etempvar _t'3 (tptr tvoid)) :: nil)))
                    (Ssequence
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_8 (tarray tschar 10)) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'5
                            (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
                          (Scall None
                            (Evar _traverseInorder (Tfunction
                                                     (Tcons
                                                       (tptr (tptr (Tstruct _tree_t noattr)))
                                                       Tnil) tvoid
                                                     cc_default))
                            ((Etempvar _t'5 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                             nil)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'4
                              (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
                            (Scall None
                              (Evar _treebox_free (Tfunction
                                                    (Tcons
                                                      (tptr (tptr (Tstruct _tree_t noattr)))
                                                      Tnil) tvoid cc_default))
                              ((Etempvar _t'4 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                               nil)))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))
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
    Member_plain _lock (tptr (Tstruct _atom_int noattr)) :: nil)
   noattr ::
 Composite _pn Struct
   (Member_plain _p (tptr (Tstruct _tree_t noattr)) ::
    Member_plain _n (tptr (Tstruct _tree_t noattr)) :: nil)
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
     cc_default)) :: (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
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
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) :: (_tb, Gvar v_tb) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_treebox_new, Gfun(Internal f_treebox_new)) ::
 (_tree_free, Gfun(Internal f_tree_free)) ::
 (_treebox_free, Gfun(Internal f_treebox_free)) ::
 (_findnext, Gfun(Internal f_findnext)) ::
 (_traverse, Gfun(Internal f_traverse)) ::
 (_insertOp, Gfun(Internal f_insertOp)) ::
 (_insert, Gfun(Internal f_insert)) :: (_lookup, Gfun(Internal f_lookup)) ::
 (_Inorder, Gfun(Internal f_Inorder)) ::
 (_traverseInorder, Gfun(Internal f_traverseInorder)) ::
 (_lookup2, Gfun(Internal f_lookup2)) ::
 (_thread_func, Gfun(Internal f_thread_func)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func :: _lookup2 :: _traverseInorder :: _Inorder ::
 _lookup :: _insert :: _insertOp :: _traverse :: _findnext ::
 _treebox_free :: _tree_free :: _treebox_new :: _surely_malloc :: _tb ::
 _spawn :: _release :: _acquire :: _freelock :: _makelock :: _exit ::
 _free :: _malloc :: _printf :: ___builtin_debug ::
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


