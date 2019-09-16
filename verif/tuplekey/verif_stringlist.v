Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import stringlist.
Require Import FunInd.
Require FMapWeakList.
Require Coq.Strings.String.
Require Import DecidableType.
Require Import Program.Basics. Open Scope program_scope.
Require Import Structures.OrdersEx.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import definitions.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Default Timeout 20.

(* ------------------------ DEFINITIONS ------------------------ *)

(* string as a decidable type *)
Module Str_as_DT <: DecidableType.
 Definition t := string.
 Definition eq := @eq t.
 Definition eq_refl := @eq_refl t.
 Definition eq_sym := @eq_sym t.
 Definition eq_trans := @eq_trans t.
 Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
 Proof. apply string_dec. Qed.
End Str_as_DT.

Module stringlist := FMapWeakList.Make Str_as_DT.

Definition t_scell := Tstruct _scell noattr.
Definition t_stringlist := Tstruct _stringlist noattr.

(* convert between Coq string type & list of bytes *)
Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => O
  | String c s' => S (length s')
  end.

Definition string_rep (s: string) (p: val) : mpred := !! (~ List.In Byte.zero (string_to_list_byte s)) &&
  data_at Ews (tarray tschar (Z.of_nat(length(s)) + 1)) (map Vbyte (string_to_list_byte s ++ [Byte.zero])) p.

Lemma length_string_list_byte_eq:
  forall str: string, Z.of_nat (length str) = Zlength (string_to_list_byte str).
Proof.
  intros str. induction str.
  - simpl. auto.
  - unfold length; fold length. unfold string_to_list_byte; fold string_to_list_byte.
     autorewrite with sublist. rewrite <- IHstr. apply Nat2Z.inj_succ.
Qed.

Definition string_rep_local_facts:
  forall s p, string_rep s p |-- !! (is_pointer_or_null p /\ 
  0 <= Z.of_nat (length s) + 1 <= Ptrofs.max_unsigned).
Proof.
  intros. assert (K: string_rep s p |-- cstring Ews (string_to_list_byte s) p).
  unfold string_rep. unfold cstring. rewrite length_string_list_byte_eq. entailer!.
  sep_apply K. sep_apply cstring_local_facts. entailer!. 
  rewrite length_string_list_byte_eq. split.
  assert (M: 0 <= Zlength (string_to_list_byte s)). apply Zlength_nonneg. omega.
  rewrite <- initialize.max_unsigned_modulus in H. omega.
Qed.
Hint Resolve string_rep_local_facts: saturate_local.

Fixpoint scell_rep (l: list (string*V)) (p: val): mpred :=
  match l with
  | [] => !!(p = nullval) && emp
  | (k, v) :: tl => EX q:val, EX str_ptr: val, 
                    malloc_token Ews t_scell p *
                    data_at Ews t_scell (str_ptr, (V_repr v, q)) p *
                    string_rep k str_ptr *
                    malloc_token Ews (tarray tschar (Z.of_nat (length k) + 1)) str_ptr *
                    scell_rep tl q
  end.

Definition scell_rep_local_facts:
  forall l p, scell_rep l p |-- !! (is_pointer_or_null p /\ (p=nullval <-> l = [])).
Proof.
  intros l. induction l as [ | [] tl]; intro p; simpl.
  + entailer!. easy.
  + Intros q str_ptr. unfold string_rep. entailer!. now apply field_compatible_nullval1 in H1.
Qed.
Hint Resolve scell_rep_local_facts: saturate_local.

Definition scell_rep_valid_pointer:
  forall l p, scell_rep l p |-- valid_pointer p.
Proof. intros [|[]] p; cbn; entailer. Qed.
Hint Resolve scell_rep_valid_pointer: valid_pointer.

Import stringlist.

Definition stringlist_rep (lst: stringlist.t V) (p: val): mpred :=
  let elts := elements lst in 
  EX cell_ptr: val,
  malloc_token Ews t_stringlist p *
  data_at Ews t_stringlist cell_ptr p *
  scell_rep elts cell_ptr.

Definition stringlist_rep_local_facts:
  forall lst p, stringlist_rep lst p |-- !! (is_pointer_or_null p).
Proof.
  intros. unfold stringlist_rep. Intros cell_ptr. entailer!.
Qed.

(* ------------------------ STRLIB SPECS ------------------------ *)

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP ()
    LOCAL (temp 1 str1; temp 2 str2)
    SEP (cstring Ews s1 str1; cstring Ews s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring Ews s1 str1; cstring Ews s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH dest : val, n : Z, src : val, s : list byte
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP (Zlength s < n)
    LOCAL (temp 1 dest; temp 2 src)
    SEP (data_at_ Ews (tarray tschar n) dest; cstring Ews s src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn Ews s n dest; cstring Ews s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH s : list byte, str: val
  PRE [ 1 OF tptr tschar ]
    PROP ( )
    LOCAL (temp 1 str)
    SEP (cstring Ews s str)
  POST [ size_t ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring Ews s str).


(* ------------------------ STRINGLIST.V SPECS ------------------------ *)

Definition stringlist_new_spec: ident * funspec :=
   DECLARE _stringlist_new
 WITH gv: globals
 PRE [ ] 
   PROP()
   LOCAL(gvars gv)
   SEP(mem_mgr gv)
 POST [ tptr t_stringlist] 
   EX p:val,
      PROP() 
      LOCAL(temp ret_temp p) 
      SEP(stringlist_rep (stringlist.empty V) p; mem_mgr gv).

Definition copy_string_spec: ident * funspec :=
 DECLARE _copy_string
  WITH wsh: share, s : val, str : string, gv: globals
  PRE [ _s OF tptr tschar ]
    PROP ()
    LOCAL (temp _s s; gvars gv)
    SEP (string_rep str s; mem_mgr gv)
  POST [ tptr tschar ]
    EX p: val, 
      PROP ()
      LOCAL (temp ret_temp p)
      SEP (string_rep str s; string_rep str p;
             malloc_token Ews (tarray tschar (Z.of_nat(length(str)) + 1)) p;
             mem_mgr gv). 

Definition new_scell_spec: ident * funspec :=
   DECLARE _new_scell
 WITH gv: globals, k: val, str: string, value: V, pnext: val, tl: list (string*V)
 PRE [ _key OF tptr tschar, _value OF tptr tvoid, _next OF tptr t_scell ] 
   PROP()
   LOCAL(gvars gv; temp _key k; temp _value (V_repr value); temp _next pnext)
   SEP(string_rep str k; scell_rep tl pnext; mem_mgr gv)
 POST [ tptr t_scell ] 
   EX p:val,
      PROP() 
      LOCAL(temp ret_temp p) 
      SEP(string_rep str k * scell_rep ((str, value) :: tl) p; mem_mgr gv).

Definition Gprog : funspecs :=
        ltac:(with_library prog [ strcmp_spec; strcpy_spec; strlen_spec;
        stringlist_new_spec; copy_string_spec; new_scell_spec]).


(* --------------------------HELPERS-------------------------- *)


Lemma scell_rep_modus: forall lst1 lst2 q, scell_rep lst1 q * (scell_rep lst1 q -* scell_rep lst2 q) 
      |-- scell_rep lst2 q.
Proof. 
  intros. apply wand_frame_elim'. entailer!.
Qed.

Definition stringlist_hole_rep (lst1: list (string * V)) (lst: stringlist.t V) (p: val) (q: val): mpred :=
  EX cell_ptr: val,
  malloc_token Ews t_stringlist p *
  data_at Ews t_stringlist cell_ptr p *
  (scell_rep lst1 q * (scell_rep lst1 q -* scell_rep (elements lst) cell_ptr)). 

Lemma ascii_range: forall a, 0 <= Z.of_N (Ascii.N_of_ascii a) <= Byte.max_unsigned.
Proof. 
  intros. destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; simpl; rep_omega.
Qed.

Lemma list_byte_eq: forall s str, string_to_list_byte s = string_to_list_byte str <-> s = str.
Proof. 
  split.
  { intros. generalize dependent str. induction s.
  - intros. inversion H. destruct str.
     + auto.
     + inversion H1.
  - intros. destruct str.
     + inversion H.
     + simpl in H. set (b:= Byte.repr (Z.of_N (Ascii.N_of_ascii a))) in *. 
        set (b0:= Byte.repr (Z.of_N (Ascii.N_of_ascii a0))) in *. assert (K: b = b0) by congruence.
        unfold b, b0 in K.
        apply f_equal with (f:= Byte.unsigned) in K. rewrite !Byte.unsigned_repr in K.
        apply N2Z.inj in K.
        apply f_equal with (f:= Ascii.ascii_of_N) in K.
        rewrite !Ascii.ascii_N_embedding in K. f_equal. auto. inversion H. auto.
        apply ascii_range. apply ascii_range. }
  { intros. f_equal. auto. }
Qed.

Lemma notin_lst_find_none:  forall str lst, 
  ~ Raw.PX.In str (elements (elt:=V) lst) -> find (elt:=V) str lst = None.
Proof.
  intros. case_eq (find (elt := V) str lst).
  - intros v hfind%find_2. unfold Raw.PX.In in H. unfold MapsTo in hfind. 
     unfold not in H. exfalso. apply H. exists v. auto.
  - intros. auto.
Qed.


(* ------------------------ BODY PROOFS ------------------------ *)


Lemma body_stringlist_new: semax_body Vprog Gprog f_stringlist_new stringlist_new_spec.
Proof.
  start_function. 
  (* Problem: malloc expects tulong
      Am I just not importing Clightdefs.tulong? *)

  forward_call (t_stringlist, gv).
  { split3; auto. cbn. computable. }
  Intros p. 
  forward_if
    (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_stringlist p * data_at_ Ews t_stringlist p)).
  { destruct eq_dec; entailer. }
  { forward_call tt. entailer. }
  { forward. rewrite if_false by assumption. entailer. }
  { Intros. forward. forward. Exists p. entailer!. 
    unfold stringlist_rep. unfold stringlist.empty. simpl.
    Exists (Vint (Int.repr 0)). entailer!. }
Qed.



Lemma body_copy_string: semax_body Vprog Gprog f_copy_string copy_string_spec.
Proof.
  start_function. forward_call (string_to_list_byte str, s).
  - unfold string_rep. unfold cstring. entailer!. 
    assert (L: Z.of_nat (length str) = Zlength (string_to_list_byte str)).
    { apply length_string_list_byte_eq. }
    rewrite L. entailer!. 
  - forward. sep_apply cstring_local_facts. Intros.
     forward_call (tarray tschar (Z.of_nat(length(str)) + 1), gv).
    + unfold cstring. simpl. entailer!. rewrite length_string_list_byte_eq. auto.
    + split; auto. assert (M: 0 <= Zlength (string_to_list_byte str)). 
        apply Zlength_nonneg. rewrite sizeof_tarray_tschar; auto; 
        rewrite length_string_list_byte_eq. 
        split. omega.
        rewrite <- initialize.max_unsigned_modulus in H. omega.
        omega.
    + autorewrite with norm. Intros p. forward_if (p <> nullval).
        if_tac; entailer!.
       * rewrite if_true by auto. forward_call tt. entailer!.
       * forward. entailer!.
       * Intros. rewrite if_false by auto.
          forward_call (p, Z.of_nat (length str) + 1, s, string_to_list_byte str).
         { entailer!. }
         { rewrite length_string_list_byte_eq; omega. }
         { forward. Exists p. entailer!. 
           unfold cstringn, cstring, string_rep; entailer!.
           autorewrite with sublist. rewrite <- length_string_list_byte_eq.
           assert (K: Z.of_nat (length str) - Z.of_nat (length str) = 0).
          { induction str; auto. unfold length; fold length. omega. }
          rewrite K. rewrite list_repeat_0. autorewrite with sublist. entailer!. }
Qed.

Lemma body_new_scell: semax_body Vprog Gprog f_new_scell new_scell_spec.
Proof.
  start_function. 
  forward_call (t_scell, gv).
  { now compute. }
  Intros p. forward_if (p <> nullval).
  if_tac; entailer!.
  - forward_call tt. entailer!.
  - forward. entailer!.
  - Intros. rewrite if_false by auto. Intros.
     forward_call (Ews, k, str, gv).
     Intros cp. forward. forward. forward. forward.
     Exists p. entailer!. unfold scell_rep at 2; fold scell_rep.
     Exists pnext cp. entailer!.
Qed.



