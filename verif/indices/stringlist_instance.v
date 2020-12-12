Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.stringlist.
Require Import indices.unordered_interface.
Require Import indices.unordered_flat.
Require Import indices.verif_stringlist.
Require Import indices.definitions.

Import UnorderedIndex.

Lemma in_whole_in_fst: forall a l,
  SetoidList.InA (stringlist_model.Raw.PX.eqk (elt:=V)) a l -> In (fst a) (map fst l).
Proof. 
  intros. induction l.
  - inversion H; inversion H0; inversion H2.
  - simpl. apply SetoidList.InA_cons in H. inversion H; clear H.
     + left. destruct a, a0. inversion H0. simpl in H. subst. auto.
     + right. auto.
Qed. 

Lemma notin_whole_notin_fst:  forall a l,
   ~SetoidList.InA (stringlist_model.Raw.PX.eqk (elt:=V)) a l -> ~In (fst a) (map fst l).
Proof.
  intros. induction l.
  - unfold not. intros. inversion H0.
  - simpl.
     rewrite SetoidList.InA_cons in H.
     apply Classical_Prop.not_or_and in H.
     apply Classical_Prop.and_not_or. split.
     + inversion H; clear H. 
        unfold stringlist_model.Raw.PX.eqk in H0. auto.
     + inversion H; clear H. auto.
Qed.

Lemma lstnodup: forall lst, NoDup (map fst (stringlist_model.elements (elt:=V) lst)).
Proof. 
  intros. assert 
  (K: SetoidList.NoDupA (stringlist_model.Raw.PX.eqk (elt:=V)) (stringlist_model.this lst)).
  apply stringlist_model.NoDup.
  assert (M: (stringlist_model.this lst) = (stringlist_model.elements (elt:=V) lst)) by auto.
  rewrite M in K. clear M.
  induction (stringlist_model.elements (elt:=V) lst); auto.
  - simpl. apply NoDup_nil.
  - simpl. inversion K; subst. apply IHl in H2.
     apply NoDup_cons; auto. clear H2 K IHl.
     apply notin_whole_notin_fst. auto.
Qed.

Definition stringlist_index : index :=
  {| key := stringlist_model.key;
     eq_dec_key := Str_as_DT.eq_dec;
     default_key := ""%string;
     key_repr := fun sh s p => string_rep s p;
     key_type := tschar;

     default_value := nullV;

     t := stringlist_model.t V;
     t_repr := fun sh lst p => stringlist_rep lst p;
     t_type := t_stringlist;
     
     create := stringlist_model.empty V;

     cursor_repr := fun mc p => stringlist_cursor_rep mc p;

     flatten := fun lst => mk_flat _  (stringlist_model.elements (elt:=V) lst) (lstnodup lst);
     
     insert := fun t k v => stringlist_model.add k v t;

   |}.

Definition create_funspec := create_spec(stringlist_index).
Definition stringlist_create_spec := (_stringlist_new, create_funspec).

Definition lookup_funspec := lookup_spec(stringlist_index).
Definition stringlist_lookup_spec := (_stringlist_lookup, lookup_funspec).

Definition insert_funspec := insert_spec(stringlist_index).
Definition stringlist_insert_spec := (_stringlist_insert, insert_funspec).

Definition malloc_funspec := malloc_spec'.
Definition malloc_spec := (_malloc, malloc_funspec).

Definition exit_funspec := exit_spec'.
Definition exit_spec := (_exit, exit_funspec).

Definition cardinality_funspec := cardinality_spec(stringlist_index).
Definition stringlist_cardinality_spec := (_stringlist_cardinality, cardinality_funspec).

Definition move_to_first_funspec := move_to_first_spec(stringlist_index).
Definition stringlist_move_to_first_spec := (_stringlist_move_to_first, move_to_first_funspec).

Definition move_to_next_funspec := move_to_next_spec(stringlist_index).
Definition stringlist_move_to_next_spec := (_stringlist_move_to_next, move_to_next_funspec).

Definition get_cursor_funspec := get_cursor_spec(stringlist_index).
Definition stringlist_get_cursor_spec := (_stringlist_get_cursor, get_cursor_funspec).

Definition Gprog : funspecs := [ new_scell_spec; strcmp_spec; malloc_spec;
    exit_spec; stringlist_create_spec; stringlist_lookup_spec; stringlist_insert_spec;
    stringlist_cardinality_spec; stringlist_move_to_first_spec;
    stringlist_move_to_next_spec; stringlist_get_cursor_spec].

(* ==================== HELPERS ==================== *)

Definition strlst_rep (add: val) (cellptr: val) (lst: list(string*V)) :=
  (data_at Ews (tptr t_scell) cellptr add * scell_rep lst cellptr)%logic.

Lemma not_stringlist_raw_in_inv :
  forall (elt : Type) (k k' : string) (e : elt) (l : list (string * elt)),
  ~stringlist_model.Raw.PX.In k ((k', e) :: l) -> ~(k = k' \/ stringlist_model.Raw.PX.In k l).
Proof.
  intros. 
  unfold not. intros. apply H. inversion H0.
  - rewrite H1 in H. unfold not in H. unfold stringlist_model.Raw.PX.In in H.
     exfalso. apply H. exists e. auto.
  - exfalso. unfold not in H. apply H. unfold stringlist_model.Raw.PX.In in *.
     inversion H1. exists x. auto.
Qed.

Lemma notin_lst_add_end: forall lst k (v: V),
  ~stringlist_model.Raw.PX.In k lst ->
  lst ++ [(k, v)] = stringlist_model.Raw.add k v lst.
Proof.
  intros. induction lst; try auto.
  simpl. destruct a. apply not_stringlist_raw_in_inv in H.
  apply Decidable.not_or in H. inversion H; clear H.
  destruct (Str_as_DT.eq_dec k s); try contradiction.
  apply IHlst in H1. rewrite H1. auto.
Qed.

Lemma notin_lst_add_middle: forall lst1 lst2 k (v: V) (v0: V),
  ~stringlist_model.Raw.PX.In k lst1 ->
  lst1 ++ (k, v) :: lst2 = stringlist_model.Raw.add k v (lst1 ++ (k, v0) :: lst2).
Proof.
  intros. induction lst1.
  - simpl. destruct (Str_as_DT.eq_dec k k); try auto.
     unfold not in n. unfold Str_as_DT.eq in n. contradiction.
  - simpl. destruct a. apply not_stringlist_raw_in_inv in H.
     apply Decidable.not_or in H. inversion H; clear H.
     destruct (Str_as_DT.eq_dec k s); try contradiction.
     apply IHlst1 in H1. rewrite H1. auto.
Qed.

Require Import Coq.Program.Equality. 
Lemma stringlistfind_eq_find: forall m k,
  find Str_as_DT.eq_dec (stringlist_model.elements (elt:=V) m) k =
  stringlist_model.find (elt:=V) k m.
Proof.
  intros. unfold stringlist_model.find. unfold stringlist_model.Raw.find. unfold stringlist_model.Raw.t.
  replace (stringlist_model.this m) with (stringlist_model.elements (elt:=V) m); auto.
  induction (stringlist_model.elements (elt:=V) m); auto.
  destruct a. simpl. destruct (Str_as_DT.eq_dec k0 k).
     + unfold Str_as_DT.eq in e. subst. destruct (Str_as_DT.eq_dec k k); auto.
         unfold Str_as_DT.eq in n. contradiction.
     + destruct (Str_as_DT.eq_dec k k0). unfold Str_as_DT.eq in e.
         unfold Str_as_DT.eq in n. symmetry in e. contradiction.
         auto.
Qed.

Lemma find_middle: forall s lst1 lst2 v, ~ In s (map fst lst1 ++ map fst lst2) -> 
                          @find stringlist_model.key V Str_as_DT.eq_dec (lst1 ++ (s, v) :: lst2) s = Some v.
Proof. 
  induction lst1, lst2; intros.
  - simpl. destruct (Str_as_DT.eq_dec s s); auto. unfold Str_as_DT.eq in n. contradiction.
  - simpl. destruct (Str_as_DT.eq_dec s s); auto. unfold Str_as_DT.eq in n. contradiction.
  - remember [] as k. simpl in H. apply Decidable.not_or in H. inversion H; clear H.
     rewrite Heqk in H1.
     eapply (IHlst1 [] v) in H1. simpl.  destruct a. simpl in H0.
     destruct (Str_as_DT.eq_dec k0 s); auto. contradiction. subst. eapply H1.
  - remember (p :: lst2) as k. simpl in H. apply Decidable.not_or in H. inversion H; clear H.
     eapply (IHlst1 k v) in H1. simpl. destruct a. simpl in H0.
     destruct (Str_as_DT.eq_dec k0 s); auto. contradiction.
Qed.

Lemma find_add: forall k v m,
  @find stringlist_model.key V Str_as_DT.eq_dec (stringlist_model.Raw.add k v (stringlist_model.this m)) k = Some v.
Proof. 
  intros. induction (stringlist_model.this m).
  - simpl. destruct (Str_as_DT.eq_dec k k); auto. unfold not in n. 
     unfold Str_as_DT.eq in n. contradiction.
  - simpl. destruct a. destruct (Str_as_DT.eq_dec k s).
     + simpl. destruct (Str_as_DT.eq_dec k k); auto.
        unfold not in n. unfold Str_as_DT.eq in n. contradiction.
     + simpl. destruct (Str_as_DT.eq_dec s k). exfalso; apply n; auto.
        rewrite IHt0. auto.
Qed.

Lemma list_byte_neq: forall s str, 
  string_to_list_byte s <> string_to_list_byte str -> s <> str.
Proof.
  intros. generalize dependent str. induction s.
  - unfold not. intros. apply H. apply list_byte_eq in H0. auto.
  - unfold not. intros. apply H. apply list_byte_eq. auto.
Qed.

Lemma notin_cons: forall k lst k0 (v0: V),
  ~ stringlist_model.Raw.PX.In k lst ->
  k0 <> k ->
  ~ stringlist_model.Raw.PX.In k (lst ++ [(k0, v0)]).
Proof.
  intros. destruct lst.
  - simpl. unfold stringlist_model.Raw.PX.In. unfold not. intros.
     inversion H1. inversion H2; subst.
     + inversion H4. simpl in H3. symmetry in H3. contradiction.
     + inversion H4.
  - simpl. unfold stringlist_model.Raw.PX.In. unfold not. intros.
     inversion H1; clear H1. inversion H2; subst.
     + inversion H3. destruct p; simpl in *; subst. apply H.
         unfold stringlist_model.Raw.PX.In. exists v. auto.
     + clear H3.
         apply H. unfold stringlist_model.Raw.PX.In. exists x.
         unfold stringlist_model.Raw.PX.MapsTo in *.
         apply 
         (@SetoidList.InA_app _ (stringlist_model.Raw.PX.eqke (elt:=V)) (p::lst) ([(k0,v0)]) (k, x)) 
         in H2. inversion H2; clear H2; auto.
         unfold not in H0. inversion H1; subst; inversion H3; subst; simpl in *.
         symmetry in H2. contradiction.
Qed.

Lemma data_at_stringlist_ptr: forall cell_ptr p,
  data_at Ews t_stringlist cell_ptr p |-- data_at Ews (tptr t_scell) cell_ptr p.
Proof. 
  intros. unfold_data_at (data_at _ _ _ p). rewrite field_at_data_at.
  unfold field_address. if_tac; simpl; auto.
  * entailer!.
  * entailer!. apply field_compatible_isptr in H0. inversion H0.
Qed.

(* ==================== GET CURSOR ==================== *)

Definition undef_cursor (p vret : val) : mpred :=
  (malloc_token Ews t_cursor vret * data_at Ews t_cursor (p, Vundef) vret)%logic. 

Lemma body_stringlist_get_cursor: semax_body Vprog Gprog 
    f_stringlist_get_cursor stringlist_get_cursor_spec.
Proof.
  unfold stringlist_get_cursor_spec. unfold get_cursor_funspec.
  unfold get_cursor_spec. start_function.
  simpl. Intros. forward. forward_call (t_cursor, gv).
  { split; try auto; try omega. simpl. easy. }
  { Intros vret. autorewrite with norm. 
    forward_if (vret <> nullval). if_tac; entailer!.
    { rewrite if_true by auto. forward_call 1. entailer!. }
    { forward. entailer!. }
    { Intros. rewrite if_false by auto. Intros. forward.
      simpl. 
      forward_loop 
      (EX lst1: list (string * V), EX lst2: list (string * V), EX p0: val,
      PROP( lst1 ++ lst2 = stringlist_model.elements m /\ 
                not (stringlist_model.Raw.PX.In k lst1)) 
      LOCAL(temp _mc vret; temp _cur (Vptrofs(Ptrofs.repr(Zlength(lst1)))); 
                 gvars gv; temp _p p; temp _key q; temp _q p0)
      SEP(mem_mgr gv;
            stringlist_hole_rep lst2 m p p0 * string_rep k q *
            undef_cursor p vret))
      (* break cond *)
      break: 
      (EX lst2: list (string * V), EX p0: val, PROP ( )
      LOCAL (temp _mc vret; temp _cur (Vlong (Int64.repr 0)); 
                  gvars gv; temp _p p; temp _key q; temp _q p0)
      SEP (mem_mgr gv; stringlist_hole_rep lst2 m p p0; 
             string_rep k q; undef_cursor p vret)).
      { unfold stringlist_rep. Intros cell_ptr. forward.
        Exists (@nil (string * V)) (stringlist_model.elements m).
        Exists cell_ptr.
        unfold stringlist_hole_rep.
        Exists cell_ptr. autorewrite with sublist. entailer!.
        { inversion H8. inversion H9. }
        { unfold undef_cursor.  cancel. apply wand_refl_cancel_right. }}
      { Intros lst1 lst2 p0. forward_if (p0 <> nullval).
        { unfold stringlist_hole_rep. Intros cell_ptr. entailer!. }
        { forward. entailer!. }
        { forward. Exists lst2 p0. entailer!. admit. }
        { destruct lst2.
          { unfold stringlist_hole_rep. Intros cell_ptr.
            unfold scell_rep; fold scell_rep. Intros. contradiction. }
          { unfold stringlist_hole_rep. Intros cell_ptr. destruct p1.
            unfold scell_rep at 1; fold scell_rep. Intros q0 str_ptr.
            forward. 
            forward_call (str_ptr, string_to_list_byte s, q, string_to_list_byte k).
            { unfold cstring. unfold string_rep.
              repeat rewrite length_string_list_byte_eq. cancel. }
            Intros vret0. forward_if. destruct Int.eq_dec in H3.
            { unfold undef_cursor. Intros. forward. forward.
              Exists vret. unfold cursor. Exists (m, 0). entailer!.
              simpl t_repr. simpl key_repr. simpl cursor_repr.
              unfold string_rep. unfold cstring at 2. repeat rewrite length_string_list_byte_eq.
              cancel. unfold stringlist_rep. Exists cell_ptr. cancel.
              unfold stringlist_cursor_rep. Exists p. cancel.
              apply wand_sepcon_adjoint.
              assert (K: (cstring Ews (string_to_list_byte s) str_ptr * malloc_token Ews t_scell p0 *
                 data_at Ews t_scell (str_ptr, (V_repr v, q0)) p0 *
                 malloc_token Ews (tarray tschar (Zlength (string_to_list_byte s) + 1)) str_ptr *
                 scell_rep lst2 q0)%logic |-- 
                 scell_rep ((s, v) :: lst2) p0).
                 { unfold scell_rep at 2; fold scell_rep. Exists q0 str_ptr.
                   unfold cstring. unfold string_rep. rewrite length_string_list_byte_eq.
                   cancel. }
              sep_apply K. apply wand_sepcon_adjoint. admit. 
              (* apply modus_ponens_wand. *) }
            { unfold not in n. contradiction. }
            { forward. forward. Exists (lst1 ++ [(s, v)]) lst2. Exists q0.
              entailer!. 
              { repeat split. 
                 { rewrite <- H0. rewrite app_assoc_reverse. simpl. auto. }
                 { destruct (Int.eq_dec vret0 Int.zero) in H3.
                   contradiction. unfold not. intros. unfold stringlist_model.Raw.PX.In in H15. 
                   unfold stringlist_model.Raw.PX.In in H1. unfold not in H1.
                   unfold stringlist_model.Raw.PX.MapsTo in H15. inversion H15. 
                   rewrite SetoidList.InA_app_iff in H16. inversion H16.
                   { unfold stringlist_model.Raw.PX.MapsTo in H1. apply H1. exists x. auto. }
                   { inversion H17. inversion H19. simpl in H21. rewrite H21 in H3. 
                      contradiction. inversion H19. }}
                   { admit. }}
               { admit. }}}}}
      { Intros lst2 p0. unfold undef_cursor. Intros. forward. forward.
        Exists vret (m, 0). entailer!. simpl. cancel. unfold stringlist_cursor_rep.
        Exists p. cancel. unfold stringlist_hole_rep. Intros cell_ptr.
        unfold stringlist_rep at 1. Exists cell_ptr. cancel. admit.
        (* apply modus_ponens_wand. *)  } 

(* need to fix the double definition of stringlist and also the cursor number *)
Admitted.



(* ==================== MOVE TO NEXT ==================== *)

Lemma body_stringlist_move_to_next: semax_body Vprog Gprog 
    f_stringlist_move_to_next stringlist_move_to_next_spec.
Proof. 
  unfold stringlist_move_to_next_spec. unfold move_to_next_funspec.
  unfold move_to_next_spec. start_function. 
  forward. simpl. unfold stringlist_cursor_rep. Intros strlst_p.
  sep_apply stringlist_rep_local_facts.
  simpl. forward.
  forward. forward_call (sh, strlst_p, m).
    { simpl. entailer!. }
    { forward. autorewrite with norm.
      remember (Int64.repr (prevcur + 1)) as nextcur.
      remember (Int64.repr (Zlength (elements (flatten stringlist_index m)))) as length.
      remember (Int64.ltu nextcur length) as cond1.
      remember (Int64.ltu (Int64.repr 0) nextcur) as cond2.
      remember (andb cond1 cond2) as condition.
      forward_if
        (PROP ( )
        LOCAL (temp _cur (Vlong nextcur);
                    temp _length (Vlong length); temp _lst strlst_p; 
                    temp _mc p; temp _mcc p; temp _t'2 (if condition then Vtrue else Vfalse))
        SEP (t_repr stringlist_index sh m strlst_p; mem_mgr gv;
               malloc_token Ews t_cursor p;
               data_at Ews t_cursor (strlst_p, Vlong (Int64.repr prevcur)) p)).
      { forward. entailer!. unfold cardinality in H.
        rewrite H. simpl. unfold Val.of_bool. auto. }
      { forward. entailer!. unfold cardinality in H. rewrite H. simpl. auto. }
      { forward_if
        (PROP ( )
        LOCAL (temp _cur (Vlong nextcur); temp _length (Vlong length);
                    temp _lst strlst_p; temp _mc p; temp _mcc p;
                    temp _t'2 (if condition then Vtrue else Vfalse))
        SEP (mem_mgr gv;
         cursor_repr stringlist_index
           (move_to_next stringlist_index (m, prevcur)) p)).
      destruct condition.
        { forward. entailer!.
          assert (K: (move_to_next stringlist_index (m, prevcur)) = (m, prevcur+1)).
          { simpl in *. rewrite <- Heqcondition. auto. }
          rewrite K. simpl. unfold stringlist_cursor_rep.
          Exists strlst_p. entailer!. }
        { inversion H. }
        { forward. entailer!. 
          assert (K: (move_to_next stringlist_index (m, prevcur)) = (m, 0)).
          { simpl in *. rewrite H. auto. }
          rewrite K. simpl. unfold stringlist_cursor_rep.
          Exists strlst_p. entailer!. } 
       forward. Exists p. entailer!. }}
Qed.


(* ==================== MOVE TO FIRST ==================== *)

Lemma body_stringlist_move_to_first: semax_body Vprog Gprog 
    f_stringlist_move_to_first stringlist_move_to_first_spec.
Proof. 
  unfold stringlist_move_to_first_spec. unfold move_to_first_funspec.
  unfold move_to_first_spec. start_function. 
  forward. simpl. unfold stringlist_cursor_rep. Intros strlst_p.
  simpl.
  forward. forward. Exists p. simpl. unfold stringlist_cursor_rep.
  entailer!. Exists strlst_p. simpl. entailer!.
Qed.


(* ================== CARDINALITY ================== *)


Lemma body_stringlist_cardinality: semax_body Vprog Gprog 
    f_stringlist_cardinality stringlist_cardinality_spec.
Proof. 
  unfold stringlist_cardinality_spec. unfold cardinality_funspec.
  unfold cardinality_spec. start_function. 
  forward. simpl. unfold stringlist_rep. Intros cell_ptr.
  simpl in m.  
  (* invariant *)
   forward_loop 
  (EX lst1: list (string * V), EX lst2: list (string * V), EX p0: val,
  PROP( lst1 ++ lst2 = stringlist_model.elements m) 
  LOCAL(temp _q p0; temp _size (Vptrofs (Ptrofs.repr (Zlength(lst1)))); temp _p p)
  SEP(stringlist_hole_rep lst2 m p p0))
  (* break cond *)
  break: 
  (PROP () 
  LOCAL(temp _size (Vptrofs (Ptrofs.repr (Zlength(stringlist_model.elements m)))))
  SEP((stringlist_rep m p))).
  (* holds on entry *)
  - forward.
     Exists (@nil (string * V)) (stringlist_model.elements m) cell_ptr.
     entailer!. unfold stringlist_hole_rep. Exists cell_ptr. entailer!.
     apply wand_refl_cancel_right.
  (* holds on iteration *)
  - Intros lst1 lst2 p0. unfold stringlist_hole_rep.
     Intros cp0. forward_if (p0 <> nullval).
     { forward. entailer!. }
     { forward. autorewrite with norm. 
       entailer!.
       { assert (K: nullval = nullval) by auto.  apply H4 in K.
         subst. rewrite <- H. autorewrite with sublist. auto. }
       unfold stringlist_rep. Exists cp0.
       cancel. apply modus_ponens_wand. }
      { forward. autorewrite with norm. destruct lst2.
        (* lst2 empty *)
       { unfold scell_rep; fold scell_rep. Intros. contradiction. }
         (* lst2 not empty *)
       { destruct p1.
         unfold scell_rep at 1; fold scell_rep. Intros q0 str_ptr.
         forward. entailer!.
         Exists (lst1 ++ [(s,v)]) lst2 q0. entailer!.
         split.
         { rewrite app_assoc_reverse. simpl. auto. }
         { f_equal. f_equal. rewrite Zlength_app. easy. }
         unfold stringlist_hole_rep. Exists cp0. 
         entailer!. apply wand_frame_intro'.
         apply wand_sepcon_adjoint. apply wand_frame_intro'. 
         assert (W: (malloc_token Ews t_scell p0 * 
                         data_at Ews t_scell (str_ptr, (V_repr v, q0)) p0 *
                         string_rep s str_ptr *
                         malloc_token Ews (tarray tschar (Z.of_nat (length s) + 1)) str_ptr * 
                         scell_rep lst2 q0)%logic |-- scell_rep ((s, v) :: lst2) p0).
         { unfold scell_rep at 2; fold scell_rep. Exists q0 str_ptr. cancel. }
         sep_apply W. sep_apply modus_ponens_wand. cancel. }}
 - autorewrite with norm. forward. 
Qed.



(* ==================== LOOKUP ==================== *)

Lemma body_stringlist_lookup: semax_body Vprog Gprog 
    f_stringlist_lookup stringlist_lookup_spec.
Proof. unfold stringlist_lookup_spec. unfold lookup_funspec. unfold lookup_spec.
  start_function. simpl. remember m as lst. remember k as str.
  (* loop invariant *)
  forward_loop 
  (EX lst1: list (string * V), EX lst2: list (string * V), EX p0: val,
  PROP( lst1 ++ lst2 = stringlist_model.elements lst /\ not (stringlist_model.Raw.PX.In str lst1)) 
  LOCAL(temp _q p0; temp _key q)
  SEP(mem_mgr gv; stringlist_hole_rep lst2 lst p p0 * string_rep str q))
  (* break cond *)
  break: 
  (PROP (nullval = proj1_sig (lookup stringlist_index m k)) 
  LOCAL()
  SEP((mem_mgr gv * stringlist_rep lst p * string_rep str q))).
 (* invariant holds entering loop*) 
  - unfold stringlist_rep. Intros cell_ptr. forward. 
     Exists (@nil (string * V)) (stringlist_model.elements lst).
     Exists cell_ptr.
     unfold stringlist_hole_rep.
     Exists cell_ptr. autorewrite with sublist. entailer!.
     { inversion H4. inversion H5. }
     { apply wand_refl_cancel_right. }
  (* invariant holds in the loop *)
  - Intros lst1 lst2 p0. forward_if (p0 <> nullval).
    { unfold stringlist_hole_rep. Intros cell_ptr. entailer!. }
    { forward. entailer!. }
    { (* break inv used *) unfold stringlist_hole_rep. Intros cell_ptr.
      rewrite H1.  forward. entailer!.
      { assert (K: nullval = nullval). auto. apply H5 in K. 
        subst. autorewrite with sublist in H.
        rewrite H in H0. replace (lookup stringlist_index m k) with nullV; auto.
        unfold lookup. simpl. simpl in k. simpl in m. apply notin_lst_find_none in H0.
        assert 
        (P: @find stringlist_model.key V Str_as_DT.eq_dec (stringlist_model.elements (elt:=V) m) k = None).
        { rewrite <- H0.
          apply stringlistfind_eq_find. }
          rewrite P; auto. }
        { unfold stringlist_rep. Exists cell_ptr. cancel.
         apply modus_ponens_wand. }}
    { destruct lst2. 
        (* lst2 empty *)
       { unfold stringlist_hole_rep. Intros cell_ptr.
         unfold scell_rep; fold scell_rep. Intros. contradiction. }
         (* lst2 not empty *)
       { unfold stringlist_hole_rep. Intros cell_ptr. destruct p1.
         unfold scell_rep at 1; fold scell_rep. Intros q0 str_ptr.
         forward. 
         forward_call (str_ptr, string_to_list_byte s, q, string_to_list_byte str).
         { unfold cstring. unfold string_rep.
           repeat rewrite length_string_list_byte_eq. cancel. }
         Intros vret. forward_if.
         { destruct (Int.eq_dec vret Int.zero) in H2.
           { forward.
              { unfold V in v. entailer!.
                destruct v. auto. }
              { forward. entailer!.
                { assert (M: lookup stringlist_index m k = v).
                  { apply list_byte_eq in H2; rewrite <- H2. unfold lookup. simpl in k. simpl in m.
                    assert (K: stringlist_model.elements m = (elements (flatten stringlist_index m))) by auto.
                    rewrite <- K. rewrite <- H. simpl.
                    assert 
                    (P: @find stringlist_model.key V Str_as_DT.eq_dec (lst1 ++ (s, v) :: lst2) s 
                     = (Some v)).
                    { assert (W: NoDup (map fst (stringlist_model.elements (elt:=V) m))).
                      apply lstnodup. rewrite <- H in W. rewrite map_app in W. simpl in W. 
                      apply (@NoDup_remove_2 string (map fst (lst1)) (map fst (lst2)) s) in W.
                      apply find_middle; auto. }
                    rewrite P. auto. } rewrite M; simpl; auto. } 
                 simpl t_repr. simpl key_repr. unfold string_rep. unfold cstring at 2. rewrite length_string_list_byte_eq.
                 cancel. unfold stringlist_rep. Exists cell_ptr. cancel.
                 apply wand_sepcon_adjoint.
                 assert (K: (cstring Ews (string_to_list_byte s) str_ptr * malloc_token Ews t_scell p0 *
                 data_at Ews t_scell (str_ptr, (V_repr v, q0)) p0 *
                 malloc_token Ews (tarray tschar (Zlength (string_to_list_byte s) + 1)) str_ptr *
                 scell_rep lst2 q0)%logic |-- 
                 scell_rep ((s, v) :: lst2) p0).
                 { unfold scell_rep at 2; fold scell_rep. Exists q0 str_ptr.
                   unfold cstring. unfold string_rep. rewrite length_string_list_byte_eq.
                   cancel. }
                  sep_apply K. apply wand_sepcon_adjoint. apply modus_ponens_wand. }}
           { contradiction. }}
          { destruct (Int.eq_dec vret Int.zero) in H2.
            contradiction.
            abbreviate_semax. forward. Exists (lst1 ++ [(s, v)]) lst2.
            Exists q0. entailer!.
            { split.
              { rewrite <- H. rewrite app_assoc_reverse. simpl. auto. }
              { unfold not. intros. unfold stringlist_model.Raw.PX.In in H14. 
                unfold stringlist_model.Raw.PX.In in H0. unfold not in H0.
                unfold stringlist_model.Raw.PX.MapsTo in H14. inversion H14. 
                rewrite SetoidList.InA_app_iff in H15. inversion H15.
                { unfold stringlist_model.Raw.PX.MapsTo in H0. apply H0. exists x. auto. }
                { inversion H16. inversion H18. simpl in H20. rewrite H20 in H2. 
                  contradiction. inversion H18. }}}
             { unfold string_rep. unfold cstring at 2. rewrite length_string_list_byte_eq.
               cancel. unfold stringlist_hole_rep. Exists cell_ptr. 
               entailer!. apply wand_frame_intro'.
               apply wand_sepcon_adjoint. apply wand_frame_intro'.
               assert (K: (cstring Ews (string_to_list_byte s) str_ptr * malloc_token Ews t_scell p0 *
               data_at Ews t_scell (str_ptr, (V_repr v, q0)) p0 *
               malloc_token Ews (tarray tschar (Zlength (string_to_list_byte s) + 1)) str_ptr * 
               scell_rep lst2 q0)%logic |-- 
               scell_rep ((s, v) :: lst2) p0).
               { unfold scell_rep at 2; fold scell_rep. Exists q0 str_ptr.
                 unfold cstring. unfold string_rep. rewrite length_string_list_byte_eq.
                 cancel. }
               sep_apply K. apply modus_ponens_wand. }}}}
  (* invariant holds after loop *) (* break inv used *)
  - forward. entailer!. simpl. auto. 
Qed.
  




(* ==================== CREATE ==================== *)

Lemma body_stringlist_create: semax_body Vprog Gprog 
    f_stringlist_new stringlist_create_spec.
Proof. 
  unfold stringlist_create_spec. unfold create_funspec.
  unfold create_spec.
  start_function. 
  forward_call (t_stringlist, gv).
  { split3; auto. cbn. computable. }
  Intros p. 
  forward_if
    (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_stringlist p * data_at_ Ews t_stringlist p)).
  { destruct eq_dec; entailer. }
  { forward_call 1. entailer. }
  { forward. rewrite if_false by assumption. entailer. }
  { Intros. forward. forward. Exists p. Exists (stringlist_model.empty V).
    entailer!. simpl.
    unfold stringlist_rep. unfold stringlist_model.empty. simpl.
    Exists  (Vlong (Int64.repr 0)). entailer!. } 
Qed.

(* ==================== INSERT ==================== *)


Lemma body_stringlist_insert: semax_body Vprog Gprog 
    f_stringlist_insert stringlist_insert_spec.
Proof. 
  unfold stringlist_insert_spec. unfold insert_funspec. unfold insert_spec.
  start_function.
  simpl. Intros. unfold stringlist_rep. forward.
  { Intros cell_ptr. rewrite data_at_isptr. entailer!. }
  remember (offset_val (align 0 (alignof (tptr (Tstruct _scell noattr))))
               mptr) as r.
  (* invariant *)
  forward_loop
  (EX lst1, EX lst2, EX add,
  PROP( lst1 ++ lst2 = stringlist_model.elements m /\ not (stringlist_model.Raw.PX.In k lst1)
            /\ field_compatible t_stringlist [StructField _root] mptr) 
  LOCAL(gvars gv; temp _r add; temp _p mptr; temp _key kptr; temp _value (V_repr v)) 
  SEP(mem_mgr gv; string_rep k kptr; malloc_token Ews t_stringlist mptr;
        EX cp2: val, strlst_rep add cp2 lst2 *
        (ALL lst', ALL cpnew, EX cp', strlst_rep add cpnew lst' -* 
         strlst_rep mptr cp' (lst1 ++ lst')))).
  (* invariant holds on entry *)
  - entailer!. Exists (@nil (string * V)) (stringlist_model.elements m) mptr.
     simpl. entailer!.
     { inversion H5. inversion H6. }
     { Exists cell_ptr. 
       assert (K: data_at Ews t_stringlist cell_ptr mptr |-- data_at Ews (tptr t_scell) cell_ptr mptr).
       { unfold_data_at (data_at _ _ _ mptr). rewrite field_at_data_at.
         unfold field_address. if_tac; simpl; auto.
         * entailer!.
         * entailer!. apply field_compatible_isptr in H6. inversion H6. }
       sep_apply K. clear K. unfold strlst_rep at 1. cancel.
       apply allp_right. intro. apply allp_right. intro. Exists v1.
       apply wand_refl_cancel_right. }
  (* invariant holds after *) 
  - Intros lst1 lst2 addr. Intros cellptr2. clear Heqr. unfold strlst_rep at 1. Intros.
     forward. sep_apply scell_rep_local_facts. forward_if. 
     (* if list empty *)
     +  rewrite H2. sep_apply string_rep_local_facts. Intros.
         (* we know 2nd part is empty *)
         assert (M: nullval = nullval) by auto. 
         apply H4 in M. rewrite M.
         (* create new cell with (k,v) *) 
         forward_call (gv, kptr, k, v, nullval, (@nil (string * V))).
         Intros vret. forward. forward. Exists (stringlist_model.add k v m). entailer!. 
         split. 
           { unfold lookup. simpl.
             rewrite find_add. auto. }
           { (* prove return null *) unfold lookup. simpl. 
             rewrite stringlistfind_eq_find. assert (W: stringlist_model.find (elt:=V) k m = None).
             { apply notin_lst_find_none. rewrite <- H. autorewrite with sublist. auto. }
             rewrite W. auto. }
           { simpl t_repr. simpl key_repr. unfold stringlist_rep. 
             allp_left [(k, v)]. allp_left vret. Intros cp'. Exists cp'.
             entailer!.
             rewrite sepcon_assoc. rewrite sepcon_comm.
             replace (scell_rep [(k, v)] vret * data_at Ews (tptr t_scell) vret addr)%logic
             with (strlst_rep addr vret [(k,v)]). sep_apply modus_ponens_wand.
             replace (@stringlist_model.elements V (@stringlist_model.add V k v m)) with (lst1 ++ [(k, v)]).
             unfold strlst_rep; entailer!.
             assert (K: data_at Ews (tptr t_scell) cp' mptr |-- data_at Ews t_stringlist cp' mptr).
            { (* this is where we need the extra premise of field_compatible *)
              unfold_data_at (data_at _ t_stringlist _ mptr). rewrite field_at_data_at.
              unfold field_address. if_tac; simpl; auto.
              * entailer!. * contradiction. } 
             sep_apply K. clear K. entailer!. 
            { autorewrite with sublist in H. simpl. unfold stringlist_model.elements in H.
              unfold stringlist_model.Raw.elements in H. rewrite <- H.
              apply (@notin_lst_add_end lst1 k v) in H0.
              rewrite <- H0. reflexivity. }
            { unfold strlst_rep. apply sepcon_comm. }}
             
      (* if list nonempty *)
      + simpl. destruct lst2.
          { Intros. assert (M: @nil (string * V) = @nil (string * V)); auto.
            apply H3 in M. contradiction. }
          { unfold scell_rep; fold scell_rep. destruct p. Intros q str_ptr.
            forward.
            forward_call (str_ptr, string_to_list_byte k0, kptr, string_to_list_byte k).
            { unfold string_rep. unfold cstring. rewrite length_string_list_byte_eq.
              entailer!. rewrite length_string_list_byte_eq. entailer!. }
            Intros vret. forward_if.
            { destruct (Int.eq_dec vret Int.zero); try contradiction.
              apply list_byte_eq in H4; subst. forward.
              { entailer!. unfold V in v0. destruct v0. auto. }
              { forward. forward. Exists (stringlist_model.add k v m).
                simpl. entailer!.
                { unfold lookup. simpl. rewrite <- H. simpl in k.
                  assert 
                  (P: @find stringlist_model.key V Str_as_DT.eq_dec (lst1 ++ (k, v0) :: lst2) k 
                         = (Some v0)).
                        { assert (W: NoDup (map fst (stringlist_model.elements (elt:=V) m))).
                          apply lstnodup. rewrite <- H in W. rewrite map_app in W. simpl in W. 
                          apply (@NoDup_remove_2 string (map fst (lst1)) (map fst (lst2)) k) in W.
                          apply find_middle; auto. }
                  rewrite P. split; auto. rewrite find_add. auto. }  
                unfold string_rep. unfold cstring at 2. 
                rewrite length_string_list_byte_eq. cancel.
                unfold stringlist_rep. 
                unfold strlst_rep. allp_left ((k, v) :: lst2).
                allp_left cellptr2. Intros cp'. Exists cp'. cancel. 
                assert (M: (cstring Ews (string_to_list_byte k) str_ptr *
                malloc_token Ews t_scell cellptr2 *
                data_at Ews t_scell (str_ptr, (V_repr v, q)) cellptr2 * 
                malloc_token Ews (tarray tschar (Zlength (string_to_list_byte k) + 1)) str_ptr *
                scell_rep lst2 q)%logic
                |-- scell_rep ((k, v) :: lst2) cellptr2).
                { unfold scell_rep at 2; fold scell_rep. Exists q str_ptr. 
                  cancel. unfold cstring. unfold string_rep.
                  rewrite length_string_list_byte_eq. entailer!. }
                sep_apply M. rewrite sepcon_comm.
                rewrite sepcon_assoc. 
                remember (data_at Ews (tptr t_scell) cellptr2 addr * 
                scell_rep ((k, v) :: lst2) cellptr2)%logic as P.
                remember (data_at Ews (tptr t_scell) cp' mptr * 
                scell_rep (lst1 ++ (k, v) :: lst2) cp')%logic as Q.
                sep_apply wand_frame_elim''. subst Q. clear HeqP.
                assert (K: data_at Ews (tptr t_scell) cp' mptr  |-- data_at Ews t_stringlist cp' mptr).
                { unfold_data_at (data_at _ t_stringlist _ mptr). rewrite field_at_data_at.
                  unfold field_address. if_tac; simpl; auto.
                  * entailer!. * contradiction. }
                sep_apply K; clear K; cancel. unfold key. 
                replace (@stringlist_model.elements V (@stringlist_model.add V k v m))
                with (lst1 ++ (k, v) :: lst2).
                entailer!. simpl.
                unfold stringlist_model.elements in H.
                unfold stringlist_model.Raw.elements in H. clear M. clear P. clear H3. 
                rewrite <- H.
                apply notin_lst_add_middle. auto. }}
              { forward. entailer!.
                Exists (lst1 ++ [(k0,v0)]) lst2 (offset_val 16 cellptr2) q. entailer!.
                { split.
                  * rewrite app_assoc_reverse. simpl. rewrite H. auto.
                  * apply notin_cons. auto. destruct (Int.eq_dec vret Int.zero).
                    contradiction. apply list_byte_neq in H4.  auto. }
                unfold cstring at 2. unfold string_rep.
                rewrite length_string_list_byte_eq. entailer!.
                unfold strlst_rep at 3. cancel.
                unfold_data_at (data_at _ _ _ cellptr2).
                rewrite (field_at_data_at' _ _ [StructField _next]). 
                simpl nested_field_type. simpl nested_field_offset.
                entailer!.
                apply allp_right. intro lst'. apply allp_right. intro cpnew.
                allp_left ((k0,v0)::lst').
                allp_left cellptr2. Intros cp'. Exists cp'.
                rewrite <- wand_sepcon_adjoint.
                assert (Q: ((cstring Ews (string_to_list_byte k0) str_ptr *
                (malloc_token Ews t_scell cellptr2 *
                (field_at Ews t_scell [StructField _key] str_ptr cellptr2 *
                (malloc_token Ews
                (tarray tschar (Zlength (string_to_list_byte k0) + 1)) str_ptr * 
                (field_at Ews t_scell [StructField _value] (V_repr v0) cellptr2 *
                data_at Ews (tptr t_scell) cellptr2 addr))))) *
                strlst_rep (offset_val 16 cellptr2) cpnew lst')%logic |-- strlst_rep addr cellptr2 ((k0, v0) :: lst')).
                { unfold strlst_rep. cancel. unfold scell_rep at 2; fold scell_rep.
                  Exists cpnew str_ptr. cancel.
                  unfold cstring. unfold string_rep.
                  rewrite length_string_list_byte_eq. entailer!. 
                  unfold_data_at (data_at _ _ _ cellptr2).
                  rewrite (field_at_data_at _ _ [StructField _next]), field_address_offset.
                  entailer!. auto. } sep_apply Q. sep_apply modus_ponens_wand. 
                rewrite app_assoc_reverse. simpl. entailer!. }}
Qed.


