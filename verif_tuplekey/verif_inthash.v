Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.Address.
Require Import inthash.
Require FMapWeakList.
Require Import Program.Basics. Open Scope program_scope.
Require Import Structures.OrdersEx.

Definition N: Z := 10.
Global Opaque N.
Lemma N_eq: N = 10. reflexivity. Qed.
Hint Rewrite N_eq: rep_omega.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Default Timeout 20. 
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.library.

Definition V := sig is_pointer_or_null.
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

Instance EqDecV: EqDec V.
Proof.
  intros [x hx] [y hy]. destruct (eq_dec x y).
  + left. now apply exist_ext.
  + right. intro hcontr. apply n. exact (f_equal (@proj1_sig _ _) hcontr).
Qed.

Module int_table := FMapWeakList.Make Z_as_DT.

Notation "{{ m }}" := (int_table.this m).

Section IntTable.
  Import int_table.
  Check SetoidList.InA .
  Definition get_buckets (m: t V): list (int_table.Raw.t V) :=
    List.map (fun n => filter (fun kv => eq_dec (fst kv mod N) n) {{ m }}) (upto (Z.to_nat N)).

  Lemma Zlength_get_buckets: forall m, Zlength (get_buckets m) = N.
  Proof.
    intros []. unfold get_buckets.
    rewrite Zlength_map, Zlength_upto. reflexivity.
  Qed.

  Lemma get_buckets_spec (m: t V):
    forall k v, MapsTo k v m <-> SetoidList.InA (eq_key_elt (elt := V)) (k, v) (Znth (k mod N) (get_buckets m)).
  Proof.
    intros.
    unshelve epose proof (Z_mod_lt k N _). rep_omega.
    assert (mapsto_iff: MapsTo k v m <-> SetoidList.InA (@eq_key_elt _) (k, v) (elements m)).
    split; [apply elements_1 | apply elements_2].
    rewrite mapsto_iff. clear mapsto_iff.
    destruct m as [l nodup]. unfold get_buckets.
    rewrite Znth_map, SetoidList.filter_InA, Znth_upto.
    now destruct eq_dec.
    rep_omega.
    intros x y hxy%Raw.PX.eqke_eqk. rewrite hxy; reflexivity.
    rewrite Zlength_upto; rep_omega.
  Qed.

  Lemma add_bucket_Znth: forall key v m,
      let i := key mod N in
      Znth i (get_buckets (add key v m)) = Raw.add key v (Znth i (get_buckets m)).
  Proof.
    intros key v m i.
    assert (0 <= i < N). { unfold i. apply Z_mod_lt. rep_omega. }
    unfold get_buckets.
    do 2 rewrite Znth_map, Znth_upto by (try rewrite Zlength_upto; rep_omega).
    unfold i, int_table.add. cbn.
    symmetry.
    induction {{m}} as [|[k' v'] l]; cbn.
    + rewrite proj_sumbool_is_true; reflexivity.
    + destruct (Z_as_DT.eq_dec key k'). subst key. cbn.
      rewrite proj_sumbool_is_true by reflexivity.
      cbn. destruct Z_as_DT.eq_dec.  reflexivity. contradiction.
      cbn. destruct eq_dec. cbn.
      destruct Z_as_DT.eq_dec. contradiction. f_equal. apply IHl.
      apply IHl.
  Qed.

  Lemma NoDupA_filter: forall (m: t V) (p: Z * V -> bool),
      Proper (eq_key (elt := V) ==> eq) p ->
 SetoidList.NoDupA (int_table.Raw.PX.eqk (elt:=V))
    (filter p (int_table.elements (elt:=V) m)).
  Proof.
    intros [] p h.
    induction this0.
    constructor.
    cbn. destruct p. constructor.
    intros hcontr%SetoidList.filter_InA. now inversion NoDup0.
    assumption.
    unshelve eapply IHthis0. inversion NoDup0. assumption.
    unshelve eapply IHthis0. inversion NoDup0. assumption.
  Qed.
  
  Lemma NoDupA_bucket: forall k m,
    SetoidList.NoDupA (Raw.PX.eqk (elt:=V)) (Znth (k mod N) (get_buckets m)).
  Proof.
    intros k [].
    unfold get_buckets.
    unshelve epose proof (Z_mod_lt k N _). rep_omega.
    rewrite Znth_map, Znth_upto by (try rewrite Zlength_upto; rep_omega). apply NoDupA_filter.
    intros x y <-; reflexivity.
  Qed.

  Definition get_bucket (k: Z) (m: t V): t V :=
    Build_slist (NoDupA_bucket k m).

  Lemma add_buckets: forall k v m,
      let i := k mod N in
      get_buckets (add k v m) =
     upd_Znth i (get_buckets m) (add k v (get_bucket k m)).
  Proof.
    intros k v [l nodup].
    unshelve epose proof (Z_mod_lt k N _). rep_omega.
    unfold get_bucket, get_buckets. 
    rewrite upd_Znth_eq, map_length, upto_length by (rewrite Zlength_map, Zlength_upto; rep_omega).
    cbn. rewrite Znth_map, Znth_upto by (try rewrite Zlength_upto; rep_omega).
    apply list_map_exten. intros x hx%In_upto.
    destruct (eq_dec x (k mod N)). subst.
    { clear nodup.
      rewrite Raw.add_equation. induction l as [|[k' v'] l]; cbn. admit. admit. }
    rewrite Znth_map, Znth_upto by (try rewrite Zlength_upto; assumption).
    admit.
  Admitted.

  Lemma get_buckets_spec' (m: t V):
    forall k v, MapsTo k v m <-> MapsTo k v (get_bucket k m).
  Proof.
    intros. destruct m as [l nodup].
    unshelve epose proof (Z_mod_lt k N _). rep_omega.
    unfold MapsTo, get_bucket, Raw.PX.MapsTo.
    unfold get_buckets, this.
    rewrite Znth_map, SetoidList.filter_InA, Znth_upto; try rewrite Zlength_upto; try rep_omega.
    now destruct eq_dec.
    intros x y hxy%Raw.PX.eqke_eqk. rewrite hxy. reflexivity.
  Qed.

  Lemma find_None: forall m k,
      find k m = None <-> forall v: V, not (MapsTo k v m).
  Proof.
    intros.
    split; intro h.
    + intros v hmapsto%find_1; congruence.
    + case_eq (find (elt := V) k m).
      intros v hfind%find_2. specialize (h v). contradiction.
      easy.
  Qed.

  Corollary find_get_bucket (m: t V):
    forall k, find k m = find k (get_bucket k m).
  Proof.
    intro.
    case_eq (find (elt := V) k m).
    + intros v hv%find_2.
      symmetry. apply find_1. now rewrite <- get_buckets_spec'.
    + intro hnone.
      symmetry. rewrite find_None in hnone |- *.
      intros v hcontr.
      rewrite <- get_buckets_spec' in hcontr.
      now apply (hnone v).
  Qed.

  Lemma MapsTo_inj: forall (m: t V) k v1 v2,
      MapsTo k v1 m -> MapsTo k v2 m -> v1 = v2.
  Proof.
    intros * h1 h2.
    apply find_1 in h1. apply find_1 in h2.
    rewrite h1 in h2. now inv h2.
  Qed.
    

End IntTable.

Definition t_icell := Tstruct _icell noattr.
Definition t_inthash := Tstruct _inthash noattr.

Definition maybe {A: Type} (o: option A) (default: A) :=
  match o with Some a => a | None => default end.

Definition V_repr: V -> val := @proj1_sig _ _.

Fixpoint icell_rep (l: int_table.Raw.t V) (p: val): mpred :=
  match l with
  | [] => !!(p = nullval) && emp
  | (k, v) :: tl => EX q: val,
                    !! (0 <= k < Int.max_unsigned) &&
                       malloc_token Ews t_icell p *
                    data_at Ews t_icell (Vint (Int.repr k), (V_repr v, q)) p *
                    icell_rep tl q
  end.

Definition icell_rep_local_facts:
  forall l p, icell_rep l p |-- !! (is_pointer_or_null p /\ (p=nullval <-> l = [])).
Proof.
  intros l. induction l as [ | [] tl]; intro p; simpl.
  + entailer!. easy.
  + Intros q. entailer!. now apply field_compatible_nullval1 in H1.
Qed.
Hint Resolve icell_rep_local_facts: saturate_local.

Definition icell_rep_valid_pointer:
  forall l p, icell_rep l p |-- valid_pointer p.
Proof. intros [|[]] p; cbn; entailer. Qed.
Hint Resolve icell_rep_valid_pointer: valid_pointer.

Definition inthash_rep (m: int_table.t V) (p: val): mpred :=
  let buckets := get_buckets m in
  EX buckets_p: list val,
  !! (Zlength buckets_p = N) &&
     malloc_token Ews t_inthash p *
  data_at Ews t_inthash buckets_p p *
  iter_sepcon (prod_curry icell_rep) (combine buckets buckets_p).

Definition inthash_new_spec: ident * funspec :=
   DECLARE _inthash_new
 WITH gv: globals
 PRE [ ] 
   PROP()
   LOCAL(gvars gv)
   SEP(mem_mgr gv)
 POST [ tptr t_inthash ] 
   EX p:val,
      PROP() 
      LOCAL(temp ret_temp p) 
      SEP(inthash_rep (int_table.empty V) p; mem_mgr gv).

Definition new_icell_spec: ident * funspec :=
   DECLARE _new_icell
 WITH gv: globals, key: Z, value: V, pnext: val, tl: list (Z*V)
 PRE [ _key OF tuint, _value OF tptr tvoid, _next OF tptr t_icell ] 
   PROP( 0 <= key < Int.max_unsigned )
   LOCAL(gvars gv; temp _key (Vint (Int.repr key)); temp _value (V_repr value); temp _next pnext)
   SEP(icell_rep tl pnext; mem_mgr gv)
 POST [ tptr t_icell ] 
   EX p:val,
      PROP() 
      LOCAL(temp ret_temp p) 
      SEP(icell_rep ((key, value) :: tl) p; mem_mgr gv).

Definition inthash_lookup_spec: ident * funspec :=
   DECLARE _inthash_lookup
 WITH gv: globals, m: int_table.t V, key: Z, pm: val
 PRE [ _p OF tptr t_inthash, _key OF tuint ] 
   PROP(0 <= key < Int.max_unsigned)
   LOCAL(gvars gv; temp _p pm; temp _key (Vint (Int.repr key)))
   SEP(mem_mgr gv; inthash_rep m pm)
 POST [ tptr tvoid ] 
      PROP() 
      LOCAL(temp ret_temp (V_repr (maybe (int_table.find key m) nullV))) 
      SEP(mem_mgr gv; inthash_rep m pm).

Definition inthash_insert_list_spec: ident * funspec :=
   DECLARE _inthash_insert_list
 WITH gv: globals, l: int_table.t V, key: Z, ppl: val, pl: val
 PRE [ _r0 OF tptr (tptr t_icell), _key OF tuint ] 
   PROP(0 <= key < Int.max_unsigned)
   LOCAL(gvars gv; temp _r0 ppl; temp _key (Vint (Int.repr key)))
   SEP(mem_mgr gv; data_at Ews (tptr t_icell) pl ppl; icell_rep (int_table.this l) pl)
 POST [ tptr t_icell ] 
   EX p_ret: val, EX r: val, EX tl: int_table.Raw.t V,
            let v := maybe (int_table.find key l) nullV in 
      PROP( )
      LOCAL(temp ret_temp p_ret) 
      SEP(mem_mgr gv; data_at Ews (tptr t_icell) p_ret r * icell_rep ((key, v) :: tl) p_ret;
          ALL v: V, data_at Ews (tptr t_icell) p_ret r * icell_rep ((key, v) :: tl) p_ret -*
          EX pl: val, data_at Ews (tptr t_icell) pl ppl * icell_rep (int_table.Raw.add key v {{ l }}) pl).

Definition inthash_insert_spec: ident * funspec :=
   DECLARE _inthash_insert
 WITH gv: globals, m: int_table.t V, key: Z, pm: val, v: V
 PRE [ _p OF tptr t_inthash, _key OF tuint, _value OF tptr tvoid ] 
   PROP(0 <= key < Int.max_unsigned)
   LOCAL(gvars gv; temp _p pm; temp _key (Vint (Int.repr key)); temp _value (proj1_sig v))
   SEP(mem_mgr gv; inthash_rep m pm)
 POST [ tptr tvoid ] 
      PROP( ) 
      LOCAL(temp ret_temp (V_repr (maybe (int_table.find key m) nullV))) 
      SEP(mem_mgr gv; inthash_rep (int_table.add key v m) pm).

Definition Gprog : funspecs :=
        ltac:(with_library prog [ inthash_new_spec; new_icell_spec; inthash_lookup_spec ;
             inthash_insert_list_spec ; inthash_insert_spec ]).

Lemma focus_bucket (m: int_table.t V) (key: Z) (buckets_p: list val)
      (h: Zlength buckets_p = N):
  let l := combine (get_buckets m) buckets_p in
  let i := key mod N in
  iter_sepcon (prod_curry icell_rep) l =
  iter_sepcon (prod_curry icell_rep) (sublist 0 i l) *
  (icell_rep (Znth i (get_buckets m)) (Znth i buckets_p) *
   iter_sepcon (prod_curry icell_rep) (sublist (i + 1) N l)).
Proof.
  intros l i.
  assert (0 <= i < N). { apply Z_mod_lt. rep_omega. }
  assert (Zlength l = N).
  { unfold l. rewrite Zlength_correct, combine_length.
    rewrite Min.min_l, <- Zlength_correct. apply Zlength_get_buckets.
    apply Nat2Z.inj_le. rewrite <- Zlength_correct, <- Zlength_correct, Zlength_get_buckets. omega. }
  replace l with (sublist 0 i l ++ [(Znth i (get_buckets m), Znth i buckets_p)]
                          ++ sublist (i+1) N l) at 1.
  do 2 rewrite iter_sepcon_app.
  simpl iter_sepcon. rewrite sepcon_emp. reflexivity.
  symmetry.
  erewrite <- sublist_same at 1.
  erewrite sublist_split at 1. f_equal.
  erewrite sublist_split at 1. erewrite sublist_len_1 at 1.
  unfold l. rewrite <- sublist.nth_Znth, combine_nth, sublist.nth_Znth, sublist.nth_Znth. reflexivity.
  omega.
  rewrite Zlength_get_buckets. assumption.
  apply Nat2Z.inj. rewrite <- Zlength_correct, <- Zlength_correct, Zlength_get_buckets. congruence.
  fold l. omega. omega. omega. omega. omega. omega. omega. symmetry. assumption.
Qed.


Lemma body_inthash_insert: semax_body Vprog Gprog f_inthash_insert inthash_insert_spec.
Proof.
  start_function.
  unfold inthash_rep. Intros buckets_p.
  rewrite focus_bucket with (key := key) by assumption.
  Intros.
  unfold_data_at (data_at _ _ _ pm).
  rewrite field_at_data_at'. simpl nested_field_type. rewrite <- N_eq. fold t_icell.
  pose (i := key mod N). fold i.
  assert (h_i: 0 <= i < N). { apply Z_mod_lt. rep_omega. }
  rewrite wand_slice_array with (lo := i) (hi := i + 1) by (cbn; rep_omega).
  replace (i+1-i) with 1 by omega.
  rewrite sublist_len_1 by (cbn; rep_omega).
  erewrite data_at_singleton_array_eq by reflexivity. simpl reptype.
  forward_call (gv, get_bucket key m, key, (field_address0 (tarray (tptr t_icell) N) [ArraySubsc i]
           (offset_val (nested_field_offset t_inthash [StructField _buckets]) pm)), Znth i buckets_p).
  cbn. entailer!. entailer!.
  rewrite field_address0_offset. simpl nested_field_offset.
  rewrite Z.add_0_l. reflexivity.
  eapply field_compatible0_cons_Tarray. reflexivity. auto.
  unfold i. unshelve epose proof (Z_mod_lt key N _). rep_omega. rep_omega.
  instantiate (Frame := [malloc_token Ews t_inthash pm; array_with_hole Ews (tptr t_icell) i (i + 1) N buckets_p pm; iter_sepcon (prod_curry icell_rep) (sublist 0 i (combine (get_buckets m) buckets_p));
  iter_sepcon (prod_curry icell_rep) (sublist (i + 1) N (combine (get_buckets m) buckets_p))]).
  unfold Frame, fold_right_sepcon, i. entailer!.
  Intros vret.
  destruct vret as [[p_ret r] tl]. unfold fst, snd in *.
  unfold icell_rep at 1; fold icell_rep. Intros q.
  forward. entailer!. now destruct (maybe (int_table.find (elt:=V) key (get_bucket key m)) nullV).
  do 2 forward.
  {
    entailer!.
    { rewrite <- find_get_bucket. reflexivity. }
    allp_left v.
    sep_apply (wand_frame_elim' (data_at Ews (tptr t_icell) p_ret r * malloc_token Ews t_icell p_ret *
  data_at Ews t_icell (Vint (Int.repr key), (proj1_sig v, q)) p_ret * icell_rep tl q)).
    cbn. Exists q. entailer!.
    Intro pl.
    unfold inthash_rep.
    Exists (upd_Znth i buckets_p pl).
    rewrite focus_bucket with (key := key) by (rewrite upd_Znth_Zlength; rep_omega). fold i.
    unfold_data_at (data_at _ _ _ pm).
    rewrite field_at_data_at'. simpl nested_field_type.
    rewrite <- N_eq, wand_slice_array with (lo := i) (hi := i + 1) by (try rewrite upd_Znth_Zlength; cbn; rep_omega).
    replace (i+1-i) with 1 by omega.
    rewrite sublist_len_1 by (rewrite upd_Znth_Zlength; cbn; rep_omega).
    erewrite data_at_singleton_array_eq by reflexivity.
    simpl nested_field_offset.
    rewrite upd_Znth_same, isptr_offset_val_zero by (auto; cbn; rep_omega).
    replace (array_with_hole Ews (tptr (Tstruct _icell noattr)) i (i + 1) N (upd_Znth i buckets_p pl) pm)
            with (array_with_hole Ews (tptr t_icell) i (i + 1) N buckets_p pm).
    replace (sublist 0 i
            (combine (get_buckets (int_table.add key v m))
               (upd_Znth i buckets_p pl))) with
        (sublist 0 i
            (combine (get_buckets m) buckets_p)).
    replace (sublist (i + 1) N
             (combine (get_buckets (int_table.add key v m))
                      (upd_Znth i buckets_p pl)))
            with
              (sublist (i + 1) N
             (combine (get_buckets m) buckets_p)).
    fold t_icell.
    entailer!. rewrite upd_Znth_Zlength; rep_omega.
    unfold get_bucket. cbn. unfold i. rewrite add_bucket_Znth, upd_Znth_same by rep_omega. apply derives_refl.
    rewrite add_buckets, combine_upd_Znth, sublist_upd_Znth_r by
    (try rewrite Zlength_combine, Z.min_r; try rewrite Zlength_get_buckets; rep_omega). reflexivity.
    rewrite add_buckets, combine_upd_Znth, sublist_upd_Znth_l by
    (try rewrite Zlength_combine, Z.min_r; try rewrite Zlength_get_buckets; rep_omega). reflexivity.
    unfold array_with_hole. rewrite sublist_upd_Znth_l, sublist_upd_Znth_r by (cbn; rep_omega). reflexivity. }
Qed.

Lemma body_inthash_insert_list: semax_body Vprog Gprog f_inthash_insert_list inthash_insert_list_spec.
Proof.
  start_function.
  forward. 
  forward_loop
    (EX l1 l2: list (Z * V), EX r: val,
      PROP ( {{ l }} = l1 ++ l2; not (int_table.Raw.PX.In key l1) )
     LOCAL (temp _r r; gvars gv; temp _r0 ppl; temp _key (Vint (Int.repr key)))
     SEP (mem_mgr gv;
          EX p: val, data_at Ews (tptr t_icell) p r * icell_rep l2 p;
          ALL l', (EX p, data_at Ews (tptr t_icell) p r * icell_rep l' p) -* EX pl: val, data_at Ews (tptr t_icell) pl ppl * icell_rep (l1 ++ l') pl)).
  + Exists (@nil (Z*V)) {{ l }} ppl pl.
    entailer!. destruct H3 as [x hx]. inversion hx.
    apply allp_right. intro.
    apply wand_refl_cancel_right.
  + Intros l1 l2 r p.
    forward.
    forward_if.
  - forward_call (gv, key, nullV, nullval, @nil (Z*V)).
    cbn. entailer!.
    Intro vret.
    do 2 forward.
    replace l2 with (@nil (Z*V)) in * by intuition.
    rewrite app_nil_r in H0.
    replace (maybe (int_table.find (elt:=V) key l) nullV) with nullV.        
    Exists vret r (@nil (Z*V)).
    unfold icell_rep at 2.
    entailer!.
    apply allp_right. intro v.
    sep_apply (allp_instantiate (fun l' =>
                                   (EX p0 : val, data_at Ews (tptr t_icell) p0 r * icell_rep l' p0) -*
   (EX pl0 : val, data_at Ews (tptr t_icell) pl0 ppl * icell_rep ({{l}} ++ l') pl0)) [(key, v)]).
    
    apply wand_derives. Exists vret. apply derives_refl.
    
    replace (int_table.Raw.add key v {{ l }}) with ({{l}} ++ [(key, v)]).
    apply derives_refl.
    
    { induction {{l}} as [|[]]. reflexivity.
      rewrite int_table.Raw.add_equation, if_false, <- app_comm_cons, IHt.
      reflexivity.
      intro hcontr. apply H1. 
      destruct hcontr as [e he]. exists e. now apply SetoidList.InA_cons_tl.
      intro heq. subst. apply H1. exists v0. constructor. now constructor. }
    replace (int_table.find (elt := V) key l) with (@None V). reflexivity.
    symmetry. rewrite find_None. intros v hv. apply H1. exists v. subst. apply hv.
  - destruct l2 as [|[k v]]. unfold icell_rep. Intros. contradiction.
    unfold icell_rep; fold icell_rep. Intros q.    
    forward. forward_if.
    ++ forward.

       Exists p r l2.
       replace (maybe (int_table.find (elt:=V) key l) nullV) with v.
       
       unfold icell_rep at 4; fold icell_rep. Exists q.
       entailer!.
       apply allp_right. intro v'.

       allp_left ((key, v') :: l2).

       apply wand_derives.
       Exists p. apply derives_refl.
       replace (int_table.Raw.add key v' {{l}}) with (l1 ++ (key, v') :: l2).
       apply derives_refl.

       { rewrite H0.
         rename H1 into h.
         clear - h.
         induction l1 as [ | [k v'']].
         + cbn. now destruct Z_as_DT.eq_dec.
         + rewrite int_table.Raw.add_equation. cbn.
           destruct Z_as_DT.eq_dec.
           exfalso. apply h. subst k. rewrite int_table.Raw.PX.In_alt. exists v''.
           constructor. constructor.
           f_equal. apply IHl1. intro hcontr. apply h.
           rewrite int_table.Raw.PX.In_alt in hcontr |- *.
           destruct hcontr as [e he]. exists e.
           apply SetoidList.InA_cons_tl. assumption. }
       
       { replace (int_table.find (elt := V) key l) with (Some v). reflexivity.
         symmetry. apply int_table.find_1. 
         unfold int_table.MapsTo, int_table.Raw.PX.MapsTo.
         rewrite H0, SetoidList.InA_app_iff. right. constructor. easy. }
    ++ forward. simpl offset_val.
       Exists (l1 ++ [(k,v)]) l2 (offset_val 8 p) q.
       entailer!.
       split.
       { rewrite <- app_assoc. easy. }
       { intros [e hcontr%SetoidList.InA_app].
         destruct hcontr.
         + apply H1. exists e. assumption.
         + apply SetoidList.InA_singleton in H12.
           compute in H12. omega. }
       
       unfold_data_at (data_at _ _ _ p).
       rewrite (field_at_data_at' _ _ [StructField _next]). simpl nested_field_type. simpl nested_field_offset.
       entailer!.

       apply allp_right. intro l'.
       allp_left ((k,v)::l').
       rewrite <- wand_sepcon_adjoint.
       sep_apply (wand_frame_elim' ((data_at Ews (tptr t_icell) p r *
   (malloc_token Ews t_icell p *
    (field_at Ews t_icell [StructField _key] (Vint (Int.repr k)) p *
     field_at Ews t_icell [StructField _value] (V_repr v) p))) *
  (EX p0 : reptype (tptr t_icell), data_at Ews (tptr t_icell) p0 (offset_val 8 p) * icell_rep l' p0))).
       cbn. Intro p0.
       Exists p p0. unfold_data_at (data_at _ _ _ p).
       rewrite (field_at_data_at _ _ [StructField _next]), field_address_offset.
       entailer!.
       auto with field_compatible.
       rewrite <- app_assoc. apply derives_refl.
Qed.


Lemma body_inthash_lookup: semax_body Vprog Gprog f_inthash_lookup inthash_lookup_spec.
Proof.
  start_function.
  unfold inthash_rep.
  Intros buckets_p.
  rewrite focus_bucket with (key := key) by assumption. Intros.
  forward.
  { pose proof (Z_mod_lt key N).
    entailer. }
  { 
    remember (key mod N) as i.
    remember (Znth i buckets_p) as q0.
    remember (Znth i (get_buckets m)) as kvs.
    remember (combine (get_buckets m) buckets_p) as l.
    forward_while (
        EX kvs1 kvs2: list (Z * V), EX q: val,
     PROP ( kvs = kvs1 ++ kvs2 /\ not (int_table.Raw.PX.In key kvs1))
     LOCAL (temp _q q; gvars gv; temp _p pm; temp _key (Vint (Int.repr key)))
     SEP (mem_mgr gv; malloc_token Ews t_inthash pm; data_at Ews t_inthash buckets_p pm;
     iter_sepcon (prod_curry icell_rep) (sublist 0 i l);
     icell_rep kvs2 q;
     icell_rep kvs2 q -* icell_rep kvs q0;
     emp; iter_sepcon (prod_curry icell_rep) (sublist (i + 1) N l)))%assert.
    + Exists (@nil (Z*V)) kvs q0.
      entailer!.
      { rewrite int_table.Raw.PX.In_alt in H6. destruct H6 as [e he].
        inv he. }
      replace (Zlength (combine (get_buckets m) buckets_p)) with N. cancel.
      apply wand_refl_cancel_right.
      rewrite Zlength_combine, Z.min_l, Zlength_get_buckets. reflexivity.
      rewrite Zlength_get_buckets; omega.
    + entailer!.
    + destruct kvs2. assert_PROP (q = nullval). entailer!. intuition.
      subst q. contradiction.
      destruct p as [k v].
      unfold icell_rep at 2; fold icell_rep.
      Intros q1. forward.
      forward_if.
      - pose (v_sig := v).
        destruct v as [v hv].
        forward.
        forward.
        replace (int_table.find key m) with (Some v_sig).
        entailer!.
        unfold inthash_rep. Exists buckets_p.
        rewrite focus_bucket with (key := key) by rep_omega.
        entailer!.
        sep_apply (wand_frame_elim'
                     (malloc_token Ews t_icell q * data_at Ews t_icell (vint key, (V_repr (exist is_pointer_or_null v hv), q1)) q * icell_rep kvs2 q1)).
        unfold icell_rep at 2; fold icell_rep.
        Exists q1. entailer. apply derives_refl.
        symmetry. eapply int_table.find_1. rewrite get_buckets_spec.
        rewrite (proj1 H1), SetoidList.InA_app_iff. right. constructor. reflexivity.
      - forward. Exists (kvs1 ++ [(k,v)], kvs2, q1).
        entailer!.
        destruct H1. split.
        rewrite <- app_assoc. unfold app at 2. assumption.
        { intro hcontr.
          rewrite int_table.Raw.PX.In_alt in hcontr, H11.
          destruct hcontr as [e he].
          rewrite SetoidList.InA_app_iff in he. destruct he as [he|he].
          apply H11. exists e. assumption.
          rewrite SetoidList.InA_singleton in he.
          compute in he. subst. contradiction. }
        cancel. rewrite <- wand_sepcon_adjoint.
        rewrite sepcon_comm, <- sepcon_assoc.
        apply modus_ponens_wand'. unfold icell_rep at 2; fold icell_rep.
        Exists q1. entailer!.
      + forward.
        replace (int_table.find (elt := V) key m) with (@None V).
        unfold inthash_rep. Exists buckets_p.
        rewrite focus_bucket with (key := key). entailer!. apply modus_ponens_wand.
        assumption.
        replace kvs2 with (@nil (Z*V)) in H1 by intuition. rewrite app_nil_r in H1.
        symmetry. apply find_None.
        intros v hv. apply (proj2 H1). exists v.
        rewrite <- (proj1 H1). rewrite get_buckets_spec' in hv.
        unfold int_table.MapsTo in hv. apply hv.
  }
Qed.

Lemma body_inthash_new: semax_body Vprog Gprog f_inthash_new inthash_new_spec.
Proof.
  start_function.
  forward_call (t_inthash, gv).
  { split3; auto. cbn. computable. }
  Intros vret.
  forward_if
    (PROP ( )
     LOCAL (temp _p vret; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_inthash vret * data_at_ Ews t_inthash vret)).
  { destruct eq_dec; entailer. }
  { forward_call tt. entailer. }
  { forward. rewrite if_false by assumption. entailer. }
  { Search complete. forward_for_simple_bound N
      (EX i: Z,
       PROP ( 0 <= i <= N )
       LOCAL (temp _p vret; gvars gv)
       SEP (mem_mgr gv;
              malloc_token Ews t_inthash vret;
              data_at Ews t_inthash (Zrepeat i nullval ++ Zrepeat (N-i) Vundef) vret))%assert.
    + entailer!. apply data_at__data_at. reflexivity.
    + forward.
      entailer!.
      autorewrite with sublist.
      rewrite Zlength_Zrepeat, Z.sub_diag, upd_Znth0, Zlength_Zrepeat by rep_omega.
      replace (Zrepeat (N - i) Vundef) with (Vundef :: Zrepeat (N - (i + 1)) Vundef).
      rewrite sublist_1_cons.
      unfold Zrepeat. rewrite Z2Nat.inj_add, repeat_plus, sublist_repeat by omega.
      change (Z.to_nat 1) with 1%nat.
      cbn. replace (N - i - 1 - 0) with (N - (i+1)) by omega.
      rewrite <- app_assoc.
      apply derives_refl.
      change (Vundef :: Zrepeat (N - (i + 1)) Vundef) with (Zrepeat 1 Vundef ++ Zrepeat (N-(i+1)) Vundef).
      unfold Zrepeat. rewrite <- repeat_plus. rewrite <- Z2Nat.inj_add by omega.
      replace  (1 + (N - (i + 1))) with (N - i) by omega. reflexivity.
    + forward. Exists vret. unfold inthash_rep, int_table.empty.
      Exists (Zrepeat N nullval).
      rewrite iter_sepcon_emp'.
      entailer!.
      { intros [l p] hxl. pose proof hxl as hxr.
        apply in_combine_l in hxl. apply in_combine_r in hxr.
        cbn in hxl.
        apply list_in_map_inv in hxl. rewrite <- Zrepeat_fold in hxr. apply in_list_repeat in hxr.
        destruct hxl as [? []].
        subst. cbn.
        apply pred_ext; entailer. }}
Qed.

Lemma body_new_icell: semax_body Vprog Gprog f_new_icell new_icell_spec.
Proof.
  start_function.
  forward_call (t_icell, gv).
  { now compute. }
  Intro vret.
  forward_if (PROP ( )
     LOCAL (temp _p vret; gvars gv; temp _key (Vint (Int.repr key)); temp _value (proj1_sig value);
     temp _next pnext)
     SEP (mem_mgr gv; malloc_token Ews t_icell vret * data_at_ Ews t_icell vret;
     icell_rep tl pnext)).
  + destruct eq_dec; entailer.
  + forward_call tt. contradiction.
  + forward. rewrite if_false by assumption. entailer.
  + Intros. do 4 forward. Exists vret. cbn.
    Exists pnext. entailer!.
Qed.
