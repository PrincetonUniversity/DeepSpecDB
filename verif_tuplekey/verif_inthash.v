Require Import VST.floyd.proofauto.
Require Import inthash.
Require FMapWeakList.
Require Import Program.Basics. Open Scope program_scope.
Require Import Structures.OrdersEx.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Default Timeout 20. 
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.library.

Definition V := sig is_pointer_or_null.
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.
Definition N: Z := 10.

Module int_table := FMapWeakList.Make Z_as_DT.
Print int_table.

Section IntTable.
  Import int_table.
  Check SetoidList.InA .
  Definition get_buckets (m: t V): list (list (Z*V)) :=
    List.map (fun n => filter (fun kv => eq_dec (fst kv mod N) (Z.of_nat n)) (elements m)) (seq 0%nat (Z.to_nat N)).

  Lemma Zlength_get_buckets: forall m, Zlength (get_buckets m) = N.
  Proof.
    intros []. cbn.
    rewrite Zlength_map, Zlength_correct, seq_length. reflexivity.
  Qed.

  Lemma get_buckets_spec (m: t V):
    forall k v, MapsTo k v m <-> SetoidList.InA (eq_key_elt (elt := V)) (k, v) (Znth (k mod N) (get_buckets m)).
  Proof.
    intros.
    unshelve epose proof (Z_mod_lt k N _). unfold N. computable.
    assert (N = Zlength (seq 0%nat (Z.to_nat N))). rewrite Zlength_correct, seq_length. reflexivity.
    assert (mapsto_iff: MapsTo k v m <-> SetoidList.InA (@eq_key_elt _) (k, v) (elements m)).
    split; [apply elements_1 | apply elements_2].
    rewrite mapsto_iff.
    destruct m as [l nodup]. unfold get_buckets.
    rewrite Znth_map, SetoidList.filter_InA.
    rewrite <- nth_Znth by omega.
    rewrite seq_nth by now apply Z2Nat.inj_lt.
    cbn. rewrite Z2Nat.id by omega.
    now destruct initial_world.EqDec_Z.
    intros x y hxy. apply Raw.PX.eqke_eqk in hxy. now rewrite hxy.
    rewrite Zlength_correct, seq_length, Z2Nat.id.
    apply Z_mod_lt. unfold N; omega. unfold N; omega.
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
    intros. destruct m.
    unfold get_buckets.
    unshelve epose proof (Z_mod_lt k N _). unfold N. omega.
    rewrite Znth_map, <- nth_Znth, seq_nth, Nat.add_0_l, Z2Nat.id. apply NoDupA_filter.
    intros x y <-; reflexivity.
    omega. rep_omega.
    rewrite Zlength_correct, seq_length; rep_omega.
    rewrite Zlength_correct, seq_length; rep_omega.
  Qed.

  Definition get_bucket (k: Z) (m: t V): t V :=
    Build_slist (NoDupA_bucket k m).

  Lemma get_buckets_spec' (m: t V):
    forall k v, MapsTo k v m <-> MapsTo k v (get_bucket k m).
  Proof.
    intros. destruct m as [l nodup].
    unshelve epose proof (Z_mod_lt k N _). unfold N. omega.
    unfold MapsTo, get_bucket, Raw.PX.MapsTo.
    unfold get_buckets, this.
    rewrite Znth_map, SetoidList.filter_InA, <- nth_Znth, seq_nth, Nat.add_0_l, Z2Nat.id;
    fold N; try rewrite Zlength_correct, seq_length; try rep_omega.
    now destruct eq_dec.
    intros x y hxy%Raw.PX.eqke_eqk. rewrite hxy. reflexivity.
  Qed.

  Lemma MapsTo_inj: forall (m: t V) k v1 v2,
      MapsTo k v1 m -> MapsTo k v2 m -> v1 = v2.
  Proof.
    intros * h1 h2.
    apply find_1 in h1. apply find_1 in h2.
    rewrite h1 in h2. now inv h2.
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

End IntTable.

Definition t_icell := Tstruct _icell noattr.
Definition t_inthash := Tstruct _inthash noattr.

Fixpoint icell_rep (l: list (Z*V)) (p: val): mpred :=
  match l with
  | [] => !!(p = nullval) && emp
  | (k, v) :: tl => EX q: val,
                    !! (0 <= k < Int.max_unsigned) &&
                       malloc_token Ews t_icell p *
                    data_at Ews t_icell (Vint (Int.repr k), (proj1_sig v, q)) p *
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
   LOCAL(gvars gv; temp _key (Vint (Int.repr key)); temp _value (proj1_sig value); temp _next pnext)
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
      LOCAL(temp ret_temp (match int_table.find key m with
             | Some res => proj1_sig res
             | None => Vnullptr
          end)) 
      SEP(mem_mgr gv; inthash_rep m pm).

Definition inthash_insert_list_spec: ident * funspec :=
   DECLARE _inthash_insert_list
 WITH gv: globals, l: list (Z * V), key: Z, ppl: val, pl: val
 PRE [ _r0 OF tptr (tptr t_icell), _key OF tuint ] 
   PROP(0 <= key < Int.max_unsigned; SetoidList.NoDupA (int_table.Raw.PX.eqk (elt:=V)) l)
   LOCAL(gvars gv; temp _r0 ppl; temp _key (Vint (Int.repr key)))
   SEP(mem_mgr gv; data_at Ews (tptr t_icell) pl ppl; icell_rep l pl)
 POST [ tptr t_icell ] 
   EX p_ret: val, EX r: val, EX tl: list (Z*V),
            let v := match int_table.Raw.find key l with
                         | Some v => v
                         | None => nullV
                           end in
      PROP( )
      LOCAL(temp ret_temp p_ret) 
      SEP(mem_mgr gv; data_at Ews (tptr t_icell) p_ret r * icell_rep ((key, v) :: tl) p_ret;
          ALL v: V, data_at Ews (tptr t_icell) p_ret r * icell_rep ((key, v) :: tl) p_ret -*
          EX pl: val, data_at Ews (tptr t_icell) pl ppl * icell_rep (int_table.Raw.add key v l) pl).

Definition inthash_insert_spec: ident * funspec :=
   DECLARE _inthash_insert
 WITH gv: globals, m: int_table.t V, key: Z, pm: val, v: V
 PRE [ _p OF tptr t_inthash, _key OF tuint, _value OF tptr tvoid ] 
   PROP(0 <= key < Int.max_unsigned)
   LOCAL(gvars gv; temp _p pm; temp _key (Vint (Int.repr key)); temp _value (proj1_sig v))
   SEP(mem_mgr gv; inthash_rep m pm)
 POST [ tptr tvoid ] 
      PROP( ) 
      LOCAL(temp ret_temp (match int_table.find key m with Some v => proj1_sig v | None => nullval end)) 
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
  assert (0 <= i < N). { apply Z_mod_lt. unfold N. omega. }
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
  unfold l. rewrite <- nth_Znth, combine_nth, nth_Znth, nth_Znth. reflexivity.
  omega.
  rewrite Zlength_get_buckets. assumption.
  apply Nat2Z.inj. rewrite <- Zlength_correct, <- Zlength_correct, Zlength_get_buckets. congruence.
  fold l. omega. omega. omega. omega. omega. omega. omega. symmetry. assumption.
Qed.


Lemma body_inthash_insert: semax_body Vprog Gprog f_inthash_insert inthash_insert_spec.
Proof.
  start_function.
  unfold inthash_rep. Intros buckets_p.
  rewrite focus_bucket with (key := key).
  Intros.
  unfold_data_at (data_at _ _ _ pm).
  rewrite field_at_data_at'. simpl nested_field_type. fold t_icell.
  pose (i := key mod N). fold i.
  assert (h_i: 0 <= i < N). apply Z_mod_lt. unfold N. omega.
  rewrite wand_slice_array with (lo := i) (hi := i + 1).
  replace (i+1-i) with 1 by omega.
  rewrite sublist_len_1.
  erewrite data_at_singleton_array_eq by reflexivity.
  forward_call (gv, Znth i (get_buckets m), key,  (field_address0 (tarray (tptr t_icell) 10) [ArraySubsc i]
           (offset_val (nested_field_offset t_inthash [StructField _buckets]) pm)), Znth i buckets_p).
  entailer!.
  rewrite field_address0_offset. simpl nested_field_offset.
  rewrite Z.add_0_l. reflexivity.
  eapply field_compatible0_cons_Tarray. reflexivity. auto.
  fold N. unfold i. unshelve epose proof (Z_mod_lt key N _). unfold N. omega. omega.
  instantiate (Frame := [malloc_token Ews t_inthash pm; array_with_hole Ews (tptr t_icell) i (i + 1) 10 buckets_p pm;
  iter_sepcon (prod_curry icell_rep) (sublist 0 i (combine (get_buckets m) buckets_p));
  iter_sepcon (prod_curry icell_rep)
    (sublist (i + 1) N (combine (get_buckets m) buckets_p))]). unfold Frame. unfold fold_right_sepcon, i. entailer!.
  split. assumption.
  unfold get_buckets. rewrite Znth_map.
  apply NoDupA_filter.
  { intros x y ->. reflexivity. }
  { rewrite Zlength_correct, seq_length. rep_omega. }
  Intros vret.
  destruct vret as [[p_ret r] tl]. unfold fst, snd in *.
  unfold icell_rep at 1; fold icell_rep. Intros q.
  remember (match int_table.Raw.find (elt:=V) key (Znth i (get_buckets m)) with
          | Some v0 => v0
          | None => nullV
          end) as old_v. destruct old_v as [old_v hold_v].
  do 3 forward.
  {
    entailer!.
    {
      case_eq (int_table.find (elt := V) key m).
      + intros v0 hv0. apply int_table.find_2 in hv0.
        rewrite get_buckets_spec' in hv0.
        apply int_table.find_1 in hv0. unfold get_bucket, int_table.find, int_table.this in hv0.
        fold i in hv0. rewrite hv0 in Heqold_v.
        subst v0. reflexivity.
      + intro hnone.
        replace (int_table.Raw.find (elt := V) key (Znth i (get_buckets m)))
                with (@None V) in Heqold_v.
        now inversion Heqold_v.
        symmetry. 
        pose proof find_None as fn. unfold int_table.find in fn.
        specialize (fn (get_bucket key m)). unfold get_bucket, int_table.this in fn. fold i in fn.
        rewrite fn. intros v0 hcontr.
        rewrite find_None in hnone. apply (hnone v0).
        rewrite get_buckets_spec'. assumption.
       }
    
    allp_left v.
    sep_apply (wand_frame_elim' (data_at Ews (tptr t_icell) p_ret r * malloc_token Ews t_icell p_ret *
  data_at Ews t_icell (Vint (Int.repr key), (proj1_sig v, q)) p_ret * icell_rep tl q)).
    cbn. Exists q. entailer!.

    Intro pl.
    unfold inthash_rep.
    
    Exists (sublist 0 i buckets_p ++ pl :: sublist (i + 1) N buckets_p).
    rewrite focus_bucket with (key := key). fold i.
    
    unfold_data_at (data_at _ _ _ pm).
    rewrite field_at_data_at'. simpl nested_field_type.
    rewrite wand_slice_array with (lo := i) (hi := i + 1).
    replace (i+1-i) with 1 by omega.
    rewrite sublist_len_1.
    erewrite data_at_singleton_array_eq by reflexivity.

    
    do 2 replace (Znth i (sublist 0 i buckets_p ++ pl :: sublist (i + 1) N buckets_p))
    with pl.
    replace (sublist 0 i
            (combine (get_buckets (int_table.add key v m))
               (sublist 0 i buckets_p ++ pl :: sublist (i + 1) N buckets_p))) with
        (sublist 0 i
            (combine (get_buckets m) buckets_p)).

    replace (sublist (i + 1) N
             (combine (get_buckets (int_table.add key v m))
                      (sublist 0 i buckets_p ++ pl :: sublist (i + 1) N buckets_p)))
            with
              (sublist (i + 1) N
             (combine (get_buckets m) buckets_p)).
    fold t_icell.
    
    replace (array_with_hole Ews (tptr t_icell) i (i + 1) 10
          (sublist 0 i buckets_p ++ pl :: sublist (i + 1) N buckets_p)
          (offset_val (nested_field_offset t_inthash [StructField _buckets]) pm)) with
          (array_with_hole Ews (tptr t_icell) i (i + 1) 10 buckets_p pm).

    replace (Znth i (get_buckets (int_table.add key v m))) with
        (int_table.Raw.add key v (Znth i (get_buckets m))).
    entailer!.
    { autorewrite with sublist. omega. }
    
    apply derives_refl.
    
   

    admit.
    admit.
    admit.
    admit.
    
    now autorewrite with sublist.
    reflexivity.
    now autorewrite with sublist.
    autorewrite with sublist; omega.
    omega.
    fold N; omega.
    fold N; autorewrite with sublist; omega.
    autorewrite with sublist; omega.
 }

  cbn; omega.
  omega.
  fold N; omega.
  fold N; assumption.
  assumption.
Admitted.


Lemma body_inthash_insert_list: semax_body Vprog Gprog f_inthash_insert_list inthash_insert_list_spec.
Proof.
  start_function.
  forward. 
  forward_loop
    (EX l1 l2: list (Z * V), EX r: val,
      PROP ( l = l1 ++ l2; not (int_table.Raw.PX.In key l1) )
     LOCAL (temp _r r; gvars gv; temp _r0 ppl; temp _key (Vint (Int.repr key)))
     SEP (mem_mgr gv;
          EX p: val, data_at Ews (tptr t_icell) p r * icell_rep l2 p;
          ALL l', (EX p, data_at Ews (tptr t_icell) p r * icell_rep l' p) -* EX pl: val, data_at Ews (tptr t_icell) pl ppl * icell_rep (l1 ++ l') pl)).
  + Exists (@nil (Z*V)) l ppl pl.
    entailer!. destruct H4 as [x hx]. inversion hx.
    apply allp_right. intro.
    apply wand_refl_cancel_right.
  + Intros l1 l2 r p.
    forward.
    forward_if.
  - forward_call (gv, key, nullV, nullval, @nil (Z*V)).
    cbn. entailer!.
    Intro vret.
    do 2 forward.
    replace l2 with (@nil (Z*V)) by intuition. rewrite app_nil_r.
    replace (int_table.Raw.find (elt := V) key l1) with (@None V).
    Exists vret r (@nil (Z*V)).
    unfold icell_rep at 2.
    entailer!.
    apply allp_right. intro v.
    sep_apply (allp_instantiate (fun l' =>
                                   (EX p0 : val, data_at Ews (tptr t_icell) p0 r * icell_rep l' p0) -*
   (EX pl0 : val, data_at Ews (tptr t_icell) pl0 ppl * icell_rep (l1 ++ l') pl0)) [(key, v)]).
    
    apply wand_derives. Exists vret. apply derives_refl.
    
    replace (int_table.Raw.add key v l1) with (l1 ++ [(key, v)]).
    apply derives_refl.
    
    { clear H0. induction l1 as [|[]]. reflexivity.
      rewrite int_table.Raw.PX.In_alt in H2, IHl1.
      cbn. rewrite if_false. rewrite IHl1. reflexivity.
      intro hcontr. apply H2. 
      destruct hcontr as [e he]. exists e. now apply SetoidList.InA_cons_tl.
      intro heq. subst. apply H2. exists v0. constructor. constructor. }

    case_eq (int_table.Raw.find (elt := V) key l1).
    { intros v hv.
      exfalso. apply H2. apply int_table.Raw.find_2 in hv.
      rewrite int_table.Raw.PX.In_alt. exists v.
      now apply int_table.Raw.PX.InA_eqke_eqk. }
    easy.
  - destruct l2 as [|[k v]]. unfold icell_rep. Intros. contradiction.
    unfold icell_rep; fold icell_rep. Intros q.    
    forward. forward_if.
    ++ forward.

       Exists p r l2.
       replace (match int_table.Raw.find (elt:=V) key (l1 ++ (key, v) :: l2) with
           | Some v0 => v0
           | None => nullV
           end) with v.
       
       unfold icell_rep at 4; fold icell_rep. Exists q.
       entailer!.
       apply allp_right. intro v'.

       allp_left ((key, v') :: l2).

       apply wand_derives.
       Exists p. apply derives_refl.
       replace (int_table.Raw.add key v' (l1 ++ (key, v) :: l2)) with (l1 ++ (key, v') :: l2).
       apply derives_refl.

       { rename H2 into h.
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
       
       { replace (int_table.Raw.find (elt := V) key (l1 ++ (key, v) :: l2)) with (Some v). reflexivity.
         symmetry. apply int_table.Raw.find_1. assumption.
         unfold int_table.Raw.PX.MapsTo.
         rewrite SetoidList.InA_app_iff. right. constructor. easy.
Qed.

Lemma body_inthash_lookup: semax_body Vprog Gprog f_inthash_lookup inthash_lookup_spec.
Proof.
  start_function.
  unfold inthash_rep.
  Intros buckets_p.
  remember (combine (get_buckets m) buckets_p) as l.
  remember (key mod N) as i.
  remember (iter_sepcon (prod_curry icell_rep) l) as buckets_rep eqn:hb.
  pose proof hb as save_buckets_rep.
  replace l with (sublist 0 i l ++ [(Znth i (get_buckets m), Znth i buckets_p)]
                          ++ sublist (i+1) (Zlength l) l) in hb.
  do 2 rewrite iter_sepcon_app in hb.
  simpl iter_sepcon in hb.
  subst buckets_rep.
  Intros.
  forward.
  { pose proof (Z_mod_lt key 10).
    entailer. }
  { 
    change 10 with N.
    rewrite <- Heqi.
    remember (Znth i buckets_p) as q0.
    remember (Znth i (get_buckets m)) as kvs.
    forward_while (
        EX kvs1 kvs2: list (Z * V), EX q: val,
     PROP ( kvs = kvs1 ++ kvs2 /\ not (int_table.Raw.PX.In key kvs1))
     LOCAL (temp _q q; gvars gv; temp _p pm; temp _key (Vint (Int.repr key)))
     SEP (mem_mgr gv; malloc_token Ews t_inthash pm; data_at Ews t_inthash buckets_p pm;
     iter_sepcon (prod_curry icell_rep) (sublist 0 i l);
     icell_rep kvs2 q;
     icell_rep kvs2 q -* icell_rep kvs q0;
     emp; iter_sepcon (prod_curry icell_rep) (sublist (i + 1) (Zlength l) l)))%assert.
    + Exists (@nil (Z*V)) kvs q0.
      entailer!.
      { rewrite int_table.Raw.PX.In_alt in H5. destruct H5 as [e he].
        inv he. }      
      apply wand_refl_cancel_right.
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
        rewrite <- save_buckets_rep.
        entailer!.
        eapply modus_ponens_wand'. unfold icell_rep at 2; fold icell_rep.
        Exists q1. entailer. 
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
        rewrite <- save_buckets_rep. entailer!. apply modus_ponens_wand.
        replace kvs2 with (@nil (Z*V)) in H1 by intuition.
        rewrite app_nil_r in H1.
        remember (int_table.find (elt := V) key m) as f. destruct f.
        symmetry in Heqf. apply int_table.find_2 in Heqf.
        rewrite get_buckets_spec in Heqf.
        destruct H1 as [hnth hnin].
        rewrite hnth in Heqf.
        exfalso. apply hnin.
        rewrite int_table.Raw.PX.In_alt.
        exists v. apply int_table.Raw.PX.InA_eqke_eqk. assumption.
        reflexivity.
  }
  assert (hlenl: Zlength l = N).
  { subst l. rewrite Zlength_correct, combine_length, Min.min_l, <- Zlength_correct, Zlength_get_buckets.
    reflexivity.
     apply Nat2Z.inj_le. rewrite <- Zlength_correct, <- Zlength_correct, H0, Zlength_get_buckets. omega. }
  { symmetry.
  rewrite <- (sublist_same_gen 0 (Zlength l) l) at 1 by omega. rewrite hlenl.
  assert (0 <= i < 10). subst i. apply Z_mod_lt. computable.
  assert (N = 10) by reflexivity. 
  erewrite sublist_split. f_equal.
  erewrite sublist_split. f_equal.
  rewrite sublist_len_1. subst l. rewrite <- nth_Znth, <- nth_Znth, <- nth_Znth, combine_nth.
  reflexivity.
  apply Nat2Z.inj.
  now rewrite <- Zlength_correct, <- Zlength_correct, Zlength_get_buckets.
  rep_omega.
  rewrite Zlength_get_buckets. omega.
  rewrite Zlength_correct, combine_length. split. easy.
  rewrite Min.min_r. rewrite <- Zlength_correct. omega. 
  apply Nat2Z.inj_le. rewrite <- Zlength_correct, <- Zlength_correct, H0, Zlength_get_buckets. omega.
  omega.  omega. omega. omega. omega. }
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
  { forward_for_simple_bound N
      (EX i: Z,
       PROP ( 0 <= i <= N )
       LOCAL (temp _p vret; gvars gv)
       SEP (mem_mgr gv;
              malloc_token Ews t_inthash vret;
              data_at Ews t_inthash (list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat (N-i)) Vundef) vret))%assert.
    + unfold N. omega.
    + now compute.
    + entailer!. unfold N. omega.
      rewrite Z2Nat.inj_0. unfold list_repeat at 1.
      rewrite app_nil_l. apply derives_refl.
    + forward.
      entailer!.
      autorewrite with sublist.
      rewrite upd_Znth0, semax_lemmas.cons_app.
      rewrite <- list_repeat_app', <- app_assoc.
      autorewrite with sublist.
      change (list_repeat (Z.to_nat 1) nullval) with [Vint (Int.repr 0)].
      replace (N-(i+1)) with (N-i-1) by omega.
      apply derives_refl. omega. omega.
    + change (list_repeat (Z.to_nat (N - N)) Vundef) with (@nil val).
      rewrite app_nil_r.
      forward. Exists vret. unfold inthash_rep, int_table.empty.
      Exists (list_repeat (Z.to_nat N) nullval).
      rewrite iter_sepcon_emp'.
      entailer!.
      { intros [l p] hxl. pose proof hxl as hxr.
        apply in_combine_l in hxl. apply in_combine_r in hxr.
        cbn in hxl.
        apply list_in_map_inv in hxl. apply in_list_repeat in hxr.
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
