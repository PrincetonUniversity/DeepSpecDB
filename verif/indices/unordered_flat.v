Require Import VST.floyd.functional_base SetoidList Relation_Definitions.

(*
  A simple implementation of unordered association lists
  mapping keys to VST's vals.
  Inspired from, but much simpler than Coq Standard Library's FMapWeakList.
  However, this is designed *without* using modules.
*)

Record flat (key: Type) :=
  mk_flat
  {
    elements: list (key * val);
    nodup: NoDup (map fst elements);
  }.

Arguments elements {key}.
Arguments nodup {key}.

Section K.
  Context {key: Type} {eq_dec: EqDec key}.

  Definition flat_card (m: flat key): nat := length (elements m).
  Definition flat_Zcard (m: flat key): Z := Z.of_nat (flat_card m).
  
  Definition flat_In (k: key) (m: flat key): Prop :=
    In k (map fst (elements m)).
  
  Lemma flat_In_dec: forall k m, {flat_In k m} + {~ flat_In k m}.
  Proof. intros. apply in_dec, eq_dec. Defined.

  Definition flat_lookup (k0: key) (m: flat key): option val :=
    findA (eq_dec k0) (elements m).

  (* findA_NoDupA could have been another choice here here *)
  Lemma flat_In_lookup_Some: forall k m,
      flat_In k m -> exists p, flat_lookup k m = Some p.
  Proof.
    intros * h%in_map_iff.
    destruct h as [[k' p] [keq hin]]. simpl in keq. subst.
    exists p. destruct m as [elts nodup]. simpl in hin.
    induction elts as [|[k' p'] elts].
    + inversion hin.
    + apply in_inv in hin. unfold flat_lookup. destruct hin as [heq|hin]; cbn.
    - inversion heq. subst.
      rewrite proj_sumbool_is_true by reflexivity. reflexivity.
    - inversion nodup. pose proof (in_map fst _ _ hin).
      rewrite proj_sumbool_is_false by (intro hcontr; subst; contradiction).
      unshelve eapply IHelts; assumption.
  Qed.

  Lemma flat_lookup_Some_In: forall k m p,
      flat_lookup k m = Some p -> flat_In k m.
  Proof.
    intros * h.
    unfold flat_lookup in h.
    refine (proj1 (find_some (fun k' => eq_dec k k') _ _)).
    induction (elements m) as [|[k' p'] elts].
    + discriminate.
    + cbn in h |- *.
      destruct eq_dec; cbn. congruence.
      apply IHelts. apply h.
  Qed.

  Lemma flat_not_In_lookup_None: forall k m,
      ~ flat_In k m -> flat_lookup k m = None.
  Proof.
    intros * h.
    destruct m as [elts nodup].
    induction elts as [|[k' p'] elts].
    + reflexivity.
    + unfold flat_lookup in IHelts |- *. unfold flat_In in h; simpl in h, nodup |- *.
      rewrite NoDup_cons_iff in nodup.
      apply not_in_cons in h.
      rewrite proj_sumbool_is_false by easy. unshelve eapply IHelts.
      easy. unfold flat_In. cbn. easy.
  Qed.

  Lemma flat_lookup_None_not_In: forall k m,
      flat_lookup k m = None -> ~ flat_In k m.
  Proof.
    intros * h hcontr%flat_In_lookup_Some. destruct hcontr. congruence.
  Qed.

  Definition flat_equiv: relation (flat key) := fun m m' => forall (k: key), flat_lookup k m = flat_lookup k m'.

  Notation "m1 '=f=' m2" := (flat_equiv m1 m2) (at level 20).
  
  Lemma flat_equiv_refl: reflexive _ flat_equiv.
  Proof. congruence. Qed.

  Lemma flat_equiv_sym: symmetric _ flat_equiv.
  Proof. congruence. Qed.

  Lemma flat_equiv_trans: transitive _ flat_equiv.
  Proof. congruence. Qed.

  Add Parametric Relation: (flat key) flat_equiv
      reflexivity proved by flat_equiv_refl
      symmetry proved by flat_equiv_sym
      transitivity proved by flat_equiv_trans
        as FlatEquivSetoid.

  Add Parametric Morphism: flat_lookup with
      signature eq ==> flat_equiv ==> eq as flat_lookup_morphism.
  Proof. congruence. Qed.

  Lemma flat_MapsTo_lookup_Some: forall k p m,
      In (k, p) (elements m) <-> flat_lookup k m = Some p.
  Proof.
    intros k p [elts nodup].
    unfold flat_lookup.
    setoid_rewrite <- (findA_NoDupA (Eqsth _)).
    simpl.
    split.
    + intro h. eapply In_InA in h. eassumption.
      constructor.
    - intro kp1; split; congruence.
    - intros kp1 kp2 []; split; congruence.
    - intros kp1 kp2 kp3 [] []; split; congruence.
    + intros h%InA_alt.
      destruct h as [[k' p'] [[hk hp] hin]].
      cbn in hk, hp. subst. assumption.
    + simpl.
      induction elts as [|[k' p'] elts].
    - constructor.
    - constructor. simpl in nodup. apply NoDup_cons_iff in nodup.
      intros hcontr%InA_alt. apply (proj1 nodup). 
      destruct hcontr as [[k1 p1] [hfst hin]].
      cbn in hfst. subst. change k1 with (fst (k1, p1)).
      apply in_map. assumption.
      apply IHelts. now inversion nodup.
  Qed.
      
  Lemma flat_equiv_incl: forall m m',
      m =f= m' -> incl (elements m) (elements m').
  Proof.
    intros * h.
    unfold incl, flat_equiv in h |- *.
    intros [k p] hkp%flat_MapsTo_lookup_Some.
    rewrite flat_MapsTo_lookup_Some. congruence.
  Qed.

  Add Parametric Morphism: flat_card with
      signature flat_equiv ==> eq as flat_card_morphism.
  Proof. intros m m' hmm'.
         pose proof (flat_equiv_incl _ _ hmm') as h1.
         apply flat_equiv_sym, flat_equiv_incl in hmm'.
         destruct m as [eltsm nodupm], m' as [eltsm' nodupm'].
         unfold flat_card. simpl in hmm', h1 |- *.
         apply NoDup_map_inv in nodupm. apply NoDup_map_inv in nodupm'.
         apply NoDup_incl_length in h1; apply NoDup_incl_length in hmm'; try assumption.
         omega.
  Qed.

  Add Parametric Morphism: flat_In with
      signature eq ==> flat_equiv ==> iff as flat_In_morphism.
  Proof. intros k m m' hmm'.
         split; intros h%flat_In_lookup_Some;
         [rewrite hmm' in h|rewrite <- hmm' in h];
         destruct h; eapply flat_lookup_Some_In; eassumption.
  Qed.
  
  Fixpoint flat_insert_aux (k: key) (p: val) (l: list (key * val)) :=
    match l with
    | nil => (k, p) :: nil
    | (k', p') :: tl => if eq_dec k k' then (k', p) :: tl
                     else (k', p') :: flat_insert_aux k p tl
    end.

  Lemma flat_insert_aux_In: forall k p l,
      In k (map fst l) -> map fst l = map fst (flat_insert_aux k p l).
  Proof.
    induction l as [|[k' p'] l].
    + intro h. inversion h. 
    + intro h. simpl in h |- *.
      destruct h. rewrite if_true by congruence. reflexivity.
      destruct eq_dec. reflexivity.
      rewrite IHl by assumption. reflexivity.
  Qed.

  Lemma flat_insert_aux_not_In: forall k p l,
      ~ In k (map fst l) -> Add k (map fst l) (map fst (flat_insert_aux k p l)).
  Proof.
    induction l as [|[k' p'] l].
    + constructor.
    + intro h. simpl in h |- *. apply not_in_cons in h.
      destruct eq_dec. destruct h; contradiction.
      constructor. now apply IHl.
  Qed.

  Lemma flat_insert_aux_NoDup: forall k p l,
      NoDup (map fst l) -> NoDup (map fst (flat_insert_aux k p l)).
  Proof.
    intros * h.
    induction l as [|[k' p'] l].
    + constructor. apply in_nil. constructor.
    + simpl. destruct eq_dec.
      subst. assumption.
      simpl in h |- *.
      destruct (in_dec eq_dec k (map fst l)) as
          [hin%(flat_insert_aux_In _ p)|hnin%(flat_insert_aux_not_In _ p)].
      - rewrite <- hin. assumption.
      - apply NoDup_cons_iff in h.
        constructor.
        rewrite (Add_in hnin).
        now intros [heq|hin].
        now apply IHl.
  Qed.

  Definition flat_insert (k: key) (p: val) (m: flat key): flat key :=
    mk_flat _ (flat_insert_aux k p (elements m)) (flat_insert_aux_NoDup _ _ _ (nodup m)).

  Lemma flat_lookup_insert: forall k p m k',
      flat_lookup k' (flat_insert k p m) = if eq_dec k k' then Some p else flat_lookup k' m.
  Proof.
    intros. unfold flat_insert, flat_lookup.
    simpl. induction (elements m) as [|[k1 n1] elts].
    + cbn. destruct eq_dec; [rewrite if_true by congruence | rewrite if_false by congruence]; reflexivity.
    + simpl. destruct eq_dec.
      destruct eq_dec; cbn; [rewrite proj_sumbool_is_true|rewrite proj_sumbool_is_false]; congruence.
      destruct eq_dec. cbn.
      rewrite proj_sumbool_is_false by congruence. reflexivity.
      cbn. destruct eq_dec; cbn. reflexivity. assumption.
  Qed.

  Corollary flat_lookup_insert_same: forall k p m,
      flat_lookup k (flat_insert k p m) = Some p.
  Proof.
    intros. rewrite flat_lookup_insert. rewrite if_true; reflexivity.
  Qed.

  Add Parametric Morphism: flat_insert with
      signature eq ==> eq ==> flat_equiv ==> flat_equiv as flat_insert_morphism.
  Proof.
    intros k p m m' hmm'.
    unfold flat_equiv in hmm' |- *.
    intro k1. do 2 rewrite flat_lookup_insert.
    destruct eq_dec; congruence.
  Qed.

  Lemma flat_double_insert_same: forall k p p' m,
      flat_insert k p (flat_insert k p' m) =f= flat_insert k p m.
  Proof.
    intros k p p' [elts nodup]. unfold flat_equiv. intro k1.
    do 3 rewrite flat_lookup_insert.
    destruct eq_dec; reflexivity.
  Qed.

  Lemma flat_double_insert_commute: forall k p k' p' m,
      k <> k' ->
      flat_insert k p (flat_insert k' p' m) =f= flat_insert k' p' (flat_insert k p m).
  Proof.
    intros * hkk'.
    unfold flat_equiv. intro k1.
    do 4 rewrite flat_lookup_insert.
    destruct eq_dec.
    + rewrite if_false; congruence.
    + reflexivity.
  Qed.
  
End K.
