Require Import VST.floyd.proofauto.
Import Share.
Import sepalg.

Search O boolean_alg.height.

Module Type REBASE.
  Parameter rebase: forall (a b: share) (x y: share), Prop.
  Axiom rebase_root: forall a b, rebase a b a b.
  Axiom rebase_join1: forall a b x1 x2 x y,
     join x1 x2 x ->
     rebase a b x1 y /\ rebase a b x2 y <-> rebase a b x y.
  Axiom rebase_join2: forall a b x y1 y2 y,
     join y1 y2 y ->
     rebase a b x y1 /\ rebase a b x y2 <-> rebase a b x y.
  Axiom rebase_bot:  forall a b,
     rebase a b bot bot.
  Axiom rebase_sub:  forall a b x y,
     rebase a b x y -> join_sub x a /\ join_sub y b.
End REBASE.

Module Rebase : REBASE.
  
   Fixpoint factors' (h: nat) (a: share) : list share :=
   if dec_share_full a then a::nil
   else if dec_share_identity a then nil
   else 
   match h with
   | O => nil (* impossible *)
   | S h' => let (x,y) := split a in factors' h' x ++ factors' h' y
   end.

  Definition factors a := factors' (tree_height a) a.

  Fixpoint join_list (al: list share) (s: share) : Prop :=
    match al with
    | a::al' => exists s', join_list al' s' /\ join a s' s
    | nil => s=bot
    end.

Axiom tree_height_0: (* easy, this is already proved in the model *)
  forall s, tree_height s = O -> s=top \/ s=bot.

Axiom split_height: (* easy, this is already proved in the model *)
  forall n a x y,
    tree_height a = S n ->
    split a = (x,y) ->
     (tree_height x <= n /\ tree_height y <= n)%nat.

Axiom sub_eq:  (* easy, this is the definition of "sub" *)
  forall x y,
  sub x y = 
  match eq_dec (glb x y) y with
  | left _ => Some (glb x (comp y))
  | right _ => None
  end.
 
Axiom glb_comp_rel:   (* not so easy, this needs to be proved in the model *)
 forall a x, glb a (comp (rel a x)) = rel a (comp x).

  Lemma factors'_inc:
  forall x n m, (tree_height x <= n -> tree_height x <= m ->
    factors' n x = factors' m x)%nat.
  Proof.
   intros.
   remember (tree_height x) as h.
   assert (Hh: (tree_height x <= h)%nat) by omega. clear Heqh.
   revert x n m Hh H H0; induction h; simpl; intros.
   assert (tree_height x = 0)%nat by omega.
   apply tree_height_0 in H1; destruct H1; subst.
   destruct n,m; simpl; auto.
   if_tac; auto.
   contradiction H1; apply fullshare_full.
   if_tac; auto.
   contradiction H1; apply fullshare_full.
   if_tac; auto.
   contradiction H1; apply fullshare_full.
   destruct n,m; simpl; auto.
   if_tac; auto; if_tac; auto;  contradiction bot_identity.
   if_tac; auto; if_tac; auto;  contradiction bot_identity.
   if_tac; auto; if_tac; auto;  contradiction bot_identity.
   destruct n,m; simpl; auto; try omega.
   if_tac; auto. if_tac; auto.
   destruct (split x) as [a b] eqn:?H.
   destruct (tree_height x) eqn:?H.
   apply tree_height_0 in H4; destruct H4; subst.
   contradiction H1; apply fullshare_full.
   contradiction bot_identity.
   destruct (split_height _ _ _ _ H4 H3).
   f_equal; apply IHh; try omega.
 Qed.
  
 Lemma join_list_app:
      forall a b x y z, join_list a x -> join_list b y -> join x y z ->
            join_list (a++b) z.
  Proof.
   intros.
   revert x H z H1; induction a; simpl; intros.
   subst. apply join_unit1_e in H1. subst; auto. apply bot_identity.
   destruct H as [s' [? ?]].
   destruct (join_assoc H2 H1) as [u [? ?]].
   specialize (IHa _ H).
   apply IHa in H3.
   exists u; split; auto.
  Qed.

  Lemma factors_join':
   forall n a, (tree_height a <= n)%nat -> join_list (factors a) a.
  Proof.
   unfold factors.
   induction n; intros.
  -
   assert (tree_height a = O) by omega.  rewrite H0.
   simpl.
   if_tac. simpl; exists bot; auto.
   apply tree_height_0 in H0; destruct H0; subst.
   contradiction H1. apply fullshare_full.
   rewrite if_true; simpl; auto.
  -
   destruct (tree_height a) eqn:?H; simpl.
   if_tac. simpl; exists bot; auto.
   apply tree_height_0 in H0; destruct H0; subst.
   contradiction H1. apply fullshare_full.
   rewrite if_true; simpl; auto.
   destruct (split a) as [x y] eqn:?H.
   destruct (split_height _ _ _ _ H0 H1).
   assert (tree_height x <= n)%nat by omega.
   assert (tree_height y <= n)%nat by omega.
   pose proof (IHn _ H4).
   pose proof (IHn _ H5). clear IHn.
   if_tac. simpl. exists bot; auto.
   if_tac. simpl.  apply identity_share_bot; auto.
   replace (factors' n0 x) with (factors' (tree_height x) x)
      by (apply factors'_inc; omega).
   replace (factors' n0 y) with (factors' (tree_height y) y)
      by (apply factors'_inc; omega).
   eapply join_list_app; try eassumption.
   apply split_join in H1. auto.
  Qed.

  Lemma factors_join:
   forall a, join_list (factors a) a.
  Proof.
  intros.
  eapply factors_join'.
  apply Nat.le_refl.
  Qed.

  Fixpoint interp (al: list bool) : share :=
  match al with
  | nil => top
  | b::al' => rel (if b then Rsh else Lsh) (interp al')
  end.

 Lemma full_e: forall a, full a -> a=top.
 Proof. intros.
  apply full_maximal in H.
 apply H. apply top_correct'.
 Qed.

  Lemma factors_interp:
  forall a sh,
  In a (factors sh) ->
  exists bl, a = interp bl.
 Proof.
 intros.
 unfold factors in H.
 remember (tree_height sh) as n.
 assert (tree_height sh <= n)%nat by omega.
 clear Heqn.
 revert sh H0 a H.
 induction n; simpl; intros.
 if_tac in H. simpl in H. destruct H; try contradiction.
 apply full_e in H1. subst.
 exists nil. simpl.   reflexivity.
 if_tac in H. inv H. inv H.
 if_tac in H. destruct H; try contradiction. apply full_e in H1.
 subst. exists nil; reflexivity.
 if_tac in H. inv H.
 destruct (tree_height sh) eqn:?H.
 destruct (tree_height_0 _ H3); subst.
 contradiction H1; apply fullshare_full.
 contradiction H2; apply bot_identity.
 destruct (split sh) as [x y] eqn:?H.
 apply in_app in H.
 destruct (split_height _ _ _ _ H3 H4).
 destruct H.
 apply IHn in H; auto. omega.
 apply IHn in H; auto. omega.
 Qed.

 Lemma interp_app: forall al bl, interp (al++bl)  = rel (interp al) (interp bl).
 Proof.
 induction al; intros; simpl; auto.
 rewrite rel_top2; auto.
 destruct a; rewrite IHal, rel_assoc; auto.
 Qed.

Lemma rel_join' : forall a x y z,
  nonidentity a ->
  join (rel a x) (rel a y) (rel a z) ->
  join x y z.
Proof.
  intros.
  assert (a <> bot). intro. subst. apply H. apply bot_identity.
  inv H0. 
  replace bot with (rel a bot) in H2 by apply rel_bot1.
  rewrite <- rel_preserves_glb in H2.
  apply rel_inj_l  in H2; auto.
  rewrite <- rel_preserves_lub in H3.
  apply rel_inj_l  in H3; auto.
  split; auto.
Qed.

Lemma rel_join3 : forall a x y s,
  nonidentity a ->
  join (rel a x) s (rel a y) ->
  exists z, s = rel a z /\ join x z y.
Proof.
  simpl; intros.
  apply sub_join in H0.
  rewrite sub_eq in H0.
  if_tac in H0; inv H0.
  rewrite <- rel_preserves_glb in H1.
  apply rel_inj_l in H1.
  2:{ intro; subst. apply H. apply bot_identity. }
  exists (glb y (comp x)).
split.
2:{
rewrite <- H1 at 1.
split.
rewrite (glb_commute y (comp x)).
rewrite glb_assoc.
rewrite <- (glb_assoc x).
rewrite comp2.
rewrite (glb_commute bot), !glb_bot. auto.
rewrite <- distrib1.
rewrite comp1. rewrite glb_top. auto.
}
rewrite rel_preserves_glb.
clear.
assert (glb a (comp (rel a x)) = glb a (rel a (comp x))).
2:{
transitivity (glb (rel a y) (glb a (comp (rel a x)))).
rewrite <- glb_assoc.
replace (glb (rel a y) a) with (rel a y).
auto.
rewrite <- (rel_top1 a) at 3.
rewrite <- rel_preserves_glb.
rewrite glb_top. auto.
rewrite H.
clear.
f_equal.
rewrite <- (rel_top1 a) at 1.
rewrite <- rel_preserves_glb.
rewrite (glb_commute top), glb_top.
auto.
}
rewrite <- (rel_top1 a) at 3.
rewrite <- rel_preserves_glb.
rewrite (glb_commute top), glb_top.
apply glb_comp_rel.
Qed.

Lemma rel_join_sub3 : forall a x y,
  nonidentity a ->
  join_sub (rel a x) (rel a y) -> join_sub x y.
Proof.
intros.
destruct H0 as [s ?].
apply rel_join3 in H0; auto.
destruct H0 as [z [? ?]].
exists z; auto.
Qed.

Lemma interp_not_bot: forall el, nonidentity (interp el).
Proof.
induction el; simpl.
intro. apply identity_share_bot in H. apply nontrivial; auto.
unfold nonidentity in *.
contradict IHel.
apply rel_nontrivial in IHel.
destruct IHel; auto.
destruct a.
contradiction (Rsh_nonidentity).
contradiction (Lsh_nonidentity).
Qed.

Lemma Lsh_not_top: Share.Lsh <> Share.top.
Proof.
unfold Share.Lsh.
case_eq (Share.split Share.top); intros.
simpl; intro. subst.
apply nonemp_split_neq1 in H.
apply H; auto.
apply top_share_nonidentity.
Qed.

Lemma join_sub_rel_disj:
  forall a b c d, 
    glb a b = bot ->
    nonidentity a ->
    nonidentity c ->
    join_sub (rel a c) (rel b d) -> 
    False.
Proof.
intros * H H0 H2 H3.
pose proof I.
rename c into sh.
rename b into u.
destruct H3 as [b [_ ?]].
pose proof (share_rel_nonidentity H0 H2).
pose proof (rel_leq a sh).
pose proof (rel_leq u d).
rewrite <- H3 in H6; clear H3.
pose proof (lub_upper1 (rel a sh) b).
apply leq_join_sub in H3.
pose proof (join_sub_trans H3 H6); clear H3 H6.
forget (rel a sh) as c. clear sh H2.
destruct H5 as [e [? ?]]. destruct H7 as [f [? ?]].
subst.
rewrite <- distrib2 in H.
clear - H4 H.
apply lub_bot_e in H; destruct H. subst.
apply H4. apply bot_identity.
Qed.

Lemma joins_list_rel:
 forall d (Nd: nonidentity d) cl sh bl,
   join_list cl sh ->
   Forall2 (fun a b => a = rel d b) cl bl ->
   exists sh', join_list bl sh'.
Proof.
intros.
revert sh H bl H0.
induction cl; intros; destruct bl; inv H0.
eauto.
destruct H as [s' [? ?]].
specialize (IHcl _ H _ H6).
destruct IHcl as [sh' ?].
assert (joins t0 sh').
2:{ destruct H2 as [x ?]; exists x.  simpl. exists sh'; split; auto. }
assert (joins (rel d t0) s') by eauto.
clear - H6 H2 H H1 Nd.
assert (s' = rel d sh'). {
 clear - H1 H H6. 
 revert sh' s' H H1; induction H6; intros.
 hnf in H,H1; subst. symmetry; apply rel_bot1.
 subst x.
 destruct H0 as [a [? ?]].
 destruct H1 as [b [? ?]].
 specialize (IHForall2 _ _ H H1).
 subst.
 apply (join_eq H0 (rel_join d _ _ _ H2)).
}
subst s'.
destruct H2 as [x H2].
destruct (rel_join2 _ _ _ _ Nd H2) as [e [? ?]].
subst x.
eauto.
Qed.

 Definition rel_interp_sub:
  forall al sh,
   join_sub sh (interp al) ->
  exists sh', sh = rel (interp al) sh'.
 Proof.
  intros.
  set (x := factors sh).
  pose proof (factors_join sh).
  assert (Forall (fun a => exists sh', a = rel (interp al) sh') (factors sh)). {
    clear - H.
    assert (Forall (fun a => join_sub a (interp al)) (factors sh)). {
     forget (interp al) as b. clear al.
     pose proof (factors_join sh).
     assert (Forall (fun a => join_sub a sh) (factors sh)).
     2:{ clear - H1 H; induction H1; constructor; auto. eapply join_sub_trans; eassumption. }
     clear - H0.
     forget (factors sh) as s. 
     revert sh H0; induction s; intros; constructor; auto.
     destruct H0 as [s' [? ?]]. exists s'; auto.
     destruct H0 as [s' [? ?]].
     apply IHs in H.
     apply join_comm in H0; apply join_join_sub in H0.
     clear - H H0.
     induction H; constructor; auto.
     eapply join_sub_trans; eassumption. 
   }
    clear H.
    remember (factors sh) as cl.
    change cl with (nil++cl) in Heqcl,H0.
    forget (@nil share) as dl.
    revert dl Heqcl H0.
    induction cl; simpl; intros; auto.
    constructor; auto.
    destruct (factors_interp a sh) as [el ?].
    rewrite <- Heqcl. apply in_app. right. left. auto.
    subst a.
    rewrite -> Forall_forall in H0.
    specialize (H0 (interp el)).
    spec H0.  apply in_app. right. left. auto.
    assert (exists f, el = al++f). {
       clear - H0.
     revert al H0.
     induction el as [ | e el] ; intros. {
       exists nil. simpl in *. replace al with (@nil bool); [reflexivity|].
       destruct al; auto. elimtype False.
       simpl in H0. destruct b.
       pose proof (rel_leq Rsh (interp al)).
       pose proof (join_sub_trans H0 H); clear H0 H.
       destruct H1 as [? H]; apply juicy_mem_lemmas.join_top in H.
       contradiction juicy_mem.Rsh_not_top.
       pose proof (rel_leq Lsh (interp al)).
       pose proof (join_sub_trans H0 H); clear H0 H.
       destruct H1 as [? H]; apply juicy_mem_lemmas.join_top in H.
       contradiction Lsh_not_top.
    }
    destruct al as [ | a al].
    exists (e::el); auto.
    simpl in H0.
    destruct e,a.
  +
    apply rel_join_sub3 in H0; [ | apply Rsh_nonidentity].
    apply IHel in H0. destruct H0 as [f ?].
    exists f; simpl; f_equal; auto.
  +
    elimtype False; clear - H0.
    apply join_sub_rel_disj in H0; auto.
    apply glb_Rsh_Lsh.
    apply Rsh_nonidentity.
    apply interp_not_bot.
  +
    elimtype False; clear - H0.
    apply join_sub_rel_disj in H0; auto.
    apply glb_Lsh_Rsh.
    apply Lsh_nonidentity.
    apply interp_not_bot.
  +
    apply rel_join_sub3 in H0; [ | apply Lsh_nonidentity].
    apply IHel in H0. destruct H0 as [f ?].
    exists f; simpl; f_equal; auto.
 }
destruct H as [f ?].
exists (interp f).
subst el.
rewrite interp_app. auto.
apply IHcl with (dl++[a]).
rewrite app_ass. auto.
rewrite app_ass; auto.
}
clear x.
assert (exists bl, Forall2 (fun a b => a = rel (interp al) b) (factors sh) bl).
clear - H1.
induction (factors sh). exists nil; auto.
inv H1.
destruct H2 as [sh' ?].
apply IHl in H3.
destruct H3 as [bl ?].
exists (sh'::bl). constructor; auto.
destruct H2 as [bl ?].
assert (exists sh', join_list bl sh'). {
  forget (factors sh) as cl.
  assert (Nd := interp_not_bot al).
  forget (interp al) as d. clear H1 H. clear - H0 H2 Nd.
 eapply joins_list_rel; eauto.
}
destruct H3 as [sh' ?].
exists sh'.
assert (factors sh = map (rel (interp al)) bl). {
 forget (interp al) as c; clear al H1 sh' H3.
 clear - H2. induction H2; simpl; auto. subst. f_equal.
}
rewrite H4 in H0.
assert (join_list (map (rel (interp al)) bl) (rel (interp al) sh')).
clear - H3.
forget (interp al) as c.
revert sh' H3; induction bl; simpl; intros. subst. apply rel_bot1.
  destruct H3 as [s' [? ?]]. apply IHbl in H.
  exists (rel c s'); split; auto.
  apply rel_join; auto.
  clear - H0 H5.
  forget (rel (interp al) sh') as d.
  forget (map (rel (interp al)) bl) as u.
  revert sh d H0 H5; induction u; simpl; intros; subst; auto.
  destruct H0 as [s1 [? ?]]; destruct H5 as [s2 [? ?]].
  specialize (IHu _ _ H H1). subst. eapply join_eq; eassumption.
Qed.

 Fixpoint splitn n sh :=
 match n with
 | O => sh::nil
 | S n' => let (x,y) := split sh in x::splitn n' y
 end.

  Definition rebase1 (a: share) (x y: share) : Prop :=
    x <= a /\
    let al := factors a in
    let xl := map (glb x) al in 
    exists yl, 
      Forall2  (fun x y => x = rel a y) xl yl /\
      join_list yl y.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z: C)
                     (l : list A) (l' : list B) (l'': list C),
                   R x y z->
                   Forall3 R l l' l'' ->
                   Forall3 R (x :: l) (y :: l') (z::l'').

Inductive Forall4 {A B C D : Type} (R : A -> B -> C -> D -> Prop)
  : list A -> list B -> list C -> list D -> Prop :=
    Forall4_nil : Forall4 R [] [] [] []
  | Forall4_cons : forall (a : A) (b : B) (c: C) (d: D)
                     (al : list A) (bl : list B) (cl: list C) (dl: list D),
                   R a b c d->
                   Forall4 R al bl cl dl ->
                   Forall4 R (a :: al) (b :: bl) (c:: cl) (d::dl).

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

Section Rebase1.

 Variable a: t.
 Variable Na: nonidentity a.

Lemma factors_nonnil: factors a <> nil.
Proof.
rename Na into H.
intro.
unfold factors in H0.
remember (tree_height a) as n.
assert (tree_height a <= n)%nat by omega.
clear Heqn.
revert a H H1 H0.
induction n; simpl; intros.
if_tac in H0. inv H0.
assert (tree_height a = O) by omega.
apply tree_height_0 in H3.
destruct H3; subst.
contradiction fullshare_full.
contradiction bot_identity.
if_tac in H0. inv H0.
if_tac in H0.
contradiction.
destruct (split a) as [x y] eqn:?.
destruct (tree_height a) eqn:?H.
apply tree_height_0 in H4.
destruct H4; subst.
contradiction fullshare_full.
contradiction bot_identity.
destruct (split_height _ _ _ _ H4 Heqp).
destruct (factors' n x) eqn:?H.
pose proof (split_nontrivial' _ _ _ Heqp).
apply IHn in H7; auto.
intro; auto.
omega.
inv H0.
Qed.

  Lemma rebase1_exists: forall x, 
   x <= a ->
   exists y, rebase1 a x y.
    intros.
    unfold rebase1.
  assert (H1: exists bll: list (list bool), exists cl,
           Forall3 (fun a bl c => a = interp bl /\ glb x a = rel a c)
               (factors a) bll cl). {
 assert (H5 := trivial_Forall_inclusion (factors a)).
 clear - H5.
 set (al := factors a).
 assert (al = factors a) by reflexivity.
 change (Forall (fun x => In x (factors a)) al) in H5.
 clearbody al. clear H.
 induction H5. exists nil, nil. constructor.
 rename x0 into a1.
 destruct IHForall as [bll [cl ?]].
 apply factors_interp in H.
 destruct H as [bl H].
 destruct (rel_interp_sub bl (glb x a1)) as [c ?].
 subst a1. apply leq_join_sub. apply glb_lower2.
 exists (bl::bll), (c::cl). constructor; auto.
 split; auto.
 rewrite H at 2; auto.
}
destruct H1 as [bll [cl H0]].
pose (dl := splitn (pred (length cl)) top).
assert (length cl > 0)%nat. {
 replace (length cl) with (length (factors a)).
 pose proof factors_nonnil.
 destruct (factors a). contradiction H1; auto. simpl; omega.
 forget (factors a) as al.
 clear - H0. induction H0; auto. simpl; f_equal; auto.
}
Admitted.  (* looks promising *)

Lemma join_list_eq:
 forall al b c, join_list al b -> join_list al c -> b=c.
Proof.
induction al; intros.
red in H,H0; subst; auto.
destruct H as [x [? ?]].
destruct H0 as [y [? ?]].
specialize (IHal _ _ H H0).
subst.
eapply join_eq; eauto.
Qed.

Lemma rebase1_eq1: forall x y y', 
    rebase1 a x y -> rebase1 a x y' -> y=y'.
intros.
destruct H, H0.
remember (factors a) as al eqn:?H.
simpl in *.
clear H0.
destruct H1 as [yl [? ?]].
destruct H2 as [zl [? ?]].
assert (yl=zl). {
 forget (map (glb x) al) as bl.
 clear - H0 H2 Na.
 revert zl H2; induction H0; destruct zl; intros; inv H2; auto.
 f_equal; auto.
 apply rel_inj_l in H5; auto.
 red in Na. contradict Na. subst. apply bot_identity.
}
subst zl; clear H2.
eapply join_list_eq; eauto.
Qed.

Lemma rebase1_eq2: forall x x' y, 
    rebase1 a x y -> rebase1 a x' y -> x=x'.
Proof.
intros.
destruct H,H0.
remember (factors a) as al eqn:?H.
simpl in *.
destruct H1 as [yl [? ?]].
destruct H2 as [zl [? ?]].
assert (HN: Forall nonidentity (factors a)). {
  clear.
  apply Forall_forall; intros.
  apply factors_interp in H. destruct H; subst.
  apply interp_not_bot.
}
assert (exists a', join_list (factors a) a') by ( pose proof (factors_join a); eauto).
assert (Forall (fun x => In x (factors a)) al) by admit.
clear H3.
assert (yl = zl). { 
 revert al y yl zl HN H1 H2 H4 H5 H6 H7; induction (factors a); intros; destruct al; inv H7;
   destruct yl; inv H1; destruct zl; inv H2; auto.
 inv H9.
 inv HN. rename H7 into HN. rename H3 into HN0.
 simpl in H9.
 destruct H4 as [y' [? ?]].
 destruct H5 as [z' [? ?]].
 destruct H6 as [a' [sh' [H6 ?]]].
 specialize (IHl al y' yl zl).
 specialize (IHl HN H13 H14).
 assert (t0=t1). {
   

 destruct H9.
 subst a0.
 clear H3.
 revert y yl H1 H4 zl H2 H5.
 induction H6; intros.
 inv H1; inv H2. auto.
 destruct yl; inv H2.
 destruct zl; inv H3.
 destruct H4 as [u [? ?]].
 destruct H5 as [v [? ?]].
 
 specialize (IHForall 
 f_equal; auto.
  
 

destruct yl
de
subst al.

Search Forall2.
(*

Set Nested Proofs Allowed.
Lemma joins_list_rel':
 forall d (Nd: nonidentity d) cl sh bl,
   join_list bl sh ->
   Forall2 (fun a b => a = rel d b) cl bl ->
   exists sh', join_list cl sh'.
Admitted.

destruct (joins_list_rel' _ Na _ _ _ H4 H1) as [yl' ?].
destruct (joins_list_rel' _ Na _ _ _ H5 H2) as [zl' ?].
*)
Admitted.

Lemma rebase1_ident: forall x, 
       rebase1 a a x <-> x=top.
Proof.
intros.
unfold rebase1.
split; intro.
destruct H as [_ H].
destruct H as [yl [? ?]].
remember (map (glb a) (factors a)) as al.
pose proof factors_nonnil.
pose proof (factors_join a).
assert (al = factors a). {
  clear - Heqal. admit.
}
clear Heqal.
rewrite <- H3 in H2, H1.
clear H3.
Admitted.

Lemma rebase1_join: forall x x' y y' z,
   rebase1 a x x' -> rebase1 a y y' -> 
   join x y z -> exists z', rebase1 a z z' /\ join x' y' z'.
Admitted.

Lemma rebase1_join2: forall x x' y y' z',
   rebase1 a x x' -> rebase1 a y y' -> 
   join x' y' z' -> exists z, rebase1 a z z' /\ join x y z.
Admitted.

Lemma rebase1_join3: forall x x' y z z',
   rebase1 a x x' -> rebase1 a z z' -> 
   join x y z -> exists y', rebase1 a y y' /\ join x' y' z'.
Admitted.

Lemma rebase1_join4: forall x x' y' z z',
   rebase1 a x x' -> rebase1 a z z' -> 
   join x' y' z' -> exists y, rebase1 a y y' /\ join x y z.
Admitted.

Lemma rebase1_bot: forall x, rebase1 a bot x <-> x=bot.
Proof.
intros.
split; intros.
-
pose proof (bot_join_eq x).
pose proof (proj2 (rebase1_ident top) (eq_refl _)).
destruct (rebase1_join _ _ _ _ a H H1 (bot_join_eq a)) as [z' [? ?]].
pose proof (rebase1_eq1 _ _ _ H1 H2); subst z'; clear H2.
pose proof (bot_join_eq top).
apply (join_canc H3 H2).
-
subst.
destruct (rebase1_exists bot).
apply bot_correct.
pose proof (proj2 (rebase1_ident top) (eq_refl _)).
pose proof (bot_join_eq a).
destruct (rebase1_join _ _ _ _ _ H H0 H1) as [z [? ?]].
pose proof (juicy_mem_lemmas.join_top _ _ (join_comm H3)).
subst z.
pose proof (bot_join_eq top).
pose proof (join_canc H3 H4). subst x.
auto.
Qed.

Lemma rebase1_sub: forall x z, rebase1 a x z -> join_sub x a.
  intros.
  apply leq_join_sub.
  apply H.
Qed.

End Rebase1.

 Definition rebase a b x y :=
    exists z, rebase1 a x z /\ rebase1 b y z.
 
Section Rebase.
 Variable a b : t.
 Variable Na: nonidentity a.
 Variable Nb: nonidentity b.

 Lemma rebase_root: rebase a b a b.
 Proof.
   intros. 
     destruct (rebase1_exists a Na a).
     apply ord_refl.
     exists x; split; auto. apply rebase1_ident; auto. apply rebase1_ident in H; auto.
  Qed.

  Lemma rebase_symm: forall x y, rebase a b x y -> rebase b a y x.
  Proof.
  intros. destruct H as [c [? ?]]. exists c; split; auto.
  Qed.

  Lemma rebase_join1: forall x1 x2 x y1 y2 y,
     rebase a b x1 y1 -> rebase a b x2 y2 -> join x1 x2 x -> 
     (join y1 y2 y <-> rebase a b x y).
  Proof.
    intros.
    destruct H as [c [? ?]].
    destruct H0 as [d [? ?]].
    destruct (rebase1_join a Na _ _ _ _ _ H H0 H1) as [z [? ?]].
    split; intro.
    -
    destruct (rebase1_join b Nb _ _ _ _ _ H2 H3 H6) as [u [? ?]].
    pose proof (join_eq H5 H8); subst u; clear H8.
    exists z; split; auto.
   -
    destruct H6 as [e [? ?]].
    pose proof (rebase1_eq1 _ Na _ _ _ H4 H6); subst e; clear H6.
    destruct (rebase1_join2 b Nb _ _ _ _ _ H2 H3 H5) as [z' [? ?]].
    pose proof (rebase1_eq2 b Nb _ _ _ H7 H6); subst z'; clear H7.
    auto.
  Qed.

  Lemma rebase_join2: forall x1 x2 x y1 y2 y,
     rebase a b x1 y1 -> rebase a b x y -> join x1 x2 x ->
     (join y1 y2 y <-> rebase a b x2 y2).
  Proof.
    intros.
    destruct H as [c [? ?]].
    destruct H0 as [d [? ?]].
    split; intros.
    -
    destruct (rebase1_join3 a Na _ _ _ _ _ H H0 H1) as [z [? ?]].
    destruct (rebase1_join3 b Nb _ _ _ _ _ H2 H3 H4) as [u [? ?]].
    pose proof (join_canc (join_comm H6) (join_comm H8)); subst u; clear H8.
    exists z; split; auto.
    -
    destruct H4 as [z [? ?]].
    destruct (rebase1_join a Na _ _ _ _ _ H H4 H1) as [u [? ?]].
    pose proof (rebase1_eq1 a Na _ _ _ H0 H6); subst u; clear H6. 
    destruct (rebase1_join2 b Nb _ _ _ _ _ H2 H5 H7) as [v [? ?]].
    pose proof (rebase1_eq2 b Nb _ _ _ H3 H6); subst v; clear H6.
    auto.    
  Qed.

  Lemma rebase_bot: rebase a b bot bot.
  Proof.
   intros.
   exists bot; split;    apply rebase1_bot; auto.
  Qed.

  Lemma rebase_sub:  forall x y,
     rebase a b x y -> join_sub x a /\ join_sub y b.
  Proof.
    intros.
    destruct H as [z [? ?]].
    split; eapply rebase1_sub; eauto.
  Qed.
