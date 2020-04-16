Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.




Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Section TREES.
Context { V : Type } .
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.
 
 
 Inductive In (k : key) : tree -> Prop :=
  | InRoot l r x v :
       (k = x) -> In k (T l x v r )
  | InLeft l r x v' :
      In k l -> In k (T l x v' r)
  | InRight l r x v' :
      In k r -> In k (T l x v' r). 
 
Definition lt (t: tree) (k: key) := forall x : key, In x t -> k < x . 
Definition gt (t: tree) (k: key) := forall x : key, In x t -> k > x . 

Inductive sorted_tree : tree -> Prop :=
    | Sorted_Empty : sorted_tree E
    | Sorted_Tree x v l r : sorted_tree l -> sorted_tree r -> gt l x -> lt r x -> sorted_tree (T l x v r ).
 
Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.



Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.
 
 (* ghost tree properties and function *)
 
 Inductive ghost_tree: Type :=
 |  E_ghost :  ghost_tree
 | T_ghost: ghost_tree ->gname -> key -> V  -> ghost_tree -> gname -> ghost_tree .
 
 
 Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 r g2 x v :
       (k = x) -> In_ghost k (T_ghost l g1 x v r g2 )
  | InLeft_ghost l g1 r g2 x v' :
      In_ghost k l -> In_ghost k (T_ghost l g1 x v' r g2)
  | InRight_ghost l g1 r g2 x v' :
      In_ghost k r -> In_ghost k (T_ghost l g1 x v' r g2).
      

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k < x . 
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k > x . 

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
    | Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
    | Sorted_Ghost_Tree x v l g1 r g2 : sorted_ghost_tree l -> sorted_ghost_tree r -> gt_ghost l x -> lt_ghost r x -> sorted_ghost_tree (T_ghost l g1 x v r g2 ).
        
 
 Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree) (g1:gname) (g2:gname) : ghost_tree :=
 match s with
 | E_ghost => T_ghost E_ghost g1 x v E_ghost g2
 | T_ghost a ga y v' b gb => if  x <? y then T_ghost (insert_ghost x v a g1 g2) ga y v' b gb
                        else if (y <? x) then T_ghost a ga y v' (insert_ghost x v b g1 g2) gb else T_ghost a ga x v b gb
                        
 end.

 
End TREES.

 Lemma  sample_tree_correctness : sorted_tree (T (T (T E 1 1 E) 2 2 (T E 3 3 E)) 4 4 (T E 5 5 E)).
 Proof.
 apply Sorted_Tree. 
  + apply Sorted_Tree.
     -  apply Sorted_Tree. apply Sorted_Empty. apply Sorted_Empty. unfold gt. intros. inversion H. unfold lt;intros;inversion H.
     - apply Sorted_Tree. apply Sorted_Empty. apply Sorted_Empty. unfold gt. intros. inversion H. unfold lt;intros;inversion H.
     - unfold gt. intros. inversion H. rep_omega.  inversion H1. inversion H1.
     - unfold lt. intros. inversion H. rep_omega.  inversion H1. inversion H1.
  + apply Sorted_Tree. apply Sorted_Empty.  apply Sorted_Empty. unfold gt. intros. inversion H. unfold lt;intros;inversion H.
  + unfold gt. intros. inversion H. rep_omega.  inversion H1. rep_omega. inversion H6. inversion H6. inversion H1. rep_omega. inversion H6. inversion H6.
  + unfold lt. intros. inversion H. rep_omega. inversion H1. inversion H1.
Qed. 

Lemma value_in_tree : forall x v k (t: @tree val ), In k (insert x v t ) -> ( x = k) \/ In k t .
Proof.
intros.
induction t.
 - simpl in H. inversion H;subst; auto.
 - simpl in H. destruct (x <? k0) eqn: Heqn.
   * inversion H;subst. right. apply InRoot. auto. specialize ( IHt1 H1). destruct IHt1. left. auto. right. apply InLeft. auto. right. apply InRight. auto.
   * destruct (k0 <? x) eqn: Heqn'. inversion H;subst. right. apply InRoot. auto. right. apply InLeft. auto. specialize ( IHt2 H1). destruct IHt2. left. auto. right. apply InRight. auto.
      assert( k0 = x). {  apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. omega. } subst. right. inversion H;subst. apply InRoot. auto. apply InLeft. auto. apply InRight. auto.
Qed.


   Lemma insert_sorted : forall x v (t: @tree val ), sorted_tree t -> sorted_tree (insert x v t).
   Proof.
   intros.
   induction t.
   * simpl. apply Sorted_Tree.
     - auto.
     - auto.
     - unfold gt. intros. inversion H0.
     - unfold lt. intros. inversion H0.
   * simpl. destruct (x <? k)  eqn: Heqn. 
      - constructor. 
          + apply IHt1. inversion H; auto.
          + inversion H; auto.
          + unfold gt. intros. apply value_in_tree in H0. destruct H0. subst. apply Z.ltb_lt in Heqn. omega.  inversion H;subst. auto.
          +  unfold lt. intros. inversion H;subst. auto.
     - destruct (k <? x) eqn: Heqn'.
        + apply Sorted_Tree. inversion H;subst. auto. apply IHt2. inversion H. auto. unfold gt. intros. inversion H;subst. auto.
            unfold lt. intros.  apply value_in_tree in H0. destruct H0. subst. apply Z.ltb_lt in Heqn'. omega. inversion H;subst. auto.
         + assert( k = x). {  apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. omega. } subst. apply Sorted_Tree. inversion H;subst. auto. inversion H;subst. auto. inversion H;subst. auto. inversion H;subst. auto.
Qed.

Fixpoint left_keys ( k : key) ( t: @ tree Z ) : list key := 
  match t with 
      | E => nil
      | T a x v b => if ( x <? k ) then  x :: left_keys k a ++ left_keys k b else  left_keys k a 
      
   end.
   
 Fixpoint right_keys (k : key) ( t: @ tree Z ) : list key := 
  match t with 
      | E => nil
      | T a x v b => if ( x >? k ) then  x :: right_keys k a ++ right_keys k b else  right_keys k b      
   end.

Definition example := T (T (T E 1 1 E) 2 2 (T E 3 3 E)) 4 4 (T E 5 5 E).


Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.


Definition lsh1 := fst (slice.cleave Ews).
Definition lsh2 := snd (slice.cleave Ews).

Definition sh1 := fst (slice.cleave lsh1).
Definition sh2 := snd (slice.cleave lsh1).

Lemma readable_lsh1 : readable_share lsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_lsh2 : readable_share lsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma lsh1_lsh2_join : sepalg.join lsh1 lsh2 Ews.
Proof.
  apply slice.cleave_join; unfold lsh1, lsh2; destruct (slice.cleave Ews); auto.
Qed.

Hint Resolve readable_lsh1 readable_lsh2 lsh1_lsh2_join.

Lemma readable_sh1 : readable_share sh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_sh2 : readable_share sh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma sh1_sh2_join : sepalg.join sh1 sh2 lsh1.
Proof.
  apply slice.cleave_join; unfold sh1, sh2; destruct (slice.cleave Ews); auto.
Qed.

Hint Resolve readable_sh1 readable_sh2 sh1_sh2_join.

Inductive number : Type :=
 | Finite_Integer (n : Z)
 | Neg_Infinity
 | Pos_Infinity.
 
 Definition left (range:number * number) : number := match range with (n1,n2) => n1 end.
  Definition right (range:number * number) : number := match range with (n1,n2) => n2 end.
 
 Definition min_number a b :number :=
 match a with 
 | Finite_Integer a1 => match b with 
                                          | Finite_Integer b1 => Finite_Integer ( Z.min a1 b1)
                                          | Neg_Infinity => b
                                          | Pos_Infinity => a
                                          end
 | Neg_Infinity => a
 | Pos_Infinity => b
 end.

Definition max_number a b :number :=
 match a with 
 | Finite_Integer a1 => match b with 
                                          | Finite_Integer b1 => Finite_Integer ( Z.max a1 b1)
                                          | Neg_Infinity => a
                                          | Pos_Infinity => b
                                          end
 | Neg_Infinity => b
 | Pos_Infinity => a
 end.
 
 Definition less_than_equal a b: bool :=
    match a with 
 | Finite_Integer a1 => match b with 
                                          | Finite_Integer b1 => (a1 <=? b1)
                                          | Neg_Infinity => false
                                          | Pos_Infinity => true
                                          end
 | Neg_Infinity => true
 | Pos_Infinity => match b with 
                                  | Pos_Infinity => true
                                  | _ => false
                                  end
 end.
 
  Definition less_than a b: bool :=
    match a with 
 | Finite_Integer a1 => match b with 
                                          | Finite_Integer b1 => (a1 <? b1)
                                          | Neg_Infinity => false
                                          | Pos_Infinity => true
                                          end
 | Neg_Infinity => match b with 
                                          | Neg_Infinity => false
                                          | _ => true
                                          end
 | Pos_Infinity => false
 end.
 
 Definition range_inclusion r1 r2 : bool :=
              match r1, r2 with
              | (a1,a2), (b1,b2) => less_than_equal b1 a1 && less_than_equal a2 b2 end.
 
 Definition check_key_exist (k:Z) ( range : number * number) : bool :=
 match range with 
 | (Finite_Integer a1, Finite_Integer b1) => if ( andb (a1 <? k) (k <? b1) ) then true else false
 | (Neg_Infinity, Finite_Integer b1) => if ( k <? b1) then true else false
 | (Finite_Integer a1, Pos_Infinity) => if ( a1 <? k) then true else false
 | (Neg_Infinity, Pos_Infinity) => true
 | (_, _) => false end.
 
 Definition check_key_exist' (k:Z) ( range : number * number) : bool :=
 match range with | (a1, a2) => less_than a1 (Finite_Integer k) && less_than (Finite_Integer k)  a2 
 end.

Definition merge_range (a : number*number) (b:number*number) : (number*number):=
match a, b with 
|(a1,a2), (b1, b2) => (min_number a1 b1, max_number a2 b2)
end.

 
 Theorem merge_assoc: forall a b c, merge_range (merge_range a b) c = merge_range a (merge_range b c ).
 Proof.
 intros.
 destruct  a, b, c.
 unfold merge_range. f_equal.
  + destruct n eqn:En.
     - destruct n1 eqn:En1.
       { destruct n3 eqn: En3.
          - simpl. f_equal.  rewrite Z.min_assoc. reflexivity.
          -  simpl. reflexivity.
          - simpl. reflexivity.
        }
        { simpl; reflexivity.
        }
         { simpl. reflexivity.
          }
     - simpl. reflexivity.
     - simpl. reflexivity.
  + destruct n0 eqn:En0.
     - destruct n2 eqn:En2.
       { destruct n4 eqn: En4.
          - simpl. f_equal.  rewrite Z.max_assoc. reflexivity.
          -  simpl. reflexivity.
          - simpl. reflexivity.
        }
         { simpl; reflexivity.
        }
         { simpl. reflexivity.
          }
     - simpl. reflexivity.
     - simpl. reflexivity. 
 Qed.
 
  Theorem merge_comm: forall a b , merge_range a b = merge_range b a .
 Proof.
 intros.
 destruct a, b.
 unfold merge_range. f_equal.
 + destruct n eqn:En.
    - destruct n1 eqn:En1. simpl. f_equal.  apply Z.min_comm. reflexivity. reflexivity.
    - destruct n1 eqn:En1;simpl;reflexivity.
    - destruct n1 eqn:En1;simpl;reflexivity.
 + destruct n0 eqn:En0.
    - destruct n2 eqn:En2;simpl. f_equal.  apply Z.max_comm. reflexivity. reflexivity.
    - destruct n2 eqn:En2;simpl;reflexivity.
    - destruct n2 eqn:En2;simpl;reflexivity. 
Qed.

Global Obligation Tactic := idtac. 
Program Instance range_ghost : Ghost :=
  { G := (number*number); valid g := True; Join_G a b c := c =  merge_range a b }.
  
  Next Obligation.
  exists (fun _ => (Pos_Infinity,Neg_Infinity)). 
  + intros.
      hnf.
      simpl.
      destruct t.
      auto.
    + auto.  
  Defined.

 Next Obligation.
 constructor.
 + intros; hnf in *. subst;auto.
 + intros; hnf in *. exists (merge_range b c);split; hnf. auto. rewrite H0. rewrite H. apply merge_assoc.
 + intros; hnf in *. rewrite merge_comm. apply H.
 + intros; hnf in *.  destruct a,b. destruct a',b'. unfold merge_range in H, H0.  inversion H. inversion H0. clear H H0. f_equal.
     - destruct n1 eqn:En1.
        * destruct n5 eqn:En5.
         destruct n3 eqn: En3. 
          { simpl.  simpl in H4. rewrite H4 in H2. simpl in H2.  injection H2. intros. f_equal. symmetry. apply Z.min_l. rewrite <- Z.min_assoc in H. 
            symmetry in H .  apply Z.min_l_iff in H.  apply Z.min_glb_iff in H. rewrite  Z.min_le_iff. left. omega. }
          { destruct n in H2;simpl in H2;inversion H2. }
          { simpl. reflexivity. }
         simpl. reflexivity. 
        destruct n3 eqn: En3. 
        { simpl. simpl in H4. rewrite H4 in H2. simpl in H2. apply H2. }
        { destruct n in H2;simpl in H2;inversion H2. }
        { simpl. reflexivity. }
       * simpl. reflexivity.
       *  simpl. destruct n3. destruct n in H2;simpl in H2;inversion H2. destruct n in H2;simpl in H2;inversion H2. destruct n5;simpl;reflexivity. 
   - destruct n2 eqn:En2.
   * destruct n6 eqn:En6.
         destruct n4 eqn: En4. 
          { simpl.  simpl in H5. rewrite H5 in H3. simpl in H3.  injection H3. intros. f_equal. symmetry. apply Z.max_l. rewrite <- Z.max_assoc in H. 
            symmetry in H .  apply Z.max_l_iff in H.   apply Z.max_lub_iff in H. rewrite  Z.max_le_iff. left. omega. }
          { simpl. reflexivity. }
          { destruct n0 in H3;simpl in H3;inversion H3. }
        destruct n4 eqn: En4. 
        { simpl. simpl in H5. rewrite H5 in H3. simpl in H3. apply H3. }
        { simpl. reflexivity. }
        {  destruct n0 in H3;simpl in H3;inversion H3. }
        simpl. reflexivity. 
       * simpl. destruct n4. destruct n0 in H3;simpl in H3;inversion H3. destruct n6;simpl;reflexivity. destruct n0 in H3;simpl in H3;inversion H3. 
       * simpl. reflexivity.
Defined.

Next Obligation.
constructor.
Defined.

Global Obligation Tactic := repeat constructor || let x := fresh "x" in intros ?? x; repeat destruct x as [x ?]; simpl; auto.

Instance bst_ghost : Ghost := ref_PCM range_ghost.

Definition ghost_ref g r1 := ghost_reference(P := set_PCM) r1 g.
(* Definition in_tree g sh r1 := ghost_part(P := set_PCM) sh (Ensembles.Singleton _ r1) g. *)
Definition in_tree g r1 := EX sh: share, ghost_part(P := set_PCM) sh (Ensembles.Singleton _ r1) g.


Definition finite (S : Ensemble gname) := exists m, forall x, Ensembles.In _ S x -> (x <= m)%nat.

Lemma finite_new : forall S, finite S -> exists g, ~Ensembles.In _ S g.
Proof.
  intros ? [m ?].
  exists (Datatypes.S m); intros X.
  specialize (H _ X); omega.
Qed.

Lemma finite_add : forall S g, finite S -> finite (Add _ S g).
Proof.
  intros ?? [m ?].
  exists (max g m); intros ? X.
  rewrite Nat.max_le_iff.
  inv X; auto.
  inv H0; auto.
Qed.

Lemma finite_union : forall S1 S2, finite S1 -> finite S2 -> finite (Union _ S1 S2).
Proof.
  intros ?? [m1 H1] [m2 H2].
  exists (max m1 m2); intros ? X.
  rewrite Nat.max_le_iff.
  inv X; auto.
Qed.

Lemma finite_empty : finite (Empty_set _).
Proof.
  exists O; intros; inv H.
Qed.

Lemma finite_singleton : forall x, finite (Singleton _ x).
Proof.
  intros; exists x; intros; inv H; auto.
Qed.

Definition ghost_info :Type := (key * val* gname * gname)%type.

Lemma in_tree_add : forall g g1 s, finite s -> (in_tree g g1 * ghost_ref g s |--
  |==> EX g', (* EX sh1 sh2, !!(sepalg.join sh1 sh2 sh) && *) ghost_ref g (Add _ s g') * in_tree g g1 * in_tree g g')%I.
Proof.
  intros.
  unfold in_tree at 1; Intros sh; iIntros "H".
  iPoseProof (ref_sub with "H") as "%".
  rewrite ghost_part_ref_join.
  destruct (finite_new s) as [g' Hout]; auto.
  assert (Ensembles.In _ s g1).
  { destruct (eq_dec sh Tsh); subst.
    - constructor.
    - destruct H0 as (? & ? & ?); subst.
      repeat constructor. }
  iMod (ref_add(P := set_PCM) _ _ _ _ (Singleton _ g') (Add _ (Singleton _ g1) g') (Add _ s g') with "H") as "H".
  { repeat constructor.
    inversion 1; subst.
    inv H3; inv H4; contradiction. }
  { split; auto.
    constructor; intros ? X; inv X.
    inv H3; contradiction. }
  { intros; exists (Add _ c g'); split; auto.
    constructor; intros ? X; inv X.
    inv H5; contradiction Hout.
    destruct H3 as (? & ? & ?); subst.
    constructor; auto. }
  change (own g _ _) with (ghost_part_ref(P := set_PCM) sh (Add nat (Singleton nat g1) g') (Add nat s g') g).
  rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>"; iExists g'. (* Exists sh1 sh2. *)
  iDestruct "H" as "[in set]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := set_PCM) sh1 sh2 sh (Singleton _ g1) (Singleton _ g')); auto.
  iDestruct "in" as "[in1 in2]"; iFrame; auto.
  { (* This is a hack *)
    iVST.
    unfold in_tree.
    change (bi_sep (exp (fun sh0 : share => ghost_part(P := set_PCM) sh0 (Singleton nat g1) g))
                   (exp (fun sh0 : share => ghost_part(P := set_PCM) sh0 (Singleton nat g') g)))
    with (sepcon (exp (fun sh0 : share => ghost_part(P := set_PCM) sh0 (Singleton nat g1) g))
            (exp (fun sh0 : share => ghost_part(P := set_PCM) sh0 (Singleton nat g') g))).
    Exists sh1 sh2.
    change (sepcon (ghost_part(P := set_PCM) sh1 (Singleton nat g1) g)
                   (ghost_part(P := set_PCM) sh2 (Singleton nat g') g))
    with (bi_sep (ghost_part(P := set_PCM) sh1 (Singleton nat g1) g)
                 (ghost_part(P := set_PCM) sh2 (Singleton nat g') g)).
    iIntros "$". }
  { split; auto; constructor; intros ? X; inv X.
    inv H5; inv H6; contradiction. }
  { intro; contradiction H2; eapply Share.split_nontrivial; eauto. }
  { intro; contradiction H2; eapply Share.split_nontrivial; eauto. }
Qed.


(* helper for node_lock_inv_r *)
Definition node_lock_inv_r' (R : (val * (own.gname * (number * number * option ghost_info)) → mpred)) p gp lock :=
  sync_inv(A := (number * number * option ghost_info)) gp (uncurry (uncurry R p)) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
  malloc_token Ews tlock lock (* * malloc_token Ews t_struct_tree_t p *).

(* selflock *)
Definition node_lock_inv_r (R : (val * (own.gname * (number * number * option ghost_info)) → mpred)) p gp lock :=
      selflock (node_lock_inv_r' R p gp lock) lsh2 lock.

Definition ltree_r R (g_root:gname) sh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at sh t_struct_tree_t [StructField _lock] lock p * 
   lock_inv sh lock (node_lock_inv_r R p g_root lock)).

 Definition node_rep_r (g:gname)  R arg : mpred := let '(np, (g_current,(r,g_info))) := arg in
EX tp:val,
(* (field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * in_tree g lsh1 g_current * *)
(field_at Ews (t_struct_tree_t) [StructField _t] tp np) * malloc_token Ews t_struct_tree_t np * in_tree g g_current *
if eq_dec tp nullval then !!( g_info = None) && emp  else
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !! (g_info = Some(x,v,ga,gb) /\ Int.min_signed <= x <= Int.max_signed/\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v 
     /\ check_key_exist' x r) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp  *
    |> ltree_r R ga lsh1 pa locka * |> ltree_r R gb lsh1 pb lockb.

Definition node_rep_closed g  := HORec (node_rep_r g ).

Definition node_rep np g g_current r := node_rep_closed g (np, (g_current, r)) . 

Definition node_lock_inv_pred g p gp lock :=
  sync_inv(A := (number * number * option ghost_info)) gp (node_rep p g) *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
  malloc_token Ews tlock lock (* * malloc_token Ews t_struct_tree_t p *).
(* No malloc token for t_struct_tree_t because node_rep_r contains one *)

Definition node_lock_inv g p gp lock :=
  selflock (node_lock_inv_pred g p gp lock) lsh2 lock.

 Fixpoint ghost_tree_rep (t: @ ghost_tree val ) (g:gname) range : mpred := 
 match t, range with
 | E_ghost , _ => public_half g (range,@None ghost_info)
 | (T_ghost a ga x v b gb ), (l, r) => public_half g (range,(@Some ghost_info (x,v,ga,gb))) *  ghost_tree_rep a ga (l, Finite_Integer x) * ghost_tree_rep b gb (Finite_Integer x, r)
 end.
 
Fixpoint find_pure_tree (t : @ghost_tree val) : @tree val :=
  match t with 
  | E_ghost => E
  | (T_ghost a ga x v  b gb) => T (find_pure_tree a) x v (find_pure_tree b)
end.

Fixpoint find_ghost_set (t : @ghost_tree val) (g:gname) : Ensemble gname :=
  match t with 
  | E_ghost => (Ensembles.Singleton _ g)
  | (T_ghost a ga x v  b gb) => (Add _  (Union _ (find_ghost_set a ga) (find_ghost_set b gb)) g)
end.

Lemma find_ghost_set_finite : forall t g, finite (find_ghost_set t g).
Proof.
  induction t; intros; simpl.
  - apply finite_singleton.
  - apply finite_add, finite_union; auto.
Qed.

Definition tree_rep2 (g:gname) (g_root: gname)  (t: @tree val  ) : mpred := EX (tg:ghost_tree), !! (find_pure_tree tg = t) && ghost_tree_rep tg g_root (Neg_Infinity, Pos_Infinity) * ghost_ref g (find_ghost_set tg g_root).

Definition ltree (g:gname) ( g_root:gname) sh p lock :=   !!(field_compatible t_struct_tree_t nil p) &&
  ( field_at sh t_struct_tree_t [StructField _lock] lock p  * lock_inv sh lock (node_lock_inv g p g_root lock)).
  

Definition nodebox_rep (g : gname) ( g_root:gname) (sh : share) (lock : val) (nb: val) :=
 EX np: val, data_at sh (tptr (t_struct_tree_t)) np nb * ltree g g_root sh np lock .
 

 Fixpoint prospect_key_range  (t: @tree val  ) k (p_range:number * number) : (number * number)  :=
 match t, p_range with 
 | E, _ => p_range
 | T a x v b, (l,r) => if ( k <? x) then prospect_key_range a k (l,Finite_Integer x) else 
                             if ( x <? k) then prospect_key_range b k (Finite_Integer x,r) else p_range end.

Inductive IsEmptyNode (range : number * number ) :  (@tree val) -> (number * number) -> Prop :=
 | InEmptyTree n1 n2 : (range = (n1,n2)) -> IsEmptyNode range E (n1,n2)
 | InLeftSubTree l x v r  n1 n2 : IsEmptyNode range l (n1, Finite_Integer x) -> IsEmptyNode range (T l x v r) (n1,n2) 
 | InRightSubTree l x v r  n1 n2 :  IsEmptyNode range r (Finite_Integer x, n2) -> IsEmptyNode range (T l x v r) (n1,n2).
 
(*  tg -> EmptyNode r t -> check_key_exist' x r -> ~In x tg *)
 
 Lemma less_than_equal_transitivity: forall a b c, less_than_equal a b = true ->  less_than_equal b c = true -> less_than_equal a c = true .
 Proof.
 intros.
 unfold less_than_equal in *.
 destruct a. 
   - destruct c. destruct b. apply Zle_bool_imp_le in H . apply Zle_bool_imp_le in H0. apply Zaux.Zle_bool_true. omega. discriminate.  discriminate.
     destruct b; discriminate. auto.
   - auto.
   -  destruct c;destruct b. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. auto. auto.
Qed.

Lemma less_than_equal_less_than_transitivity: forall a b c, less_than_equal a b = true ->  less_than b c = true -> less_than a c = true .
 Proof.
 intros.
 unfold less_than_equal in *. unfold less_than in *.
 destruct a. 
   - destruct c. destruct b. apply Zle_bool_imp_le in H . apply Z.ltb_lt in H0. apply Zaux.Zlt_bool_true. omega. discriminate.  discriminate.
     destruct b; discriminate. auto.
   - destruct c. auto. destruct b;discriminate. auto.
   -  destruct b;destruct c. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. 
Qed.

 Lemma less_than__transitivity: forall a b c, less_than a b = true ->  less_than b c = true -> less_than a c = true .
 Proof.
 intros.
 unfold less_than in *.
 destruct a. 
   - destruct c. destruct b. apply Z.ltb_lt in H . apply Z.ltb_lt in H0. apply Zaux.Zlt_bool_true. omega. discriminate.  discriminate.
     destruct b; discriminate. auto.
   - destruct c. auto. destruct b. discriminate. discriminate. discriminate. auto.
   -  destruct c;destruct b. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Qed.

 Lemma less_than_equal_itself: forall a, less_than_equal a a = true.
 Proof.
 intros.
 destruct a;unfold less_than_equal;auto. apply Z.leb_refl.
 Qed.
 
 Lemma range_iteself : forall r, range_inclusion r r = true.
 Proof.
 intros.
 unfold range_inclusion.
 destruct r. 
 assert ( forall a, less_than_equal a a = true ) . { intros. destruct a;simpl;auto. apply Z.leb_refl. }
 rewrite H . rewrite H. auto.
 Qed.
 
 Lemma less_than_to_less_than_equal: forall a b, less_than a b = true -> less_than_equal a b = true .
 Proof.
 intros.
 destruct a.
  - destruct b;simpl. simpl in H. apply Z.ltb_lt in H. apply Zaux.Zle_bool_true. omega. simpl in H. discriminate. auto.
  - destruct b; auto. 
  - destruct b;auto.
Qed.
 
 Lemma range_inside_range : forall r  r_root t, IsEmptyNode r t r_root -> (forall k, In k t -> check_key_exist' k r_root = true) -> sorted_tree t -> range_inclusion r r_root = true.
 Proof.
 intros.
 revert dependent r_root.
 induction t.
  - intros. inversion H. subst r. apply range_iteself. 
  - intros. inversion H;subst.
   * assert ( range_inclusion r (n1, Finite_Integer k) = true ) . 
       { apply IHt1 in H7. apply H7. inversion H1;subst. apply H6. inversion H1;subst. unfold gt in H9.  intros. 
          assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft. apply H2. } unfold check_key_exist' in *. apply andb_prop in H3. destruct H3. 
          apply H9 in H2. rewrite H3. assert (less_than (Finite_Integer k0) (Finite_Integer k) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H5. auto. } 
    assert ( check_key_exist' k (n1, n2) = true ) . { apply H0.  apply InRoot. auto. } unfold check_key_exist' in H3. apply andb_prop in H3. destruct H3.
    unfold range_inclusion in *. destruct r. apply less_than_to_less_than_equal in H4. apply andb_prop in H2. destruct H2. rewrite H2. 
    simpl. apply less_than_equal_transitivity with ( b:= Finite_Integer k). apply H5. apply H4. 
   * assert ( range_inclusion r (Finite_Integer k, n2) = true ) . 
         { apply IHt2 in H7. apply H7. inversion H1;subst. apply H8.   inversion H1;subst. unfold lt in H10.  intros.
           assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight. apply H2. } unfold check_key_exist' in *. apply andb_prop in H3. destruct H3. apply H10 in H2. rewrite H4.
           assert (less_than (Finite_Integer k) (Finite_Integer k0) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H5. auto. }  
   assert ( check_key_exist' k (n1, n2) = true ) . { apply H0.  apply InRoot. auto. } unfold check_key_exist' in H3. apply andb_prop in H3. destruct H3.
   unfold range_inclusion in *. destruct r. apply less_than_to_less_than_equal in H3. apply andb_prop in H2. destruct H2. rewrite H5. 
  rewrite andb_comm.   simpl. apply less_than_equal_transitivity with ( b:= Finite_Integer k). apply H3. apply H2.
 Qed.
  
Lemma fact_about_prospect_node:  forall r x r_root t1 t2 v, IsEmptyNode r (T t1 x v t2 ) r_root -> (forall k, In k (T t1 x v t2 ) -> check_key_exist' k r_root = true) -> sorted_tree(T t1 x v t2 )  -> less_than_equal (right r) (Finite_Integer x) = true \/ less_than_equal (Finite_Integer x) (left r) = true.
Proof.
 intros.
remember (T t1 x v t2) as t.
revert dependent r_root.
revert dependent t2.
revert dependent v.
revert dependent x.
revert dependent t1.
induction t.
 - intros. discriminate. 
 - intros. inversion Heqt. inversion H;subst.
     *  inversion H1;subst. left. destruct t0.
      {  inversion H11;subst. simpl. apply Z.leb_refl . }
      {  assert ( x > k). { unfold gt in H8. apply H8. apply InRoot. auto. }  edestruct IHt1.
         + apply H6.
         + reflexivity.
         + apply H11.
         + intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft. apply H3. } unfold check_key_exist' in * . apply andb_prop in H4. destruct H4.
             unfold gt in H8. apply H8 in H3. rewrite H4;simpl. apply Zaux.Zlt_bool_true. omega.
         + apply less_than_equal_transitivity with (b := Finite_Integer k). apply H3. simpl. apply Zaux.Zle_bool_true. omega.
         + apply range_inside_range in H11.
              {  unfold range_inclusion in H11. destruct r. simpl.  apply andb_prop in H11. destruct H11.  apply H5. }
              {  intros. assert ( check_key_exist' k0 (n1, n2) = true ). { apply H0. apply InLeft. apply H4. } unfold check_key_exist' in * . apply andb_prop in H5. 
                 destruct H5. rewrite H5;simpl. unfold gt in H8. apply H8 in H4. apply Zaux.Zlt_bool_true. omega. }
               { apply H6. } }
    * inversion H1;subst. right. destruct t3.
      {  inversion H11;subst. simpl. apply Z.leb_refl . }
      {  assert ( x < k). { unfold lt in H9. apply H9. apply InRoot. auto. }  edestruct IHt2.
         + apply H7.
         + reflexivity.
         + apply H11.
         + intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight. apply H3. } unfold check_key_exist' in * . apply andb_prop in H4. destruct H4.
             unfold lt in H9. apply H9 in H3. rewrite H5; rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega.
         + apply range_inside_range in H11.
              {  unfold range_inclusion in H11. destruct r.  apply andb_prop in H11. destruct H11. unfold left. apply H4. }
              {  intros. assert ( check_key_exist' k0 (n1, n2) = true ). { apply H0. apply InRight. apply H4. } unfold check_key_exist' in * . apply andb_prop in H5. 
                 destruct H5. rewrite H10;rewrite andb_comm;simpl. unfold lt in H9. apply H9 in H4. apply Zaux.Zlt_bool_true. omega. }
               { apply H7. }
         +  apply less_than_equal_transitivity with (b := Finite_Integer k).  simpl. apply Zaux.Zle_bool_true. omega. apply H3. }
Qed.

Lemma prospect_key_in_leaf: forall r t x r_root, (check_key_exist' x r = true)  ->  IsEmptyNode r t r_root -> (forall k, In k t -> check_key_exist' k r_root = true) -> sorted_tree t -> ~ In x t ->
                                                           prospect_key_range t x r_root = r.
Proof.
intros.
revert dependent r_root.  
induction t.
- intros. simpl. inversion H0. auto.
-  intros.  destruct r_root. simpl.  destruct (x <? k) eqn:E1. SearchAbout Z.ltb.
 * inversion H2;subst. apply IHt1. apply H8. intro a. contradiction H3. apply InLeft. apply a.  inversion H0;subst. apply H5.  apply range_inside_range in H5.
   + unfold range_inclusion in H5. destruct r. apply andb_prop in H5. destruct H5. unfold check_key_exist' in H. apply andb_prop in H.
     destruct H. apply less_than_to_less_than_equal in H. assert ( less_than_equal (Finite_Integer k) (Finite_Integer x) = true ).
     { apply less_than_equal_transitivity with (b := n1) . apply H4. apply H. } simpl in H7. apply Z.ltb_lt in E1. apply Zle_bool_imp_le in H7. omega.
   + intros. assert ( check_key_exist' k0 (n, n0) = true). { apply H1. apply InRight. apply H4. } unfold check_key_exist' in * . apply andb_prop in H6. destruct H6.
      unfold lt in H11. apply H11 in H4. rewrite H7. rewrite andb_comm. simpl. apply Zaux.Zlt_bool_true. omega.
   + apply H9.
   + intros. assert ( check_key_exist' k0 (n, n0) = true). { apply H1. apply InLeft. apply H4. } unfold check_key_exist' in * . apply andb_prop in H5. destruct H5.
      unfold gt in H10. apply H10 in H4. rewrite H5. simpl. apply Zaux.Zlt_bool_true. omega.
 * destruct  (k <? x) eqn:E2.
     + inversion H2;subst. apply IHt2. apply H9. intro a. contradiction H3. apply InRight. apply a.  inversion H0;subst.  apply range_inside_range in H5.
       { unfold range_inclusion in H5. destruct r. apply andb_prop in H5. destruct H5. unfold check_key_exist' in H. apply andb_prop in H.
         destruct H. apply less_than_to_less_than_equal in H6. assert ( less_than_equal (Finite_Integer x) (Finite_Integer k) = true ).
         { apply less_than_equal_transitivity with (b := n2) . apply H6. apply H5. } simpl in H7. apply Z.ltb_lt in E2. apply Zle_bool_imp_le in H7. omega. }
       { intros. assert ( check_key_exist' k0 (n, n0) = true). { apply H1. apply InLeft. apply H4. } unfold check_key_exist' in * . apply andb_prop in H6. destruct H6. 
          unfold gt in H10. apply H10 in H4. rewrite H6. simpl. apply Zaux.Zlt_bool_true. omega. }
       { apply H8. }
      { apply H5. }
       { intros. assert ( check_key_exist' k0 (n, n0) = true). { apply H1. apply InRight. apply H4. } unfold check_key_exist' in * . apply andb_prop in H5. destruct H5.
        unfold lt in H11. apply H11 in H4. rewrite H6. rewrite andb_comm. simpl. apply Zaux.Zlt_bool_true. omega. }
    + assert (k = x ). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. omega. } contradiction H3. apply InRoot. omega.
Qed.



 
(* Lemma public_half_insert: forall x v g1 g2 t r g_root (n n0 : number), prospect_key_range t x r = (n,n0) -> ~ In x t ->
                                        public_half g1 (n, Finite_Integer x) * public_half g2 (Finite_Integer x,n0) * tree_rep g_root t r  |-- tree_rep g_root ( insert x v t) r.
Proof.
intros. 
revert dependent g_root .
revert dependent r.  
induction t.
 - simpl.  intros. cancel. subst r.  Exists g1 g2.  cancel.
 - simpl.  intros. destruct r.  Intros ga gb. destruct (x <? k) eqn: IHe. 
    *  simpl.  Exists ga gb. cancel. apply IHt1. intros a. contradiction H0. apply InLeft. apply a. apply H.
    *  destruct (k <? x) eqn: IHe'. simpl. Exists ga gb.  cancel. apply IHt2. intros a. contradiction H0. apply InRight. apply a. apply H. 
    contradiction H0. SearchAbout Z.ltb. apply Z.ltb_nlt in IHe. apply Z.ltb_nlt in IHe'. assert (k = x). { omega. } apply InRoot. omega.
Qed.
 
 Lemma empty_tree_rep: forall g r,  tree_rep g E r = public_half g r.
 Proof.
 intros. simpl. auto.
 Qed.
 *)

Definition tree_rep_R (tp:val) (r:(number * number)) (g_info:option ghost_info) g : mpred :=
if eq_dec tp nullval then !!( g_info = None) && emp  else 
EX ga:gname, EX gb: gname, EX x: Z, EX v: val, EX pa : val, EX pb : val, EX locka : val, EX lockb : val,
     !! (g_info = Some(x,v,ga,gb) /\ Int.min_signed <= x <= Int.max_signed/\ is_pointer_or_null pa /\ is_pointer_or_null pb  /\ tc_val (tptr Tvoid) v 
     /\ check_key_exist' x r) && data_at Ews t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp * malloc_token Ews t_struct_tree tp *
     |> ltree g ga lsh1 pa locka * |> ltree g gb lsh1 pb lockb.

Lemma eqp_subp : forall P Q, P <=> Q |-- P >=> Q.
Proof.
  intros; constructor.
  apply subtypes.eqp_subp, predicates_hered.derives_refl.
Qed.

Lemma selflock_nonexpansive2 : forall {A} (P Q : A -> mpred) sh p x,
    (ALL x : _, |> (P x <=> Q x) |--
    |> selflock (P x) sh p <=> |> selflock (Q x) sh p).
Proof.
  intros. apply allp_left with x. rewrite <- eqp_later; apply later_derives.
  apply nonexpansive_entail with (F := fun P => selflock P sh p).
  apply selflock_nonexpansive.
Qed.

Lemma lock_inv_node_lock_inv_r_nonexpansive:
  ∀ (P Q : val * (own.gname * (number * number * option ghost_info)) → mpred) 
    (sh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * (number * number * option ghost_info)),
    |> P x <=> |> Q x
       |-- |> lock_inv sh lock (node_lock_inv_r P p gp lock) >=>
           |> lock_inv sh lock (node_lock_inv_r Q p gp lock).
Proof.
  intros. eapply derives_trans, eqp_subp. eapply derives_trans, lock_inv_nonexpansive2.
  apply allp_right. intros v. unfold node_lock_inv_r.
  remember (fun (M: val * (own.gname *
                           (number * number * option ghost_info)) -> mpred)
                (x: gname * val) =>
              (node_lock_inv_r' M (snd x) (fst x) v)) as func.
  pose proof (selflock_nonexpansive2 (func P) (func Q) lsh2 v (gp, p)).
  replace (func P (gp, p)) with (node_lock_inv_r' P p gp v) in H by 
    now rewrite Heqfunc.
  replace (func Q (gp, p)) with (node_lock_inv_r' Q p gp v) in H by
      now rewrite Heqfunc. rewrite eqp_later. eapply derives_trans, H.
  apply allp_right. intros (?, ?). clear H. subst func. unfold fst, snd.
  unfold node_lock_inv_r'. unfold sync_inv, uncurry.
  rewrite eqp_later. repeat rewrite -> later_sepcon. erewrite !later_exp'; eauto.
  - do 2 apply eqp_sepcon, eqp_refl.
    apply eqp_exp. intros (?, ?). apply allp_left with (v0, (g, (p0, o))).
    rewrite <- !eqp_later. apply later_derives, eqp_sepcon.
    + apply derives_refl.
    + apply eqp_refl.
  - exact ((Pos_Infinity, Pos_Infinity), None).
  - exact ((Pos_Infinity, Pos_Infinity), None).
Qed.

Lemma ltree_r_nonexpansive:
  ∀ (P Q : val * (own.gname * (number * number * option ghost_info)) → mpred) 
    (sh: share) (gp : own.gname) (p lock : val),
    ALL x : val * (own.gname * (number * number * option ghost_info)),
    |> P x <=> |> Q x |-- |> ltree_r P gp sh p lock >=> |> ltree_r Q gp sh p lock.
Proof.
  intros. unfold ltree_r. rewrite !later_andp. apply subp_andp. 1: apply subp_refl.
  rewrite !later_sepcon. apply subp_sepcon. 1: apply subp_refl.
  apply lock_inv_node_lock_inv_r_nonexpansive.
Qed.

Lemma node_rep_def : forall np r g g_current,
    node_rep np g g_current r =
    EX tp:val, (field_at Ews (t_struct_tree_t) [StructField _t] tp np) *
(*                malloc_token Ews t_struct_tree_t np *  in_tree g lsh1 g_current * *)
               malloc_token Ews t_struct_tree_t np *  in_tree g g_current *
               tree_rep_R tp (fst r) (snd r) g.
Proof.
   intros. assert (HOcontractive (node_rep_r g)). {
    apply prove_HOcontractive. intros ?? (?, (?, (?, ?))). unfold node_rep_r.
    apply subp_exp; intros. apply subp_sepcon; [apply subp_refl|].
    destruct (eq_dec x nullval). 1: apply subp_refl. repeat (apply subp_exp; intro).
    rewrite !sepcon_assoc; apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; [apply subp_refl|].
    apply subp_sepcon; apply ltree_r_nonexpansive. }
  unfold node_rep, node_rep_closed.
  etransitivity; [eapply equal_f, HORec_fold_unfold|]; auto.
  unfold node_rep_r at 1. destruct r. f_equal.
Qed.

Theorem node_lock_inv_def : forall p lock g g_current,
  node_lock_inv g p g_current lock = 
  (EX a : number * number * option ghost_info,
    node_rep p g g_current a * my_half g_current a) *
    field_at lsh2 t_struct_tree_t [StructField _lock] lock p *
    malloc_token Ews tlock lock * (* malloc_token Ews t_struct_tree_t p * *)
    |> lock_inv lsh2 lock (node_lock_inv g p g_current lock).
Proof.
  intros p lock g g_current.
  unfold node_lock_inv at 1.
  setoid_rewrite (selflock_eq) at 1.
  unfold node_lock_inv_pred at 1.
  unfold sync_inv at 1.
  unfold node_lock_inv at 1.
  reflexivity.
Qed.

Lemma node_lock_exclusive : forall p lock g g_current,
  exclusive_mpred (node_lock_inv g p g_current lock).
Proof.
  intros. rewrite node_lock_inv_def.
  eapply derives_exclusive, exclusive_sepcon1 with
  (P := field_at lsh2 t_struct_tree_t [StructField _lock] lock p)
  (Q := (EX a : number * number * option ghost_info, node_rep p g g_current a * my_half g_current a) *
         malloc_token Ews tlock lock * (* malloc_token Ews t_struct_tree_t p * *) _).
  - Intros a. Exists a. cancel. apply derives_refl.
  - apply field_at_exclusive; auto.
    simpl. omega.
Qed.
Hint Resolve node_lock_exclusive.

Lemma node_lock_inv_rec: forall g p gp lock,
    rec_inv lsh2 lock (node_lock_inv_pred g p gp lock) (node_lock_inv g p gp lock).
Proof. intros. apply node_lock_inv_def. Qed.
Hint Resolve node_lock_inv_rec.

(* insert proof related lemmas *)

(* Lemma node_exist_in_tree: forall g s sh g_in,  in_tree g sh g_in  * ghost_ref g s |-- !! (Ensembles.In _ s g_in). *)
Lemma node_exist_in_tree: forall g s g_in,  in_tree g g_in  * ghost_ref g s |-- !! (Ensembles.In _ s g_in).
Proof. 
intros. unfold ghost_ref, in_tree; Intros sh. rewrite ref_sub.  destruct  (eq_dec sh Tsh).
- Intros. apply log_normalize.prop_derives. intros. subst s.  apply In_singleton. 
- apply log_normalize.prop_derives. intros [m H].  unfold sepalg.join in H. hnf in H. destruct H. rewrite H0. apply Union_introl. apply In_singleton. 
Qed.

Lemma insert_preserved_in_ghost_tree: forall t tg x v g1 g2, find_pure_tree tg = t -> find_pure_tree (insert_ghost x v tg g1 g2) = (insert x v t).
Proof.
intros.
revert dependent t.
induction tg.
  - intros. simpl.  simpl in H. symmetry in H. subst t. simpl. reflexivity.  
 - intros. simpl. destruct (x <? k) eqn:E1. 
    *  simpl. rewrite ( IHtg1  (find_pure_tree tg1)).  simpl in H. rewrite <- H. simpl. rewrite E1. auto. auto.
    * destruct (k <? x) eqn:E2. simpl. rewrite ( IHtg2  (find_pure_tree tg2)). simpl in H. rewrite <- H. simpl. rewrite E1. rewrite E2. auto. auto.
       simpl. simpl in H. rewrite <- H. simpl. rewrite E1. rewrite E2. auto.    
Qed.

(* Lemma update_ghost_ref: forall g (tg : @ ghost_tree val)  s g_in, finite s -> (in_tree g lsh1 g_in * ghost_ref g s |-- |==> EX sh1 sh2 g1 g2, ghost_ref g ( Add _ ( Add _ s g1) g2) *
    in_tree g sh1 g1 * in_tree g sh2 g2 * in_tree g lsh1 g_in)%I . *)
Lemma update_ghost_ref: forall g (tg : @ ghost_tree val)  s g_in, finite s -> (in_tree g g_in * ghost_ref g s |-- |==> EX g1 g2, ghost_ref g ( Add _ ( Add _ s g1) g2) *
    in_tree g g1 * in_tree g g2 * in_tree g g_in)%I .
 Proof.
 intros.
 iIntros "H".
iDestruct "H" as "[Ha Hb]". iPoseProof ( in_tree_add with "[$Ha $Hb]") as ">H"; auto.
iDestruct "H" as ((* sh3 sh4  *)g1) "[[Ha Hb] Hc]". iPoseProof( in_tree_add with "[$Hb $Ha]") as ">Hnew". apply finite_add; auto.
 iDestruct "Hnew" as ((* sh5 sh6 *) g2) "[[Ha Hb ] Hd]". iModIntro. iExists (* sh4, sh6, *) g1, g2. iFrame.
Qed.


Lemma update_ghost_tree_with_insert: forall x v tg g1 g2 g_root, ~In_ghost x tg ->  (find_ghost_set (insert_ghost x v tg g1 g2) g_root) =  (Add _ ( Add _ (find_ghost_set tg g_root) g1) g2).
Proof.
intros.
revert dependent g_root.
induction tg.
 + intros. simpl.   unfold Add.   rewrite Union_comm.  rewrite <- Union_assoc. reflexivity.
 + simpl. destruct (x <? k) eqn:E1. 
    -  intros. simpl. rewrite IHtg1. unfold Add. remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set tg2 g0) as a2. remember (Singleton gname g1) as b. 
        remember (Singleton gname g2) as c. remember (Singleton gname g_root) as d. rewrite (Union_comm _ a2). rewrite <- Union_assoc. 
        rewrite <- Union_assoc. rewrite (Union_comm a2 a1). rewrite Union_comm. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite ( Union_comm d _). reflexivity. 
        unfold not. intros. apply (InLeft_ghost x tg1 g tg2 g0 k v0) in H0. unfold not in H. apply H in H0. auto.
    - destruct (k <? x) eqn:E2.
        * intros;simpl. rewrite IHtg2. unfold Add. remember (find_ghost_set tg1 g) as a1. remember (find_ghost_set tg2 g0) as a2. remember (Singleton gname g1) as b. 
        remember (Singleton gname g2) as c. remember (Singleton gname g_root) as d. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite Union_comm. rewrite <- Union_assoc. rewrite <- Union_assoc. rewrite (Union_comm d _). reflexivity.
        unfold not. intros. apply (InRight_ghost x tg1 g tg2 g0 k v0) in H0. unfold not in H. apply H in H0. auto.
        * intros. assert (x = k). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. omega. } apply (InRoot_ghost x tg1 g tg2 g0 k v0) in H0. contradiction H.
Qed.


Lemma update_ghost_tree_with_insert2: forall x v tg g1 g2 g_root, ((In_ghost x tg) /\ (sorted_ghost_tree tg)) ->  (find_ghost_set (insert_ghost x v tg g1 g2) g_root) =  (find_ghost_set tg g_root).
Proof.
intros.
destruct H.
revert dependent g_root.
induction tg.
 + intros. inversion H.
 + intros. 
    inversion H.
    -  simpl. 
        destruct (x <? k) eqn:E2.
        * apply Z.ltb_lt in E2. omega.
        * destruct (k <? x) eqn:E3. {apply Z.ltb_lt in E3. omega. } { simpl. reflexivity. }
    - simpl.
      destruct (x <? k) eqn:E2.
      * simpl.
        rewrite IHtg1.
        reflexivity.
        apply H2.
        inversion H0.
        apply H12.
      * destruct (k <? x) eqn:E3.
        { inversion H0.
          unfold gt_ghost in H16.
          apply H16 in H2.
          apply Z.ltb_lt in E3.
          omega. }
       { simpl. reflexivity. }
    - simpl.
      destruct (x <? k) eqn:E2.
      * inversion H0.
        unfold lt_ghost in H17.
        apply H17 in H2.
        apply Z.ltb_lt in E2.
        omega.
      * destruct (k <? x) eqn:E3.
        { simpl. 
          rewrite IHtg2.
          reflexivity.
          apply H2.
          inversion H0.
          apply H15. }
        { simpl. reflexivity. }
Qed.


Lemma extract_public_half_from_ghost_tree_rep_combined:  forall  tg  g_root  g_in g1 g2 x v v0 (r_root: number * number), 
   Ensembles.In gname (find_ghost_set tg g_root) g_in ->(forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> sorted_ghost_tree tg -> ghost_tree_rep tg g_root r_root  |-- EX n:number, EX n0:number, EX o:option ghost_info, !!(range_inclusion (n,n0) r_root = true ) && public_half g_in (n, n0, o) *
  ( (( !!(o = None /\ (check_key_exist' x (n,n0) = true)) &&  public_half g_in (n, n0, Some(x,v,g1,g2)) * public_half g1 (n, Finite_Integer x,@None ghost_info) * public_half g2 (Finite_Integer x, n0, @None ghost_info)) -* ghost_tree_rep (insert_ghost x v tg g1 g2) g_root r_root )
  && (( !!(o = Some(x,v0,g1,g2) /\ (check_key_exist' x (n,n0) = true)) &&  public_half g_in (n, n0, Some(x,v, g1,g2))) -* ghost_tree_rep (insert_ghost x v tg g1 g2) g_root r_root )
  &&  ( public_half g_in (n, n0, o) -* ghost_tree_rep tg g_root r_root)) .
Proof.
  intros.
revert dependent r_root.
revert dependent g_root.
induction tg.
  - intros. simpl. simpl in H. inv H. destruct r_root. Exists n n0. Exists (@None ghost_info). entailer!. rewrite less_than_equal_itself. rewrite less_than_equal_itself. auto. repeat apply andp_right. rewrite <- wand_sepcon_adjoint. entailer!. rewrite <- wand_sepcon_adjoint. entailer!. inv H.  apply wand_refl_cancel_right. 
  - intros. simpl in H. inv H.
    * inv H2.
     { simpl.  destruct r_root. destruct (x <? k) eqn: E1.
      + simpl. inv H1.  sep_apply IHtg1.
        {  intros. assert (check_key_exist' k0 (n, n0) = true). { apply H0. apply InLeft_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H2. destruct H2.
             unfold gt_ghost in H10. apply H10 in H1. rewrite H2;simpl. apply Zaux.Zlt_bool_true. omega. }
        Intros n1 n2 o. Exists n1 n2 o. entailer!.
        { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n, n0) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H3.  apply andb_prop in H3. destruct H3. rewrite H1;simpl. apply less_than_to_less_than_equal in H4. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H2. apply H4. }
           rewrite sepcon_assoc. 
        rewrite (sepcon_comm _ (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg2 g0 (Finite_Integer k, n0))). repeat rewrite distrib_sepcon_andp.    repeat apply andp_derives. 
       {  rewrite (sepcon_comm (public_half g_root (n, n0, Some (k,v1,g, g0))) (ghost_tree_rep (insert_ghost x v tg1 g1 g2) g (n, Finite_Integer k))).
       rewrite <- (emp_wand (public_half g_root (n, n0, Some (k,v1, g, g0)) *ghost_tree_rep tg2 g0 (Finite_Integer k, n0))) at 1. rewrite wand_sepcon_wand. rewrite emp_sepcon. 
       rewrite ( sepcon_assoc (ghost_tree_rep (insert_ghost x v tg1 g1 g2) g (n, Finite_Integer k)) _ _). rewrite ( sepcon_comm _ (ghost_tree_rep (insert_ghost x v tg1 g1 g2) g (n, Finite_Integer k)) ). unfold check_key_exist'. simpl less_than. entailer!. }
       { rewrite <- (emp_wand (public_half g_root (n, n0, Some (k, v1, g, g0)) * ghost_tree_rep tg2 g0 (Finite_Integer k, n0) )). rewrite wand_sepcon_wand. rewrite emp_sepcon. rewrite sepcon_assoc. rewrite (sepcon_comm (ghost_tree_rep tg2 g0 (Finite_Integer k, n0)) _). rewrite <- sepcon_assoc.  unfold check_key_exist'. simpl less_than. entailer!. }
       { rewrite <- ( emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg2 g0 (Finite_Integer k, n0))). rewrite wand_sepcon_wand. rewrite emp_sepcon.  rewrite (pull_right _ _ (ghost_tree_rep tg1 g (n, Finite_Integer k))). cancel.  }
      + inv H1. unfold gt_ghost in H10. sep_apply IHtg1. 
      { intros. assert (check_key_exist' k0 (n, n0) = true). { apply H0. apply InLeft_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H2. destruct H2.
             unfold gt_ghost in H10. apply H10 in H1. rewrite H2;simpl. apply Zaux.Zlt_bool_true. omega. }
      Intros n1 n2 o. Exists n1 n2 o. entailer!.
      { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n, n0) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H3.  apply andb_prop in H3. destruct H3. rewrite H1;simpl. apply less_than_to_less_than_equal in H4. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H2. apply H4. }
       rewrite sepcon_assoc.  rewrite (sepcon_comm _ (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg2 g0 (Finite_Integer k, n0))). repeat rewrite distrib_sepcon_andp.  repeat  apply andp_derives.
        { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
          assert (x < k). { simpl in H1. apply andb_prop in H2. apply andb_prop in H1.  destruct H1,H2. unfold less_than_equal, less_than in *. destruct n2.  apply Z.ltb_lt in H4. apply Zle_bool_imp_le in H3. omega. discriminate. discriminate.  } 
          apply Z.ltb_nlt in E1. omega. }
         { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
          assert (x < k). { simpl in H1. apply andb_prop in H2. apply andb_prop in H1.  destruct H1,H2. unfold less_than_equal, less_than in *. destruct n2.  apply Z.ltb_lt in H4. apply Zle_bool_imp_le in H3. omega. discriminate. discriminate.  } 
          apply Z.ltb_nlt in E1. omega. }
        { rewrite <- ( emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg2 g0 (Finite_Integer k,n0))) at 1. rewrite wand_sepcon_wand. rewrite emp_sepcon. rewrite sepcon_assoc. rewrite (sepcon_comm (ghost_tree_rep tg2 g0 (Finite_Integer k, n0)) _). rewrite sepcon_assoc. cancel.  } 
     }
   { simpl;destruct r_root. destruct (x <? k) eqn:E1.
      + simpl. inv H1.  unfold lt_ghost in H11. sep_apply IHtg2.
         { intros. assert (check_key_exist' k0 (n, n0) = true). { apply H0. apply InRight_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H2. destruct H2.
              apply H11 in H1. rewrite H3;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }
      Intros n1 n2 o. Exists n1 n2 o. entailer!. 
       { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n, n0) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H3.  apply andb_prop in H3. destruct H3. rewrite H2;simpl. rewrite andb_comm;simpl. apply less_than_to_less_than_equal in H3. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H3. apply H1. }
       rewrite sepcon_assoc.  rewrite (sepcon_comm _ (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg1 g (n, Finite_Integer k))). repeat rewrite distrib_sepcon_andp.   repeat apply andp_derives.
        { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
          assert (k < x). { simpl in H1. apply andb_prop in H2. apply andb_prop in H1.  destruct H1,H2. unfold less_than_equal, less_than in *. destruct n1.  apply Zle_bool_imp_le in H1. apply Z.ltb_lt in H2. omega. discriminate. discriminate.  } 
          apply Z.ltb_lt in E1. omega. }
          { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
          assert (k < x). { simpl in H1. apply andb_prop in H2. apply andb_prop in H1.  destruct H1,H2. unfold less_than_equal, less_than in *. destruct n1.  apply Zle_bool_imp_le in H1. apply Z.ltb_lt in H2. omega. discriminate. discriminate.  } 
          apply Z.ltb_lt in E1. omega. }
        { rewrite <- ( emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg1 g (n,Finite_Integer k))) at 1. rewrite wand_sepcon_wand. rewrite emp_sepcon. rewrite sepcon_assoc. cancel.  } 

   + destruct (k <? x) eqn:E2. simpl;inv H1. sep_apply IHtg2.
     {  intros. assert (check_key_exist' k0 (n, n0) = true). { apply H0. apply InRight_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H2. destruct H2.
             unfold lt_ghost in H11. apply H11 in H1. rewrite H3;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }
      Intros n1 n2 o. Exists n1 n2 o. entailer!. 
      { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n, n0) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H3.  apply andb_prop in H3. destruct H3. rewrite H2;simpl. rewrite andb_comm;simpl.  apply less_than_to_less_than_equal in H3. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H3. apply H1. } 
       rewrite sepcon_assoc. rewrite (sepcon_comm _ (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg1 g (n,Finite_Integer k))). repeat rewrite distrib_sepcon_andp.  repeat apply andp_derives.
        {  rewrite (sepcon_comm (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg1 g (n, Finite_Integer k)) (ghost_tree_rep (insert_ghost x v tg2 g1 g2) g0 (Finite_Integer k,n0))).
         rewrite <- (emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg1 g (n,Finite_Integer k))) at 1.  rewrite wand_sepcon_wand.  rewrite emp_sepcon. 
         rewrite ( sepcon_comm _ (ghost_tree_rep (insert_ghost x v tg2 g1 g2) g0 (Finite_Integer k,n0)) ). unfold check_key_exist'. unfold less_than. entailer!. }
        {  rewrite (sepcon_comm (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg1 g (n, Finite_Integer k)) (ghost_tree_rep (insert_ghost x v tg2 g1 g2) g0 (Finite_Integer k,n0))).
           rewrite <- (emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) *ghost_tree_rep tg1 g (n,Finite_Integer k))) at 1.  rewrite wand_sepcon_wand.  rewrite emp_sepcon. 
           rewrite ( sepcon_comm _ (ghost_tree_rep (insert_ghost x v tg2 g1 g2) g0 (Finite_Integer k,n0)) ). unfold check_key_exist'. unfold less_than. entailer!. }
       { rewrite <- ( emp_wand (public_half g_root (n, n0, Some (k,v1,g, g0)) * ghost_tree_rep tg1 g (n,Finite_Integer k))) at 1. rewrite wand_sepcon_wand. rewrite emp_sepcon. cancel.  }
       inv H1. assert (k = x ). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. omega. }  sep_apply IHtg2.
         { intros. assert (check_key_exist' k0 (n, n0) = true). { apply H0. apply InRight_ghost. apply H2. } unfold check_key_exist' in * . apply andb_prop in H3. destruct H3.
              unfold lt_ghost in H11. apply H11 in H2. rewrite H4;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }
      Intros n1 n2 o. Exists n1 n2 o. entailer!. 
       { simpl in H2.  apply andb_prop in H2. destruct H2. assert (check_key_exist' x (n, n0) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H3.  apply andb_prop in H3. destruct H3. rewrite H2;simpl. rewrite andb_comm;simpl. apply less_than_to_less_than_equal in H3. apply less_than_equal_transitivity with (b := (Finite_Integer x) ). apply H3. apply H1. }
       rewrite sepcon_assoc.  rewrite (sepcon_comm _ (public_half g_root (n, n0, Some (x,v1,g, g0)) *ghost_tree_rep tg1 g (n, Finite_Integer x))). repeat rewrite distrib_sepcon_andp.   repeat apply andp_derives.
        { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
         simpl in H2.  apply andb_prop in H2. apply andb_prop in H1.  destruct H2, H1. destruct n1. simpl in H1. apply Z.ltb_lt in H1. apply Zle_bool_imp_le in H2. omega. discriminate. simpl in H1. discriminate. }
        { rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. rewrite <- sepcon_assoc. entailer!. 
         simpl in H2.  apply andb_prop in H2. apply andb_prop in H1.  destruct H2, H1. destruct n1. simpl in H1. apply Z.ltb_lt in H1. apply Zle_bool_imp_le in H2. omega. discriminate. simpl in H1. discriminate. }
    
        { rewrite <- ( emp_wand (public_half g_root (n, n0, Some (x,v1,g, g0)) * ghost_tree_rep tg1 g (n,Finite_Integer x))) at 1. rewrite wand_sepcon_wand. rewrite emp_sepcon. rewrite sepcon_assoc. cancel.  } 
     }  
  * inv H2. simpl. destruct r_root. Exists n n0. Exists (Some(k,v1,g,g0)). entailer!. repeat rewrite less_than_equal_itself. simpl;auto. repeat  apply andp_right.
       { rewrite <- wand_sepcon_adjoint. Intros a. }
       { rewrite <- wand_sepcon_adjoint. entailer!. inv H. simpl. destruct (x <? x) eqn: E1. apply Z.ltb_lt in E1. omega. simpl. entailer!. }
       {   rewrite sepcon_assoc. rewrite <- (sepcon_emp (public_half g_in (n, n0, Some (k,v1, g, g0) ))) at 1. rewrite <- wand_sepcon_wand. rewrite emp_wand. cancel. apply wand_refl_cancel_right. }
  
Qed.
Inductive IsEmptyGhostNode (range : number * number ) :  (@ghost_tree val) -> (number * number) -> Prop :=
 | InEmptyGhostTree n1 n2 : (range = (n1,n2)) -> IsEmptyGhostNode range E_ghost (n1,n2)
 | InLeftGhostSubTree l g1 x v r g2  n1 n2 : IsEmptyGhostNode range l (n1, Finite_Integer x) -> IsEmptyGhostNode range (T_ghost l g1 x v r g2) (n1,n2) 
 | InRightGhostSubTree l g1 x v r g2 n1 n2 :  IsEmptyGhostNode range r (Finite_Integer x, n2) -> IsEmptyGhostNode range (T_ghost l g1 x v r g2) (n1,n2).
 
 Lemma key_not_exist_in_tree: forall  (tg : @ghost_tree val) r_root range x, IsEmptyGhostNode range tg r_root -> check_key_exist' x range = true  -> ~ In_ghost x tg.
 Proof.
 Admitted.
 
  Lemma key_exist_in_tree: forall  (tg : @ghost_tree val) r_root range x, ~IsEmptyGhostNode range tg r_root -> check_key_exist' x range = true ->  In_ghost x tg.
 Proof.
 Admitted.
 
 Lemma sortedness_preserved__in_ghosttree: forall t tg, find_pure_tree tg = t -> sorted_tree t -> sorted_ghost_tree tg.
  Proof.
 intros.
 revert dependent t.
    induction tg.
      - intros. simpl in H0. apply Sorted_Empty_Ghost.
      - intros. simpl in H.  inv H0.  discriminate. inv H5. apply Sorted_Ghost_Tree. apply (IHtg1 (find_pure_tree tg1)). auto. apply H1. 
         apply (IHtg2 (find_pure_tree tg2)). auto. apply H2. 
         { clear H1. clear H2. clear IHtg1. clear IHtg2. unfold gt_ghost. intros. unfold gt in H3. apply H3. induction tg1. inv H. simpl. inv H.  apply InRoot. auto.
           apply InLeft. apply IHtg1_1. intros. apply H3. simpl. apply InLeft. apply H. apply H1. apply InRight. apply IHtg1_2. intros. apply H3. simpl. apply InRight. apply H. apply H1. }
         { clear H1. clear H2. clear IHtg1. clear IHtg2. unfold lt_ghost. intros. unfold lt in H4. apply H4. induction tg2. inv H. simpl. inv H.  apply InRoot. auto.
         apply InLeft. apply IHtg2_1. intros. apply H4. simpl. apply InLeft. apply H. apply H1. apply InRight. apply IHtg2_2. intros. apply H4. simpl. apply InRight. apply H. apply H1. }

Qed.

(* Lemma extract_lemmas_for_treerep2:  forall  t  g g_root  g_in g1 g2 x v v0,
  sorted_tree t -> tree_rep2 g g_root t * in_tree g lsh1 g_in |-- EX n:number, EX n0:number, EX o : option ghost_info, public_half g_in (n, n0, o) *
  (  (( !!(o = None /\ (check_key_exist' x (n,n0) = true)) &&public_half g_in (n, n0, Some(x,v,g1,g2)) * public_half g1 (n, Finite_Integer x,@None ghost_info) * public_half g2 (Finite_Integer x, n0, @None ghost_info)) -*  (|==> tree_rep2 g g_root (insert x v t ) *  in_tree g lsh1 g_in * in_tree g lsh1 g1 * in_tree g lsh1 g2)%I )
    && (( !!(o = Some(x,v0,g1,g2) /\ (check_key_exist' x (n,n0) = true)) &&  public_half g_in (n, n0, Some(x,v, g1,g2))) -* (|==> tree_rep2 g g_root (insert x v t ) *  in_tree g lsh1 g_in)%I )
   && ( public_half g_in (n, n0, o) -* (tree_rep2 g g_root t * in_tree g lsh1 g_in ) )). *)
Lemma extract_lemmas_for_treerep2:  forall  t  g g_root  g_in g1 g2 x v v0,
  sorted_tree t -> tree_rep2 g g_root t * in_tree g g_in |-- EX n:number, EX n0:number, EX o : option ghost_info, public_half g_in (n, n0, o) *
  (  (( !!(o = None /\ (check_key_exist' x (n,n0) = true)) && public_half g_in (n, n0, Some(x,v,g1,g2)) * public_half g1 (n, Finite_Integer x,@None ghost_info) * public_half g2 (Finite_Integer x, n0, @None ghost_info)) -*  (|==> tree_rep2 g g_root (insert x v t ) *  in_tree g g_in * in_tree g g1 * in_tree g g2)%I )
    && (( !!(o = Some(x,v0,g1,g2) /\ (check_key_exist' x (n,n0) = true)) &&  public_half g_in (n, n0, Some(x,v, g1,g2))) -* (|==> tree_rep2 g g_root (insert x v t ) *  in_tree g g_in)%I )
   && ( public_half g_in (n, n0, o) -* (tree_rep2 g g_root t * in_tree g g_in ) )).
Proof.
 intros.
unfold tree_rep2 at 1. Intros tg. 
assert_PROP( Ensembles.In _ (find_ghost_set tg g_root) g_in ). {  rewrite -> sepcon_assoc. rewrite  sepcon_comm.   apply sepcon_derives_prop. rewrite sepcon_comm. apply node_exist_in_tree. }
 rewrite sepcon_assoc. rewrite (sepcon_comm (ghost_ref g (find_ghost_set tg g_root)) _).  rewrite (sepcon_comm (ghost_tree_rep tg g_root (Neg_Infinity, Pos_Infinity)) _).
rewrite extract_public_half_from_ghost_tree_rep_combined.
  { Intros n1 n2 o.  instantiate (1 := g_in). Exists n1 n2 o.
(*  cancel. repeat rewrite ( distrib_sepcon_andp (in_tree g lsh1 g_in * ghost_ref g (find_ghost_set tg g_root) ) _ _). *)
 cancel. repeat rewrite ( distrib_sepcon_andp (in_tree g g_in * ghost_ref g (find_ghost_set tg g_root) ) _ _).
    repeat apply andp_derives.
     +   assert_PROP ( IsEmptyGhostNode (n1,n2) tg (Neg_Infinity, Pos_Infinity) /\ check_key_exist' x (n1, n2) = true ). { admit. }
(*       unfold tree_rep2. rewrite <- ( emp_wand (in_tree g lsh1 g_in * ghost_ref g (find_ghost_set tg g_root) )). rewrite wand_sepcon_wand. apply wand_derives. *)
      unfold tree_rep2. rewrite <- ( emp_wand (in_tree g g_in * ghost_ref g (find_ghost_set tg g_root) )). rewrite wand_sepcon_wand. apply wand_derives.
        { instantiate (1 := x).  instantiate(2:=g1). instantiate(1:= g2). instantiate (1 := v). entailer!. } 
         {  iIntros "H". iDestruct "H" as "[[Ha Hb] Hc]".  normalize. iPoseProof(update_ghost_ref with "[Ha Hb]") as "Hnew". auto. instantiate(1:= (find_ghost_set tg g_root) ). apply find_ghost_set_finite. iFrame. iMod "Hnew".  iExists (insert_ghost x v tg g1 g2). iModIntro. 
          rewrite ( insert_preserved_in_ghost_tree t tg _ _ _ _). rewrite update_ghost_tree_with_insert.  iFrame. admit. apply (key_not_exist_in_tree tg (Neg_Infinity, Pos_Infinity) (n1,n2) x). destruct H3; auto. destruct H3;auto. auto. } 
     +   assert_PROP ( ~IsEmptyGhostNode (n1,n2) tg (Neg_Infinity, Pos_Infinity) /\ check_key_exist' x (n1, n2) = true). { admit. }
(*      unfold tree_rep2.  rewrite <- ( emp_wand (in_tree g lsh1 g_in * ghost_ref g (find_ghost_set tg g_root) )). rewrite wand_sepcon_wand. apply wand_derives. *)
     unfold tree_rep2.  rewrite <- ( emp_wand (in_tree g g_in * ghost_ref g (find_ghost_set tg g_root) )). rewrite wand_sepcon_wand. apply wand_derives.
     { entailer!. }
     { iIntros "H". iDestruct "H" as "[[Ha Hb] Hc]". iModIntro. normalize.   iExists (insert_ghost x v tg g1 g2). rewrite ( insert_preserved_in_ghost_tree t tg _ _ _ _).  rewrite update_ghost_tree_with_insert2. iFrame. iSplit;auto.
       split.  apply (key_exist_in_tree tg (Neg_Infinity, Pos_Infinity) (n1,n2) x).  destruct H3. apply H3. destruct H3. auto. apply (sortedness_preserved__in_ghosttree t tg). auto. auto. auto. }
(*     + rewrite <- (emp_wand (in_tree g lsh1 g_in * ghost_ref g (find_ghost_set tg g_root))). rewrite wand_sepcon_wand. apply wand_derives. *)
    + rewrite <- (emp_wand (in_tree g g_in * ghost_ref g (find_ghost_set tg g_root))). rewrite wand_sepcon_wand. apply wand_derives.
       entailer!. unfold tree_rep2. Exists tg. entailer!.
   }
   apply H1. intros. unfold check_key_exist'. simpl. auto.
   { 
     apply (sortedness_preserved__in_ghosttree t tg). auto. auto.   
   }   
Admitted.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ _n OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))); gvars gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH gv: globals
  PRE  [  ]
    PROP () LOCAL (gvars gv) SEP (mem_mgr gv)
  POST [ tptr (tptr t_struct_tree_t) ]
    EX v:val, EX lock:val, EX g:gname, EX g_root:gname,
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (mem_mgr gv; nodebox_rep g g_root lsh1 lock v;
         (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) v;
         malloc_token Ews (tptr t_struct_tree_t) v;
         tree_rep2 g g_root E).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH lock: val, b: val, gv: globals, g: gname, g_root: gname
  PRE  [ _b OF (tptr (tptr t_struct_tree_t)) ]
       PROP() 
       LOCAL(gvars gv; temp _b b) 
       SEP (mem_mgr gv; nodebox_rep g g_root lsh1 lock b;
              (* leftover slice of pointer *) data_at_ lsh2 (tptr t_struct_tree_t) b;
              malloc_token Ews (tptr t_struct_tree_t) b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).
(*  DECLARE _treebox_free
   ATOMIC TYPE (rmaps.ConstType ( val* val * val * share * globals  * gname * gname)) OBJ BST INVS empty top
  WITH  lock: _, b:_,np:_, sh:_, gv: _, g:_, g_root: gname
  PRE  [ _b OF (tptr (tptr t_struct_tree_t)) ]
       PROP(readable_share sh) 
       LOCAL(gvars gv; temp _b b) 
           SEPS (mem_mgr gv; nodebox_rep g g_root sh lock np b; 
           malloc_token Ews (tptr t_struct_tree_t) b) | (tree_rep2 g g_root BST)
  POST [ Tvoid ]
  EX t : unit,
    PROP()
    LOCAL()
    SEP (mem_mgr gv). *)

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH lock: val, p: val, gv : globals, g: gname, g_root: gname
  PRE  [ _p OF (tptr t_struct_tree_t) ]
       PROP() 
       LOCAL(gvars gv; temp _p p) 
       SEP (mem_mgr gv;
            ltree g g_root lsh1 p lock)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv).
(*  DECLARE _tree_free
   ATOMIC TYPE (rmaps.ConstType ( val * val  * share * globals  * gname)) OBJ BST INVS empty top
  WITH lock: _, np: _, sh:_, gv : _, g: _
  PRE  [ _p OF (tptr t_struct_tree_t) ]
       PROP(readable_share sh) 
       LOCAL(gvars gv; temp _p np) 
       SEPS (mem_mgr gv)|(ltree  BST g  lock np)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (mem_mgr gv). *)

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH l: val, tl: val, x: Z, vx: val, tll: val,
       r: val, tr: val, y: Z, vy: val, mid: val, trr: val
  PRE  [_tgl OF (tptr t_struct_tree_t),
        _tgr OF (tptr t_struct_tree_t)]
    PROP (is_pointer_or_null mid)
    LOCAL (temp _tgl l; temp _tgr r)
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tl l;
         field_at Ews (t_struct_tree_t) [StructField _t] tr r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, r))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (mid, trr))) tr)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (field_at Ews (t_struct_tree_t) [StructField _t] tr l;
         field_at Ews (t_struct_tree_t) [StructField _t] tl r;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (tll, mid))) tl;
         data_at Ews t_struct_tree (Vint (Int.repr y), (vy, (r, trr))) tr).

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType ( val *  share * val * Z * val * globals*gname* gname)) OBJ BST INVS base.empty base.top
  WITH  b:_, sh: _, lock : _,  x: _, v:_, gv : _ , g:_, g_root:_
  PRE [  _t OF (tptr (tptr t_struct_tree_t)), _x OF tint,  _value OF (tptr tvoid) ]
          PROP (  readable_share sh; Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v; is_pointer_or_null lock )
          LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv )
          SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) | (!!(sorted_tree BST)&&tree_rep2 g g_root  BST )
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) | (!!(sorted_tree (insert x v BST))&&tree_rep2 g g_root  (insert x v BST) ). 

Program Definition delete_spec :=
 DECLARE _delete
  ATOMIC TYPE (rmaps.ConstType (_ * _ * _ * _ * _ * _ * _)) OBJ BST INVS base.empty base.top
  WITH b: val, x: Z, lockb: val, gv: globals, sh: share, g: gname, g_root: gname
  PRE  [ _t OF (tptr (tptr t_struct_tree_t)), _x OF tint]
    PROP (Int.min_signed <= x <= Int.max_signed; readable_share sh)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lockb b) | (tree_rep2 g g_root BST)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv; nodebox_rep g g_root sh lockb b) | (tree_rep2 g g_root (delete x BST)).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (VST.veric.rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (VST.veric.rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11), Q, inv_names) := __a in
     PROP () LOCAL () ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0, x11 at level 0,
             S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (VST.veric.rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (VST.veric.rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12), Q, inv_names) := __a in
     PROP () LOCAL () ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0, x11 at level 0, x12 at level 0,
             S2 at level 0).

Program Definition pushdown_left_spec :=
 DECLARE _pushdown_left
 ATOMIC TYPE (rmaps.ConstType (val * val * val * Z * val * val * val * val * val * gname * gname * globals)) OBJ BST INVS base.empty base.top
 WITH p: val, tp: val, lockp: val,
       x: Z, vx: val, locka: val, lockb: val, ta: val, tb: val,
       g: gname, g_root: gname, gv: globals
  PRE [ _tgp OF (tptr t_struct_tree_t)]
    PROP (Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) vx)
    LOCAL (temp _tgp p; gvars gv)
    SEP (mem_mgr gv;
         field_at Ews t_struct_tree_t [StructField _t] tp p;
         data_at Ews t_struct_tree (Vint (Int.repr x), (vx, (ta, tb))) tp;
         ltree g g_root lsh2 p lockp;
         ltree g g_root lsh1 ta locka;
         ltree g g_root lsh1 tb lockb;
         malloc_token Ews t_struct_tree tp;
         malloc_token Ews tlock lockp;
         malloc_token Ews t_struct_tree_t p) | (tree_rep2 g g_root BST)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (mem_mgr gv) | (tree_rep2 g g_root (delete x BST)).

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType (val * share * val * Z * globals * gname * gname))
         OBJ BST INVS base.empty base.top
  WITH b:_, sh:_, lock:_, x:_, gv:_, g:_, g_root:_
  PRE [_t OF (tptr (tptr t_struct_tree_t)), _x OF tint]
    PROP (readable_share sh;
          Int.min_signed <= x <= Int.max_signed; is_pointer_or_null lock)
    LOCAL (temp _t b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b) | (tree_rep2 g g_root BST)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b) |
        (!!(ret = lookup nullval x BST) && tree_rep2 g g_root BST).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt nil gv
  POST [ tint ] main_post prog nil gv.


Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.*)

(*no freelock_spec, spawn_spec, freelock2_spec, release2_spec*)
Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
    surely_malloc_spec;
    treebox_new_spec; tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec ;
    (* spawn_spec; thread_func_spec; *) main_spec 
  ]).

Lemma node_rep_saturate_local:
   forall r p g g_current, node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof.
  intros. rewrite node_rep_def. Intros tp. entailer!.
Qed.
Hint Resolve node_rep_saturate_local: saturate_local.


Lemma node_rep_valid_pointer:
  forall t g g_current p, node_rep p g g_current t |-- valid_pointer p.
Proof.
  intros; rewrite node_rep_def.
  Intros tp; entailer!.
Qed.
Hint Resolve node_rep_valid_pointer : valid_pointer.



Lemma tree_rep_R_saturate_local:
   forall t p g_children g, tree_rep_R p t g_children g |-- !! is_pointer_or_null p.
Proof. 
intros. unfold tree_rep_R. destruct (eq_dec p nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!. 
Qed.
Hint Resolve tree_rep_R_saturate_local: saturate_local.

Lemma tree_rep_R_valid_pointer:
  forall t tp g_children g, tree_rep_R tp t g_children g |-- valid_pointer tp.
Proof.
intros. unfold tree_rep_R. destruct (eq_dec tp nullval). entailer!.
Intros ga gb x v pa pb locka lockb. entailer!. 
Qed.
Hint Resolve tree_rep_R_valid_pointer : valid_pointer.


Lemma ltree_saturate_local:
  forall g g_root lsh p lock, ltree g g_root lsh p lock |-- !! isptr p.
Proof.
  intros; unfold ltree; entailer!.
Qed.
Hint Resolve ltree_saturate_local: saturate_local.


 Definition insert_inv (b: val)  (lock:val)  (sh: share) (x: Z) (v: val) ( g_root:gname) gv (inv_names : invG) (Q : mpred) (g:gname) : environ -> mpred :=
(  EX r : number * number * option ghost_info, EX g_in :gname, EX lock_in :val, EX np: val,
PROP (  check_key_exist' x (fst r) = true )
LOCAL (temp _l lock_in; temp _tgt np; temp _t b; 
temp _x (vint x); temp _value v; gvars gv)
SEP (nodebox_rep g g_root sh lock b; 
  field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
  malloc_token Ews tlock lock_in;
node_rep np g g_in r; my_half g_in r;
 |> lock_inv lsh2 lock_in  (node_lock_inv g np g_in lock_in);
atomic_shift (λ BST : @tree val, !! sorted_tree BST && tree_rep2 g g_root BST ) ∅ ⊤
  (λ (BST : @tree val) (_ : ()),
     fold_right_sepcon [!! sorted_tree  (insert x v BST) && tree_rep2 g g_root (insert x v BST) ]) 
  (λ _ : (), Q); mem_mgr gv ))%assert.

Definition lookup_inv (b: val) (lock:val) (sh: share) (x: Z) gv (inv_names : invG)
           (Q : val -> mpred) (g g_root:gname) : environ -> mpred :=
  (EX tp: val, EX np: val, EX r : number * number * option ghost_info,
   EX g_in :gname, EX lock_in: val,
   PROP ()
   LOCAL (temp _p tp; temp _l lock_in; temp _tgt np; temp _t b;
          temp _x (vint x); gvars gv)
   SEP (nodebox_rep g g_root sh lock b;
       field_at lsh2 t_struct_tree_t [StructField _lock] lock_in np ;
       |> lock_inv lsh2 lock_in (node_lock_inv g np g_in lock_in);
       field_at Ews t_struct_tree_t [StructField _t] tp np;
(*        malloc_token Ews t_struct_tree_t np; in_tree g lsh1 g_in; *)
       malloc_token Ews t_struct_tree_t np; in_tree g g_in;
       tree_rep_R tp r.1 r.2 g; my_half g_in r; malloc_token Ews tlock lock_in;
       atomic_shift (λ BST : tree,  tree_rep2 g g_root BST) ∅ ⊤
                    (λ (BST : tree) (ret : val),
                     fold_right_sepcon
                       [!! (ret = lookup nullval x BST) && tree_rep2 g g_root BST]) Q;
       mem_mgr gv))%assert.

(*
Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp. auto.
  + rewrite emp_sepcon. auto.
Qed.

Lemma node_rep_nullval: forall t,
  node_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl node_rep.
  Intros pa pb locka lockb. entailer!.
Qed.
Hint Resolve node_rep_nullval: saturate_local. *)

(*Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- nodebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.*)

(*Lemma bst_left_entail: forall sh1 lock1 p1 b1 pa tp locka,
  lock_inv sh1 lock1 (t_lock_pred p1 lock1) *
  data_at Ews (tptr t_struct_tree_t) p1 b1 *
  field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1
  |-- data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
    ltree sh1 pa locka *
    (data_at Ews (tptr t_struct_tree_t) pa (offset_val 8 tp) *
     ltree sh1 pa locka -*
     data_at Ews (tptr t_struct_tree_t) p1 b1 *
     field_at sh1 t_struct_tree_t [StructField _lock] lock1 p1 *
     lock_inv sh1 lock1 (t_lock_pred p1 lock1)).
Proof.
  intros.
  unfold ltree at 1; entailer!.
  { admit. }
  unfold_data_at (data_at _ _ _ b1). Check field_at_data_at.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  Check wand_sepcon_adjoint.
  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  node_rep t1 p1 * node_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.
*)

Lemma tree_rep_R_nullval: forall t g_info g,
  tree_rep_R nullval t (g_info: option ghost_info) g |-- !! (g_info = @None ghost_info).
Proof.
  intros.
  unfold tree_rep_R. simpl. entailer!.
Qed.
Hint Resolve tree_rep_R_nullval: saturate_local.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree. Intros np.
  forward. (* _tgt = *_t; *)
  forward. (* _l = (_tgt -> _lock); *)
  forward_call (lock, sh, (node_lock_inv g np g_root lock)). (* _acquire(_l); *)
  unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.
  Intros a. destruct a as (p, o). rewrite node_rep_def. Intros tp.
  forward. (* _p = (_tgt -> _t); *) simpl fst. simpl snd.
  forward_while (lookup_inv b lock sh x gv inv_names Q g g_root).
  (* while (_p != (tptr tvoid) (0)) *)
  - (* current status implies lookup_inv *)
    unfold lookup_inv. Exists tp np (p, o) g_root lock. entailer. cancel.
    unfold nodebox_rep. Exists np. cancel. unfold ltree, node_lock_inv. entailer!.
  - (* type check *) entailer!.
  - (* loop body *)
    unfold tree_rep_R. rewrite if_false; auto. Intros ga gb x0 v pa pb locka lockb.
    forward. (* _y = (_p -> _key); *)
    forward_if. (* if (_x < _y) { *)
    + forward. (* _tgt = (_p -> _left); *)
      forward. (* _l_old = _l; *) unfold ltree at 1. Intros.
      forward. (* _l = (_tgt -> _lock); *)
      forward_call (locka, lsh1, (node_lock_inv g pa ga locka)). (* _acquire(_l); *)
      unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
      change (selflock (node_lock_inv_pred g pa ga locka) lsh2 locka) with
          (node_lock_inv g pa ga locka). unfold node_lock_inv_pred, sync_inv.
      Intros a. rewrite node_rep_def. Intros tpa.
      forward. (* _p = (_tgt -> _t); *)
      forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                    node_lock_inv g np0 g_in lock_in). (* _release2(_l_old); *)
      * lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
        Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
        rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
        unfold ltree. entailer!. rewrite sepcon_comm. rewrite !later_sepcon. cancel.
      * Exists ((((tpa, pa), a), ga), locka). entailer!. cancel.
    + forward_if. (* if (_y < _x) { *)
      * forward. (* _tgt = (_p -> _right); *)
        forward. (* _l_old__1 = _l; *) unfold ltree at 2. Intros.
        forward. (* _l = (_tgt -> _lock); *)
        forward_call (lockb, lsh1, (node_lock_inv g pb gb lockb)). (* _acquire(_l); *)
        unfold node_lock_inv at 2. rewrite selflock_eq. Intros.
        change (selflock (node_lock_inv_pred g pb gb lockb) lsh2 lockb) with
            (node_lock_inv g pb gb lockb). unfold node_lock_inv_pred, sync_inv.
        Intros a. rewrite node_rep_def. Intros tpb.
        forward. (* _p = (_tgt -> _t); *)
        forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                      node_lock_inv g np0 g_in lock_in). (* _release2(_l_old__1); *)
        -- lock_props. setoid_rewrite node_lock_inv_def at 4. simpl. cancel.
           Exists r. rewrite node_rep_def. Exists tp0. cancel. unfold tree_rep_R at 2.
           rewrite if_false; auto. Exists ga gb x0 v pa pb locka lockb. entailer!.
           unfold ltree. entailer!. rewrite !later_sepcon. cancel.
        -- Exists ((((tpb, pb), a), gb), lockb). entailer!. cancel.
      * forward. (* _v = (_p -> _value); *)
        assert (x0 = x) by lia. subst x0. clear H6 H7.
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _) (in_tree g _).
(*         viewshift_SEP 0 ((EX y, Q y * (!!(y = v) && in_tree g lsh1 g_in)) * *)
        viewshift_SEP 0 ((EX y, Q y * (!!(y = v) && in_tree g g_in)) *
                         my_half g_in r). {
          go_lower. (* apply sync_commit_gen. *) admit. } Intros y. subst y.
        forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                      node_lock_inv g np0 g_in lock_in). (* _release2(_l); *)
        -- lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
           fold (node_lock_inv g np0 g_in lock_in). unfold node_lock_inv_pred.
           unfold sync_inv. Exists r. rewrite node_rep_def. Exists tp0. cancel.
           unfold tree_rep_R. rewrite if_false; auto.
           Exists ga gb x v pa pb locka lockb. entailer!.
        -- forward. Exists v. entailer!.
  - gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _) (in_tree g _).
(*     viewshift_SEP 0 (Q nullval * my_half g_in r * in_tree g lsh1 g_in). { *)
    viewshift_SEP 0 (Q nullval * my_half g_in r * in_tree g g_in). {
      admit. }
    forward_call (lock_in, lsh2, node_lock_inv_pred g np0 g_in lock_in,
                  node_lock_inv g np0 g_in lock_in). (* _release2(_l); *)
    + lock_props. unfold node_lock_inv at 2. rewrite selflock_eq.
      fold (node_lock_inv g np0 g_in lock_in). unfold node_lock_inv_pred.
      unfold sync_inv. Exists r. rewrite node_rep_def. Exists tp0. cancel.
    + forward. Exists nullval. entailer!.
Abort.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (tptr t_struct_tree_t, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros p. (* treebox p *)
  forward_call (t_struct_tree_t, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros newt. (* tree_t *newt *)
  forward.
  forward_call (tarray (tptr tvoid) 2, gv).
  { split; simpl; [ unfold Z.max; simpl; rep_omega | auto]. }
  Intros l. (* lock_t *l *)
  ghost_alloc (both_halves (Neg_Infinity, Pos_Infinity, @None(ghost_info))).
  { apply @part_ref_valid. }
  Intros g_root'. rewrite <- both_halves_join.
  ghost_alloc (ghost_part_ref (P := set_PCM) Tsh (Ensembles.Singleton nat g_root') (find_ghost_set E_ghost g_root')).
  { apply @part_ref_valid. }
  Intros g'.
  Local Typeclasses eauto := 1. (* Improve forward_call speed *)
  Time forward_call (l, Ews, node_lock_inv g' newt g_root' l).
  Local Typeclasses eauto := 10. (* Restore *)
  forward.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] newt) by entailer!.
  rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
  forward_call (l, lsh2, node_lock_inv_pred g' newt g_root' l, node_lock_inv g' newt g_root' l).
  { lock_props.
    setoid_rewrite node_lock_inv_def at 3.
    Exists ((Neg_Infinity, Pos_Infinity, None : (option (ghost_info)))).
    unfold_data_at (data_at Ews t_struct_tree_t _ _).
    rewrite node_rep_def. Exists (vint 0).
    erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto.
    cancel. simpl.
    rewrite <- ghost_part_ref_join.
    unfold in_tree; Exists (Tsh).
    cancel. unfold tree_rep_R; simpl.
    entailer!. }
  forward.
  unfold nodebox_rep. unfold ltree.
  Exists p l g' g_root'. Exists newt. entailer!.
  erewrite <- data_at_share_join by eauto; cancel.
  unfold tree_rep2. unfold ghost_ref.
  Exists (E_ghost : @ghost_tree val).
  simpl. entailer!.
Qed.

(* Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function. simpl.
  unfold ltree; Intros.
  forward.
  forward_call (lock, lsh1, t_lock_pred p lock).
  rewrite t_lock_pred_def at 2.
  Intros treeval tp.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _p tp; temp _l lock; gvars gv; temp _tgp p)
    SEP (lock_inv lsh1 lock (t_lock_pred p lock);
        field_at Ews t_struct_tree_t [StructField _t] tp p;
        field_at lsh2 t_struct_tree_t [StructField _lock] lock p;
        malloc_token Ews t_struct_tree_t p; malloc_token Ews tlock lock;
        lock_inv lsh2 lock (t_lock_pred p lock); mem_mgr gv;
        field_at lsh1 t_struct_tree_t [StructField _lock] lock p)).
  { unfold node_rep. destruct treeval.
    { Intros. contradiction. }
    { Intros pa pb locka lockb.
      forward. (* p->left *)
      forward. (* p -> right *)
      forward_call (t_struct_tree, tp, gv).
      { if_tac.
        - contradiction.
        - entailer!. }
      unfold ltree at 1; Intros.
      forward_call (locka, pa, gv).
      { unfold ltree at 2. entailer!. }
      forward_call (lockb, pb, gv).
      entailer!. }}
  { forward.
    entailer!.
    unfold node_rep.
    destruct treeval; Intros.
    - cancel.
    - Intros pa pb locka lockb.
      entailer!. }
  forward_call (lock, Ews, lsh2, t_lock_pred_base p lock, t_lock_pred p lock).
  { lock_props.
    rewrite <- (lock_inv_share_join lsh1 lsh2 Ews) by auto.
    entailer!. }
  forward_call (tlock, lock, gv).
  { if_tac.
    - entailer!.
    - entailer!. }
  forward_call (t_struct_tree_t, p, gv).
  { if_tac.
    - entailer!.
    - entailer!.
      unfold_data_at_ p.
      unfold_data_at (data_at Ews t_struct_tree_t _ p).
      rewrite <- (field_at_share_join lsh2 lsh1 Ews t_struct_tree_t [StructField _lock] _ p) by eauto.
      cancel. }
    forward.
  
Qed. *)

(* Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold nodebox_rep.
  Intros np.
  forward.
  forward_call (lock, np, gv).
  forward_call (tptr t_struct_tree_t, b, gv).
  { destruct (eq_dec b nullval).
    { entailer!. }
    { erewrite <- (data_at__share_join _ _ Ews) by eauto; entailer!. }}
  forward.
Qed. *)


Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  { entailer!. }
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  unfold nodebox_rep, ltree .
  Intros np.
  forward.
  forward.
  forward_call (lock, sh, (node_lock_inv g np g_root lock)).
   eapply semax_pre; [
    | apply (semax_loop _ (insert_inv b  lock sh x v g_root gv inv_names Q g) (insert_inv b  lock sh  x v g_root gv  inv_names Q g) )]. 
  * (* Precondition *)
    unfold insert_inv.
    unfold node_lock_inv at 2. rewrite selflock_eq. unfold node_lock_inv_pred at 1. unfold sync_inv at 1. unfold nodebox_rep, ltree. Intro r. Exists r g_root lock np. Exists np.
     unfold node_lock_inv. entailer!. admit. 
  * (* Loop body *)
    unfold insert_inv.
    Intros  r g_in lock_in np0.
    forward. (* Sskip *)
    rewrite node_rep_def.
    Intros tp.
    forward. (*p=tgt->t*)
    forward_if.
    + (* then clause *)
      subst tp.
      unfold tree_rep_R. simpl. Intros.
      forward_call (t_struct_tree_t, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p1'.
      forward_call (t_struct_tree_t, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p2'.
      forward. (* p1->t=NULL *)      
     assert_PROP (field_compatible t_struct_tree_t [] p1') by entailer!.  
      simpl.
      forward. (* p1->t=NULL *)      
     assert_PROP (field_compatible t_struct_tree_t [] p2') by entailer!.  
      simpl. 
      forward_call (tlock, gv).
      { simpl. rewrite Z.max_r. repeat (split; auto); rep_omega. rep_omega. }
      Intros l1.
      unfold tlock.
      destruct r.
      destruct p.
      ghost_alloc (both_halves (n, Finite_Integer x,@None(gname*gname))).
       { apply @part_ref_valid. }
      Intros g1. rewrite <- both_halves_join.
      ghost_alloc (both_halves ( Finite_Integer x, n0,@None(gname*gname))).
       { apply @part_ref_valid. }
      Intros g2. rewrite <- both_halves_join.
      simpl in H4. Intros.
     gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _) (public_half  g1 _) (public_half g2 _) (in_tree g _ _).
         viewshift_SEP 0 (Q  * my_half g_in (n,n0,Some(g1,g2)) * ( in_tree g lsh1 g_in * in_tree g lsh1 g1 * in_tree g lsh1 g2)).
         {  go_lower.
          rewrite -> sepcon_assoc. rewrite -> sepcon_assoc.  eapply sync_commit_gen1.
            -  apply @bi.sep_timeless. apply own_timeless. apply @bi.sep_timeless.  apply own_timeless. apply own_timeless. 
            - intros. iIntros "[[Ha Hb] Hc]". iDestruct "Hc" as "[% Hc]". iDestruct "Hb" as "[Hb Hd]".  iPoseProof ( extract_lemmas_for_treerep2 with "[Hd Hc]") as "Hadd". apply H7.    iFrame.   
               iDestruct "Hadd" as (n1 n2 o0) "[Hc Hd]".  iExists (n1,n2,o0). iModIntro.  iFrame. instantiate (1:= fun x0 => !! sorted_tree x0 && public_half g1 (n, Finite_Integer x, None) * public_half g2 (Finite_Integer x, n0, None) * 
              ( (( !!(o = None /\ check_key_exist' x (n,n0) = true) &&public_half g_in (n,n0,Some(g1,g2))* public_half g1 (n, Finite_Integer x, @None(gname*gname))* public_half g2 (Finite_Integer x, n0,@None(gname*gname)))-* (|==> tree_rep2 g g_root (insert x v x0)*  in_tree g lsh1 g_in * in_tree g lsh1 g1 * in_tree g lsh1 g2)%I) && (public_half g_in (n,n0,o) -* (tree_rep2 g g_root x0 * in_tree g lsh1 g_in)))).
               simpl.  iIntros "a". iDestruct "a"as "%". injection H8;intros. subst o0 n1 n2. iFrame. iSplit. auto. auto. 
           - intros. iIntros "[Ha Hb]". iDestruct "Hb" as  "[[[% Hb] Hc] He]". iModIntro.  rewrite <- ( sepcon_comm (in_tree g lsh1 g_in) ( tree_rep2 g g_root x0)) . iPoseProof ( bi.and_elim_r with "He") as "Hnew". iFrame.
             iPoseProof (modus_ponens_wand with "[Ha Hnew]") as "H". instantiate (1 :=  in_tree g lsh1 g_in * tree_rep2 g g_root x0). iFrame. iDestruct "H" as "[H H']". iFrame. iSplit;repeat auto.    
           - intros. iIntros "[Ha Hb]". iDestruct "Hb" as  "[[[% Hb] Hc] Hd]".   iPoseProof ( bi.and_elim_l with "Hd") as "Hnew". iPoseProof (modus_ponens_wand with "[Ha Hb Hc Hnew]") as "H". iFrame. repeat iSplit. auto. auto. auto. 
             iMod "H". iModIntro.  iDestruct "H" as "[[[Ha Hb] Hc] Hd]". iFrame. iExists (). iSplit. apply (insert_sorted x v) in H7. auto. auto. 
         }
      forward_call (l1, Ews, (node_lock_inv g p1' g1 l1)).
      Intros.
      forward. (*p1->lock = l1*)      
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto.
      forward_call (l1, lsh2,(node_lock_inv_pred g p1' g1 l1) , (node_lock_inv g p1' g1 l1)).
     { lock_props.
       unfold node_lock_inv at 4. rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (n, Finite_Integer x,@None(gname*gname)). 
       rewrite node_rep_def . Exists nullval.
       unfold_data_at 2%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }       
     forward_call (tlock, gv). 
      { simpl.  rewrite Z.max_r. repeat (split; auto); rep_omega. rep_omega. }
      Intros l2.
      forward_call (l2, Ews, (node_lock_inv g p2' g2 l2)).
      forward. (*p2->lock = l2*)    
      rewrite <- (lock_inv_share_join lsh1 lsh2) by auto. 
      forward_call (l2, lsh2,(node_lock_inv_pred g p2' g2 l2), (node_lock_inv g p2' g2 l2)).
     { lock_props.
       unfold node_lock_inv at 5. rewrite selflock_eq .  unfold node_lock_inv_pred at 1. unfold sync_inv at 1.  Exists (Finite_Integer x,n0,@None(gname*gname)). 
       rewrite node_rep_def . Exists nullval.
       unfold_data_at 1%nat. erewrite <- (field_at_share_join _ _ _ _ [StructField _lock]) by eauto. unfold tree_rep_R. simpl. unfold node_lock_inv at 2. entailer!. }
      forward_call (t_struct_tree, gv).
      { simpl. repeat (split; auto); rep_omega. }
      Intros p'.
      forward. (* tgt->t=p; *)  
      forward. (* p->key=x; *)
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)      
      forward_call(lock_in, lsh2,(node_lock_inv_pred g np0 g_in lock_in),  (node_lock_inv g np0 g_in lock_in)).
      { lock_props.
        unfold node_lock_inv at 4.  rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists (n, n0, Some(g1,g2)). 
       rewrite node_rep_def. Exists p'. unfold node_lock_inv.  cancel. unfold tree_rep_R. assert_PROP (p' <> nullval). { entailer!. }  destruct (eq_dec p' nullval).  entailer!. 
       Exists g1 g2 x v p1' p2' l1 l2. unfold node_lock_inv.  unfold ltree. entailer!.   rewrite <- later_sepcon; eapply derives_trans; [|apply sepcon_derives, derives_refl; apply now_later]. unfold node_lock_inv. entailer!.
       
       } 
      forward. entailer!.   (* return; *)
    + (* else clause *)
      unfold tree_rep_R. rewrite if_false. 
      Intros ga gb x0 v0 pa pb locka lockb .
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. 
        forward.
        unfold_data_at (data_at _ _ _ tp).
        unfold ltree at 1; Intros.
        forward.
        forward_call (locka, lsh1,(node_lock_inv g pa ga locka)).
        Intros .
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
          unfold node_lock_inv at 4.  rewrite selflock_eq . unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Exists r. 
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R. rewrite if_false.  assert_PROP (tp <> nullval). { entailer!. }  
          Exists ga gb x0 v0 pa pb locka lockb.  unfold ltree at 2. entailer!.   repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp); entailer!. auto. 
           }
          unfold node_lock_inv at 1. rewrite selflock_eq. unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Intros a.
         Exists a ga locka pa. unfold node_lock_inv.
         entailer!. admit.
      - (* Inner if, second branch:  k<x *)
        forward. 
        forward.
        unfold_data_at (data_at _ _ _ tp).
        unfold ltree at 2; Intros.
        forward.
        forward_call (lockb, lsh1,(node_lock_inv g pb gb lockb)).
        Intros .
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
          unfold node_lock_inv at 4.  rewrite selflock_eq . unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Exists r. 
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R. rewrite if_false.  assert_PROP (tp <> nullval). { entailer!. }  
          Exists ga gb x0 v0 pa pb locka lockb.  unfold ltree at 3. entailer!.   repeat rewrite later_sepcon. unfold node_lock_inv at 3. unfold_data_at (data_at _ _ _ tp); entailer!. auto. 
         }
         unfold node_lock_inv at 1. rewrite selflock_eq. unfold node_lock_inv_pred at 1.  unfold sync_inv at 1. Intros a.
         Exists a gb lockb pb. unfold node_lock_inv.
         entailer!. admit.
      - (* x = k *)
        forward.
        gather_SEP (atomic_shift _ _ _ _ _) (my_half g_in _) ( in_tree g _ _). 
        viewshift_SEP 0 (Q  * my_half g_in r * in_tree g lsh1 g_in).
        {
          go_lower. destruct r. destruct p.  eapply sync_commit_gen1.
           - apply own_timeless. 
           - intros. iIntros "H". iDestruct "H" as "[ Ha H ]". iDestruct "H" as "[% H]".  iPoseProof ( extract_lemmas_for_treerep2 with "[Ha H]") as "Hadd". apply H11. iFrame.
               iDestruct "Hadd" as (n1 n2 o0) "[Hc Hd]".  iExists (n1,n2,o0). iModIntro.  iFrame.  iIntros "a". iDestruct "a"as "%". inv H12;intros.  instantiate (1:= fun x2 => !! sorted_tree x2 &&
              ((( !!(o = None /\ check_key_exist' x (n,n0) = true) &&public_half g_in (n,n0,Some(ga,gb))* public_half ga (n, Finite_Integer x, @None(gname*gname))* public_half gb (Finite_Integer x, n0,@None(gname*gname)))-* (|==> tree_rep2 g g_root (insert x v x2)*  in_tree g lsh1 g_in * in_tree g lsh1 ga * in_tree g lsh1 gb)%I) && (public_half g_in (n,n0,o) -* (tree_rep2 g g_root x2 * in_tree g lsh1 g_in)))).
              iFrame. iSplit. auto. auto.
           - intros. iIntros "[Ha Hb]". iDestruct "Hb" as  "[% Hb]". iModIntro. rewrite (sepcon_comm (in_tree g lsh1 g_in) _) .  iPoseProof ( bi.and_elim_r with "Hb") as "Hnew".
             iPoseProof (modus_ponens_wand with "[Ha Hnew]") as "H". instantiate (1 :=  tree_rep2 g g_root x1* in_tree g lsh1 g_in). iFrame. iDestruct "H" as "[H H']". iFrame. iSplit;repeat auto.
           - intros. iIntros "[Ha Hb]". iDestruct "Hb" as  "[% Hb]". iPoseProof ( bi.and_elim_r with "Hb") as "Hnew". admit.       
       
        }
        forward_call(lock_in, lsh2, (node_lock_inv_pred g np0 g_in lock_in) ,(node_lock_inv g np0 g_in lock_in)).
        { lock_props.
           unfold node_lock_inv at 2.  rewrite selflock_eq . unfold node_lock_inv_pred at 1. unfold sync_inv at 1. Exists r. 
          rewrite node_rep_def. Exists tp.  cancel. unfold tree_rep_R. rewrite if_false.  assert_PROP (tp <> nullval). { entailer!. }  
          Exists ga gb x0 v pa pb locka lockb. unfold node_lock_inv. entailer!. auto. }
        forward. entailer!.
       - auto.
  * (* After the loop *)
    forward. normalize.
Admitted. 


(* Program Definition lookup_spec :=
 DECLARE _lookup
   ATOMIC TYPE (rmaps.ConstType ( val * val *  Z * share * val  * gname)) OBJ BST INVS empty top
  WITH  b: _, np : _,  x: _, sh:_, lock : _, g: _
  PRE  [ _t OF (tptr (tptr t_struct_tree_t(*t_struct_tree*))), _x OF tint  ]
    PROP(readable_share sh; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEPS (nodebox_rep sh lock np b) | ( ltree  BST g  lock np)   
  POST [ tptr Tvoid ]
   EX ret : val,
    PROP ()
    LOCAL(temp ret_temp ret)
    SEP (!! (ret =  lookup(Vint (Int.repr x))  x  BST) && nodebox_rep sh lock np b;  ltree  BST g  lock np  ).
    
Definition thread_lock_R sh lock np gv:=
   (mem_mgr gv*
   data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb)*
   data_at Ers (tarray tschar 16)
   (map (Vint oo cast_int_int I8 Signed)
   [Int.repr 79; Int.repr 78; Int.repr 69;
   Int.repr 95; Int.repr 70; Int.repr 82;
   Int.repr 79; Int.repr 77; Int.repr 95;
   Int.repr 84; Int.repr 72; Int.repr 82;
   Int.repr 69; Int.repr 65; Int.repr 68; 
   Int.repr 0]) (gv ___stringlit_1)*
   nodebox_rep sh lock np).

Definition thread_lock_inv sh1 lsh2 np gv lockb lockt :=
  selflock (thread_lock_R sh1 lockb np gv) lsh2 lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * val * val * globals
    PRE [ _args OF (tptr tvoid) ]
         let '(sh, lock, np, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   ( mem_mgr gv; 
                 data_at lsh1 (tptr (tptr (t_struct_tree_t))) np (gv _tb);
                 data_at Ers (tarray tschar 16)
                 (map (Vint oo cast_int_int I8 Signed)
                 [Int.repr 79; Int.repr 78; Int.repr 69;
                 Int.repr 95; Int.repr 70; Int.repr 82;
                 Int.repr 79; Int.repr 77; Int.repr 95;
                 Int.repr 84; Int.repr 72; Int.repr 82;
                 Int.repr 69; Int.repr 65; Int.repr 68; 
                 Int.repr 0]) (gv ___stringlit_1);
                 nodebox_rep sh1 lock np;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh1 sh np gv lock (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (). *)



Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.
(*
Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; omega)
                          | rewrite if_falseb by (apply Z.ltb_ge; omega)].

Lemma t_lock_exclusive : forall p l,
  exclusive_mpred (t_lock_pred p l).
Proof.
  intros. rewrite t_lock_pred_def.
  eapply derives_exclusive, exclusive_sepcon1 with 
  (P := EX tp : _, field_at Ews t_struct_tree_t [StructField _t] tp p)
  (Q:= EX t0 : tree val, EX tp : val, _ * node_rep t0 tp * malloc_token Ews t_struct_tree_t p * malloc_token Ews tlock l * _).
  - unfold t_lock_pred_base. Intros t0 tp. Exists tp. cancel. Exists t0 tp. apply derives_refl.
  - apply ex_field_at_exclusive; auto.
    simpl. omega.
Qed.
Hint Resolve t_lock_exclusive.

Lemma t_lock_rec : forall p l,
  rec_inv lsh2 l (t_lock_pred_base p l) (t_lock_pred p l).
Proof.
  intros; apply t_lock_pred_def.
Qed.
Hint Resolve t_lock_rec.


Lemma thread_inv_exclusive : forall sh1 lsh2 nb gv lockb lockt,
  exclusive_mpred (thread_lock_inv sh1 lsh2 nb gv lockb lockt).
Proof.
  intros; apply selflock_exclusive. unfold thread_lock_R. apply exclusive_sepcon1. apply exclusive_sepcon1.
  apply exclusive_sepcon2. apply data_at_exclusive. auto. simpl. omega.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
start_function.
forward. 
unfold nodebox_rep.
Intros np0.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_1)). { entailer!. }
forward_call(sh1,lock,np,1,gv ___stringlit_1,gv).
 * unfold nodebox_rep. Exists np0. entailer!.
 * split. auto. split. rep_omega. auto.
 * forward_call (gv _thread_lock, sh, thread_lock_R sh1 lock np gv, thread_lock_inv sh1 sh np gv lock (gv _thread_lock)).
    { lock_props. unfold thread_lock_inv, thread_lock_R. rewrite selflock_eq at 2. entailer!. }
    forward.
Qed.

Lemma ltree_share_join : forall (sh1 sh2 sh : share) (p : val) (lock : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
  ltree sh1 p lock * ltree sh2 p lock = ltree sh p lock.
Proof.
  intros; unfold ltree.
  rewrite sepcon_andp_prop, sepcon_andp_prop', <- andp_assoc, andp_dup; f_equal.
  rewrite <- sepcon_assoc, (sepcon_assoc (field_at _ _ _ _ _)), (sepcon_comm (lock_inv _ _ _)), <- sepcon_assoc.
  erewrite field_at_share_join by eauto.
  rewrite sepcon_assoc.
  erewrite lock_inv_share_join by eauto; reflexivity.
Qed.

(* for conclib *)
Lemma field_at_value_cohere : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p, readable_share sh1 ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |--
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v1 p.
Proof.
  intros; unfold field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.

Lemma field_at_value_eq : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject (nested_field_type t gfs) v1 <> Vundef -> repinject (nested_field_type t gfs) v2 <> Vundef ->
  type_is_by_value (nested_field_type t gfs) = true -> type_is_volatile (nested_field_type t gfs) = false ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold field_at, at_offset; Intros.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  sep_apply mapsto_value_eq; Intros; apply prop_right.
  set (t' := nested_field_type t gfs) in *.
  pose proof (f_equal (valinject t') H6) as Heq.
  rewrite !valinject_repinject in Heq; auto.
Qed.

Lemma data_at_value_eq : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  repinject t v1 <> Vundef -> repinject t v2 <> Vundef ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |-- !!(v1 = v2).
Proof.
  intros; unfold data_at; apply field_at_value_eq; auto.
Qed.

Lemma nodebox_rep_share_join : forall (sh1 sh2 sh : share) (lock : val) (nb : val),
       readable_share sh1 ->
       readable_share sh2 ->
       sepalg.join sh1 sh2 sh ->
       nodebox_rep sh1 lock nb * nodebox_rep sh2 lock nb = nodebox_rep sh lock nb.
Proof.
  intros; unfold nodebox_rep.
  apply pred_ext.
  - Intros np1 np2.
    assert_PROP (np1 <> Vundef) by entailer!.
    assert_PROP (np2 <> Vundef) by entailer!.
    sep_apply data_at_value_eq; Intros; subst.
    erewrite data_at_share_join, ltree_share_join by eauto.
    Exists np2; auto.
  - Intros np; Exists np np.
    erewrite <- data_at_share_join, <- (ltree_share_join sh3 sh4); eauto; cancel.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
forward_call(gv).
Intros vret.
forward.
forward.
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_2)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),3,gv ___stringlit_2,gv).
 { split3. auto. rep_omega. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_3)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),1,gv ___stringlit_3,gv).
 { split3. auto. rep_omega. auto. }
forward.
assert_PROP ( is_pointer_or_null (gv ___stringlit_4)). { entailer!. }
forward_call(lsh1,(snd vret), (fst vret),4,gv ___stringlit_4,gv).
 { split3. auto. rep_omega. auto. }
forward_call ((gv _thread_lock), Ews, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)). 
forward_spawn _thread_func nullval (lsh2,(snd vret),(fst vret), gv).
 { erewrite <- lock_inv_share_join; try apply lsh1_lsh2_join; auto.
   erewrite <- nodebox_rep_share_join; try apply sh1_sh2_join; auto.
   erewrite <- data_at_share_join; try apply lsh1_lsh2_join; auto.
    entailer!. }
assert_PROP ( is_pointer_or_null (gv ___stringlit_5)). { entailer!. }
forward.
sep_apply (create_mem_mgr gv).
forward_call(sh2,(snd vret), (fst vret),1,gv ___stringlit_5,gv).
 { split3. auto. rep_omega. auto. }
forward_call ((gv _thread_lock), lsh1, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
unfold thread_lock_inv at 2. rewrite selflock_eq. Intros.

forward_call ((gv _thread_lock), Ews, lsh2, thread_lock_R sh1 (snd vret) (fst vret) gv, thread_lock_inv sh1 lsh2 (fst vret) gv (snd vret) (gv _thread_lock)).
{ lock_props. unfold thread_lock_inv. erewrite <- (lock_inv_share_join _ _ Ews); try apply lsh1_lsh2_join; auto. entailer!. }
forward.
forward_call((snd vret), (fst vret), gv).
 { unfold thread_lock_R. erewrite <- (nodebox_rep_share_join _ _ lsh1) ; try apply sh1_sh2_join; auto.
entailer!. }
forward.
Qed.

Lemma node_rep_D {TR p} (P: p<>nullval) :
  node_rep TR p |-- (EX l k v r, !!(TR = T l k v r) && node_rep TR p).
Proof.
destruct TR as [ | l k v r]; simpl; Intros. contradiction.
Exists l k v r. entailer!.
Qed.

(*Variant of t_lock_pred but without the |> lock_inv lsh2 lock (t_lock_pred p lock) term*)
Definition tlp TR (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt * 
  node_rep TR p * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

(*Version of tlp that existentially quantifies over the semantic tree*)
Definition tlp' (p tgt lock:val) : mpred :=
  field_at Ews t_struct_tree_t [StructField _t] p tgt *
  field_at lsh2 t_struct_tree_t [StructField _lock] lock tgt * 
  (EX TR, node_rep TR p) * malloc_token Ews t_struct_tree_t tgt *
  malloc_token Ews tlock lock.

Definition lookup_inv (*TR*) b lsh0 lock0 (x:Z): environ -> mpred :=
  EX p: val, EX tgt:val, EX lock:val,
  PROP() 
  LOCAL(temp _p p; temp _l lock; temp _x (Vint (Int.repr x)))
  SEP (|>lock_inv lsh2 lock (t_lock_pred tgt lock); 
       tlp' (* TR*) p tgt lock;  nodebox_rep lsh0 lock0 b).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof. 
  start_function. rename H into Hx.
  unfold nodebox_rep; Intros tgt.
  forward. deadvars.
  unfold ltree; Intros. rename H into FC_tgt. rewrite lock_inv_isptr; Intros.
  forward.

  (*aquire(l)*)
  forward_call (lock, sh, t_lock_pred tgt lock). 
  rewrite t_lock_pred_def at 2. Intros TREE1 p.
  forward. (*p=tgt->t*)
  deadvars. 

  forward_while (lookup_inv (*TREE1*) b sh lock x).
  + Exists p tgt lock. entailer. 
    unfold tlp' at 1. cancel. Exists TREE1; cancel.
    unfold nodebox_rep. Exists tgt; cancel.
    unfold ltree. entailer!.

  + unfold tlp'; try Intros TR. entailer!.
  + clear TREE1. unfold tlp'; Intros TR.
    clear FC_tgt tgt p. rename p0 into p. rename tgt0 into tgt.
    sep_apply (@node_rep_D TR p HRE); Intros l k v r; subst. simpl; Intros pa pb locka lockb.
    rename H into K. 
    forward.
    forward_if.
    - rename H into HK. 
      forward. forward.
      unfold ltree at 1; Intros. rename H into FC_pa.
      forward. deadvars.
      
      (*aquire(l)*)
      forward_call (locka, lsh1, t_lock_pred pa locka).
      rewrite t_lock_pred_def at 2. Intros pa_T pa_t.

      forward. (*p=tgt->t*)

      (*release*)
      forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
      { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] locka pa;
                  node_rep pa_T pa_t; malloc_token Ews t_struct_tree_t pa;
                  malloc_token Ews tlock locka; lock_inv lsh2 locka (t_lock_pred pa locka);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pa_t pa]); 
          subst Frame; [ reflexivity | clear H].
        lock_props.
        setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
        (*Parameter TR1: tree val.
          Parameter TR2: tree val.*)
        Exists (T (*TR1*)l k v (*TR2*)r) p.
        cancel. unfold node_rep.
        Exists pa pb locka lockb; entailer!.
        unfold ltree; entailer!.
        rewrite later_sepcon. eapply derives_trans.
        2: apply sepcon_derives, derives_refl; try apply now_later.
        cancel. }
      Exists ((pa_t, pa), locka); entailer!.
      unfold tlp'; cancel. Exists pa_T; cancel.

    - rename H into XK.
      forward_if.
      * rename H into KX. forward. forward. 
        unfold ltree at 2; Intros. rename H into FC_pb.
        forward. deadvars.

        (*aquire(l)*)
        forward_call (lockb, lsh1, t_lock_pred pb lockb).
        rewrite t_lock_pred_def at 2. Intros pb_T pb_t.

        forward. (*p=tgt->t*)

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [field_at lsh2 t_struct_tree_t [StructField _lock] lockb pb;
                  node_rep pb_T pb_t; malloc_token Ews t_struct_tree_t pb;
                  malloc_token Ews tlock lockb; lock_inv lsh2 lockb (t_lock_pred pb lockb);
                  nodebox_rep sh lock b;
                  field_at Ews t_struct_tree_t [StructField _t] pb_t pb]);
            subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 4; simpl. cancel.
          (*Parameter TR4: tree val.
            Parameter TR5: tree val.*)
          Exists (T (*TR4*)l k v (*TR5*)r) p.
          cancel. unfold node_rep. 
          Exists pa pb locka lockb. entailer!.
          unfold ltree; entailer.
          rewrite later_sepcon. eapply derives_trans.
          2: apply sepcon_derives, derives_refl; try apply now_later.
          cancel. }
        Exists ((pb_t, pb), lockb). entailer!.
        unfold tlp'. cancel. Exists pb_T; cancel.
      * rename H into KX. 
        forward.

        (*release*)
        forward_call(lock0, lsh2, t_lock_pred_base tgt lock0, t_lock_pred tgt lock0).
        { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
          lock_props.
          setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
          (*Parameter TR6: tree val.
            Parameter TR7: tree val.*)
          Exists (T (*TR6*)l k v (*TR7*)r) p.
          cancel. unfold node_rep.
          Exists pa pb locka lockb. entailer!. }
        forward. Exists v; entailer!.
  + subst. unfold tlp'; simpl; Intros. Intros TR.

    (*release*)
    forward_call(lock0, lsh2, t_lock_pred_base tgt0 lock0, t_lock_pred tgt0 lock0).
    { assert (Frame = [nodebox_rep sh lock b]); subst Frame; [ reflexivity | clear H].
      lock_props.
      setoid_rewrite t_lock_pred_def at 2; simpl. cancel.
      Exists (@E val) nullval; simpl. entailer!. simpl; entailer!. }
    forward. Exists (vint 0); entailer!.
Qed.
*)
Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.



