Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks. 
Require Import VST.progs.conclib.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.

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
 | E_ghost :  ghost_tree
 | T_ghost: ghost_tree ->gname ->val -> key -> V -> val ->val -> val -> key -> ghost_tree -> gname ->val -> ghost_tree .
 
 Inductive operation: Type :=
 | ADD_op : bool -> key -> V -> operation (* bool indicate operation will be performed in left child *)
 | DELETE_op : bool-> key -> operation. (* bool indicate operation will be performed in left child *)
  
Inductive ghost_op_tree : Type :=
 | E_op : ghost_op_tree
 | T_op: ghost_op_tree-> gname -> val -> key -> V -> val -> option operation -> val -> ghost_op_tree -> gname -> val -> ghost_op_tree.

 Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 lp r g2 rp x v vp aop rop t :
       (k = x) -> In_ghost k (T_ghost l g1 lp x v vp aop rop t r g2 rp )
  | InLeft_ghost l g1 lp r g2 rp x v' vp aop rop t :
      In_ghost k l -> In_ghost k (T_ghost l g1 lp x v' vp aop rop t r g2 rp)
  | InRight_ghost l g1 lp r g2 rp x v' vp aop rop t :
      In_ghost k r -> In_ghost k (T_ghost l g1 lp x v' vp aop rop t  r g2 rp).
      

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k < x . 
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k > x . 

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
    | Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
    | Sorted_Ghost_Tree x v vp aop rop t l g1 lp r g2 rp : sorted_ghost_tree l -> sorted_ghost_tree r -> gt_ghost l x -> lt_ghost r x -> sorted_ghost_tree (T_ghost l g1 lp x v vp aop rop t r g2 rp ).
        
 
 Fixpoint insert_ghost (x: key) (v: V) (vp:val) (aop rop:val) (t: key) (s: ghost_tree) (g1:gname) (lp:val) (g2:gname) (rp:val): ghost_tree :=
 match s with
 | E_ghost => T_ghost E_ghost g1 lp x v vp aop rop t E_ghost g2 rp
 | T_ghost a ga la y v' vp' aop' rop' t' b gb rb => if  x <? y then T_ghost (insert_ghost x v vp aop rop t a g1 lp g2 rp) ga la y v' vp' aop' rop' t' b gb rb
                        else if (y <? x) then T_ghost a ga la y v' vp' aop' rop' t' (insert_ghost x v vp aop rop t b g1 lp g2 rp) gb rb else T_ghost a ga la x v vp' aop' rop' t' b gb rb
                        
 end.

 Lemma pushdown_left_In: forall (t1 t2: tree) (x: key),
     In x (pushdown_left t1 t2) -> In x t1 \/ In x t2.
 Proof.
   intros. revert t2 H. induction t2; intros; simpl in *; auto. inv H.
   - right. now apply InRoot.
   - apply IHt2_1 in H1. destruct H1; [left | right]; auto. now apply InLeft.
   - right. now apply InRight.
 Qed.

 Lemma delete_In: forall (x: key) (t: tree) (y: key), In y (delete x t) -> In y t.
 Proof.
   intros. revert t H. induction t; intros; simpl in *; auto. destruct (x <? k).
   - inv H; try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
     apply IHt1 in H1. now apply InLeft.
   - destruct (k <? x).
     + inv H; try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
       apply IHt2 in H1. now apply InRight.
     + apply pushdown_left_In in H. destruct H; [apply InLeft | apply InRight]; easy.
 Qed.

 Lemma pushdown_left_sorted: forall (t1 t2: tree),
     sorted_tree t1 -> sorted_tree t2 -> (forall x y, In x t1 -> In y t2 -> x < y) ->
     sorted_tree (pushdown_left t1 t2).
 Proof.
   intros. revert t2 H0 H1. induction t2; intros; simpl in H0 |-* ; auto.
   inv H0. constructor; auto.
   - apply IHt2_1; auto. intros. apply H1; auto. now apply InLeft.
   - intros z ?. apply pushdown_left_In in H0. destruct H0.
     + apply Z.lt_gt, H1; auto. now apply InRoot.
     + now specialize (H8 _ H0).
 Qed.

 Lemma delete_sorted: forall (x: key) (t: tree),
     sorted_tree t -> sorted_tree (delete x t).
 Proof.
   intros. revert t H. induction t; intros; simpl; auto. inv H.
   destruct (x <? k) eqn: ?.
   - apply Z.ltb_lt in Heqb. constructor; auto. intros y ?.
     apply delete_In in H. now apply H6.
   - apply Z.ltb_ge in Heqb. destruct (k <? x) eqn: ?.
     + apply Z.ltb_lt in Heqb0. constructor; auto. intros y ?.
       apply delete_In in H. now apply H7.
     + apply pushdown_left_sorted; auto. intros y z ? ?.
       apply H6 in H. apply H7 in H0. lia.
 Qed.

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

Lemma min_min_number: forall a b, min_number a (min_number a b) = min_number a b.
Proof.
  intros. destruct a, b; simpl; try rewrite Z.min_id; auto. f_equal.
  destruct (Z.min_dec n n0); rewrite e; try rewrite Z.min_id; easy.
Qed.

Lemma max_max_number: forall a b, max_number a (max_number a b) = max_number a b.
Proof.
  intros. destruct a, b; simpl; try rewrite Z.max_id; auto. f_equal.
  destruct (Z.max_dec n n0); rewrite e; try rewrite Z.max_id; easy.
Qed.
 
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

 Lemma merge_self: forall a, merge_range a a = a.
 Proof.
   intros. destruct a. unfold merge_range.
   destruct n, n0; simpl; try rewrite Z.min_id; try rewrite Z.max_id; easy.
 Qed.

 Lemma merge_again: forall a b c, merge_range a b = c -> merge_range a c = c.
 Proof.
   intros. destruct a, b, c. unfold merge_range in *. inv H.
   rewrite min_min_number. rewrite max_max_number. easy.
 Qed.

 Lemma leq_min_number: forall a b, less_than_equal (min_number a b) a = true.
 Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

 Lemma leq_max_number: forall a b, less_than_equal a (max_number a b) = true.
 Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

 Lemma merge_range_incl: forall a b c,
     merge_range a b = c -> range_inclusion a c = true.
 Proof.
   intros. destruct a, b, c. unfold merge_range in H. inv H.
   simpl. rewrite andb_true_iff. split; [apply leq_min_number | apply leq_max_number].
 Qed.
 
  Lemma leq_min_number1: forall a b, less_than_equal (min_number a b) b = true.
 Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

 Lemma leq_max_number1: forall a b, less_than_equal b (max_number a b) = true.
 Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

Lemma leq_entail_min_number: forall a b, less_than_equal a b = true -> a = min_number a b.
Proof.
intros. destruct a, b; simpl; auto;simpl in H. apply Z.leb_le in H. rewrite  Z.min_l. auto. auto. discriminate. discriminate. discriminate. 
Qed.

Lemma leq_entail_max_number: forall a b, less_than_equal b a = true -> a = max_number a b.
Proof.
intros. destruct a, b; simpl; auto;simpl in H. apply Z.leb_le in H. rewrite  Z.max_l. auto. auto. discriminate. discriminate. discriminate. 
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

Lemma less_than_less_than_equal_transitivity: forall a b c,
    less_than a b = true -> less_than_equal b c = true -> less_than a c = true .
Proof.
  intros. unfold less_than_equal in *. unfold less_than in *.
  destruct a, c, b; try easy. apply Z.ltb_lt in H.  rewrite Z.ltb_lt.
  apply Zle_bool_imp_le in H0. lia.
Qed.


Lemma less_than_irrefl: forall a, less_than a a = false.
Proof. intros. destruct a; simpl; auto. apply Z.ltb_irrefl. Qed.

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

 Lemma less_than_to_less_than_equal: forall a b, less_than a b = true -> less_than_equal a b = true .
 Proof.
 intros.
 destruct a.
  - destruct b;simpl. simpl in H. apply Z.ltb_lt in H. apply Zaux.Zle_bool_true. omega. simpl in H. discriminate. auto.
  - destruct b; auto. 
  - destruct b;auto.
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
 
 Lemma range_inclusion_transitivity : forall a b c, range_inclusion a b = true -> range_inclusion b c = true -> range_inclusion a c = true.
 Proof.
 intros.
 unfold range_inclusion in *.
 destruct a as [a1 a2];destruct b as [b1 b2];destruct c as [c1 c2];simpl in *.
 rewrite andb_true_iff.  apply andb_prop in H;destruct H.   apply andb_prop in H0;destruct H0.
 split.  apply less_than_equal_transitivity with (b:= b1);auto. apply less_than_equal_transitivity with (b:= b2);auto.
 Qed.
 
 (* Program Instance  set_PCM A : Ghost := { valid := fun _ : Ensemble A => True;
  Join_G a b c :=  c = Union _ a b  }.
Next Obligation.
Proof.
  intro. exists (fun _ => Empty_set _ ); auto.
  intro;simpl. hnf. rewrite Union_Empty; auto. 
Defined.

Next Obligation.
Proof.
  constructor.
    + intros ???? H1 H2; subst;inv H1;inv H2;auto.
    + intros ????? Hd1 Hd2; subst.
      inv Hd1; inv Hd2.
      exists (Union _ b c); repeat (split; auto). hnf. apply Union_assoc.
    + intros ??? H1; subst;inv H1;hnf. apply Union_comm.
    + intros ???? H1 H2; subst; inv H1; inv H2.
      apply Extensionality_Ensembles; constructor; intros ? X.
      { left; auto. }
      rewrite H; left; auto.
Defined.

Next Obligation.
constructor.
Defined. *)


Program Instance set_gen_PCM {A} : Ghost := { valid := fun _ : Ensemble A => True;
  Join_G a b c := Disjoint a b /\ c = Union a b(*; core2 a := empty*) }.
Next Obligation. 
Proof.
  intro;exists (fun _ => Empty_set); auto.
  intro; split.
  - constructor; intros ? X.
    rewrite Intersection_Empty in X; contradiction.
  - rewrite Union_Empty; auto.
Defined.
Next Obligation.
  intro;constructor.
    + intros ???? [] []; subst; auto.
    + intros ????? [Hd1] [Hd2]; subst.
      inv Hd1; inv Hd2.
      exists (Union b c); repeat (split; auto).
      * intros ? X; inv X.
        contradiction (H0 x).
        constructor; auto.
        right; auto.
      * intros ? X; inv X.
        inv H2.
        -- contradiction (H x); constructor; auto.
        -- contradiction (H0 x); constructor; auto.
           left; auto.
      * apply Union_assoc.
    + intros ??? []; subst.
      split.
      * inv H; constructor.
        intros x X; inv X; contradiction (H0 x); constructor; auto.
      * apply Union_comm.
    + intros ???? [] []; subst.
      apply Extensionality_Ensembles; constructor; intros ? X.
      { left; auto. }
      rewrite H2; left; auto.
Defined.

Next Obligation.
constructor.
Defined.

Check set_gen_PCM .

Global Obligation Tactic := repeat constructor || let x := fresh "x" in intros ?? x; repeat destruct x as [x ?]; simpl; auto.

 Instance bst_ghost : Ghost := ref_PCM range_ghost.
 
 Instance range_info : Ghost := prod_PCM range_ghost (discrete_PCM ( val)).

Definition ghost_ref g r1 := ghost_reference(P := map_PCM (A:=gname) (P:= range_info ) ) r1 g.

Definition in_tree (g1:gname) (range :number*number) (v:val)g := EX sh: share, ghost_part(P := map_PCM (A:=gname)) sh (ghosts.singleton g1 (range,v) ) g.

Definition ghost_ref_op g o := ghost_reference(P := (set_gen_PCM (A:=@operation val))) o g.


Definition in_tree_op g (o:@operation val):= EX sh: share, ghost_part(P := set_gen_PCM (A:=@operation val)) sh (Ensembles.Singleton o) g.


Fixpoint find_pure_tree (t : @ghost_tree val) : @tree val :=
  match t with 
  | E_ghost => E
  | (T_ghost a ga lp x v vp aop rop t b gb rp) => T (find_pure_tree a) x v (find_pure_tree b)
end.

 (* Inductive operation: Type :=
 | ADD : bool -> key -> V -> operation. *)
 
Fixpoint find_pure_tree2 (t : @ghost_op_tree val) : @tree val :=
  match t with 
  | E_op => E
  | (T_op a ga lp x v vp o aop b gb rp) => match o with 
                                         | Some op => (match op with | ADD_op b' x' v' => if b' then T (T (find_pure_tree2 a) x' v' E) x v (find_pure_tree2 b)
                                                                                          else T (find_pure_tree2 a) x v (T E x' v' (find_pure_tree2 b)) 
                                                                     | DELETE_op b' x' => if  x <? x' then T (find_pure_tree2 a) x v (delete x' (find_pure_tree2 b))
                                                                                    else if x' <? x then T (delete x' (find_pure_tree2 a)) x v (find_pure_tree2 b)
                                                                                    else pushdown_left (find_pure_tree2 a) (find_pure_tree2 b)end)
                                         | None =>  T (find_pure_tree2 a) x v (find_pure_tree2 b) end
end.




Fixpoint find_ghost_set (t : @ghost_tree val) (g:gname) (range:number*number) nb: gname -> option (@G range_info) :=
  match t with 
  | E_ghost => (ghosts.singleton g (range,nb))
  | (T_ghost a ga lp x v vp aop rop t b gb rp) =>  (map_upd (map_add (find_ghost_set a ga (fst range, Finite_Integer x) lp) (find_ghost_set b gb ( Finite_Integer x, snd range) rp)) g (range,nb))
end.

Fixpoint find_ghost_set2 (t : @ghost_op_tree val) (g:gname) (range:number*number) nb: gname -> option (@G range_info) :=
  match t with 
  | E_op => (ghosts.singleton g (range,nb))
  | (T_op a ga lp x v vp o aop b gb rp) =>  (map_upd (map_add (find_ghost_set2 a ga (fst range, Finite_Integer x) lp) (find_ghost_set2 b gb ( Finite_Integer x, snd range) rp)) g (range,nb))
end.

Fixpoint find_op_set (t : @ghost_op_tree val): Ensemble operation :=
  match t with 
  | E_op => Ensembles.Empty_set
  | (T_op a ga lp x v vp o aop b gb rp) => match o with 
                                           | Some o' => Add  (Union (find_op_set a) (find_op_set b )) o'
                                           | None => Union (find_op_set a) (find_op_set b ) end                
end.

Lemma node_exist_in_tree: forall g  (range: number * number) v s (g_in:gname),  in_tree g_in range v g * ghost_ref g s |-- !! (exists r : number *number, s g_in = Some (r, v) /\ range_inclusion range r = true).
Proof.
 intros. unfold ghost_ref, in_tree; Intros sh. rewrite ref_sub. apply prop_left; intro; apply prop_right. destruct (eq_dec sh Tsh); subst.
  - exists range; split; [|apply range_iteself].
    unfold ghosts.singleton; apply eq_dec_refl.
  - destruct H as [r' J]. specialize (J g_in).
    unfold ghosts.singleton in J; rewrite eq_dec_refl in J.
    inv J.
    + exists range; split; auto; apply range_iteself.
    + destruct a3; inv H2; simpl in *.
      inv H; inv H3.
      eexists; split; [auto|].
      eapply merge_range_incl; eauto.
 Qed.
 
 Lemma op_exist_in_tree: forall g s o,  in_tree_op g o  * ghost_ref_op g s |-- !! (Ensembles.In s o).
Proof. 
intros. unfold ghost_ref_op, in_tree_op; Intros sh. rewrite ref_sub.  destruct  (eq_dec sh Tsh).
- Intros. apply log_normalize.prop_derives. intros. subst s.  apply In_singleton. 
- apply log_normalize.prop_derives. intros [m H].  unfold sepalg.join in H. hnf in H. destruct H. rewrite H0. apply Union_introl. apply In_singleton. 
Qed.
  
Lemma in_tree_add : forall g s (range:number *number) v (range':number *number) v' (g1:gname) (g':gname),  s g' = None -> in_tree g1 range v g  * ghost_ref g s |-- (|==> ghost_ref g (map_upd s g' (range',v') ) * in_tree g1 range v g * in_tree g' range' v' g)%I.
Proof.
  intros.
  unfold in_tree at 1; Intros sh; iIntros "H".
  iPoseProof (ref_sub with "H") as "%".
  destruct (eq_dec g1 g').
  { subst; if_tac in H0; subst.
    + unfold ghosts.singleton in H; rewrite eq_dec_refl in H; discriminate.
    + destruct H0 as [? J]; specialize (J g').
      unfold ghosts.singleton in J; rewrite eq_dec_refl in J; inv J; congruence. }
  rewrite ghost_part_ref_join.
  iMod (ref_add(P :=  @ map_PCM gname range_info ) _ _ _ _ (ghosts.singleton g' (range', v')) (map_upd (ghosts.singleton g1 (range, v)) g' (range', v'))
    (map_upd s g' (range', v')) with "H") as "H".
  { apply (map_upd_single (P := range_info )).
    unfold ghosts.singleton; if_tac; auto; subst; contradiction. }
  { apply (map_upd_single (P := range_info )); auto. } 
  setoid_rewrite <- ghost_part_ref_join.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsh.
  iIntros "!>".
  iDestruct "H" as "[in $]".
  iPoseProof (own_valid with "in") as "[% %]".
  pose proof (split_join _ _ _ Hsh).
  rewrite <- (ghost_part_join(P := @ map_PCM gname range_info) sh1 sh2 sh (ghosts.singleton g1 (range, v)) (ghosts.singleton g' (range', v'))); auto.
  iDestruct "in" as "[in1 in2]"; iSplitL "in1"; unfold in_tree; [iExists sh1 | iExists sh2]; auto.
  { apply  (map_upd_single (P := range_info )).
    unfold ghosts.singleton; if_tac; auto; subst; contradiction. }
  { intro; contradiction H1; eapply Share.split_nontrivial; eauto. }
  { intro; contradiction H1; eapply Share.split_nontrivial; eauto. }
Qed.


Definition ghost_info : Type := (key * val * gname * gname)%type.

Instance node_ghost : Ghost := prod_PCM range_ghost (option_PCM (P:= discrete_PCM ghost_info) ).

Notation node_info := (@G node_ghost). 

Instance range_order : PCM_order (fun a b => range_inclusion a.1 b.1 = true /\ match snd a with None => True | Some _ => snd a = snd b end ).
Proof.
 constructor; simpl; intros.
  - constructor.
    + intro;split. apply range_iteself. destruct x.2;auto.
    + intro. intros. destruct H, H0. split. apply range_inclusion_transitivity with (b := y.1);auto. 
       destruct x.2; destruct y.2;destruct z.2;auto.
       inv H1;auto. discriminate. discriminate.
  - exists ( (merge_range a.1 b.1, if eq_dec a.2 None then b.2 else a.2)). destruct H, H0. 
    destruct a as [[al ar] ao]; destruct b as [[bl br] bo]; destruct c as [[cl cr] co]. unfold sepalg.join; simpl in *;split.
     + unfold sepalg_generators.Join_prod;simpl;split.
        * unfold sepalg.join;auto.
        * unfold sepalg.join. hnf. if_tac. subst ao.  apply psepalg.lower_None1. destruct ao;destruct bo;destruct co;auto;inv H1; inv H2;
        try ( (now  apply psepalg.lower_Some) || (now apply psepalg.lower_None1 ) || (now apply psepalg.lower_None2 ) || discriminate || contradiction).
    +  apply andb_prop in H;destruct H. apply andb_prop in H0;destruct H0. split.
        * rewrite andb_true_iff;split. destruct cl;destruct al; destruct bl; simpl in *; try( repeat auto).  apply Zaux.Zle_bool_true. apply Z.leb_le in H. apply Z.leb_le in H0. apply Z.min_glb;auto.
          destruct cr;destruct ar; destruct br; simpl in *; try( repeat auto).  apply Zaux.Zle_bool_true. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.max_lub;auto.
        * if_tac. auto. auto.
 - destruct H. unfold sepalg.join in H. repeat split. apply merge_range_incl with (b := b.1);auto. inv H0;auto. destruct a.2;auto. inv H4;auto.
    rewrite merge_comm in H. apply merge_range_incl with (b := a.1);auto. inv H0;auto. destruct b.2;auto. inv H4;auto.  
- destruct a as [[al ar] ao]; destruct b as [[bl br] bo];simpl in *. unfold sepalg.join. unfold sepalg_generators.Join_prod. destruct H. unfold sepalg.join. simpl. split. apply andb_prop in H;destruct H.
   f_equal. apply leq_entail_min_number;auto. apply leq_entail_max_number;auto. destruct ao;destruct bo;inv H0;try ( (now  apply psepalg.lower_Some) || (now apply psepalg.lower_None1 ) || (now apply psepalg.lower_None2 )).

Defined.

Definition finite (m : gname -> option (number * number * val)) := exists n, forall g x, m g = Some x -> (g <= n)%nat.

Lemma finite_new : forall m, finite m -> exists g, m g = None.
Proof.
  intros ? [n ?].
  exists (S n).
  destruct (m (S n)) eqn: Hn; auto.
  apply H in Hn; lia.
Qed.

Lemma finite_upd : forall m g x, finite m -> finite (map_upd m g x).
Proof.
  intros ??? [n ?].
  exists (max n g); intros.
  rewrite Nat.max_le_iff.
  unfold map_upd in H0; if_tac in H0; subst; eauto.
Qed.

Lemma finite_add : forall m1 m2, finite m1 -> finite m2 -> finite (map_add m1 m2).
Proof.
  intros ?? [n1 H1] [n2 H2].
  exists (max n1 n2); intros.
  unfold map_add in H.
  rewrite Nat.max_le_iff.
  destruct (m1 g) eqn: Hm1; eauto.
Qed.

Lemma finite_empty : finite (empty_map ).
Proof.
  exists O.
  unfold empty_map; discriminate.
Qed.

Lemma finite_singleton : forall g x, finite (ghosts.singleton g x).
Proof.
  intros; exists g.
  unfold ghosts.singleton; intros.
  if_tac in H; inv H; auto.
Qed.

Lemma find_ghost_set_finite : forall t g r0 p, finite (find_ghost_set t g r0 p).
Proof.
  induction t; intros; simpl.
  - apply finite_singleton.
  - apply finite_upd, finite_add; auto.
Qed.

Lemma ghost_node_alloc : forall g s (g1:gname) (range : number*number) (range':number*number) v v'  (o: option ghost_info) ,
 finite s -> in_tree g1 range v g * ghost_ref g s |-- (|==> EX g', !!(s g' = None) && ghost_master1(ORD := range_order) (range', o) g' * ghost_ref g (map_upd s g' (range',v')) * in_tree g1 range v g * in_tree g' range' v' g )%I.
Proof.
  intros.
  iIntros "r".
  iMod (own_alloc_strong (RA := snap_PCM(ORD := range_order)) (fun x => s x = None) (Tsh,(range',o)) with "[$]") as (g') "[% ?]".
  { intros l.
    destruct H as [n H].
    exists (S (max (fold_right max O l) n)).
    split.
    - intros X%own.list_max.
      pose proof (Max.le_max_l (fold_right max O l) n); omega.
    - destruct (s _) eqn: Hs; auto.
      apply H in Hs.
      pose proof (Max.le_max_r (fold_right max O l) n). simpl in *. omega. }
  { simpl; auto. }
  iExists g'.
  rewrite -> prop_true_andp by auto.
  iMod (in_tree_add with "r") as "(($ & $) & $)"; auto.
Qed.

Lemma gsh1_not_Tsh : gsh1 <> Tsh.
Proof.
  pose proof gsh1_gsh2_join. intro. rewrite H0 in H. apply sepalg.join_comm in H.
  apply sepalg.unit_identity in H. now apply (readable_nonidentity readable_gsh2).
Qed.

Lemma gsh2_not_Tsh : gsh2 <> Tsh.
Proof.
  pose proof gsh1_gsh2_join. intro. rewrite H0 in H. apply sepalg.unit_identity in H.
  now apply (readable_nonidentity readable_gsh1).
Qed.
Hint Resolve gsh1_not_Tsh gsh2_not_Tsh : share.

Lemma sepalg_range_inclusion: forall  (r1 r2 r3 : node_info), sepalg.join r1 r2 r3 -> range_inclusion r1.1 r3.1 = true /\ range_inclusion r2.1 r3.1 = true.
Proof.
intros. destruct r1 as [range1 r1]. destruct r2 as [range2 r2]. destruct r3 as [range3 r3].
  hnf in H. simpl in *. destruct H. inv H; auto. destruct range1, range2. unfold range_inclusion, merge_range.
  split;rewrite andb_true_iff. split; [apply leq_min_number | apply leq_max_number]. split; [apply leq_min_number1 | apply leq_max_number1].
Qed.

Lemma merge_infinity : forall r, merge_range r (Neg_Infinity, Pos_Infinity) = (Neg_Infinity, Pos_Infinity).
Proof.
  destruct r; unfold merge_range, min_number, max_number.
  destruct n, n0; auto.
Qed.

Lemma my_half_range_inf : forall g r1 r2 o,
    my_half g gsh1 (r1, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None) =
    my_half g gsh1 (r2, o) * my_half g gsh2 (Neg_Infinity, Pos_Infinity, None).
Proof.
  intros.
  unfold my_half; erewrite 2 ghost_part_join with
                      (a := (Neg_Infinity, Pos_Infinity, o));
  eauto with share; repeat constructor; simpl; hnf; rewrite merge_infinity; auto.
Qed.

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
-  intros.  destruct r_root. simpl.  destruct (x <? k) eqn:E1.
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

(* insert proof related lemmas *)


Lemma insert_preserved_in_ghost_tree: forall t tg x v vp g1 g2 lp rp aop rop ty, find_pure_tree tg = t -> find_pure_tree (insert_ghost x v vp aop rop ty tg g1 lp g2 rp) = (insert x v t).
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

Inductive IsEmptyGhostNode (range : number * number * option ghost_info ) :  (@ghost_tree val) -> (number * number) -> Prop :=
 | InEmptyGhostTree n1 n2 : (range = (n1,n2,@None ghost_info)) -> IsEmptyGhostNode range E_ghost (n1,n2)
 | InLeftGhostSubTree l g1 lp x v vp aop rop t r g2 rp  n1 n2 :  IsEmptyGhostNode range l (n1, Finite_Integer x) -> IsEmptyGhostNode range (T_ghost l g1 lp x v vp aop rop t r g2 rp) (n1,n2) 
 | InRightGhostSubTree l g1 lp x v vp aop rop t r g2 rp n1 n2 :  IsEmptyGhostNode range r (Finite_Integer x, n2) -> IsEmptyGhostNode range (T_ghost l g1 lp x v vp aop rop t r g2 rp) (n1,n2).

 (* Lemma ghost_range_inside_ghost_range : forall r  r_root tg, IsEmptyGhostNode r tg r_root -> (forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> sorted_ghost_tree tg -> range_inclusion r.1 r_root = true.
 Proof.
 intros.
 revert dependent r_root.
 induction tg.
  - intros. inversion H. subst r. apply range_iteself. 
  - intros. inversion H;subst.
   * assert ( range_inclusion r.1 (n1, Finite_Integer k) = true ) . 
       { apply IHtg1 in H12. apply H12. inversion H1;subst. apply H6. inversion H1;subst. unfold gt_ghost in H13.  intros. 
          assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft_ghost. apply H2. } unfold check_key_exist' in *. apply andb_prop in H3. destruct H3. 
          apply H14 in H2. rewrite H3. assert (less_than (Finite_Integer k0) (Finite_Integer k) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H5. auto. } 
    assert ( check_key_exist' k (n1, n2) = true ) . { apply H0.  apply InRoot_ghost. auto. } unfold check_key_exist' in H3. apply andb_prop in H3. destruct H3.
    unfold range_inclusion in *. destruct r.1. apply less_than_to_less_than_equal in H4. apply andb_prop in H2. destruct H2. rewrite H2. 
    simpl. apply less_than_equal_transitivity with ( b:= Finite_Integer k). apply H5. apply H4. 
   * assert ( range_inclusion r.1 (Finite_Integer k, n2) = true ) . 
         { apply IHtg2 in H12. apply H12. inversion H1;subst. apply H13.   inversion H1;subst. unfold lt_ghost in H14.  intros.
           assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H2. } unfold check_key_exist' in *. apply andb_prop in H3. destruct H3. apply H15 in H2. rewrite H4.
           assert (less_than (Finite_Integer k) (Finite_Integer k0) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H5. auto. }  
   assert ( check_key_exist' k (n1, n2) = true ) . { apply H0.  apply InRoot_ghost. auto. } unfold check_key_exist' in H3. apply andb_prop in H3. destruct H3.
   unfold range_inclusion in *. destruct r.1. apply less_than_to_less_than_equal in H3. apply andb_prop in H2. destruct H2. rewrite H5. 
  rewrite andb_comm.   simpl. apply less_than_equal_transitivity with ( b:= Finite_Integer k). apply H3. apply H2.
 Qed.
 
Lemma update_ghost_tree_with_insert: forall x v vp tg g1 g2 g_root r_root (lp rp b op:val)  (n n0:number) (o1: option ghost_info) , IsEmptyGhostNode (n,n0,o1) tg r_root  -> (find_ghost_set tg g_root r_root b) g1 = None -> (map_upd (find_ghost_set tg g_root r_root b) g1 (n, Finite_Integer x, lp)) g2 = None -> ~ In_ghost x tg ->   sorted_ghost_tree tg  ->  (forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> check_key_exist' x (n,n0) = true ->  (find_ghost_set (insert_ghost x v vp op tg g1 lp g2 rp) g_root r_root b) =   
(map_upd (map_upd (find_ghost_set tg g_root r_root b) g1 (n, Finite_Integer x, lp)) g2 (Finite_Integer x, n0, rp)).
Proof.
intros.
revert dependent g_root.
revert dependent r_root.
revert dependent b.
induction tg.
 + intros. simpl in H0.  unfold ghosts.singleton in H0. inv H.  destruct (eq_dec g1 g_root).  discriminate. inv H6.  simpl. rewrite <- !map_add_single. rewrite map_add_comm. rewrite <- map_add_assoc. rewrite (map_add_comm (ghosts.singleton g2 (Finite_Integer x, n2, rp)) _ ). reflexivity.
    { simpl in H1.  apply disjoint_compatible. hnf. intros. unfold map_upd in H1. destruct (eq_dec g2 g1). discriminate. unfold ghosts.singleton in *. destruct (eq_dec k g2); destruct (eq_dec k g1). omega. auto. discriminate. auto. }
    { unfold map_upd, ghosts.singleton in *. apply disjoint_compatible. hnf. intros. unfold map_add. destruct (eq_dec g1 g_root);destruct (eq_dec g2 g1);destruct (eq_dec k g1);destruct (eq_dec k g2);simpl;auto. discriminate. omega. 
     destruct (eq_dec k g_root). omega. discriminate. destruct (eq_dec k g_root).  simpl in H1. unfold ghosts.singleton in *.  destruct (eq_dec g2 g_root ). discriminate. omega. discriminate. discriminate. omega. destruct (eq_dec k g_root). omega. discriminate.  simpl in H1. unfold ghosts.singleton in H1. destruct (eq_dec k g_root); destruct (eq_dec g2 g_root). discriminate. omega. discriminate. discriminate. }
+ simpl. destruct (x <? k) eqn:E1. 
    -  intros. simpl. rewrite IHtg1.  remember (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0) as m1. remember (find_ghost_set tg2 g0 (Finite_Integer k, r_root.2) v3) as m2. rewrite (map_upd_comm _ g_root _ g1 _). rewrite (map_upd_comm _ g_root _ g2 _).  
       rewrite (map_add_upd m1 m2 g1 (n, Finite_Integer x, lp)). rewrite (map_add_upd _ _ g2 (Finite_Integer x, n0, rp)). reflexivity.    unfold map_upd in H1. destruct (eq_dec g2 g1). discriminate. destruct (eq_dec g2 g_root). discriminate. auto. unfold map_upd in H0. destruct (eq_dec g1 g_root). discriminate. auto.
     intros a. contradiction H2. apply InLeft_ghost. auto.  inv H3. auto. 
      {  inv H. simpl. auto. apply ghost_range_inside_ghost_range in H16. unfold range_inclusion in H16. apply andb_prop in H16. 
         assert ( less_than (Finite_Integer k) (Finite_Integer x) = true ). { unfold check_key_exist' in H5. apply andb_prop in H5. destruct H5, H16. apply less_than_equal_less_than_transitivity with (b := n). apply H6. apply H. } simpl in H. apply Z.ltb_lt in E1. apply Z.ltb_lt in H. omega.
         intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H4. apply InRight_ghost. auto. } inv H3. unfold lt_ghost in H19. apply H20 in H. unfold check_key_exist' in *. apply andb_prop in H6. destruct H6. apply andb_true_intro. split. simpl. apply Zaux.Zlt_bool_true. auto. auto. inv H3;auto. }
      { intros. destruct r_root. assert (check_key_exist' k0 (n1, n2) = true). { apply H4. apply InLeft_ghost. auto. } inv H3. apply H19 in H6. unfold check_key_exist' in *.  apply andb_prop in H7.  destruct H7.  apply andb_true_intro. split. auto. simpl. apply Zaux.Zlt_bool_true. omega. }
       unfold map_upd in H0. destruct (eq_dec g1 g_root). discriminate. unfold map_add in H0. destruct (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0 g1). discriminate. auto. unfold map_upd, map_add in *. destruct (eq_dec g2 g1). discriminate.
      destruct (eq_dec g2 g_root). discriminate. destruct (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0 g2). discriminate. auto.
     - destruct (k <? x) eqn:E2.
        *  intros. simpl. rewrite IHtg2.  remember (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0) as m1. remember (find_ghost_set tg2 g0 (Finite_Integer k, r_root.2) v3) as m2. rewrite (map_upd_comm _ g_root _ g1 _). rewrite (map_upd_comm _ g_root _ g2 _). rewrite <- !map_add_single.  rewrite <- (map_add_assoc (ghosts.singleton g2 (Finite_Integer x, n0, rp)) (ghosts.singleton g1 (n, Finite_Integer x, lp)) (map_add m1 m2) ). 
           rewrite <- ( map_add_assoc  (map_add (ghosts.singleton g2 (Finite_Integer x, n0, rp)) (ghosts.singleton g1 (n, Finite_Integer x, lp))) m1 m2). rewrite <- (map_add_assoc _ _ m2). rewrite <- ( map_add_assoc m1 _ m2). rewrite (map_add_comm m1 _). reflexivity.  
          { apply disjoint_compatible. hnf. intros. unfold map_add, map_upd, ghosts.singleton in *. destruct (eq_dec g1 g_root);destruct (eq_dec g2 g1);destruct (eq_dec k0 g1);destruct (eq_dec k0 g2); destruct (eq_dec g2 g_root);try (simpl;auto;discriminate). rewrite e in e0. omega. rewrite e in H6. rewrite H6 in H0. discriminate. rewrite e in H6. rewrite H6 in H1. discriminate. }
           unfold map_upd in H0, H1. destruct (eq_dec g1 g_root); destruct (eq_dec g2 g1); destruct (eq_dec g2 g_root ).
           discriminate. auto. discriminate. auto. discriminate. auto. discriminate. auto. unfold map_upd in H0. destruct (eq_dec g1 g_root). discriminate. auto.
           intros a. contradiction H2. apply InRight_ghost. auto. inv H3. auto. 
         { inv H. simpl. apply ghost_range_inside_ghost_range in H16. unfold range_inclusion in H16. apply andb_prop in H16. 
            assert ( less_than (Finite_Integer x) (Finite_Integer k) = true ). { unfold check_key_exist' in H5. apply andb_prop in H5. destruct H5, H16. apply less_than_less_than_equal_transitivity with (b := n0). apply H5. apply H7. } simpl in H. apply Z.ltb_lt in E2. apply Z.ltb_lt in H. omega.
           intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H4. apply InLeft_ghost. auto. } inv H3. unfold gt_ghost in H19. apply H19 in H. unfold check_key_exist' in *. apply andb_prop in H6. destruct H6. apply andb_true_intro. split. auto. apply Zaux.Zlt_bool_true. omega. inv H3;auto. auto. }
         { intros. destruct r_root. assert (check_key_exist' k0 (n1, n2) = true). { apply H4. apply InRight_ghost. auto. } inv H3. apply H20 in H6. unfold check_key_exist' in *.  apply andb_prop in H7.  destruct H7.  apply andb_true_intro. split.  simpl. apply Zaux.Zlt_bool_true. omega. apply H7. }
           unfold map_upd in H0. destruct (eq_dec g1 g_root). discriminate. unfold map_add in H0. destruct (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0 g1). discriminate. auto. unfold map_upd, map_add in *. destruct (eq_dec g2 g1). discriminate.
           destruct (eq_dec g2 g_root). discriminate. destruct (find_ghost_set tg1 g (r_root.1, Finite_Integer k) v0 g2). discriminate. auto.
        
        
        * intros. assert (x = k). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. omega. } apply (InRoot_ghost x tg1 g v0 tg2 g0 v3 k v1 v2 ) in H6. contradiction H2.
 
 Qed. 


Lemma update_ghost_tree_with_insert2: forall x v vp tg g1 g2 g_root r_root lp rp op b, ((In_ghost x tg) /\ (sorted_ghost_tree tg)) ->   (find_ghost_set (insert_ghost x v vp op tg g1 lp g2 rp ) g_root r_root b) =   
find_ghost_set tg g_root r_root b.
Proof.
intros. destruct H. revert r_root. revert dependent g_root. revert b. induction tg.
 + intros. inversion H.
 + intros. inversion H.
    -  simpl. destruct (x <? k) eqn:E2. { apply Z.ltb_lt in E2. omega. } { destruct (k <? x) eqn:E3. {apply Z.ltb_lt in E3. omega. } { simpl. assert (k = x). { omega. } rewrite H11.  reflexivity. } }
    - simpl. destruct (x <? k) eqn:E2.
      * simpl. rewrite IHtg1. reflexivity. apply H2. inversion H0. apply H15.
      * destruct (k <? x) eqn:E3. { inversion H0. unfold gt_ghost in H22. apply H22 in H2. apply Z.ltb_lt in E3. omega. } { simpl. assert (k = x). { apply Z.ltb_ge in E3. apply Z.ltb_ge in E2. omega.  } rewrite H11.  reflexivity. }
    - simpl. destruct (x <? k) eqn:E2.
      * inversion H0. unfold lt_ghost in H23. apply H23 in H2. apply Z.ltb_lt in E2. omega.
      * destruct (k <? x) eqn:E3. { simpl. rewrite IHtg2. reflexivity. apply H2. inversion H0. apply H21. } { simpl. assert (k = x). { apply Z.ltb_ge in E3. apply Z.ltb_ge in E2. omega.  } rewrite H11.  reflexivity. }
Qed.

 


Notation public_half := (public_half(P := node_ghost)).

Lemma key_not_exist_in_tree: forall  (tg : @ghost_tree val) r_root range x, IsEmptyGhostNode range tg r_root ->  ( forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> sorted_ghost_tree tg -> check_key_exist' x range.1 = true  -> ~ In_ghost x tg.
 
 Proof. 
 intros. revert dependent r_root. induction tg.
  - unfold not. intros. inversion H3.
  - unfold not. intros. inversion H1. subst. inv H.
    * assert (H19 := H18). apply ghost_range_inside_ghost_range in H18.
      { apply IHtg1 in H19. 
        { assert (x < k). 
          { unfold check_key_exist' in H2. unfold range_inclusion in H18. destruct range.1. apply andb_prop in H2. apply andb_prop in H18. destruct H2. destruct H18. apply less_than_less_than_equal_transitivity with (c := (Finite_Integer k)) in H2.
            simpl in H2. apply Z.ltb_lt in H2. apply H2. apply H5. } 
          { inv H3. { omega. } { auto. } { unfold lt_ghost in H16. apply H16 in H5. omega. } } } { apply H8. }
          { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft_ghost. apply H. } unfold check_key_exist' in *. apply andb_prop in H4. destruct H4. unfold gt_ghost in H15. apply H15 in H. 
            rewrite H4. assert (less_than (Finite_Integer k0) (Finite_Integer k) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H6. auto. } }
      { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft_ghost. apply H. } 
        unfold check_key_exist' in *. apply andb_prop in H4. destruct H4. unfold gt_ghost in H14. apply H15 in H. rewrite H4. assert (less_than (Finite_Integer k0) (Finite_Integer k) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } 
        rewrite H6. auto. } 
      { apply H8. }
    * assert (H19 := H18).
      apply ghost_range_inside_ghost_range in H18.
      { apply IHtg2 in H19. 
        { assert (x > k). 
          { unfold check_key_exist' in H2. unfold range_inclusion in H14. destruct range.1. apply andb_prop in H2. apply andb_prop in H18. destruct H2. destruct H18. apply less_than_equal_less_than_transitivity with (c := (Finite_Integer x)) in H4.
            simpl in H4. apply Z.ltb_lt in H4. omega. apply H. } 
        { inv H3. { omega. } { unfold gt_ghost in H15. apply H15 in H5. omega. } { auto. } } } { apply H14. }
         { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H. } unfold check_key_exist' in *. apply andb_prop in H4. destruct H4. unfold lt_ghost in H14. apply H16 in H. rewrite H5. assert (less_than (Finite_Integer k) (Finite_Integer k0) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } 
            rewrite H6. auto. } }
      { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H. } unfold check_key_exist' in *. apply andb_prop in H4. destruct H4. unfold lt_ghost in H15. apply H16 in H. 
        rewrite H5. assert (less_than (Finite_Integer k) (Finite_Integer k0) = true). { simpl. apply Zaux.Zlt_bool_true. omega. } rewrite H6. auto. } { apply H14. }
Qed.

 *)