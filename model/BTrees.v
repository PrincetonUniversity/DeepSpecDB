Require Import Extract.
Require Import Coq.Lists.List.
Require Import Recdef.
Require Import FunInd.
Require Import Coq.Numbers.BinNums.
Require Import Coq.omega.Omega.
Export ListNotations.
(* How to limit unneeded dependencies? *)

Definition key := Z.

Section BTREES.
Variable V : Type.
Variable b : nat.

(** Basic Definitions *)

Inductive tree : Type :=
  | node : key -> treelist -> tree
  | final : treelist -> tree
  | val : key -> V -> tree
with treelist : Type :=
  | nil : treelist
  | cons : tree -> treelist -> treelist.

Scheme tree_treelist_rec := Induction for tree Sort Type
with treelist_tree_rec := Induction for treelist Sort Type.

Definition cursor : Type := (list (treelist * treelist)).

Inductive splitpair : Type :=
| One : treelist -> splitpair
| Two : treelist -> key -> treelist -> splitpair.

(** Helper Functions *)

Fixpoint eq_pos (p1 : positive) (p2 : positive) :=
  match (p1,p2) with
  | (xI p1',xI p2') => eq_pos p1' p2'
  | (xO p1',xO p2') => eq_pos p1' p2'
  | (xH,xH) => true
  | (_,_) => false
  end.

(* Definition vs Fixpoint on these? *)
Definition eq_key (k1 : key) (k2 : key) :=
  match (k1,k2) with
  | (Z0,Z0) => true
  | (Zpos p1,Zpos p2) => eq_pos p1 p2
  | (Zneg p1,Zneg p2) => eq_pos p1 p2
  | (_,_) => false
  end.

(* is p1 less than p2? *)
(* curVal carries the info of which was greater in the bit where they differed *)
Fixpoint lt_pos (p1 : positive) (p2 : positive) (curVal : bool) :=
  match p1 with
  | xH => (match p2 with
           | xH => curVal
           | _ => true
           end)
  | xO p1' => (match p2 with
               | xH => false
               | xO p2' => lt_pos p1' p2' curVal
               | xI p2' => lt_pos p1' p2' true
               end)
  | xI p1' => (match p2 with
               | xH => false
               | xO p2' => lt_pos p1' p2' false
               | xI p2' => lt_pos p1' p2' curVal
               end)
  end.

Definition lt_key (k1 : key) (k2 : key) :=
  match k1 with
  | Zpos p1 => (
    match k2 with
    | Zpos p2 => lt_pos p1 p2 false
    | _ => false
    end)
  | Z0 => (
    match k2 with
    | Zpos p2 => true
    | _ => false
    end)
  | Zneg p1 => (
    match k2 with
    | Zneg p2 => lt_pos p2 p1 false
    | _ => false
    end)
  end.

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Fixpoint unzip {A : Type} {B : Type} (l : list (A * B)) : list A * list B :=
  match l with
  | (a,b)::tl => (match unzip tl with (la, lb) => (a::la, b::lb) end)
  | [] => ([], [])
  end.

Fixpoint treelist_depth (f : treelist) : nat :=
  match f with
  | nil => O
  | cons t f => max_nat (tree_depth t) (treelist_depth f)
  end
with tree_depth (t : tree) : nat :=
  match t with
  | node _ f => S (treelist_depth f)
  | final f => S (treelist_depth f)
  | val _ _ => S O
  end.

Fixpoint zip (f1 : treelist) (f2 : treelist) : treelist :=
  match f1 with
  | cons t f' => cons t (zip f' f2)
  | nil => f2
  end.

Fixpoint treelist_length (f : treelist) : nat :=
  match f with
  | nil => O
  | cons t f' => S (treelist_length f')
  end.

(* flip false causes floor of div *)
(* flip true causes ciel of div *)
Fixpoint div_two (n : nat) (flip : bool) : nat :=
  match n with
  | O => O
  | S n' => (match flip with
             | true => S (div_two n' false)
             | false => div_two n' true
             end)
  end.

(** Theorems about helpers *)

Theorem max_nat_comm : forall (x y : nat),
  max_nat x y = max_nat y x.
Proof.
  induction x; destruct y; try reflexivity.
  simpl. rewrite IHx. reflexivity.
Qed.

Theorem max_nat_largest : forall (x y : nat),
  max_nat x y = x <-> x >= y.
Proof.
  induction x; destruct y; split; intros; try omega; try reflexivity.
  - inversion H.
  - inversion H. rewrite H1. apply IHx in H1. omega.
  - simpl. assert (H': x >= y). { omega. }
    apply IHx in H'. rewrite H'. reflexivity.
Qed.

Theorem max_nat_one : forall (x y z : nat),
  z = max_nat x y -> z = x \/ z = y.
Proof.
  induction x; destruct y; intros.
  - inversion H. left. reflexivity.
  - rewrite max_nat_comm in H. simpl in H. right. apply H.
  - simpl in H. left. apply H.
  - simpl in H. remember (max_nat x y) as z'. apply IHx in Heqz'.
    inversion Heqz'.
    + left. subst. reflexivity.
    + right. subst. reflexivity.
Qed.

Theorem zip_treelist : forall t tl1 tl2 tl,
  zip tl1 tl2 = tl <-> cons t tl = zip (cons t tl1) tl2.
Proof. intros. split.
  - intros. simpl. subst. reflexivity.
  - intros. simpl in H. inversion H. reflexivity.
 Qed.

Theorem depth_in_treelist : forall t tl tl1 tl2,
  tl = zip tl1 (cons t tl2) -> tree_depth t <= treelist_depth tl.
Proof.
  intros t. induction tl; intros.
  - simpl. destruct tl1; inversion H.
  - destruct tl1.
    + simpl in H. inversion H. subst. simpl.
      remember (max_nat (tree_depth t) (treelist_depth tl2)) as z.
      assert (H': z = tree_depth t \/ z = treelist_depth tl2). { apply max_nat_one. apply Heqz. }
      inversion H'.
      * subst; omega.
      * subst. rewrite max_nat_comm in H0. apply max_nat_largest in H0. omega.
    + simpl in H. inversion H. simpl. rewrite <- H2.
      assert (H0: tree_depth t <= treelist_depth tl). { apply IHtl with tl1 tl2. apply H2. }
      remember (max_nat (tree_depth t1) (treelist_depth tl)) as z.
      assert (H': z = tree_depth t1 \/ z = treelist_depth tl). { apply max_nat_one. apply Heqz. }
      inversion H'.
      * rewrite H3. assert (H4: treelist_depth tl <= tree_depth t1).
        { apply max_nat_largest. subst. assumption. }
        omega.
      * omega.
Qed.

Theorem max_nat_least : forall x y,
  x <= max_nat x y.
Proof.
  intros. remember (max_nat x y) as z.
  assert (z = x \/ z = y). { apply max_nat_one in Heqz. apply Heqz. }
  inversion H.
  - omega.
  - rewrite H0 in Heqz. rewrite max_nat_comm in Heqz.
    assert (y >= x). { apply max_nat_largest. omega. }
    omega.
Qed.

(** Correctness properties *)

(* Treelist in order property *)
Inductive treelist_sorted : key -> key -> treelist -> Prop :=
| ts_nil : forall ki kf, treelist_sorted ki kf nil
| ts_node : forall (ki ki' kf k : key) (f f' : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    treelist_sorted ki k f' -> (* forall x in f', ki < x <= k *)
    lt_key ki' k = false -> (* k <= ki' *)
    lt_key ki k = true -> (* ki < k *)
    treelist_sorted ki kf (cons (node k f') f)
| ts_final : forall (ki ki' kf : key) (f f' : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    treelist_sorted ki ki' f' -> (* forall x in f', ki < x <= ki' *)
    lt_key ki ki' = true -> (* ki < ki' *)
    treelist_sorted ki kf (cons (final f') f)
| ts_val : forall (ki ki' kf k : key) (v : V) (f : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    lt_key ki' k = false -> (* k <= ki' *)
    lt_key ki k = true -> (* ki < k *)
    treelist_sorted ki kf (cons (val k v) f).

(* Balance property *)
Inductive balanced_treelist : nat -> treelist -> Prop :=
| bf_nil : balanced_treelist 1 nil (* Should be 1, or 0? (has to match val) *)
| bf_val : forall k v f,
    balanced_treelist 1 f -> (* f is balanced with 1 level, i.e. f is a value treelist *)
    balanced_treelist 1 (cons (val k v) f)
| bf_node : forall n k f f',
    balanced_treelist n f -> (* f is balanced with n levels *)
    balanced_treelist (S n) f' -> (* f' is balanced with n+1 levels *)
    balanced_treelist (S n) (cons (node k f) f')
| bf_final : forall n f,
    balanced_treelist n f -> (* f is balanced with n levels *)
    balanced_treelist (S n) (cons (final f) nil).

(* Balance property on root *)
Definition balanced (f : treelist) : Prop := exists n, balanced_treelist n f.

Theorem balanced_rec : forall (t : tree) (f : treelist),
  balanced (cons t f) -> balanced f.
Proof.
  induction t.
  - intros. inversion H. inversion H0. unfold balanced. exists (S n). apply H6.
  - intros. inversion H. inversion H0. unfold balanced. exists 1. apply bf_nil.
  - intros. inversion H. inversion H0. unfold balanced. exists 1. apply H3.
Qed.

(** MAKE_CURSOR section *)

(* Functions to create a cursor (tree split) at a given key *)

Fixpoint lin_search (x : key) (f : treelist) : treelist * treelist :=
  match f with
  | cons t f' => 
    (match t with
     | node k _ => (if (lt_key k x) then
                     (match lin_search x f' with (f1,f2) => (cons t f1,f2) end)
                    else (nil, f))
     | val k _ => (if (lt_key k x) then
                    (match lin_search x f' with (f1,f2) => (cons t f1,f2) end)
                   else (nil, f))
     | final _ => (nil, cons t nil) end) (* Could also be (nil,f) *)
  | nil => (nil, nil)
  end.

Lemma lin_search_partial : forall x f t f1 f2,
  lin_search x (cons t f) = (cons t f1, f2) -> lin_search x f = (f1, f2).
Proof.
  intros. inversion H. destruct t.
  - destruct (lt_key k x). destruct (lin_search x f). inversion H1. reflexivity.
    inversion H1.
  - inversion H1.
  - destruct (lt_key k x). destruct (lin_search x f). inversion H1. reflexivity.
    inversion H1.
Qed.

Theorem lin_search_preserves_treelist : forall (x : key) (f f1 f2 : treelist),
  balanced f -> lin_search x f = (f1,f2) -> zip f1 f2 = f.
Proof.
  intros x f. induction f as [|t f'].
  - intros. inversion H0. reflexivity.
  - intros. induction t.
    * destruct f1. simpl. inversion H0. destruct (lt_key k x).
      + destruct (lin_search x f') in H2. inversion H2.
      + inversion H2. reflexivity.
      + simpl. inversion H0. destruct (lt_key k x). destruct (lin_search x f') in H2.
        inversion H2. subst. assert (zip f1 f2 = f'). apply IHf'.
        apply balanced_rec with (node k t). apply H.
        apply lin_search_partial in H0. apply H0.
        rewrite H1. reflexivity.
        inversion H2.
    * inversion H. inversion H1. subst. inversion H0. reflexivity.
    * destruct f1.
      + simpl. inversion H0. destruct (lt_key k x).
        { destruct (lin_search x f') in H2. inversion H2. }
        { inversion H2. reflexivity. }
      + simpl. inversion H0. destruct (lt_key k x).
        { destruct (lin_search x f') in H2. inversion H2. subst.
          assert (zip f1 f2 = f'). apply IHf'.
          apply balanced_rec with (val k v). apply H.
          apply lin_search_partial in H0. apply H0.
          rewrite H1. reflexivity. }
        { inversion H2. }
Qed.

Function make_cursor (x: key) (f : treelist) (c : cursor) {measure treelist_depth f} : cursor :=
  match f with
  | nil => c
  | _ =>
    (match lin_search x f with (f1,f2) =>
      (match f2 with
       | cons t _ =>
        (match t with
         | val _ _ => (f1,f2)::c
         | node _ f' => make_cursor x f' ((f1,f2)::c)
         | final f' => make_cursor x f' ((f1,f2)::c) end)
       | nil => c (* Should never happen *)
      end)end)
  end.
Proof.
  *
  intros. simpl. subst.
  generalize dependent t. generalize dependent t0. generalize dependent t2.
  destruct f' eqn:e; intros.
  - simpl. destruct t; simpl; destruct (treelist_depth t0); omega.
  - simpl.
    remember (max_nat (tree_depth t) (treelist_depth t0)) as max1.
    remember (max_nat (tree_depth t3) (treelist_depth t1)) as max2.
    apply lin_search_preserves_treelist in teq0.
    remember (node k (cons t t0)) as t'. remember (cons t3 t1) as tl.
    assert (tree_depth t' <= treelist_depth tl).
    { apply depth_in_treelist with f1 t2. rewrite teq0. reflexivity. }
    assert (tree_depth t < tree_depth t').
    { subst. simpl.
      assert (tree_depth t < S (tree_depth t)). { omega. }
      assert (tree_depth t <= (max_nat (tree_depth t) (treelist_depth t0))). { apply max_nat_least. }
      omega. }
    assert (H1: max1 = tree_depth t \/ max1 = treelist_depth t0).
    { apply max_nat_one. apply Heqmax1. }
    assert (H2: max2 = tree_depth t3 \/ max2 = treelist_depth t1).
    { apply max_nat_one. apply Heqmax2. }
    inversion H1; inversion H2; rewrite H3 in Heqmax1; rewrite H4 in Heqmax2.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H6. }
        omega. }
      omega.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t1 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (treelist_depth t1) (tree_depth t3) = treelist_depth t1).
        { apply max_nat_largest. apply H6. }
        rewrite max_nat_comm. rewrite H1. reflexivity. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H5. }
        omega. }
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H6. }
        omega. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H5. }
        omega. }
      assert (treelist_depth tl = treelist_depth t1).
      { rewrite Heqtl. simpl. rewrite max_nat_comm. apply max_nat_largest. apply H6. }
      omega.
    + admit. (* proving balanced -- impossible right now *)
  *
  intros. simpl. subst.
  generalize dependent t. generalize dependent t0. generalize dependent t2.
  destruct f' eqn:e; intros.
  - simpl. destruct t; simpl; destruct (treelist_depth t0); omega.
  - simpl.
    remember (max_nat (tree_depth t) (treelist_depth t0)) as max1.
    remember (max_nat (tree_depth t3) (treelist_depth t1)) as max2.
    apply lin_search_preserves_treelist in teq0.
    remember (final (cons t t0)) as t'. remember (cons t3 t1) as tl.
    assert (tree_depth t' <= treelist_depth tl).
    { apply depth_in_treelist with f1 t2. rewrite teq0. reflexivity. }
    assert (tree_depth t < tree_depth t').
    { subst. simpl.
      assert (tree_depth t < S (tree_depth t)). { omega. }
      assert (tree_depth t <= (max_nat (tree_depth t) (treelist_depth t0))). { apply max_nat_least. }
      omega. }
    assert (H1: max1 = tree_depth t \/ max1 = treelist_depth t0).
    { apply max_nat_one. apply Heqmax1. }
    assert (H2: max2 = tree_depth t3 \/ max2 = treelist_depth t1).
    { apply max_nat_one. apply Heqmax2. }
    inversion H1; inversion H2; rewrite H3 in Heqmax1; rewrite H4 in Heqmax2.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H6. }
        omega. }
      omega.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t1 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (treelist_depth t1) (tree_depth t3) = treelist_depth t1).
        { apply max_nat_largest. apply H6. }
        rewrite max_nat_comm. rewrite H1. reflexivity. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H5. }
        omega. }
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H6. }
        omega. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H1 H2 Heqmax1 Heqmax2 teq0. rewrite H3; rewrite H4; clear H3 H4.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H5. }
        omega. }
      assert (treelist_depth tl = treelist_depth t1).
      { rewrite Heqtl. simpl. rewrite max_nat_comm. apply max_nat_largest. apply H6. }
      omega.
    + admit. (* proving balanced -- impossible right now *)
Admitted.

(** GET section*)

(* Returns the value for key x if it exists, or None otherwise. *)
Fixpoint lookup (x : key) (f : treelist) : option V :=
  match (make_cursor x f []) with
  | [] => None
  | (_,nil)::tl => None (* Should never happen *)
  | (_,cons t _)::tl =>
      (match t with
       | val k v => if (eq_key k x) then Some v else None
       | _ => None (* Should never happen *)
       end)
  end.

(** INSERT section *)

(* separates the nth element to move up *)
Fixpoint split (f : treelist) (n : nat) : splitpair :=
  match n with
  | O => (match f with
          | nil => One f (* can't be split that far *)
          | cons t f' => (match t with
                          | node k f'' => Two (cons (final f'') nil) k f' (* the node becomes a final *)
                          | val k v => Two (cons t nil) k f' (* preserve the key-value pair *)
                          | final f'' => One f (* can't be split that far *)
                          end)
           end)
  | S n' => (match f with
             | nil => One f (* can't be split that far *)
             | cons t f' => (match split f' n' with
                             | One f1 => One (cons t f1)
                             | Two f1 k' f2 => Two (cons t f1) k' f2
                             end)
             end)
  end.

Fixpoint decide_split (f : treelist) : splitpair :=
  if (Nat.leb (treelist_length f) b)
  then One f
  else split f (div_two (treelist_length f) false).

Fixpoint insert_up (f : treelist) (c : cursor) : treelist :=
  match c with
  | (c1, cons (node k f') c2)::c' =>
    (match decide_split f with
     | One f1 => insert_up (zip c1 (cons (node k f1) c2)) c'
     | Two f1 k' f2 =>
         insert_up (zip c1 (cons (node k' f1) (cons (node k f2) c2))) c'
     end)
  | (c1, cons (final f') c2)::c' =>
     (match decide_split f with
     | One f1 => insert_up (zip c1 (cons (final f1) c2)) c'
     | Two f1 k' f2 =>
         insert_up (zip c1 (cons (node k' f1) (cons (final f2) c2))) c'
     end)
  | _ =>
     (match decide_split f with
     | One f1 => f1
     | Two f1 k f2 => cons (node k f1) (cons (final f2) nil)
     end)
  end.

Fixpoint insert (x : key) (v : V) (c : cursor) : treelist :=
  match c with
  | (c1, cons (val x' v') c2)::c' =>
    if (eq_key x' x) then insert_up (zip c1 (cons (val x v) c2)) c'
    else insert_up (zip c1 (cons (val x v) (cons (val x' v') c2))) c'
  | [] => cons (val x v) nil
  | _ => cons (val x v) nil (* shouldn't happen *)
  end.

Theorem insert_preserves_balance: forall f x v,
  balanced f ->
  balanced (insert x v (make_cursor x f [])).
Proof.
  induction f. intros.
Admitted. (* Need to prove termination of make_cursor first! *)

(** RANGE section *)
(* Note: currently not in module. *)

Parameter range : key -> key -> list V.
(* list key * V? *)
(* Relies on move-to-next, which needs to be implemented *)

(** NEXT section *)

Fixpoint get_first (f : treelist) : (treelist * treelist) :=
  match f with
  | cons t f' =>
    (match t with
     | node k f'' => (nil,f'')
     | final f'' => (nil,f'')
     | val k v => (nil,nil) (* Should be impossible *)
     end)
  | nil => (nil,nil)
  end.

Fixpoint move_to_next (c : cursor) : cursor :=
  match c with
  | (f1, cons t f2)::c' => 
    (match f2 with
     | cons t' f3 => (zip f1 (cons t nil), f2)::c'
     | nil =>
       (match (move_to_next c') with
        | (f1',f2')::c'' => (get_first f2')::(f1',f2')::c''
        | [] => c
        end)
     end)
  | (f1, nil)::c' =>
    (match (move_to_next c') with
     | (f1',f2')::c'' => (get_first f2')::(f1',f2')::c''
     | [] => c
     end)
  | [] => []
  end.

Theorem move_to_next_nil : forall (c : cursor),
  (move_to_next c) = [] <-> c = [].
Proof.
  intros. split.
  - induction c.
    * intros. reflexivity.
    * intros. simpl in H. destruct a. destruct t0.
      + destruct (move_to_next c). apply H.
        destruct p. inversion H.
      + destruct t1. destruct (move_to_next c). apply H.
        destruct p. inversion H. inversion H.
  - intros. subst. simpl. reflexivity.
Qed.

(** Test data and tests *)

Definition pos_one : key := Zpos xH.
Definition neg_one : key := Zneg xH.
Definition zero : key := Z0.
Definition pos_six : key := Zpos (xO (xI xH)).
Definition default : V. Admitted.

Definition ex_treelist : treelist :=
  cons (node neg_one
    (cons (val neg_one default)
    (cons (val pos_one default) nil)))
  (cons (final
    (cons (val pos_six default) nil))
  nil).

Compute (treelist_depth ex_treelist).

Definition ex_treelist' : treelist :=
  cons (final ex_treelist) nil.

Compute (treelist_depth ex_treelist').

Definition ex_treelist'' : treelist :=
  cons (val zero default) nil.

Compute (treelist_depth ex_treelist'').

Example b1: balanced ex_treelist.
Proof.
  unfold balanced. exists 2%nat.
  unfold ex_treelist.
  apply bf_node.
  - apply bf_val. apply bf_val. apply bf_nil.
  - apply bf_final. apply bf_val. apply bf_nil.
Qed.

End BTREES.
