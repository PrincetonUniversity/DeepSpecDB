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
  | tl_nil : treelist
  | tl_cons : tree -> treelist -> treelist.

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
  | tl_nil => O
  | tl_cons t f => max_nat (tree_depth t) (treelist_depth f)
  end
with tree_depth (t : tree) : nat :=
  match t with
  | node _ f => S (treelist_depth f)
  | final f => S (treelist_depth f)
  | val _ _ => S O
  end.

Fixpoint zip (f1 : treelist) (f2 : treelist) : treelist :=
  match f1 with
  | tl_cons t f' => tl_cons t (zip f' f2)
  | tl_nil => f2
  end.

Fixpoint treelist_length (f : treelist) : nat :=
  match f with
  | tl_nil => O
  | tl_cons t f' => S (treelist_length f')
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
  zip tl1 tl2 = tl <-> tl_cons t tl = zip (tl_cons t tl1) tl2.
Proof. intros. split.
  - intros. simpl. subst. reflexivity.
  - intros. simpl in H. inversion H. reflexivity.
 Qed.

Theorem depth_in_treelist : forall t tl tl1 tl2,
  tl = zip tl1 (tl_cons t tl2) -> tree_depth t <= treelist_depth tl.
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
| ts_nil : forall ki kf, treelist_sorted ki kf tl_nil
| ts_node : forall (ki ki' kf k : key) (f f' : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    treelist_sorted ki k f' -> (* forall x in f', ki < x <= k *)
    lt_key ki' k = false -> (* k <= ki' *)
    lt_key ki k = true -> (* ki < k *)
    treelist_sorted ki kf (tl_cons (node k f') f)
| ts_final : forall (ki ki' kf : key) (f f' : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    treelist_sorted ki ki' f' -> (* forall x in f', ki < x <= ki' *)
    lt_key ki ki' = true -> (* ki < ki' *)
    treelist_sorted ki kf (tl_cons (final f') f)
| ts_val : forall (ki ki' kf k : key) (v : V) (f : treelist),
    treelist_sorted ki' kf f -> (* forall x in f, ki' < x <= kf *)
    lt_key ki' k = false -> (* k <= ki' *)
    lt_key ki k = true -> (* ki < k *)
    treelist_sorted ki kf (tl_cons (val k v) f).

(* Balance property *)
Inductive balanced_treelist : nat -> treelist -> Prop :=
| bf_nil : balanced_treelist 1 tl_nil (* Should be 1, or 0? (has to match val) *)
| bf_val : forall k v f,
    balanced_treelist 1 f -> (* f is balanced with 1 level, i.e. f is a value treelist *)
    balanced_treelist 1 (tl_cons (val k v) f)
| bf_node : forall n k f f',
    balanced_treelist n f -> (* f is balanced with n levels *)
    balanced_treelist (S n) f' -> (* f' is balanced with n+1 levels *)
    balanced_treelist (S n) (tl_cons (node k f) f')
| bf_final : forall n f,
    balanced_treelist n f -> (* f is balanced with n levels *)
    balanced_treelist (S n) (tl_cons (final f) tl_nil).

(* Balance property on root *)
Definition balanced (f : treelist) : Prop := exists n, balanced_treelist n f.

Theorem balanced_rec : forall (t : tree) (f : treelist),
  balanced (tl_cons t f) -> balanced f.
Proof.
  induction t.
  - intros. inversion H. inversion H0. unfold balanced. exists (S n). apply H6.
  - intros. inversion H. inversion H0. unfold balanced. exists 1. apply bf_nil.
  - intros. inversion H. inversion H0. unfold balanced. exists 1. apply H3.
Qed.

(* Fanout property *)
Inductive fanout_restr : nat -> treelist -> Prop :=
| fr_nil : fanout_restr O tl_nil
| fr_val : forall n f k v,
    n < b ->
    fanout_restr n f ->
    fanout_restr (S n) (tl_cons (val k v) f)
| fr_node : forall n n' k f f',
    n' > div_two b false -> (* floor(b/2) *)
    fanout_restr n' f' ->
    n < b ->
    fanout_restr n f ->
    fanout_restr (S n) (tl_cons (node k f') f)
| fr_final : forall n f,
    n > div_two b false ->
    fanout_restr n f ->
    fanout_restr 1 (tl_cons (final f) tl_nil).

(** MAKE_CURSOR section *)

(* Functions to create a cursor (tree split) at a given key *)

Fixpoint lin_search (x : key) (f : treelist) : treelist * treelist :=
  match f with
  | tl_cons t f' => 
    (match t with
     | node k _ => (if (lt_key k x) then
                     (match lin_search x f' with (f1,f2) => (tl_cons t f1,f2) end)
                    else (tl_nil, f))
     | val k _ => (if (lt_key k x) then
                    (match lin_search x f' with (f1,f2) => (tl_cons t f1,f2) end)
                   else (tl_nil, f))
     | final _ => (tl_nil, tl_cons t tl_nil) end) (* Could also be (nil,f) *)
  | tl_nil => (tl_nil, tl_nil)
  end.

Lemma lin_search_partial : forall x f t f1 f2 t',
  lin_search x (tl_cons t f) = (tl_cons t' f1, f2) -> lin_search x f = (f1, f2) /\ t = t'.
Proof.
  intros. inversion H. destruct t.
  - destruct (lt_key k x). destruct (lin_search x f). inversion H1. split; reflexivity.
    inversion H1.
  - inversion H1.
  - destruct (lt_key k x). destruct (lin_search x f). inversion H1. split; reflexivity.
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

Theorem lin_search_max_depth : forall (x : key) (f f1 f2 : treelist),
  lin_search x f = (f1,f2) -> treelist_depth (zip f1 f2) <= treelist_depth f.
Proof.
  intros x f. induction f as [|t f']; intros.
  - inversion H. simpl. omega.
  - destruct f1.
    + inversion H. destruct t.
      * destruct (lt_key k x). destruct (lin_search x f'). inversion H1.
        inversion H1. subst. replace (zip tl_nil (tl_cons (node k t) f')) with (tl_cons (node k t) f').
        omega. reflexivity.
      * inversion H1. subst. replace (zip tl_nil (tl_cons (final t) tl_nil)) with (tl_cons (final t) tl_nil).
        simpl. destruct (treelist_depth f'). omega.
        assert (treelist_depth t <= max_nat (treelist_depth t) n). { apply max_nat_least. }
        omega. reflexivity.
      * destruct (lt_key k x). destruct (lin_search x f'). inversion H1.
        inversion H1. subst. replace (zip tl_nil (tl_cons (val k v) f')) with (tl_cons (val k v) f').
        omega. reflexivity.
    + apply lin_search_partial in H. inversion H. subst. clear H. simpl.
      remember (max_nat (tree_depth t0) (treelist_depth (zip f1 f2))) as max1.
      remember (max_nat (tree_depth t0) (treelist_depth f')) as max2.
      assert (max1 = tree_depth t0 \/ max1 = treelist_depth (zip f1 f2)).
      { apply max_nat_one. apply Heqmax1. }
      assert (max2 = tree_depth t0 \/ max2 = treelist_depth f').
      { apply max_nat_one. apply Heqmax2. }
      destruct H; destruct H1.
      * omega.
      * rewrite H. rewrite H1. subst. apply max_nat_largest. rewrite max_nat_comm. apply H1.
      * assert (treelist_depth (zip f1 f2) <= treelist_depth f'). { apply IHf'. apply H0. }
        assert (tree_depth t0 <= treelist_depth (zip f1 f2)). { apply max_nat_largest. subst. rewrite max_nat_comm. apply H. }
        assert (treelist_depth f' <= tree_depth t0). { apply max_nat_largest. subst. apply H1. }
        subst. omega.
      * rewrite H. rewrite H1. apply IHf'. apply H0.
Qed.

Function make_cursor (x: key) (f : treelist) (c : cursor) {measure treelist_depth f} : cursor :=
  match f with
  | tl_nil => c
  | _ =>
    (match lin_search x f with (f1,f2) =>
      (match f2 with
       | tl_cons t _ =>
        (match t with
         | val _ _ => (f1,f2)::c
         | node _ f' => make_cursor x f' ((f1,f2)::c)
         | final f' => make_cursor x f' ((f1,f2)::c) end)
       | tl_nil => c (* Should never happen *)
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
    assert (treelist_depth (zip f1 (tl_cons (node k (tl_cons t t0)) t2)) <= treelist_depth (tl_cons t3 t1)).
    { apply lin_search_max_depth with x. apply teq0. }
    remember (node k (tl_cons t t0)) as t'. remember (tl_cons t3 t1) as tl.
    assert (tree_depth t' <= treelist_depth (zip f1 (tl_cons t' t2))). { apply depth_in_treelist with f1 t2. reflexivity. }
    assert (tree_depth t' <= treelist_depth tl). { omega. }
    assert (tree_depth t < tree_depth t').
    { subst. simpl.
      assert (tree_depth t < S (tree_depth t)). { omega. }
      assert (tree_depth t <= (max_nat (tree_depth t) (treelist_depth t0))). { apply max_nat_least. }
      omega. }
    assert (H3: max1 = tree_depth t \/ max1 = treelist_depth t0).
    { apply max_nat_one. apply Heqmax1. }
    assert (H4: max2 = tree_depth t3 \/ max2 = treelist_depth t1).
    { apply max_nat_one. apply Heqmax2. }
    inversion H3; inversion H4; rewrite H5 in Heqmax1; rewrite H6 in Heqmax2.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H8. }
        omega. }
      omega.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t1 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (treelist_depth t1) (tree_depth t3) = treelist_depth t1).
        { apply max_nat_largest. apply H8. }
        rewrite max_nat_comm. rewrite H3. reflexivity. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H7. }
        omega. }
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H8. }
        omega. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H7. }
        omega. }
      assert (treelist_depth tl = treelist_depth t1).
      { rewrite Heqtl. simpl. rewrite max_nat_comm. apply max_nat_largest. apply H8. }
      omega.
  *
  intros. simpl. subst.
  generalize dependent t. generalize dependent t0. generalize dependent t2.
  destruct f' eqn:e; intros.
  - simpl. destruct t; simpl; destruct (treelist_depth t0); omega.
  - simpl.
    remember (max_nat (tree_depth t) (treelist_depth t0)) as max1.
    remember (max_nat (tree_depth t3) (treelist_depth t1)) as max2.
    assert (treelist_depth (zip f1 (tl_cons (final (tl_cons t t0)) t2)) <= treelist_depth (tl_cons t3 t1)).
    { apply lin_search_max_depth with x. apply teq0. }
    remember (final (tl_cons t t0)) as t'. remember (tl_cons t3 t1) as tl.
    assert (tree_depth t' <= treelist_depth (zip f1 (tl_cons t' t2))). { apply depth_in_treelist with f1 t2. reflexivity. }
    assert (tree_depth t' <= treelist_depth tl). { omega. }
    assert (tree_depth t < tree_depth t').
    { subst. simpl.
      assert (tree_depth t < S (tree_depth t)). { omega. }
      assert (tree_depth t <= (max_nat (tree_depth t) (treelist_depth t0))). { apply max_nat_least. }
      omega. }
    assert (H3: max1 = tree_depth t \/ max1 = treelist_depth t0).
    { apply max_nat_one. apply Heqmax1. }
    assert (H4: max2 = tree_depth t3 \/ max2 = treelist_depth t1).
    { apply max_nat_one. apply Heqmax2. }
    inversion H3; inversion H4; rewrite H5 in Heqmax1; rewrite H6 in Heqmax2.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H8. }
        omega. }
      omega.
    + assert (tree_depth t >= treelist_depth t0). { apply max_nat_largest. symmetry. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t1 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (treelist_depth t1) (tree_depth t3) = treelist_depth t1).
        { apply max_nat_largest. apply H8. }
        rewrite max_nat_comm. rewrite H3. reflexivity. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (tree_depth t3 >= treelist_depth t1). { apply max_nat_largest. symmetry. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H7. }
        omega. }
      assert (tree_depth t3 = treelist_depth tl).
      { rewrite Heqtl. simpl.
        assert (max_nat (tree_depth t3) (treelist_depth t1) = tree_depth t3).
        { apply max_nat_largest. apply H8. }
        omega. }
      omega.
    + assert (treelist_depth t0 >= tree_depth t). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax1. }
      assert (treelist_depth t1 >= tree_depth t3). { apply max_nat_largest. symmetry. rewrite max_nat_comm. apply Heqmax2. }
      clear H3 H4 Heqmax1 Heqmax2 teq0. rewrite H5; rewrite H6; clear H5 H6.
      assert (treelist_depth t0 < tree_depth t').
      { rewrite Heqt'. simpl.
        assert (max_nat (tree_depth t) (treelist_depth t0) = treelist_depth t0).
        { rewrite max_nat_comm. apply max_nat_largest. apply H7. }
        omega. }
      assert (treelist_depth tl = treelist_depth t1).
      { rewrite Heqtl. simpl. rewrite max_nat_comm. apply max_nat_largest. apply H8. }
      omega.
Qed.

(** GET section *)

Fixpoint get_key (c : cursor) : option key :=
  match c with
  | (_,tl_cons (val k v) _)::tl => Some k
  | _ => None (* Could search for next key if nil? *)
  end.

Fixpoint get (c : cursor) : option V :=
  match c with
  | (_,tl_cons (val k v) _)::tl => Some v
  | _ => None
  end.

(*
Lemma make_cursor_last : forall x f l f1 f2 c,
  make_cursor x f l = (f1,f2)::c -> f = nil \/ (exists f', (f1,f2) = lin_search x f').
Proof.
  intros x. induction f as [|t f']; intros.
  - left. reflexivity.
  - right. rewrite make_cursor_equation in H. make_cursor_terminate

Theorem get_key_leq : forall x f k,
  get_key (make_cursor x f []) = Some k -> (lt_key x k = true) \/ (eq_key x k = true).
Proof.
  intros x. induction f as [|t f']; intros.
  - rewrite make_cursor_equation in H. inversion H.
  - destruct (make_cursor x (cons t f') []) eqn:e1.
    * inversion H.
    * rewrite make_cursor_equation in e1.

rewrite make_cursor_equation in H. destruct (lin_search x (cons t f')) eqn:e1. destruct t1 eqn:e2.
    * inversion H.
    * 
*)

(** INSERT section *)

(* separates the nth element to move up *)
Fixpoint split (f : treelist) (n : nat) : splitpair :=
  match n with
  | O => (match f with
          | tl_nil => One f (* can't be split that far *)
          | tl_cons t f' => (match t with
                          | node k f'' => Two (tl_cons (final f'') tl_nil) k f' (* the node becomes a final *)
                          | val k v => Two (tl_cons t tl_nil) k f' (* preserve the key-value pair *)
                          | final f'' => One f (* can't be split that far *)
                          end)
           end)
  | S n' => (match f with
             | tl_nil => One f (* can't be split that far *)
             | tl_cons t f' => (match split f' n' with
                             | One f1 => One (tl_cons t f1)
                             | Two f1 k' f2 => Two (tl_cons t f1) k' f2
                             end)
             end)
  end.

Fixpoint decide_split (f : treelist) : splitpair :=
  if (Nat.leb (treelist_length f) b)
  then One f
  else split f (div_two (treelist_length f) false).

Fixpoint insert_up (f : treelist) (c : cursor) : treelist :=
  match c with
  | (c1, tl_cons (node k f') c2)::c' =>
    (match decide_split f with
     | One f1 => insert_up (zip c1 (tl_cons (node k f1) c2)) c'
     | Two f1 k' f2 =>
         insert_up (zip c1 (tl_cons (node k' f1) (tl_cons (node k f2) c2))) c'
     end)
  | (c1, tl_cons (final f') c2)::c' =>
     (match decide_split f with
     | One f1 => insert_up (zip c1 (tl_cons (final f1) c2)) c'
     | Two f1 k' f2 =>
         insert_up (zip c1 (tl_cons (node k' f1) (tl_cons (final f2) c2))) c'
     end)
  | _ =>
     (match decide_split f with
     | One f1 => f1
     | Two f1 k f2 => tl_cons (node k f1) (tl_cons (final f2) tl_nil)
     end)
  end.

Fixpoint insert (x : key) (v : V) (c : cursor) : treelist :=
  match c with
  | (c1, tl_cons (val x' v') c2)::c' =>
    if (eq_key x' x) then insert_up (zip c1 (tl_cons (val x v) c2)) c'
    else insert_up (zip c1 (tl_cons (val x v) (tl_cons (val x' v') c2))) c'
  | [] => tl_cons (val x v) tl_nil
  | _ => tl_cons (val x v) tl_nil (* shouldn't happen *)
  end.

Theorem insert_preserves_balance: forall f x v,
  balanced f ->
  balanced (insert x v (make_cursor x f [])).
Proof.
  induction f. intros.
Admitted. (* Need to prove termination of make_cursor first! *)

(** SET section *)

Fixpoint set (v : V) (c : cursor) : treelist :=
  match c with
  | (c1, tl_cons (val x' _) c2)::c' =>
    insert_up (zip c1 (tl_cons (val x' v) c2)) c'
  | _ => tl_nil (* shouldn't happen *)
  end.

(** RANGE section *)
(* Note: currently not in module. *)
(* Could be implemented entirely from things in the module... *)

Parameter range : key -> key -> list V.
(* list key * V? *)

(** NEXT section *)

Fixpoint get_first (f : treelist) : (treelist * treelist) :=
  match f with
  | tl_cons t f' =>
    (match t with
     | node k f'' => (tl_nil,f'')
     | final f'' => (tl_nil,f'')
     | val k v => (tl_nil,tl_nil) (* Should be impossible *)
     end)
  | tl_nil => (tl_nil,tl_nil)
  end.

Fixpoint move_to_next (c : cursor) : cursor :=
  match c with
  | (f1, tl_cons t f2)::c' => 
    (match f2 with
     | tl_cons t' f3 => (zip f1 (tl_cons t tl_nil), f2)::c'
     | tl_nil =>
       (match (move_to_next c') with
        | (f1',f2')::c'' => (get_first f2')::(f1',f2')::c''
        | [] => c
        end)
     end)
  | (f1, tl_nil)::c' =>
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
  tl_cons (node neg_one
    (tl_cons (val neg_one default)
    (tl_cons (val pos_one default) tl_nil)))
  (tl_cons (final
    (tl_cons (val pos_six default) tl_nil))
  tl_nil).

Compute (treelist_depth ex_treelist).

Definition ex_treelist' : treelist :=
  tl_cons (final ex_treelist) tl_nil.

Compute (treelist_depth ex_treelist').

Definition ex_treelist'' : treelist :=
  tl_cons (val zero default) tl_nil.

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
