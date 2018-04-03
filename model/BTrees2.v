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

Definition cursor : Type := list nat * list treelist.

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

Theorem fanout_rec_node : forall (n : nat) (k : key) (f : treelist) (f' : treelist),
  fanout_restr n (tl_cons (node k f') f) ->
  exists (n' : nat), n' <= b /\ n' > div_two b false /\ fanout_restr n' f'.
Proof.
  intros. inversion H. subst.
  exists n'. split; try split.
  - inversion H5; omega.
  - apply H3.
  - apply H5.
Qed.

Theorem fanout_rec_final : forall (n : nat) (f : treelist) (f' : treelist),
  fanout_restr n (tl_cons (final f') f) ->
  exists (n' : nat), n' <= b /\ n' > div_two b false /\ fanout_restr n' f'.
Proof.
  intros. inversion H. subst.
  exists n0. split; try split.
  - inversion H4; try omega.
    * admit. (* Relies on b being at least 1 *)
  - apply H3.
  - apply H4.
Admitted.

(** MAKE_CURSOR section *)

(* Functions to create a cursor (tree split) at a given key *)

Function make_cursor_rec (x: key) (f : treelist) (ci : list nat) (ct : list treelist) (n : nat) : cursor :=
  match f with
  | tl_nil => (n::ci,ct)
  | tl_cons (node k f') f =>
    if lt_key k x then make_cursor_rec x f ci ct (S n) else make_cursor_rec x f' (n::ci) (f'::ct) O
  | tl_cons (final f') tl_nil =>
    make_cursor_rec x f' (n::ci) (f'::ct) O
  | tl_cons (val k v) f =>
    if lt_key k x then make_cursor_rec x f ci ct (S n) else (n::ci,ct)
  | _ => ([],[])
  end.

Definition make_cursor (x : key) (f : treelist) : cursor := make_cursor_rec x f [] [f] O.

Function lin_search (n : nat) (f : treelist) : option tree :=
  match f with
  | tl_cons t f' => 
    (match n with
     | O => Some t
     | S n' => lin_search n' f'
     end)
  | tl_nil => None
  end.

Inductive cursor_correct : cursor -> Prop :=
| cc_nil : cursor_correct ([],[])
| cc_first : forall n f, cursor_correct ([n],[f])
| cc_node : forall n n' k f f' ci ct,
    cursor_correct (n::ci,f::ct) -> lin_search n f = Some (node k f') ->
    cursor_correct (n'::n::ci,f'::f::ct)
| cc_final : forall n n' f f' ci ct,
    cursor_correct (n::ci,f::ct) -> lin_search n f = Some (final f') ->
    cursor_correct (n'::n::ci, f'::f::ct).

Fixpoint dec (n : nat) (f : treelist) : treelist :=
  match n with
  | O => f
  | S n' => 
    (match f with
     | tl_cons t f' => dec n' f'
     | tl_nil => tl_nil
     end)
  end.

Definition mc_correct_P (x : key) (t : tree) : Prop := forall k f n ci ct n' f',
  t = node k f \/ t = final f ->
  cursor_correct (n::ci,f::ct) ->
  dec n' f = f' ->
  cursor_correct (make_cursor_rec x f' ci (f::ct) n').

Lemma dec_nil : forall n,
  dec n tl_nil = tl_nil.
Proof. destruct n; reflexivity. Qed.

(*
Lemma dec_correct_trans : forall x f n ci ct,
  cursor_correct (make_cursor_rec x (dec n f) ci (f :: ct) n) ->
  cursor_correct (make_cursor_rec x (dec (S n) f) ci (f :: ct) (S n)).
Proof.
  intros x f. induction n; intros.
  - simpl. destruct f.
    + simpl. simpl in H. inversion H.
      * apply cc_first.
      * apply cc_node with k. apply H2. apply H5.
      * apply cc_final. apply H2. apply H5.
    + simpl in H. 
*)
Lemma dec_correct_trans : forall x f n' ci ct,
  cursor_correct (make_cursor_rec x f ci (f :: ct) O) ->
  cursor_correct (make_cursor_rec x (dec n' f) ci (f :: ct) n').
Proof.
  intros x f. induction n'; intros.
  - simpl. apply H.
  - simpl. destruct f.
    + simpl. simpl in H. inversion H.
      * apply cc_first.
      * apply cc_node with k. apply H2. apply H5.
      * apply cc_final. apply H2. apply H5.
    + admit.
Admitted.

Lemma dec_cont : forall f n,
  dec (S n) f = dec 1 (dec n f).
Proof.
  induction f; intros.
  - simpl. destruct n; reflexivity.
  - induction n.
    + reflexivity.
    + replace (dec (S (S n)) (tl_cons t f)) with (dec (S n) f).
      replace (dec (S n) (tl_cons t f)) with (dec n f).
      apply IHf. reflexivity. reflexivity.
Qed.

Lemma dec_lin_search : forall n f t f'',
  dec n f = tl_cons t f'' -> lin_search n f = Some t.
Proof.
  induction n; intros.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H. destruct f. inversion H. simpl.
    apply IHn with f''. apply H.
Qed.

Theorem make_cursor_rec_correct : forall x f' n ci ct n' f,
  cursor_correct (n::ci,f::ct) ->
  dec n' f = f' ->
  cursor_correct (make_cursor_rec x f' ci (f::ct) n').
Proof.
  intros x. induction f' using treelist_tree_rec with (P := mc_correct_P x); try unfold mc_correct_P; intros.
  - inversion H; inversion H2. subst. apply dec_correct_trans. (* admitted theorem *)
    apply IHf' with O. inversion H0.
    + apply cc_first.
    + apply cc_node with k. apply H4. apply H7.
    + apply cc_final. apply H4. apply H7.
    + reflexivity.
  - inversion H; inversion H2. subst. apply dec_correct_trans. (* admitted theorem *)
    apply IHf' with O. inversion H0.
    + apply cc_first.
    + apply cc_node with k0. apply H4. apply H7.
    + apply cc_final. apply H4. apply H7.
    + reflexivity.
  - inversion H; inversion H2.
  - simpl. inversion H.
    + apply cc_first.
    + apply cc_node with k. apply H3. apply H6.
    + apply cc_final. apply H3. apply H6.
  - unfold mc_correct_P in IHf'. simpl. destruct t eqn:e. destruct (lt_key k x). 4:destruct (lt_key k x).
    + apply IHf'0 with n. apply H. rewrite dec_cont. rewrite H0. reflexivity.
    + apply IHf' with k O. left. reflexivity.
      * inversion H; subst.
        { apply cc_node with k. apply cc_first. apply dec_lin_search with f'. apply H0. }
        { apply cc_node with k. apply cc_node with k0. apply H3. apply H6. apply dec_lin_search with f'. apply H0. }
        { apply cc_node with k. apply cc_final. apply H3. apply H6. apply dec_lin_search with f'. apply H0. }
      * reflexivity.
    + destruct f'. 2:apply cc_nil. apply IHf' with x O. right. reflexivity.
      * inversion H; subst.
        { apply cc_final. apply cc_first. apply dec_lin_search with tl_nil. apply H0. }
        { apply cc_final. apply cc_node with k. apply H3. apply H6. apply dec_lin_search with tl_nil. apply H0. }
        { apply cc_final. apply cc_final. apply H3. apply H6. apply dec_lin_search with tl_nil. apply H0. }
      * reflexivity.
    + apply IHf'0 with n. apply H. rewrite dec_cont. rewrite H0. reflexivity.
    + inversion H; subst.
      * apply cc_first.
      * apply cc_node with k0. apply H3. apply H6.
      * apply cc_final. apply H3. apply H6.
Qed.

Theorem make_cursor_correct : forall x f,
  cursor_correct (make_cursor x f).
Proof.
  intros. unfold make_cursor. apply make_cursor_rec_correct with O.
  - apply cc_first.
  - reflexivity.
Qed.

Definition mc_val_P (x : key) (t : tree) : Prop := forall k f ci ct n n1 f1 ci' ct' t',
  t = node k f \/ t = final f ->
  make_cursor_rec x f ci ct n = (n1::ci',f1::ct') ->
  lin_search n1 f1 = Some t' ->
  (exists k v, t = val k v).

Theorem make_cursor_val : forall x f t ci ct n n1 f1 ci' ct',
  make_cursor_rec x f ci ct n = (n1::ci',f1::ct') -> lin_search n1 f1 = Some t -> (exists k v, t = val k v).
Proof.
  intros x. induction f using treelist_tree_rec with (P := mc_val_P x); try unfold mc_val_P; intros.
  - inversion H; inversion H2; subst. apply IHf with ci ct n n1 f1 ci' ct'. apply H0. (* apply H1.
  - inversion H; inversion H2; subst. apply IHf with ci ct n n1 f1 ci' ct'. apply H0. apply H1.
  - exists k. exists v. reflexivity.
  - admit.
  - unfold mc_val_P in IHf. destruct t eqn:e.
    + simpl in H. destruct (lt_key k x).
      * apply IHf0 with ci ct (S n) n1 f1 ci' ct'. apply H. apply H0.
      * apply IHf with k t1 (n::ci) (t1::ct) O n1 f1 ci' ct'. *)
  admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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
*)
(*
Definition make_cursor_list_P (x : key) (t : tree) : Prop := forall k f l,
  t = node k f \/ t = final f ->
  make_cursor x f l = (make_cursor x f []) ++ l.

Theorem make_cursor_list : forall x f l,
  make_cursor x f l = (make_cursor x f []) ++ l.
Proof.
  intros x f. induction f using treelist_tree_rec with (P := make_cursor_list_P x); try unfold make_cursor_list_P.
  - intros. inversion H; inversion H0. subst. apply IHf.
  - intros. inversion H; inversion H0. subst. apply IHf.
  - intros. inversion H; inversion H0.
  - intros. rewrite make_cursor_equation. rewrite make_cursor_equation. rewrite app_nil_l. reflexivity.
  - intros. admit.
Admitted.

Theorem make_cursor_cons : forall x k t f f1 f2 c,
  lt_key k x = true -> make_cursor x f [] = c ++ [(f1,f2)] ->
  make_cursor x (tl_cons (node k t) f) [] = c ++ [(tl_cons (node k t) f1, f2)].
Proof.
Admitted. *)

Definition get_key_leq_P (x : key) (t : tree) : Prop := forall k' k f l n,
  t = node k' f \/ t = final f ->
  get_key (make_cursor_rec x f l n) = Some k ->
  (lt_key x k = true) \/ (eq_key x k = true).

Theorem get_key_leq : forall x f k,
  get_key (make_cursor x f []) = Some k -> (lt_key x k = true) \/ (eq_key x k = true).
Proof.
  intros x. induction f using treelist_tree_rec with (P := get_key_leq_P x).
  - unfold get_key_leq_P. intros. apply IHf. inversion H; inversion H1. subst. apply H0.
  - unfold get_key_leq_P. intros. apply IHf. inversion H; inversion H1. subst. apply H0.
  - unfold get_key_leq_P. intros. inversion H; inversion H1.
  - intros. rewrite make_cursor_equation in H. inversion H.
  - intros. unfold get_key_leq_P in IHf. destruct t eqn:e.
    * destruct (lt_key k0 x) eqn:elt.
      + apply IHf0. destruct (make_cursor x f []) eqn:ec.
        { rewrite make_cursor_equation in ec. destruct f.
          rewrite make_cursor_equation in H. unfold lin_search in H.
          destruct (lt_key k0 x). apply H. inversion elt.
          
      admit.
    * admit.
    * admit.
Admitted.


(* rewrite make_cursor_equation. rewrite make_cursor_equation. unfold make_cursor_list_P in IHf.
    destruct t eqn:e.
    * 


    destruct (lin_search x (tl_cons t f)). destruct t1.
    * rewrite app_nil_l. reflexivity.
    * destruct t1. 


rewrite make_cursor_equation. destruct f.
  - rewrite make_cursor_equation. rewrite app_nil_l. reflexivity.
  - *)



 (* Here, the induction hypothesis I want is on the sub-treelist of t, not on f'! *)
 (* Induction "using" the induction scheme! *)
    destruct (make_cursor x (cons t f') []) eqn:e1.
    * inversion H.
    * rewrite make_cursor_equation in e1.

rewrite make_cursor_equation in H. destruct (lin_search x (cons t f')) eqn:e1. destruct t1 eqn:e2.
    * inversion H.
    * 


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

(* Theorem set_balanced : forall v x t, *)

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
