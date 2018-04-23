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

(*
treelist_tree_rec :
forall (P : tree -> Type) (P0 : treelist -> Type),
(forall (k : key) (t : treelist), P0 t -> P (node k t)) ->
(forall t : treelist, P0 t -> P (final t)) ->
(forall (k : key) (v : V), P (val k v)) ->
P0 tl_nil ->
(forall t : tree, P t -> forall t0 : treelist, P0 t0 -> P0 (tl_cons t t0)) ->
forall t : treelist, P0 t
*)


Definition cursor : Type := list nat * list treelist.

Inductive splitpair : Type :=
| One : treelist -> splitpair
| Two : treelist -> key -> treelist -> splitpair.

(** Example data *)

Definition pos_one : key := Zpos xH.
Definition neg_one : key := Zneg xH.
Definition zero : key := Z0.
Definition pos_six : key := Zpos (xO (xI xH)).
Definition default : V. Admitted.

Definition ex_treelist : treelist :=
  tl_cons (node pos_one
    (tl_cons (val neg_one default)
    (tl_cons (val pos_one default) tl_nil)))
  (tl_cons (final
    (tl_cons (val pos_six default) tl_nil))
  tl_nil).

Definition ex_treelist' : treelist :=
  tl_cons (final ex_treelist) tl_nil.

Definition ex_treelist'' : treelist :=
  tl_cons (val zero default) tl_nil.

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
    | _ => true
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

Function lin_search (n : nat) (f : treelist) : option tree :=
  match f with
  | tl_cons t f' => 
    (match n with
     | O => Some t
     | S n' => lin_search n' f'
     end)
  | tl_nil => None
  end.

Fixpoint point (n : nat) (f : treelist): (treelist * option tree * treelist) :=
  match f with
  | tl_cons t f' =>
    (match n with
     | O => (tl_nil,Some t,f')
     | S n' => (match point n' f' with (f1,t',f2) => (tl_cons t f1,t',f2) end)
     end)
  | tl_nil => (tl_nil,None,tl_nil)
  end.

(* Oh god reinventing more list stuff... *)
Function tl_app (f1 : treelist) (f2 : treelist) : treelist :=
  match f1 with
  | tl_nil => f2
  | tl_cons t f1' => tl_cons t (tl_app f1' f2)
  end.

(** MAKE_CURSOR section *)

(* Functions to create a cursor at a given key *)

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

(** NEXT & PREV section *)

(* Rectify this and prev_node; make sure it works for the root *)
Fixpoint next_node (cn : list nat) (cf : list treelist) : option (cursor * key) :=
  match (cn,cf) with
  | (n::cn',f::cf') =>
    (match point n f with
     | (_,Some (node k _),tl_cons (node _ f') _) => Some (((S n)::cn',f::cf'),k)
     | (_,Some (node k _),tl_cons (final f') _) => Some (((S n)::cn',f::cf'),k)
     | (_,Some (val k v), _) => Some ((n::cn',f::cf'),k) (* maybe None for key? *)
     | _ =>
       (match next_node cn' cf' with
        | Some ((n'::cn,f'::cf),k) =>
          (match point n' f' with
           | (_,Some (node _ f1),_) => Some ((O::n'::cn,f1::f'::cf),k)
           | (_,Some (final f1),_) => Some ((O::n'::cn,f1::f'::cf),k)
           | _ => None
           end)
        | _ => None
        end)
     end)
  | (_,_) => None
  end.

Fixpoint prev_node (cn : list nat) (cf : list treelist) : option (cursor * key) :=
  match (cn,cf) with
  | (S n::cn',f::cf') =>
     (match point n f with
      | (_,Some (node k f'),_) => Some ((n::cn',f::cf'),k)
      | (_,Some (final f'),_) => None (* Shouldn't be possible *)
      | (_,Some (val k v),_) => Some ((S n::cn',f::cf'),k) (* maybe None for key? *)
      | (_,None,_) => None (* Shouldn't be possible *)
      end)
  | (O::cn',f::cf') =>
     (match prev_node cn' cf' with
       | Some ((n::cn, f::cf),k) => 
         (match point n f with
          | (_,Some (node _ f'),_) => Some (((treelist_length f')-1::n::cn,f'::f::cf),k) (* There's gotta be a better way? *)
          | (_,Some (final f'),_) => Some (((treelist_length f')-1::n::cn,f'::f::cf),k)
          | _ => None
          end)
       | _ => None
       end)
  | (_,_) => None
  end.

Fixpoint move_to_next (c : cursor) : cursor :=
  match c with (cn,cf) =>
  (match next_node cn cf with
   | Some ((n::cn',cf'),_) => (S n::cn',cf')
   | _ => c
   end)
  end.

(* Make sure prev_node works correctly if index too big / make sure index never too big? *)
Fixpoint move_to_prev (c : cursor) : cursor :=
  match c with (cn,cf) =>
  (match prev_node cn cf with
   | Some ((S n::cn',cf'),_) => (n::cn',cf')
   | _ => c
   end)
  end.

(** GET section *)

(* Hopefully this will let me prove interesting things only once and apply to both get_key and get *)
Fixpoint get_tree (c : cursor) : option tree :=
  match c with (cn,cf) =>
  (match next_node cn cf with
   | Some ((n::_,f::_),_) => lin_search n f
   | _ => None
   end)
  end.

Fixpoint get_key (c : cursor) : option key :=
  match get_tree c with
  | Some (val k v) => Some k
  | _ => None
  end.

Fixpoint get (c : cursor) : option V :=
  match get_tree c with
  | Some (val k v) => Some v
  | _ => None
  end.

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

Fixpoint insert_across (s : splitpair) (f' : treelist) (n : nat) : treelist :=
  match f' with
  | tl_cons (node k f) f' =>
    (match n with
     | O =>
       (match s with
        | One f => tl_cons (node k f) f'
        | Two f1 k' f2 => tl_cons (node k' f1) (tl_cons (node k f2) f')
        end)
     | S n' => tl_cons (node k f) (insert_across s f' n')
     end)
  | tl_cons (final f) tl_nil =>
    (match n with
     | O =>
       (match s with
        | One f => tl_cons (final f) tl_nil
        | Two f1 k' f2 => tl_cons (node k' f1) (tl_cons (final f2) f')
        end)
     | S n' => tl_cons (final f) tl_nil (* This also should never happen! *)
     end)
  | _ => tl_nil (* Behavior here? Shouldn't ever be hit. *)
  end.

(* This is super ugly and will be a pain to reason about... *)
Fixpoint insert_up (s : splitpair) (cn : list nat) (cf : list treelist) : cursor :=
  match (cn,cf) with
  | (n::cn,f::cf) =>
    (match decide_split (insert_across s f n) with
     | One f => (match insert_up (One f) cn cf with (cn,cf) => (n::cn,f::cf) end)
     | Two f1 k f2 =>
       (match insert_up (Two f1 k f2) cn cf with (cn,cf) =>
        if (Nat.leb (treelist_length f1) n) then ((n-(treelist_length f1))::cn, f1::cf) (* should this be f2? *)
        else (n::cn,f2::cf) end)
     end)
  | (_,_) => ([],[])
  end.

Fixpoint insert_val (x : key) (v : V) (n : nat) (f : treelist) : nat * treelist :=
  match f with
  | tl_cons (val k v') f =>
    (match n with
     | O => if eq_key k x then (O, tl_cons (val k v) f)
            else (S O, tl_cons (val x v) (tl_cons (val k v') f))
     | S n => match insert_val x v n f with (n, f) => (S n, tl_cons (val k v') f) end
     end)
  | tl_nil => (S O, tl_cons (val x v) tl_nil)
  | _ => (S O, tl_cons (val x v) tl_nil) (* should never happen *)
  end.

(* Needs to point the cursor to the right place (if it's straddling a leaf divide) *)
(* Then, insert (x,v) in (either replacing next or inserting before it) *)
(* Needs to bump the first n up to be past what was just inserted *)
(* Finally, turns that treelist into a splitpair and calls insert_up. *)
Fixpoint insert (x : key) (v : V) (c : cursor) : cursor :=
  match c with
  | (n::cn,f::cf) =>
    (match next_node cn cf with
      | Some ((n'::cn',f'::cf'),k) =>
        if lt_key x k then (match insert_val x v n f with (n,f) =>
          (match decide_split f with 
           | One f => (match insert_up (One f) cn cf with (cn,cf) => (n::cn,f::cf) end)
           | Two f1 k f2 =>
             (match insert_up (Two f1 k f2) cn cf with (cn,cf) =>
              if (Nat.leb (treelist_length f1) n) then ((n-(treelist_length f1))::cn, f2::cf)
              else (n::cn,f1::cf) end)
           end) end)
        else (match insert_val x v n' f' with (n',f') =>
          (match decide_split f' with
           | One f' => (match insert_up (One f') cn' cf' with (cn',cf') => (n'::cn',f'::cf') end)
           | Two f1 k f2 =>
             (match insert_up (Two f1 k f2) cn' cf' with (cn',cf') =>
              if (Nat.leb (treelist_length f1) n) then ((n-(treelist_length f1))::cn, f2::cf)
              else (n::cn,f1::cf) end)
           end) end)
      | None => (match insert_val x v n f with (n,f) =>
        (match decide_split f with 
         | One f => (match insert_up (One f) cn cf with (cn,cf) => (n::cn,f::cf) end)
         | Two f1 k f2 =>
           (match insert_up (Two f1 k f2) cn cf with (cn,cf) =>
            if (Nat.leb (treelist_length f1) n) then ((n-(treelist_length f1))::cn, f2::cf)
            else (n::cn,f1::cf) end)
         end) end)
      | _ => ([],[]) (* shouldn't be possible *)
      end)
  | _=> ([S O], [tl_cons (val x v) tl_nil]) (* tree must be empty *)
  end.

(** CURSOR_ELEMENTS *)

Fixpoint elements' (f : treelist) (base: list (key * V)) : list (key * V) :=
  match f with
  | tl_cons (node k f1) f2 => elements' f1 (elements' f2 base)
  | tl_cons (final f1) f2 => elements' f1 (elements' f2 base)
  | tl_cons (val k v) f2 => (k,v)::(elements' f2 base)
  | tl_nil => base
  end.

Fixpoint elements (f : treelist) : list (key * V) := elements' f [].

Fixpoint right_el (f : treelist) (base : list (key * V)) : list (key * V) :=
  match f with
  | tl_cons (node k f1) f2 => right_el f2 (right_el f1 base)
  | tl_cons (final f1) f2 => right_el f2 (right_el f1 base)
  | tl_cons (val k v) f2 => right_el f2 (base++[(k,v)])
  | tl_nil => base
  end.

Fixpoint left_el (f : treelist) (base : list (key * V)) : list (key * V) :=
  match f with
  | tl_cons (node k f1) f2 => left_el f1 (left_el f2 base)
  | tl_cons (final f1) f2 => left_el f1 (left_el f2 base)
  | tl_cons (val k v) f2 => (left_el f2 base) ++ [(k,v)]
  | tl_nil => base
  end.

Fixpoint cursor_right (cn : list nat) (cf : list treelist) (base : list (key * V)) : list (key * V) :=
  match (cn,cf) with
  | (n::cn,f::cf) =>
    (match point n f with (_,_,f') => cursor_right cn cf (right_el f' base) end)
  | (_,_) => base
  end.

Fixpoint cursor_left (cn : list nat) (cf : list treelist) (base : list (key * V)) : list (key * V) :=
  match (cn,cf) with
  | (n::cn,f::cf) =>
    (match point n f with (f',_,_) => cursor_left cn cf (left_el f' base) end)
  | (_,_) => base
  end.

Fixpoint cursor_elements' (cn : list nat) (cf : list treelist) (left : list (key * V)) (right : list (key * V))
  : (list (key * V)) * (list (key * V)) :=
  match (cn,cf) with
  | (n::cn,f::cf) =>
    (match point n f with (f1,_,f2) => cursor_elements' cn cf (left_el f1 left) (right_el f2 right) end)
  | (_,_) => (left,right)
  end.

Definition cursor_elements (c : cursor) : list (key * V) * list (key * V) :=
  match c with
  | (n::cn,f::cf) =>
    (match point n f with
     | (_,Some (val k v),_) => cursor_elements' (n::cn) (f::cf) [] [(k,v)]
     | _ => cursor_elements' (n::cn) (f::cf) [] [] end)
  | (_,_) => ([],[])
  end.

(**
  * PROOFS SECTION
  *)

(** Proofs about helper functions *)

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

Theorem point_lin_search : forall f n t l1 l2,
  point n f = (l1,Some t,l2) -> lin_search n f = Some t.
Proof.
  induction f; destruct n; simpl; intros.
  - inversion H.
  - inversion H.
  - inversion H. reflexivity.
  - destruct (point n f) eqn:e. destruct p. apply IHf with t2 t1.
    rewrite e. inversion H. reflexivity.
Qed.

Theorem lin_search_point : forall f n t,
  lin_search n f = Some t -> exists l1 l2, point n f = (l1,Some t,l2).
Proof.
  induction f; destruct n; simpl; intros.
  - inversion H.
  - inversion H.
  - inversion H. subst. exists tl_nil,f. reflexivity.
  - destruct (point n f) eqn:e. destruct p. apply IHf in H. inversion H. inversion H0.
    rewrite e in H1. inversion H1. subst.
    exists (tl_cons t x),x0. reflexivity.
Qed.

(* What about when n = treelist_length f - 1? *)
Lemma point_treelist_length : forall n f,
  n >= treelist_length f <-> exists f', point n f = (f',None,tl_nil).
Proof.
  induction n; destruct f; split; intros; simpl; try omega.
  - exists tl_nil. reflexivity.
  - simpl in H. inversion H.
  - simpl in H. inversion H. inversion H0.
  - exists tl_nil. reflexivity.
  - simpl in H. assert (n >= treelist_length f) by omega.
    apply IHn in H0. inversion H0. exists (tl_cons t x). rewrite H1. reflexivity.
  - simpl in H. destruct (point n f) eqn:e. destruct p. inversion H. inversion H0. subst.
    assert (n >= treelist_length f) by (apply IHn; exists t1; apply e). omega.
Qed.


Lemma point_none : forall n f f1 f2,
  point n f = (f1,None,f2) -> f2 = tl_nil.
Proof.
  induction n; intros.
  - simpl in H. destruct f; inversion H. reflexivity.
  - simpl in H. destruct f. inversion H. reflexivity.
    destruct (point n f) eqn:e. destruct p.
    inversion H. subst. apply IHn with f t1. apply e.
Qed.

Lemma point_prev : forall n f f1 f2 t f1' f2' o,
  point n f = (f1, Some t, f2) ->
  point (S n) f = (f1', o, f2') ->
  f1' = tl_app f1 (tl_cons t tl_nil).
Proof.
  induction n; intros.
  - destruct f.
    + simpl in H. inversion H.
    + simpl in H. inversion H. subst. simpl.
      simpl in H0. destruct f2; inversion H0; reflexivity.
  - simpl in H. remember (S n) as n'. simpl in H0. destruct f.
    + inversion H.
    + destruct (point n f) eqn:e. destruct p.
      destruct (point n' f) eqn:e2. destruct p.
      subst. inversion H. inversion H0. subst.
      assert (t4 = tl_app t2 (tl_cons t tl_nil)).
      { apply IHn with f f2 f2' o. apply e. apply e2. }
      simpl. rewrite H1. reflexivity.
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

Definition sorted (f : treelist) : Prop := exists ki kf, treelist_sorted ki kf f.

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

Definition fanout (f : treelist) : Prop := exists n, fanout_restr n f.

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

Inductive cursor_correct_struct : cursor -> Prop :=
| cc_nil : cursor_correct_struct ([],[])
| cc_first : forall n f, cursor_correct_struct ([n],[f])
| cc_node : forall n n' k f f' ci ct,
    cursor_correct_struct (n::ci,f::ct) -> lin_search n f = Some (node k f') ->
    cursor_correct_struct (n'::n::ci,f'::f::ct)
| cc_final : forall n n' f f' ci ct,
    cursor_correct_struct (n::ci,f::ct) -> lin_search n f = Some (final f') ->
    cursor_correct_struct (n'::n::ci, f'::f::ct).
(* add that it ends at a leaf *)
(* first f should be correct *)

Inductive rec_prop (P : treelist -> Prop) : cursor -> Prop :=
| rp_nil : rec_prop P ([],[])
| rp_next : forall n f cn cf, P f -> rec_prop P (cn,cf) -> rec_prop P (n::cn,f::cf).

Definition cursor_correct (c : cursor) : Prop :=
  cursor_correct_struct c /\
  rec_prop balanced c /\
  rec_prop sorted c /\
  rec_prop fanout c.

(** Abstraction of cursors as bi-directional list of key-value pairs
  * Proofs about this abstraction and the implementation
  *)

(* Lemma 1 in the doc *)
(* Proof that splitting into sides is equivalent -- now I can prove about the sides separately! *)
Theorem cursor_elements'_sides_equiv : forall cn cf l r,
  cursor_elements' cn cf l r = (cursor_left cn cf l, cursor_right cn cf r).
Proof.
  induction cn,cf; intros; simpl; try reflexivity.
  destruct (point a t) eqn:e. destruct p. apply IHcn.
Qed.

(* Cursor to list of elements : cons in both directions *)
(* get returns the next thing in that list! *)

Definition right_el_P (t : tree) : Prop := forall k f b,
  t = node k f \/ t = final f ->
  exists l', right_el f b = b++l'.

(* Lemma 2 *)
Theorem right_el_interior : forall f b,
  exists l', right_el f b = b++l'.
Proof.
  induction f using treelist_tree_rec with (P := right_el_P).
  - unfold right_el_P. intros. inversion H; inversion H0. subst. apply IHf.
  - unfold right_el_P. intros. inversion H; inversion H0. subst. apply IHf.
  - unfold right_el_P. intros. inversion H; inversion H0.
  - intros. unfold right_el. exists []. rewrite app_nil_r. reflexivity.
  - intros. destruct t eqn:e.
    + simpl. unfold right_el_P in IHf.
      assert (exists l', right_el t0 b0 = b0++l').
      { apply IHf with k. left. reflexivity. }
      inversion H. rewrite H0. destruct IHf0 with (b0 ++ x).
      exists (x++x0). rewrite H1. rewrite app_assoc. reflexivity.
    + simpl. unfold right_el_P in IHf.
      assert (exists l', right_el t0 b0 = b0++l').
      { apply IHf with zero. right. reflexivity. }
      inversion H. rewrite H0. destruct IHf0 with (b0 ++ x).
      exists (x ++ x0). rewrite H1. rewrite app_assoc. reflexivity.
    + simpl. destruct IHf0 with (b0 ++ [(k,v)]).
      exists ((k,v)::x). rewrite H. rewrite <- app_assoc. reflexivity.
Qed.

Definition left_el_P (t : tree) : Prop := forall k f b,
  t = node k f \/ t = final f ->
  exists l', left_el f b = b++l'.

(* Lemma 2 *)
Theorem left_el_interior : forall f b,
  exists l', left_el f b = b++l'.
Proof.
  induction f using treelist_tree_rec with (P := left_el_P).
  - unfold left_el_P. intros. inversion H; inversion H0. subst. apply IHf.
  - unfold left_el_P. intros. inversion H; inversion H0. subst. apply IHf.
  - unfold left_el_P. intros. inversion H; inversion H0.
  - intros. unfold left_el. exists []. rewrite app_nil_r. reflexivity.
  - intros. destruct t eqn:e.
    + simpl. unfold left_el_P in IHf.
      assert (exists l', left_el f b0 = b0++l'). { apply IHf0. }
      inversion H. rewrite H0. destruct IHf with k t0 (b0 ++ x).
      * left. reflexivity.
      * exists (x ++ x0). rewrite H1. rewrite app_assoc. reflexivity.
    + simpl. unfold left_el_P in IHf.
      assert (exists l', left_el f b0 = b0++l'). { apply IHf0. }
      inversion H. rewrite H0. destruct IHf with zero t0 (b0 ++ x).
      * right. reflexivity.
      * exists (x ++ x0). rewrite H1. rewrite app_assoc. reflexivity.
    + simpl. destruct IHf0 with b0. rewrite H.
      exists (x++[(k,v)]). rewrite <- app_assoc. reflexivity.
Qed.

(* Lemma 2 *)
Theorem left_rec_interior : forall cn cf l,
  exists l', cursor_left cn cf l = (l++l').
Proof.
  induction cn,cf.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. destruct (point a t) eqn:e. destruct p.
    destruct IHcn with cf (left_el t1 l). rewrite H.
    assert (exists l', left_el t1 l = l++l') by (apply left_el_interior).
    inversion H0. rewrite H1. exists (x0++x). rewrite app_assoc. reflexivity.
Qed.

(* Lemma 2 *)
Theorem right_rec_interior : forall cn cf r,
  exists r', cursor_right cn cf r = (r++r').
Proof.
  induction cn,cf.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. exists []. rewrite app_nil_r. reflexivity.
  - intros. simpl. destruct (point a t) eqn:e. destruct p.
    destruct IHcn with cf (right_el t0 r). rewrite H.
    assert (exists r', right_el t0 r = r++r') by (apply right_el_interior).
    inversion H0. rewrite H1. exists (x0++x). rewrite app_assoc. reflexivity.
Qed.

(* I think these are now irrelevant:

Theorem cursor_elements'_rec : forall cn cf n f l r l' r',
  (n >= treelist_length f) ->
  cursor_elements' cn cf (left_el f l) r = (l',r') ->
  exists l'', cursor_elements' (n::cn) (f::cf) l r = (l'',r').
Proof.
  induction cn,cf; intros; apply point_treelist_length in H;
  simpl in H0; simpl; rewrite H; simpl; exists l'; apply H0.
Qed.

Theorem cursor_elements'_sides_indep : forall cn cf l1 l2 l' r r',
  cursor_elements' cn cf l1 r = (l',r') ->
  exists l'', cursor_elements' cn cf l2 r = (l'',r').
Proof.
  induction cn,cf; intros.
  - simpl in H. simpl. inversion H. subst. exists l2. reflexivity.
  - simpl in H. simpl. inversion H. subst. exists l2. reflexivity.
  - simpl in H. simpl. inversion H. subst. exists l2. reflexivity.
  - simpl in H. simpl. destruct (point a t).
    apply IHcn with (left_el t0 l1) l'. apply H.
Qed.
*)

(* Lemma 3 *)
(* If you split a list, the result of the elements of the first with the elements of the second is the same *)
Theorem cursor_right_elements1 : forall cn1 cf1 cn2 cf2 b,
  length cn1 = length cf1 -> length cn2 = length cf2 ->
  cursor_right (cn1++cn2) (cf1++cf2) b = cursor_right cn2 cf2 (cursor_right cn1 cf1 b).
Proof.
  induction cn1,cf1; intros; simpl.
  - reflexivity.
  - inversion H.
  - inversion H.
  - inversion H. clear H.
    destruct (point a t) eqn:e. destruct p.
    apply IHcn1. apply H2. apply H0.
Qed.

Theorem cursor_left_elements1 : forall cn1 cf1 cn2 cf2 b,
  length cn1 = length cf1 -> length cn2 = length cf2 ->
  cursor_left (cn1++cn2) (cf1++cf2) b = cursor_left cn2 cf2 (cursor_left cn1 cf1 b).
Proof.
  induction cn1,cf1; intros; simpl.
  - reflexivity.
  - inversion H.
  - inversion H.
  - inversion H. clear H.
    destruct (point a t) eqn:e. destruct p.
    apply IHcn1. apply H2. apply H0.
Qed.

(* List in increasing order *)
Inductive sorted_less : list (key * V) -> Prop :=
| sl_nil : sorted_less []
| sl_one : forall k v, sorted_less [(k,v)]
| sl_next : forall k1 v1 k2 v2 l,
  lt_key k1 k2 = true -> sorted_less ((k2,v2)::l) -> sorted_less ((k1,v1)::(k2,v2)::l).

(* List in decreasing order *)
Inductive sorted_more : list (key * V) -> Prop :=
| sm_nil : sorted_more []
| sm_one : forall k v, sorted_more [(k,v)]
| sm_next : forall k1 v1 k2 v2 l,
  lt_key k2 k1 = true -> sorted_more ((k2,v2)::l) -> sorted_more ((k1,v1)::(k2,v2)::l).

(* Theorem 4 *)
Theorem cursor_right_el_sorted : forall cn cf,
  cursor_correct (cn,cf) -> sorted_less (cursor_right cn cf []).
Proof. Admitted.

(* Theorem 4 *)
Theorem cursor_left_el_sorted : forall cn cf,
  cursor_correct (cn,cf) -> sorted_more (cursor_left cn cf []).
Proof. Admitted.

(** Theorems about next_node and prev_node *)

(* Helper for Invariants *)
Lemma point_next : forall f n f1 f1' f2 f2' o t,
  point n f = (f1, o, f2) ->
  point (S n) f = (f1', Some t, f2') ->
  f2 = tl_cons t f2'.
Proof.
  induction f.
  - intros. inversion H0.
  - intros. destruct n.
    + simpl in H. simpl in H0. destruct f.
      * inversion H0.
      * inversion H. inversion H0. reflexivity.
    + simpl in H. remember (S n) as n'. simpl in H0.
      destruct (point n f) eqn:e. destruct p. inversion H. subst. clear H.
      destruct (point (S n) f) eqn:e'. destruct p. inversion H0. subst. clear H0.
      apply IHf with n t2 t3 o. apply e. apply e'.
Qed.

(* Invariant 5 *)
Theorem cursor_right_elements4 : forall cn cf cn' cf' n f k f' t l1 l2 b k',
  cursor_correct_struct (cn,cf) ->
  next_node cn cf = Some (n::cn',f::cf',k') ->
  (* (cn,cf) <> (n::cn',f::cf') -> *)
  point n f = (l1,Some t,l2) ->
  t = node k f' \/ t = final f' ->
  cursor_right cn cf b = cursor_right (n::cn') (f::cf') (right_el f' b).
Proof.
  induction cn,cf; intros.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H0.
  - simpl in H0. destruct (point a t) eqn:e. destruct p. destruct o; try (destruct t3); destruct t1.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      * inversion H0.
      * inversion H0.
      * destruct (point n0 t1) eqn:e3. destruct p.
        destruct o. destruct t6.
        { inversion H0. subst. clear H0.
          simpl. rewrite e. destruct f. inversion H1.
          rewrite e3. simpl.
          assert (cursor_right cn cf b0 = cursor_right (n0::l) (t1::l0) (right_el (tl_cons t6 f) b0)).
          { apply IHcn with k2 (node k2 (tl_cons t6 f)) t5 t4 k'.
            inversion H. subst. apply cc_nil. apply H4. apply H4.
            apply e2.
            apply e3.
            left. reflexivity. }
          rewrite H0. simpl. rewrite e3. simpl in H1. inversion H1. subst.
          destruct H2. rewrite H2. reflexivity. rewrite H2. reflexivity. }
        { inversion H0. subst. clear H0.
          simpl. rewrite e. destruct f. inversion H1.
          rewrite e3. simpl.
          assert (cursor_right cn cf b0 = cursor_right (n0::l) (t1::l0) (right_el (tl_cons t6 f) b0)).
          { apply IHcn with k (final (tl_cons t6 f)) t5 t4 k'.
            inversion H. subst. apply cc_nil. apply H4. apply H4.
            apply e2.
            apply e3.
            right. reflexivity. }
          rewrite H0. simpl. rewrite e3. simpl in H1. inversion H1. subst.
          destruct H2. rewrite H2. reflexivity. rewrite H2. reflexivity. }
        { inversion H0. }
        { inversion H0. }
      * inversion H0.
    + destruct t1.
      * inversion H0. subst. remember (S a) as a'. simpl. rewrite e. rewrite H1.
        assert (tl_cons (node k1 t1) t4 = tl_cons t0 l2).
        { apply point_next with f a t2 l1 (Some (node k' t3)). apply e. subst. apply H1. }
        inversion H3. subst. inversion H2; inversion H4. subst.
        simpl. reflexivity.
      * inversion H0. subst. remember (S a) as a'. simpl. rewrite e. rewrite H1.
        assert (tl_cons (final t1) t4 = tl_cons t0 l2).
        { apply point_next with f a t2 l1 (Some (node k' t3)). apply e. subst. apply H1. }
        inversion H3. subst. inversion H2; inversion H4. subst.
        simpl. reflexivity.
      * admit. (* e: node and val in same treelist *)
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H0.
      inversion H0.
      destruct (point n0 t1) eqn:e3. destruct p. destruct o. destruct t6.
      { inversion H0. subst. clear H0.
        simpl. rewrite e. destruct f. inversion H1.
        rewrite e3. simpl.
        assert (cursor_right cn cf b0 = cursor_right (n0::l) (t1::l0) (right_el (tl_cons t6 f) b0)).
          { apply IHcn with k1 (node k1 (tl_cons t6 f)) t5 t4 k'.
            inversion H. subst. apply cc_nil. apply H4. apply H4.
            apply e2.
            apply e3.
            left. reflexivity. }
          rewrite H0. simpl. rewrite e3. simpl in H1. inversion H1. subst.
          destruct H2. rewrite H2. reflexivity. rewrite H2. reflexivity. }
      { inversion H0. subst. clear H0.
        simpl. rewrite e. destruct f. inversion H1.
        rewrite e3. simpl.
        assert (cursor_right cn cf b0 = cursor_right (n0::l) (t1::l0) (right_el (tl_cons t6 f) b0)).
          { apply IHcn with k (final (tl_cons t6 f)) t5 t4 k'.
            inversion H. subst. apply cc_nil. apply H4. apply H4.
            apply e2.
            apply e3.
            right. reflexivity. }
          rewrite H0. simpl. rewrite e3. simpl in H1. inversion H1. subst.
          destruct H2. rewrite H2. reflexivity. rewrite H2. reflexivity. }
      { inversion H0. }
      { inversion H0. }
      { inversion H0. }
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H0.
      inversion H0.
      destruct (point n0 t5) eqn:e3. destruct p. destruct o. destruct t8.
      { inversion H0. subst. clear H0.
        simpl. rewrite e. destruct f. inversion H1.
        rewrite e3. simpl. admit. }
      admit. admit. admit. admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

(* Helper for invariant *)
Lemma left_el_app : forall f1 f2 b,
  left_el (tl_app f1 f2) b = left_el f1 (left_el f2 b).
Proof.
  induction f1; intros.
  - reflexivity.
  - simpl. rewrite IHf1. reflexivity.
Qed.

(* Invariant 6 *)
Theorem cursor_left_elements4 : forall cn cf cn' cf' n f b f1 o f2 k,
  cursor_correct_struct (n::cn,f::cf) ->
  next_node (n::cn) (f::cf) = Some (cn',cf',k) ->
  (cn',cf') <> (n::cn,f::cf) ->
  point n f = (f1,o,f2) -> exists k f',
  (o = Some (node k f') /\ cursor_left (n::cn) (f::cf) (left_el f' b) = cursor_left cn' cf' b) \/
  (o = Some (final f') /\ cursor_left (n::cn) (f::cf) (left_el f' b) = cursor_left cn' cf' b) \/
  (o = None /\ cursor_left (n::cn) (f::cf) b = cursor_left cn' cf' b).
Proof.
  induction cn,cf; intros.
  - simpl in H0. rewrite H2 in H0. destruct o. destruct t.
    + exists k0,t. left. split. reflexivity. destruct f2. 2:destruct t0.
      * inversion H0.
      * inversion H0. remember (S n) as n'. simpl.
        destruct (point n f) eqn:e1. destruct p.
        destruct (point n' f) eqn:e2. destruct p.
        assert (t4 = tl_app t2 (tl_cons (node k t) tl_nil)).
        { apply point_prev with n f t1 t3 o0. inversion H2. subst. apply e1.
          rewrite <- Heqn'. apply e2. }
        rewrite H3. rewrite left_el_app. reflexivity.
      * inversion H0. remember (S n) as n'. simpl.
        destruct (point n f) eqn:e1. destruct p.
        destruct (point n' f) eqn:e2. destruct p.
        assert (t4 = tl_app t2 (tl_cons (node k t) tl_nil)).
        { apply point_prev with n f t1 t3 o0. inversion H2. subst. apply e1.
          rewrite <- Heqn'. apply e2. }
        rewrite H3. rewrite left_el_app. reflexivity.
      * inversion H0.
    + inversion H0.
    + inversion H0. subst. destruct H1. reflexivity.
    + inversion H0.
  - inversion H.
  - inversion H.
  - remember (a::cn) as cn1. remember (t::cf) as cf1.
    simpl in H0. rewrite H2 in H0.
    destruct (next_node cn1 cf1) eqn:e1; try (destruct p; destruct c);
    destruct o eqn:e2; destruct f2.
    + destruct l. 2:destruct l0.
      destruct t0. inversion H0. inversion H0. inversion H0. subst. destruct H1. reflexivity.
      destruct t0. inversion H0. inversion H0. inversion H0. subst. destruct H1. reflexivity.
      destruct t0. destruct (point n0 t1) eqn:e3. destruct p.
      destruct o0. destruct t4.
      { exists k1,t0. left. split. reflexivity.
        inversion H0. remember (n0::l) as cn2. remember (t1::l0) as cf2.
        simpl. rewrite H2. destruct t4. admit. (* shouldn't be possible, cuz a whole nil treelist... *)
        simpl. admit. } (* Actually need to investigate point a t, etc blahhh *)
      admit.
      admit.
      admit.
      admit.
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

(* Lemma 7 *)
Theorem next_correct_struct : forall cn cf c k,
  cursor_correct_struct (cn,cf) -> next_node cn cf = Some (c,k) -> cursor_correct_struct c.
Proof.
  induction cn,cf.
  - intros; simpl. simpl in H0. inversion H0.
  - intros; simpl. inversion H.
  - intros; simpl. inversion H.
  - intros. inversion H.
    + subst. simpl in H0. destruct (point a t) eqn:e. destruct p.
      destruct o. destruct t2; destruct t0; try (inversion H0).
      destruct t0; inversion H0; apply cc_first.
      apply H.
      apply cc_first.
      inversion H0.
    + subst. remember (n::ci) as cn'. remember (f::ct) as cf'.
      simpl in H0. destruct (point a t) eqn:e. destruct p.
      destruct o; destruct t0.
      * destruct t2. destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t2) eqn:e3. destruct p. destruct o. destruct t5.
        { inversion H0. apply cc_node with k3. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t2) eqn:e3. destruct p. destruct o. destruct t5.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        inversion H0. apply H.
      * destruct t2; destruct t0.
        { inversion H0. inversion H. apply cc_first. apply cc_node with k3.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k2.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t6.
        { inversion H0. apply cc_node with k4. apply IHcn with cf' k3. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k3. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t4) eqn:e3. destruct p. destruct o. destruct t7.
        { inversion H0. apply cc_node with k3. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t4) eqn:e3. destruct p. destruct o. destruct t7.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t6.
        { inversion H0. apply cc_node with k3. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k3.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k2.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k3.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
      * destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t4.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t3 t2. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t3 t2. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
      * apply point_none in e. inversion e.
    + subst. remember (n::ci) as cn'. remember (f::ct) as cf'.
      simpl in H0. destruct (point a t) eqn:e. destruct p.
      destruct o; destruct t0.
      * destruct t2. destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t2) eqn:e3. destruct p. destruct o. destruct t5.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t2) eqn:e3. destruct p. destruct o. destruct t5.
        { inversion H0. apply cc_node with k1. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t4 t3. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        inversion H0. apply H.
      * destruct t2; destruct t0.
        { inversion H0. inversion H. apply cc_first. apply cc_node with k2.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k1.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t6.
        { inversion H0. apply cc_node with k3. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k2. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t4) eqn:e3. destruct p. destruct o. destruct t7.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t4) eqn:e3. destruct p. destruct o. destruct t7.
        { inversion H0. apply cc_node with k1. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t6 t5. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t6.
        { inversion H0. apply cc_node with k2. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k1. apply H3. apply e2.
          apply point_lin_search with t5 t4. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k2.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k1.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
        { inversion H0. inversion H. apply cc_first. apply cc_node with k2.
          apply H7. apply H10. apply cc_final. apply H7. apply H10. }
      * destruct (next_node cn' cf') eqn:e2. destruct p. destruct c0.
        destruct l. inversion H0. destruct l0. inversion H0.
        destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t4.
        { inversion H0. apply cc_node with k1. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t3 t2. apply e3. }
        { inversion H0. apply cc_final. apply IHcn with cf' k0. apply H3. apply e2.
          apply point_lin_search with t3 t2. apply e3. }
        { inversion H0. }
        { inversion H0. }
        { inversion H0. }
      * apply point_none in e. inversion e.
Qed.

(* Helper for Lemma 7 *)
Lemma balance_carries_one : forall n f k f',
  balanced f ->
  (lin_search n f = Some (node k f') \/ lin_search n f = Some (final f')) ->
  balanced f'.
Proof.
  induction n; intros; destruct f.
  - inversion H0; inversion H1.
  - inversion H0; inversion H1; rewrite H3 in H; inversion H; inversion H2; subst.
    unfold balanced. exists n. apply H7.
    unfold balanced. exists n. apply H6.
  - inversion H0; inversion H1.
  - simpl in H0. apply IHn with f k.
    + inversion H. inversion H1; subst.
      exists 1. apply H4.
      exists (S n0). apply H6.
      exists 1. apply bf_nil.
    + apply H0.
Qed.

(* Helper for Lemma 7 *)
Lemma balance_carries : forall cn cf n f,
  cursor_correct_struct (n::cn,f::cf) ->
  rec_prop balanced (cn,cf) ->
  cn <> [] ->
  rec_prop balanced (n::cn,f::cf).
Proof.
  intros. inversion H0. destruct H1. auto.
  subst. apply rp_next. 2:apply H0.
  inversion H4. inversion H.
  - subst. apply balance_carries_one with n0 f0 k. apply H4. left. apply H12.
  - subst. apply balance_carries_one with n0 f0 Z0. apply H4. right. apply H12.
Qed.

(* Lemma 7 *)
Theorem next_node_balanced : forall cn cf c k,
  cursor_correct_struct (cn,cf) -> rec_prop balanced (cn,cf) ->
  next_node cn cf = Some (c,k) -> rec_prop balanced c.
Proof.
  induction cn,cf; intros.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H0. subst.
    assert (cursor_correct_struct (cn,cf)).
    { inversion H; subst. apply cc_nil. apply H5. apply H5. }
    assert (IHpart: forall c k, next_node cn cf = Some (c,k) -> rec_prop balanced c).
    { intros. apply IHcn with cf k0. apply H2. apply H7. apply H3. }
    assert (cursor_correct_struct c).
    { apply next_correct_struct with (a::cn) (t::cf) k. apply H. apply H1. }
    inversion H1. destruct (point a t) eqn:e1. destruct p.
    destruct o; try (destruct t2); destruct t0.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. destruct (point n t0). destruct p.
      2:inversion H6. destruct o. 2:inversion H6. destruct t5. 3:inversion H6.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k1. reflexivity.
        intros Hcontra. inversion Hcontra.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k1. reflexivity.
        intros Hcontra. inversion Hcontra.
    + destruct t0.
      { inversion H6. apply rp_next. apply H4. apply H7. }
      { inversion H6. apply rp_next. apply H4. apply H7. }
      destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. 2:inversion H6.
      destruct (point n t0) eqn:e3. destruct p. destruct o. destruct t6.
      { inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k2. reflexivity.
        intros Hcontra. inversion Hcontra. }
      { inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k2. reflexivity.
        intros Hcontra. inversion Hcontra. }
      inversion H6. inversion H6.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. destruct (point n t0). destruct p.
      2:inversion H6. destruct o. 2:inversion H6. destruct t5. 3:inversion H6.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. destruct (point n t4). destruct p.
      2:inversion H6. destruct o. 2:inversion H6. destruct t7. 3:inversion H6.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
    + inversion H6. apply H0.
    + inversion H6. apply H0.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. destruct (point n t0). destruct p.
      2:inversion H6. destruct o. 2:inversion H6. destruct t4. 3:inversion H6.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
    + destruct (next_node cn cf) eqn:e2. destruct p. destruct c0. destruct l. 2:destruct l0.
      inversion H6. inversion H6. destruct (point n t3). destruct p.
      2:inversion H6. destruct o. 2:inversion H6. destruct t6. 3:inversion H6.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
      * inversion H6. apply balance_carries.
        rewrite H8. apply H3.
        apply IHpart with k0. reflexivity.
        intros Hcontra. inversion Hcontra.
Qed.

(* Lemma 7 *)
Lemma next_node_sorted : forall cn cf c k,
  cursor_correct_struct (cn,cf) -> rec_prop sorted (cn,cf) ->
  next_node cn cf = Some (c,k) -> rec_prop sorted c.
Proof. Admitted.

(* Lemma 7 *)
Lemma next_node_fanout : forall cn cf c k,
  cursor_correct_struct (cn,cf) -> rec_prop fanout (cn,cf) ->
  next_node cn cf = Some (c,k) -> rec_prop fanout c.
Proof. Admitted.

(* Lemma 7 *)
Theorem next_node_correct : forall cn cf c k,
  cursor_correct (cn,cf) -> next_node cn cf = Some (c,k) -> cursor_correct c.
Proof.
  intros. destruct H. destruct H1. destruct H2.
  unfold cursor_correct. split. 2:split. 3:split.
  - apply next_correct_struct with cn cf k. apply H. apply H0.
  - apply next_node_balanced with cn cf k. apply H. apply H1. apply H0.
  - apply next_node_sorted with cn cf k. apply H. apply H2. apply H0.
  - apply next_node_fanout with cn cf k. apply H. apply H3. apply H0.
Qed.

Lemma next_node_none : forall cn cf cn' cf' k,
  next_node cn cf = Some (cn',cf',k) ->
  cn' <> [] /\ cf' <> [].
Proof.
  induction cn,cf; intros.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
  - simpl in H. destruct (point a t) eqn:e. destruct p.
    destruct t0; destruct o. destruct t0.
    * destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t2) eqn:e3. destruct p.
      destruct o; try (destruct t5); inversion H; split; intros Hcontra; inversion Hcontra.
      inversion H.
    * destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t2) eqn:e3. destruct p.
      destruct o; try (destruct t5); inversion H; split; intros Hcontra; inversion Hcontra.
      inversion H.
    * inversion H. split; intros Hcontra; inversion Hcontra.
    * destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t0) eqn:e3. destruct p.
      destruct o; try (destruct t4); inversion H; split; intros Hcontra; inversion Hcontra.
      inversion H.
    * destruct t3; destruct t0.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t0) eqn:e3. destruct p. destruct o. destruct t6.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. inversion H. inversion H.
      destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t4) eqn:e3. destruct p. destruct o. destruct t7.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. inversion H. inversion H.
      destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t4) eqn:e3. destruct p. destruct o. destruct t7.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. inversion H. inversion H.
      destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t0) eqn:e3. destruct p. destruct o. destruct t6.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. inversion H. inversion H.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
    * destruct (next_node cn cf) eqn:e2. destruct p. destruct c; destruct l. 2:destruct l0.
      inversion H. inversion H.
      destruct (point n t3) eqn:e3. destruct p. destruct o. destruct t6.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. split; intros Hcontra; inversion Hcontra.
      inversion H. inversion H. inversion H.
Qed.

(* Theorem 8 *)
Theorem cursor_elements_next : forall cn cf c k,
  cursor_correct_struct (cn,cf) ->
  next_node cn cf = Some (c,k) ->
  cursor_elements (cn,cf) = cursor_elements c.
Proof.
  intros. destruct cn,cf.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - simpl in H0. destruct (point n t) eqn:e. destruct p.
    destruct o. destruct t2.
    + admit. (* e should only have vals *)
    + admit. (* ditto *)
    + destruct t0. inversion H0. reflexivity.
      destruct t0. admit. admit. (* ditto *) inversion H0. reflexivity.
    + destruct t0. destruct (next_node cn cf) eqn:e2. destruct p. destruct c0.
      destruct l. 2:destruct l0. inversion H0. inversion H0.
      destruct (point n0 t0) eqn:e3. destruct p. destruct o. destruct t4.
      admit. admit. admit. admit. admit. admit.
Admitted.

(** Proofs about make_cursor *)

Fixpoint dec (n : nat) (f : treelist) : treelist :=
  match n with
  | O => f
  | S n' => 
    (match f with
     | tl_cons t f' => dec n' f'
     | tl_nil => tl_nil
     end)
  end.

Definition mc_correct_P (x : key) (t : tree) : Prop := forall k f n ci ct,
  t = node k f \/ t = final f ->
  cursor_correct_struct (n::ci,f::ct) ->
  cursor_correct_struct (make_cursor_rec x f ci (f::ct) O).

Lemma dec_nil : forall n,
  dec n tl_nil = tl_nil.
Proof. destruct n; reflexivity. Qed.

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

(* Theorem 9 *)
Theorem make_cursor_rec_correct : forall x f' n ci ct n' f,
  cursor_correct_struct (n::ci,f::ct) ->
  dec n' f = f' ->
  cursor_correct_struct (make_cursor_rec x f' ci (f::ct) n').
Proof.
  intros x. induction f' using treelist_tree_rec with (P := mc_correct_P x); try unfold mc_correct_P; intros.
  - inversion H; inversion H1. subst.
    apply IHf' with O. inversion H0.
    + apply cc_first.
    + apply cc_node with k. apply H4. apply H7.
    + apply cc_final. apply H4. apply H7.
    + reflexivity.
  - inversion H; inversion H1. subst.
    apply IHf' with O. inversion H0.
    + apply cc_first.
    + apply cc_node with k0. apply H4. apply H7.
    + apply cc_final. apply H4. apply H7.
    + reflexivity.
  - inversion H; inversion H1.
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
    + destruct f'. 2:apply cc_nil. apply IHf' with x O. right. reflexivity.
      * inversion H; subst.
        { apply cc_final. apply cc_first. apply dec_lin_search with tl_nil. apply H0. }
        { apply cc_final. apply cc_node with k. apply H3. apply H6. apply dec_lin_search with tl_nil. apply H0. }
        { apply cc_final. apply cc_final. apply H3. apply H6. apply dec_lin_search with tl_nil. apply H0. }
    + apply IHf'0 with n. apply H. rewrite dec_cont. rewrite H0. reflexivity.
    + inversion H; subst.
      * apply cc_first.
      * apply cc_node with k0. apply H3. apply H6.
      * apply cc_final. apply H3. apply H6.
Qed.

(* Theorem 9 *)
Theorem make_cursor_correct : forall x f,
  cursor_correct_struct (make_cursor x f).
Proof.
  intros. unfold make_cursor. apply make_cursor_rec_correct with O.
  - apply cc_first.
  - reflexivity.
Qed.

(* Theorem 10 *)
Theorem make_cursor_right : forall cn cf x f k v l,
  make_cursor x f = (cn,cf) ->
  cursor_right cn cf [] = (k,v)::l ->
  lt_key k x <> true.
Proof. Admitted.

(* Theorem 10 *)
Theorem make_cursor_left : forall cn cf x f k v l,
  make_cursor x f = (cn,cf) ->
  cursor_left cn cf [] = (k,v)::l ->
  lt_key k x = true.
Proof. Admitted.

(** Proofs about move_to_next and move_to_prev *)

(* Theorem 11 *)
Theorem move_to_next_correct : forall c,
  cursor_correct c ->
  cursor_correct (move_to_next c).
Proof.
  intros. destruct c. simpl. destruct (next_node l l0) eqn:e.
  destruct p. destruct c. destruct l1.
  - apply H.
  - assert (cursor_correct (n::l1,l2)).
    { apply next_node_correct with l l0 k. apply H. apply e. }
    destruct H0. destruct H1. destruct H2.
    split. 2:split. 3:split.
    + inversion H0. apply cc_first.
      apply cc_node with k0. apply H6. apply H8.
      apply cc_final. apply H6. apply H8.
    + inversion H1. apply rp_next. apply H6. apply H8.
    + inversion H2. apply rp_next. apply H6. apply H8.
    + inversion H3. apply rp_next. apply H6. apply H8.
  - apply H.
Qed.

(* Theorem 11 *)
Theorem move_to_prev_correct : forall c,
  cursor_correct c ->
  cursor_correct (move_to_prev c).
Proof. Admitted.

(* Theorem 12 *)
Theorem move_to_next_el : forall c l r k v,
  cursor_correct c ->
  cursor_elements c = (l,(k,v)::r) ->
  cursor_elements (move_to_next c) = ((k,v)::l,r).
Proof. Admitted.

(* Theorem 13 *)
Theorem move_to_prev_el : forall c l r k v,
  cursor_correct c ->
  cursor_elements c = ((k,v)::l,r) ->
  cursor_elements (move_to_next c) = (l,(k,v)::r).
Proof. Admitted.

(* Theorem 14 *)
(* Not 100% on this statement *)
Theorem move_to_next_none : forall cn cf,
  cursor_correct (cn,cf) ->
  (cursor_right cn cf [] = [] <-> move_to_next (cn,cf) = (cn,cf)).
Proof. Admitted.

(* Theorem 14 *)
(* ditto *)
Theorem move_to_prev_none : forall cn cf,
  cursor_correct (cn,cf) ->
  (cursor_left cn cf [] = [] <-> move_to_prev (cn,cf) = (cn,cf)).
Proof. Admitted.

(** Proofs about GET *)

(* Theorem 15 *)
Theorem get_correct : forall cn cf k v l,
  cursor_correct (cn,cf) ->
  cursor_right cn cf [] = (k,v)::l ->
  get_tree (cn,cf) = Some (val k v).
Proof. Admitted.

(** Proofs about INSERT *)

Definition key_rel (k : key) (c : cursor) : bool :=
  match get_key c with
  | Some k1 =>
    (match get_key (move_to_prev c) with
     | Some k2 => if andb (lt_key k2 k) (negb (lt_key k1 k)) then true else false
     | None => if negb (lt_key k1 k) then true else false
     end)
  | None =>
    (match get_key (move_to_prev c) with
     | Some k2 => if lt_key k2 k then true else false
     | None => true
     end)
  end.

(* Lemma 16 *)
Lemma bad_cursor_insert_same : forall c k v,
  key_rel k c <> true -> insert k v c = c.
Proof. Admitted.

(* Theorems 17 & 18 *)
Theorem insert_correct : forall c k v,
  cursor_correct c -> cursor_correct (insert k v c).
Proof. Admitted.

(* Theorem 19 *)
Theorem insert_eq_elements : forall c k v' v l r,
  cursor_elements c = (l,(k,v')::r) -> cursor_elements (insert k v c) = (l,(k,v)::r).
Proof. Admitted.

(* Theorem 20 *)
Theorem insert_neq_elements : forall c k v l r,
  get_key c <> Some k -> cursor_elements c = (l,r) -> cursor_elements (insert k v c) = ((k,v)::l,r).
Proof. Admitted.

(** Tests *)

Compute (treelist_depth ex_treelist).

Compute (treelist_depth ex_treelist').

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