Require Import Extract.
Require Import Coq.Lists.List.
Require Import Recdef.
Require Import FunInd.
Require Import Coq.Numbers.BinNums.
Export ListNotations.
(* How to limit unneeded dependencies? *)

Definition key := Z.

Section BTREES.
Variable V : Type.
Variable b : nat.

(* Defining tree & related types *)

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

(* Defining helper fixpoints for tree operations *)

Fixpoint eq_pos (p1 : positive) (p2 : positive) :=
  match (p1,p2) with
  | (xI p1',xI p2') => eq_pos p1' p2'
  | (xO p1',xO p2') => eq_pos p1' p2'
  | (xH,xH) => true
  | (_,_) => false
  end.

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

(* Creating test data and running tests *)

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
Proof. intros. simpl. subst. admit. intros. simpl. subst. admit. Admitted.

(* Proofs about them *)

Fixpoint zip (f1 : treelist) (f2 : treelist) : treelist :=
  match f1 with
  | cons t f' => cons t (zip f' f2)
  | nil => f2
  end.

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

Inductive splitpair : Type :=
| One : treelist -> splitpair
| Two : treelist -> key -> treelist -> splitpair.

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

(* Should this get the cursor, or make it? *)
Fixpoint insert (x : key) (v : V) (c : cursor) : treelist :=
  match c with
  | (c1, cons (val x' v') c2)::c' =>
    if (eq_key x' x) then insert_up (zip c1 (cons (val x v) c2)) c'
    else insert_up (zip c1 (cons (val x v) (cons (val x' v') c2))) c'
  | [] => cons (val x v) nil
  | _ => cons (val x v) nil (* shouldn't happen *)
  end.

Parameter range : key -> key -> list V.
(* list key * V? *)
(* Relies on move-to-next, which needs to be implemented *)

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

(* Theorems etc *)

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
  lin_search x f = (f1,f2) -> zip f1 f2 = f.
Proof.
  intros x f. induction f as [|t f'].
  - intros. inversion H. reflexivity.
  - intros. induction t.
    * destruct f1. simpl. inversion H. destruct (lt_key k x).
      + destruct (lin_search x f') in H1. inversion H1.
      + inversion H1. reflexivity.
      + simpl. inversion H. destruct (lt_key k x). destruct (lin_search x f') in H1.
        inversion H1. subst. assert (zip f1 f2 = f'). apply IHf'. apply lin_search_partial in H. apply H.
        rewrite H0. reflexivity.
        inversion H1.
    * destruct f1.
      + simpl. inversion H. destruct f'. reflexivity. 
      admit.
      + admit.
    * admit.
Admitted.

(* Treelist correct *)
Inductive treelist_correct_node : treelist -> Prop :=
| fcn_nil : treelist_correct_node nil
| fcn_final : forall f f', treelist_correct_node f -> treelist_correct_node (cons (final f') f)
| fcn_node : forall f k f', treelist_correct_node f -> treelist_correct_node (cons (node k f') f).

Inductive treelist_correct_val : treelist -> Prop :=
| fcv_nil : treelist_correct_val nil
| fcv_val : forall k v f, treelist_correct_val f -> treelist_correct_val (cons (val k v) f).

Definition treelist_correct (f : treelist) : Prop :=
  treelist_correct_node f \/ treelist_correct_val f.
(* What about ordering constraints? *)

(* Tree's are automatically structurally correct *)

(* Cursor correct *)
(* Must have at least one pair in it -- [] is not correct! *)
(* Inductively, the zip of a new pair must match the first sub-tree of the previous pair *)
Definition is_in (f1 f2 : treelist) (c : cursor) : Prop :=
  exists f1' f2' t c', c = (f1', cons t f2')::c' /\
  ((exists k, t = node k (zip f1 f2)) \/ t = final (zip f1 f2)). (* This is kinda ugly... *)

Inductive cursor_correct : cursor -> Prop :=
| cc_one : forall f1 f2, treelist_correct f1 -> treelist_correct f2 -> cursor_correct [(f1,f2)]
| cc_next : forall f1 f2 c, treelist_correct f1 -> treelist_correct f2 ->
            cursor_correct c -> is_in f1 f2 c -> cursor_correct ((f1,f2)::c).

(* Treelist in order property *)
(* I believe also encompasses treelist correctness *)
Inductive treelist_sorted : treelist -> Prop :=
| ts_nil : treelist_sorted nil
| ts_one : forall t, treelist_sorted (cons t nil)
| ts_node : forall k1 f1 k2 f2 f', lt_key k1 k2 = true -> treelist_sorted (cons (node k2 f2) f') ->
            treelist_sorted (cons (node k1 f1) (cons (node k2 f2) f'))
| ts_final : forall f1 k2 f2 f', treelist_sorted (cons (node k2 f2) f') ->
             treelist_sorted (cons (final f1) (cons (node k2 f2) f'))
| ts_val : forall k1 v1 k2 v2 f', lt_key k1 k2 = true -> treelist_sorted (cons (val k2 v2) f') ->
           treelist_sorted (cons (val k1 v1) (cons (val k2 v2) f')).

(* Balance property *)
Inductive balanced_treelist : nat -> treelist -> Prop :=
| bf_nil : forall n, balanced_treelist n nil
| bf_next : forall n t f', balanced_tree n t -> balanced_treelist n f' -> balanced_treelist n (cons t f')
with balanced_tree : nat -> tree -> Prop :=
| bt_val : forall k v, balanced_tree 1 (val k v) (* Should be 1, or 0? *)
| bt_node : forall n k f, balanced_treelist n f -> balanced_tree (S n) (node k f)
| bt_final : forall n f, balanced_treelist n f -> balanced_tree (S n) (final f).

(* Balance property on root *)
Definition balanced (f : treelist) : Prop := exists n, balanced_treelist n f.

End BTREES.
