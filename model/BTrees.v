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
  | node : key -> forest -> tree
  | final : forest -> tree
  | val : key -> V -> tree
with forest : Type :=
  | nil : forest
  | cons : tree -> forest -> forest.

Scheme tree_forest_rec := Induction for tree Sort Type
with forest_tree_rec := Induction for forest Sort Type.

Definition cursor : Type := (list (forest * forest)).

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

Fixpoint forest_depth (f : forest) : nat :=
  match f with
  | nil => O
  | cons t f => max_nat (tree_depth t) (forest_depth f)
  end
with tree_depth (t : tree) : nat :=
  match t with
  | node _ f => S (forest_depth f)
  | final f => S (forest_depth f)
  | val _ _ => S O
  end.

(* Creating test data and running tests *)

Definition pos_one : key := Zpos xH.
Definition neg_one : key := Zneg xH.
Definition zero : key := Z0.
Definition pos_six : key := Zpos (xO (xI xH)).
Definition default : V. Admitted.

Definition ex_forest : forest :=
  cons (node neg_one
    (cons (val neg_one default)
    (cons (val pos_one default) nil)))
  (cons (final
    (cons (val pos_six default) nil))
  nil).

Compute (forest_depth ex_forest).

Definition ex_forest' : forest :=
  cons (final ex_forest) nil.

Compute (forest_depth ex_forest').

Definition ex_forest'' : forest :=
  cons (val zero default) nil.

Compute (forest_depth ex_forest'').

(* Functions to create a cursor (tree split) at a given key *)

Fixpoint lin_search (x : key) (f : forest) : forest * forest :=
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

Function make_cursor (x: key) (f : forest) (c : cursor) {measure forest_depth f} : cursor :=
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

Fixpoint zip (f1 : forest) (f2 : forest) : forest :=
  match f1 with
  | cons t f' => cons t (zip f' f2)
  | nil => f2
  end.

(* Returns the value for key x if it exists, or None otherwise. *)
Fixpoint lookup (x : key) (f : forest) : option V :=
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
| One : forest -> splitpair
| Two : forest -> key -> forest -> splitpair.

Fixpoint forest_length (f : forest) : nat :=
  match f with
  | nil => O
  | cons t f' => S (forest_length f')
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
Fixpoint split (f : forest) (n : nat) : splitpair :=
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

(* Needs work *)
(* Where exactly should the split happen? (floor or ceiling of len/2?) *)
Fixpoint decide_split (f : forest) : splitpair :=
  if (Nat.leb (forest_length f) b)
  then One f
  else split f (div_two (forest_length f) false).

Fixpoint insert_up (f : forest) (c : cursor) : forest :=
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
Fixpoint insert (x : key) (v : V) (c : cursor) : forest :=
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

Fixpoint get_first (f : forest) : (forest * forest) :=
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
    * intros. simpl in H. destruct a. destruct f0.
      + destruct (move_to_next c). apply H.
        destruct p. inversion H.
      + destruct f0. destruct (move_to_next c). apply H.
        destruct p. inversion H. inversion H.
  - intros. subst. simpl. reflexivity.
Qed.
(* Representation invariant for cursors -- what makes a cursor "valid" or "invalid" *)
(* Validity predicate for B+trees *)
(* Theorem: if a B+tree is valid, then doing an operation on it returns a valid cursor *)
(* Find appropriate subtree
   Insert recursively into it
   Check if the tree produced has too many keys, if so split it
   Return the given tree with possibly another key added from a split
   Let the caller deal with possibly splitting t
*)

(* Theorems etc *)

Theorem lin_search_preserves_forest : forall (x : key) (f f1 f2 : forest),
  lin_search x f = (f1,f2) -> zip f1 f2 = f.
Proof.
  intros. induction f as [|t f'].
  - inversion H. reflexivity.
  - induction t.
    * inversion H. destruct (lt_key k x).
      admit. admit. Admitted.

Theorem insert_lookup_correct : forall (x : key) (v : V) (f : forest),
  lookup x (insert x v (make_cursor x f [])) = Some v.
Admitted.

Theorem insert_neq_correct : forall (x1 x2 : key) (v : V) (f : forest),
  x1 <> x2 ->
  lookup x1 (insert x2 v (make_cursor x2 f [])) = lookup x1 f.
Admitted.

End BTREES.
(* Theorem for zipping a cursor back into the original b+tree *)

(* balance property *)
(* insert preserves balance property *)

(* If you insert, it's still a b+tree *)

(* range returns everything in the tree between the two keys *)

(* If range returns something, then it was in the tree and is between the two keys *)

(* Version of ADT Module TABLE that's appropriate for cursors *)
(* Copy of maps but with cursors as reference implementation *)
(* Fit b+trees into module & prove theorems *)

(* finish & prove insertion *)

(* Start writing actual paper! *)
(* 2nd reader hasn't worked with VFA, but does understand correctness proofs, abstract data types, etc. *)
(* ie that stuff is standard *)