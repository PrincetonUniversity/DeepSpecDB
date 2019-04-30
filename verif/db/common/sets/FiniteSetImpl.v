(************************************************************************************)
(**                                                                                 *)
(**                             The SQLEngines Library                              *)
(**                                                                                 *)
(**            LRI, CNRS & Université Paris-Sud, Université Paris-Saclay            *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.
(** Finite sets as records, in order to have them compatible with the section mechanism of Coq. #<br>#
    This file is simply an adaptation of the finite sets of Letouzey, from the standard library of Coq. *)


Require Import FSets.

Require Import OrderedSet (*BoolFacts ListFacts ListPermut ListSort*).

Require Import ZArith.

Require Import FunInd.

Import Int.
Import Z_as_Int.

(** How to build finite sets as records, adapted from MSet.AVL.v *)
Section Make.
Local Open Scope lazy_bool_scope.

Hypothesis elt : Type.
Hypothesis Elt : Oeset.Rcd elt.

Notation eq_elt := (fun x y => Oeset.compare Elt x y = Eq).
Notation lt_elt := (fun x y => Oeset.compare Elt x y = Lt).
Notation gt_elt := (fun x y => Oeset.compare Elt x y = Gt).

Lemma equiv_eq_elt : Equivalence eq_elt.
Proof.
split.
intro; apply Oeset.compare_eq_refl.
intros x y H; rewrite Oeset.compare_lt_gt, H; apply refl_equal.
do 3 intro; apply Oeset.compare_eq_trans.
Qed.

Lemma st_ord_lt_elt : StrictOrder lt_elt.
Proof.
split.
intros x Hx; rewrite (Oeset.compare_eq_refl Elt x) in Hx; discriminate.
do 3 intro; apply (Oeset.compare_lt_trans Elt).
Qed.

Lemma proper_e_e_lt_elt : Proper (eq_elt ==> eq_elt ==> iff) lt_elt.
Proof.
intros x x' Hx y y' Hy; split; intro H.
apply Oeset.compare_eq_lt_trans with x.
rewrite Oeset.compare_lt_gt, Hx; apply refl_equal.
apply Oeset.compare_lt_eq_trans with y; assumption.
apply Oeset.compare_eq_lt_trans with x'.
assumption.
apply Oeset.compare_lt_eq_trans with y'; [assumption | ].
rewrite Oeset.compare_lt_gt, Hy; apply refl_equal.
Qed.

Lemma lt_gt_elt : forall x y, lt_elt x y <-> gt_elt y x.
Proof.
intros x y; simpl; rewrite (Oeset.compare_lt_gt Elt x y).
case (Oeset.compare Elt y x); simpl.
split; intro Abs; discriminate.
split; intro Abs; discriminate.
split; intro; apply refl_equal.
Qed.

(** ** Trees

   The fourth field of [Node] is the height of the tree *)

Notation int := (Z_as_Int.t).

Inductive tree :=
  | Leaf : tree
  | Node : tree -> elt -> tree -> int -> tree.

(** ** Basic functions on trees: height and cardinal *)

Definition height (s : tree) : int :=
  match s with
  | Leaf => Z0
  | Node _ _ _ h => h
  end.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0%nat
   | Node l _ r _ => S (cardinal l + cardinal r)
  end.

(** ** Empty Set *)

Definition empty := Leaf.

(** ** Emptyness test *)

Definition is_empty s :=
  match s with Leaf => true | _ => false end.

(** ** Membership *)

(** The [mem] function is deciding membership. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x s :=
   match s with
     |  Leaf => false
     |  Node l y r _ => match Oeset.compare Elt x y with
             | Lt => mem x l
             | Eq => true
             | Gt => mem x r
         end
   end.

(** ** Singleton set *)

Definition singleton x := Node Leaf x Leaf (1%Z).

(** ** Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x r :=
   Node l x r (Z.max (height l) (height r) + 1)%Z.

(** [bal l x r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Definition bal l x r :=
  let hl := height l in
  let hr := height r in
  if gt_le_dec hl (hr+2) then
    match l with
     | Leaf => assert_false l x r
     | Node ll lx lr _ =>
       if ge_lt_dec (height ll) (height lr) then
         create ll lx (create lr x r)
       else
         match lr with
          | Leaf => assert_false l x r
          | Node lrl lrx lrr _ =>
              create (create ll lx lrl) lrx (create lrr x r)
         end
    end
  else
    if gt_le_dec hr (hl+2) then
      match r with
       | Leaf => assert_false l x r
       | Node rl rx rr _ =>
         if ge_lt_dec (height rr) (height rl) then
            create (create l x rl) rx rr
         else
           match rl with
            | Leaf => assert_false l x r
            | Node rll rlx rlr _ =>
                create (create l x rll) rlx (create rlr rx rr)
           end
      end
    else
      create l x r.

(** ** Insertion *)

Fixpoint add x s := match s with
   | Leaf => Node Leaf x Leaf 1%Z
   | Node l y r h =>
      match Oeset.compare Elt x y with
         | Lt => bal (add x l) y r
         | Eq => Node l y r h
         | Gt => bal l y (add x r)
      end
  end.

(** ** Join

    Same as [bal] but does not assume anything regarding heights
    of [l] and [r].
*)

Fixpoint join l : elt -> tree -> tree :=
  match l with
    | Leaf => add
    | Node ll lx lr lh => fun x =>
       fix join_aux (r : tree) : tree := match r with
          | Leaf =>  add x l
          | Node rl rx rr rh =>
               if gt_le_dec lh (rh+2) then bal ll lx (join lr x r)
               else if gt_le_dec rh (lh+2) then bal (join_aux rl) rx rr
               else create l x r
          end
  end.

(** ** Extraction of minimum element

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node l x r h]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x r : tree * elt :=
  match l with
    | Leaf => (r,x)
    | Node ll lx lr lh =>
       let (l',m) := remove_min ll lx lr in (bal l' x r, m)
  end.

(** ** Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Definition merge s1 s2 :=  match s1,s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | _, Node l2 x2 r2 h2 =>
        let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
end.

(** ** Deletion *)

Fixpoint remove x s := match s with
  | Leaf => Leaf
  | Node l y r h =>
      match Oeset.compare Elt x y with
         | Lt => bal (remove x l) y r
         | Eq => merge l r
         | Gt => bal l  y (remove x r)
      end
   end.

(** ** Minimum element *)

Fixpoint min_elt s := match s with
   | Leaf => None
   | Node Leaf y _  _ => Some y
   | Node l _ _ _ => min_elt l
end.

(** ** Maximum element *)

Fixpoint max_elt s := match s with
   | Leaf => None
   | Node _ y Leaf  _ => Some y
   | Node _ _ r _ => max_elt r
end.

(** ** Any element *)

Definition choose := min_elt.

(** ** Concatenation

    Same as [merge] but does not assume anything about heights.
*)

Definition concat s1 s2 :=
   match s1, s2 with
      | Leaf, _ => s2
      | _, Leaf => s1
      | _, Node l2 x2 r2 _ =>
            let (s2',m) := remove_min l2 x2 r2 in
            join s1 m s2'
   end.

(** ** Splitting

    [split x s] returns a triple [(l, present, r)] where
    - [l] is the set of elements of [s] that are [< x]
    - [r] is the set of elements of [s] that are [> x]
    - [present] is [true] if and only if [s] contains  [x].
*)

Record triple := mktriple { t_left : tree; t_in:bool; t_right : tree }.
Notation "<< l , b , r >>" := (mktriple l b r) (at level 9).

Fixpoint split x s : triple := match s with
  | Leaf => << Leaf, false, Leaf >>
  | Node l y r h =>
     match Oeset.compare Elt x y with
      | Lt => let (ll,b,rl) := split x l in << ll, b, join rl y r >>
      | Eq => << l, true, r >>
      | Gt => let (rl,b,rr) := split x r in << join l y rl, b, rr >>
     end
 end.

(** ** Intersection *)

Fixpoint inter s1 s2 := match s1, s2 with
    | Leaf, _ => Leaf
    | _, Leaf => Leaf
    | Node l1 x1 r1 h1, _ =>
            let (l2',pres,r2') := split x1 s2 in
            if pres then join (inter l1 l2') x1 (inter r1 r2')
            else concat (inter l1 l2') (inter r1 r2')
    end.

(** ** Difference *)

Fixpoint diff s1 s2 := match s1, s2 with
 | Leaf, _ => Leaf
 | _, Leaf => s1
 | Node l1 x1 r1 h1, _ =>
    let (l2',pres,r2') := split x1 s2 in
    if pres then concat (diff l1 l2') (diff r1 r2')
    else join (diff l1 l2') x1 (diff r1 r2')
end.

(** ** Union *)

(** In ocaml, heights of [s1] and [s2] are compared each time in order
   to recursively perform the split on the smaller set.
   Unfortunately, this leads to a non-structural algorithm. The
   following code is a simplification of the ocaml version: no
   comparison of heights. It might be slightly slower, but
   experimentally all the tests I've made in ocaml have shown this
   potential slowdown to be non-significant. Anyway, the exact code
   of ocaml has also been formalized thanks to Function+measure, see
   [ocaml_union] in [MSetFullAVL].
*)

Fixpoint union s1 s2 :=
 match s1, s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | Node l1 x1 r1 h1, _ =>
     let (l2',_,r2') := split x1 s2 in
     join (union l1 l2') x1 (union r1 r2')
 end.

(** ** Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list elt) (s : tree) : list elt :=
  match s with
   | Leaf => acc
   | Node l x r _ => elements_aux (x :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux nil.

(** ** Filter *)

Fixpoint filter_acc (f : elt -> bool) acc s := match s with
  | Leaf => acc
  | Node l x r h =>
     filter_acc f (filter_acc f (if f x then add x acc else acc) l) r
 end.

Definition filter f := filter_acc f Leaf.


(** ** Partition *)

Fixpoint partition_acc (f : elt -> bool) (acc : tree * tree) (s : tree) : tree * tree :=
  match s with
   | Leaf => acc
   | Node l x r _ =>
      let (acct,accf) := acc in
      partition_acc f
        (partition_acc f
           (if f x then (add x acct, accf) else (acct, add x accf)) l) r
  end.

Definition partition f := partition_acc f (Leaf, Leaf).

(** ** [for_all] and [exists] *)

Fixpoint for_all (f : elt -> bool) s := match s with
  | Leaf => true
  | Node l x r _ => f x &&& for_all f l &&& for_all f r
end.

Fixpoint exists_ (f : elt -> bool) s := match s with
  | Leaf => false
  | Node l x r _ => f x || exists_ f l || exists_ f r
end.

(** ** Fold *)

Fixpoint fold (A : Type) (f : elt -> A -> A) (s : tree) : A -> A :=
 fun a => match s with
  | Leaf => a
  | Node l x r _ => fold f r (f x (fold f l a))
 end.
Arguments fold {A} f s a.


(** ** Subset *)

(** In ocaml, recursive calls are made on "half-trees" such as
   (Node l1 x1 Leaf _) and (Node Leaf x1 r1 _). Instead of these
   non-structural calls, we propose here two specialized functions for
   these situations. This version should be almost as efficient as
   the one of ocaml (closures as arguments may slow things a bit),
   it is simply less compact. The exact ocaml version has also been
   formalized (thanks to Function+measure), see [ocaml_subset] in
   [MSetFullAVL].
 *)

Fixpoint subsetl (subset_l1: tree -> bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node l2 x2 r2 h2 =>
     match Oeset.compare Elt x1 x2 with
      | Eq => subset_l1 l2
      | Lt => subsetl subset_l1 x1 l2
      | Gt => mem x1 r2 &&& subset_l1 s2
     end
 end.

Fixpoint subsetr (subset_r1 : tree -> bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node l2 x2 r2 h2 =>
     match Oeset.compare Elt x1 x2 with
      | Eq => subset_r1 r2
      | Lt => mem x1 l2 &&& subset_r1 s2
      | Gt => subsetr subset_r1 x1 r2
     end
 end.

Fixpoint subset s1 s2 : bool := match s1, s2 with
  | Leaf, _ => true
  | Node _ _ _ _, Leaf => false
  | Node l1 x1 r1 h1, Node l2 x2 r2 h2 =>
     match Oeset.compare Elt x1 x2 with
      | Eq => subset l1 l2 &&& subset r1 r2
      | Lt => subsetl (subset l1) x1 l2 &&& subset r1 s2
      | Gt => subsetr (subset r1) x1 r2 &&& subset l1 s2
     end
 end.

(** ** A new comparison algorithm suggested by Xavier Leroy

    Transformation in C.P.S. suggested by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [MSetFullAVL]. The following code with
    continuations computes dramatically faster in Coq, and
    should be almost as efficient after extraction.
*)

(** Enumeration of the elements of a tree *)

Inductive enumeration :=
 | End : enumeration
 | More : elt -> tree -> enumeration -> enumeration.


(** [cons t e] adds the elements of tree [t] on the head of
    enumeration [e]. *)

Fixpoint cons s e : enumeration :=
 match s with
  | Leaf => e
  | Node l x r h => cons l (More x r e)
 end.

(** One step of comparison of elements *)

Definition compare_more x1 (cont:enumeration->comparison) e2 :=
 match e2 with
 | End => Gt
 | More x2 r2 e2 =>
     match Oeset.compare Elt x1 x2 with
      | Eq => cont (cons r2 e2)
      | Lt => Lt
      | Gt => Gt
     end
 end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint compare_cont s1 (cont:enumeration->comparison) e2 :=
 match s1 with
  | Leaf => cont e2
  | Node l1 x1 r1 _ =>
     compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition compare_end e2 :=
 match e2 with End => Eq | _ => Lt end.

(** The complete comparison *)

Definition compare s1 s2 := compare_cont s1 compare_end (cons s2 End).

(** ** Equality test *)

Definition equal s1 s2 : bool :=
 match compare s1 s2 with
  | Eq => true
  | _ => false
 end.


(** * Invariants *)

(** ** Occurrence in a tree *)

Inductive InT (x : elt) : tree -> Prop :=
  | IsRoot : forall l r h y, eq_elt x y -> InT x (Node l y r h)
  | InLeft : forall l r h y, InT x l -> InT x (Node l y r h)
  | InRight : forall l r h y, InT x r -> InT x (Node l y r h).

Definition In := InT.

(** EC : Added for compatibilty with (fun x y => Oeset.compare Elt x y = Eq), the equivalence
     relation used instead of Leibniz equality. *)

Lemma eq_elt_InT_compat : 
   forall x y, eq_elt x y -> (forall s, InT x s <-> InT y s).
Proof.
intros x y Hxy s; induction s; split; intro H; inversion H; subst.
apply IsRoot; refine (Oeset.compare_eq_trans Elt _ _ _ _ H1).
rewrite Oeset.compare_lt_gt, Hxy; apply refl_equal.
apply InLeft; rewrite <- IHs1; assumption.
apply InRight; rewrite <- IHs2; assumption.
apply IsRoot; refine (Oeset.compare_eq_trans Elt _ _ _ Hxy H1).
apply InLeft; rewrite IHs1; assumption.
apply InRight; rewrite IHs2; assumption.
Qed.

(** ** Some shortcuts *)

Definition Equal s s' := forall a : elt, InT a s <-> InT a s'.
Definition Subset s s' := forall a : elt, InT a s -> InT a s'.
Definition Empty s := forall a : elt, ~ InT a s.
Definition For_all (P : elt -> Prop) s := forall x, InT x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, InT x s /\ P x.

(** ** Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x]
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y, InT y s -> lt_elt y x.
Definition gt_tree x s := forall y, InT y s -> lt_elt x y.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x l r h, bst l -> bst r ->
     lt_tree x l -> gt_tree x r -> bst (Node l x r h).

(** [bst] is the (decidable) invariant our trees will have to satisfy. *)

Definition IsOk := bst.

Class Ok (s : tree) : Prop := ok : bst s.

Instance bst_Ok s (Hs : bst s) : Ok s := { ok := Hs }.

Fixpoint ltb_tree x s :=
 match s with
  | Leaf => true
  | Node l y r _ =>
     match Oeset.compare Elt x y with
      | Gt => ltb_tree x l &&& ltb_tree x r
      | _ => false
     end
 end.

Fixpoint gtb_tree x s :=
 match s with
  | Leaf => true
  | Node l y r _ =>
     match Oeset.compare Elt x y with
      | Lt => gtb_tree x l &&& gtb_tree x r
      | _ => false
     end
 end.

Fixpoint isok s :=
 match s with
  | Leaf => true
  | Node l x r _ => isok l &&& isok r &&& ltb_tree x l &&& gtb_tree x r
 end.


(** * Correctness proofs *)

(** * Automation and dedicated tactics *)

Scheme tree_ind2 := Induction for tree Sort Prop.

Local Hint Resolve (Oeset.compare_eq_refl Elt) (Oeset.compare_eq_trans Elt) 
     (Oeset.compare_eq_lt_trans Elt)  (Oeset.compare_lt_eq_trans Elt)
     (Oeset.compare_lt_trans Elt) @ok.
Local Hint Immediate (Oeset.compare_eq_sym Elt) (Oeset.compare_lt_gt Elt).
Local Hint Unfold In lt_tree gt_tree.
Local Hint Constructors InT bst.
Local Hint Unfold Ok.

Tactic Notation "factornode" ident(l) ident(x) ident(r) ident(h)
 "as" ident(s) :=
 set (s:=Node l x r h) in *; clearbody s; clear l x r h.

(** Automatic treatment of [Ok] hypothesis *)

Ltac inv_ok := match goal with
 | H:Ok (Node _ _ _ _) |- _ => inversion_clear H; inv_ok
 | H:Ok Leaf |- _ => clear H; inv_ok
 | H:bst ?x |- _ => change (Ok x) in H; inv_ok
 | _ => idtac
end.

(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node _ _ _ _))] *)

Ltac is_tree_constr c :=
  match c with
   | Leaf => idtac
   | Node _ _ _ _ => idtac
   | _ => fail
  end.

Ltac invtree f :=
  match goal with
     | H:f ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | H:f _ ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | H:f _ _ ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | _ => idtac
  end.

Ltac inv := inv_ok; invtree InT.

Ltac intuition_in := repeat progress (intuition; inv).

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: lt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | U: gt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => idtac (* MX.order *)
end.


(** [isok] is indeed a decision procedure for [Ok] *)

Lemma ltb_tree_iff : forall x s, lt_tree x s <-> ltb_tree x s = true.
Proof.
 induction s as [|l IHl y r IHr h]; simpl.
 unfold lt_tree; intuition_in.
 case_eq (Oeset.compare Elt x y); intro Hxy.
 split; intros; try discriminate. assert (Kxy : Oeset.compare Elt y x = Lt) by auto. 
 rewrite Oeset.compare_lt_gt, Hxy in Kxy; discriminate Kxy.
 split; intros; try discriminate. assert (Kxy : Oeset.compare Elt y x = Lt) by auto.
 rewrite Oeset.compare_lt_gt, Hxy in Kxy; discriminate Kxy.
  rewrite <- andb_lazy_alt, !andb_true_iff, <-IHl, <-IHr.
  unfold lt_tree; intuition_in; order.
  apply (Oeset.compare_eq_lt_trans _ y0 y x); [ | rewrite Oeset.compare_lt_gt, Hxy]; trivial.
Qed.

Lemma gtb_tree_iff : forall x s, gt_tree x s <-> gtb_tree x s = true.
Proof.
 induction s as [|l IHl y r IHr h]; simpl.
 unfold gt_tree; intuition_in.
 case_eq (Oeset.compare Elt x y); intro Hxy.
 split; intros; try discriminate. assert (Kxy : Oeset.compare Elt x y = Lt) by auto. 
 rewrite Hxy in Kxy; discriminate Kxy.
 rewrite <- andb_lazy_alt, !andb_true_iff, <-IHl, <-IHr.
 unfold gt_tree; intuition_in; order.
 apply (Oeset.compare_lt_eq_trans _ x y y0); [ | apply Oeset.compare_eq_sym]; trivial.
 split; intros; try discriminate. assert (Kxy : Oeset.compare Elt x y = Lt) by auto. 
 rewrite Kxy in Hxy; discriminate Hxy.
Qed.

Lemma isok_iff : forall s, Ok s <-> isok s = true.
Proof.
 induction s as [|l IHl y r IHr h].
 intuition_in.
 unfold iff; simpl.
 rewrite <- 3 andb_lazy_alt, 3 !andb_true_iff.
 rewrite <- IHl, <-IHr, <- ltb_tree_iff, <- gtb_tree_iff.
intuition_in.
Qed.

Instance isok_Ok s : isok s = true -> Ok s | 10.
Proof. intros; apply <- isok_iff; auto. Qed.

(** * Basic results about [In], [lt_tree], [gt_tree], [height] *)

(** [In] is compatible with [X.eq] *)

Lemma In_1 :
 forall s x y, eq_elt x y -> InT x s -> InT y s.
Proof.
 induction s; simpl; intuition_in; eauto.
Qed.
Local Hint Immediate In_1.

Instance In_compat : Proper (eq_elt==>eq==>iff) InT.
Proof.
apply proper_sym_impl_iff_2; auto with *.
repeat red; intros; subst. apply In_1 with x; auto.
Qed.

Lemma In_node_iff :
 forall l x r h y,
  InT y (Node l x r h) <-> InT y l \/ eq_elt y x \/ InT y r.
Proof.
 intuition_in.
 Qed.

(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf : forall x : elt, lt_tree x Leaf.
Proof.
 red; inversion 1.
Qed.

Lemma gt_leaf : forall x : elt, gt_tree x Leaf.
Proof.
 red; inversion 1.
Qed.

Lemma lt_tree_node :
 forall (x y : elt) (l r : tree) (h : int),
 lt_tree x l -> lt_tree x r -> lt_elt y x -> lt_tree x (Node l y r h).
Proof.
 unfold lt_tree; intuition_in; order.
 apply Oeset.compare_eq_lt_trans with y; trivial.
 Qed.

Lemma gt_tree_node :
 forall (x y : elt) (l r : tree) (h : int),
 gt_tree x l -> gt_tree x r -> lt_elt x y -> gt_tree x (Node l y r h).
Proof.
 unfold gt_tree; intuition_in; order.
 apply Oeset.compare_lt_eq_trans with y; [ | apply Oeset.compare_eq_sym]; trivial.
Qed.

Local Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_tree_not_in :
 forall (x : elt) (t : tree), lt_tree x t -> ~ InT x t.
Proof.
 intros; intro; order.
 rewrite Oeset.compare_eq_refl; discriminate.
Qed.

Lemma lt_tree_trans :
 forall x y, lt_elt x y -> forall t, lt_tree x t -> lt_tree y t.
Proof.
 eauto.
Qed.

Lemma gt_tree_not_in :
 forall (x : elt) (t : tree), gt_tree x t -> ~ InT x t.
Proof.
 intros; intro; order.
 rewrite Oeset.compare_eq_refl; discriminate.
Qed.

Lemma gt_tree_trans :
 forall x y, lt_elt y x -> forall t, gt_tree x t -> gt_tree y t.
Proof.
 eauto.
Qed.

Local Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

(** * Inductions principles for some of the set operators *)

Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme merge_ind := Induction for merge Sort Prop.
Functional Scheme min_elt_ind := Induction for min_elt Sort Prop.
Functional Scheme max_elt_ind := Induction for max_elt Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme inter_ind := Induction for inter Sort Prop.
Functional Scheme diff_ind := Induction for diff Sort Prop.
Functional Scheme union_ind := Induction for union Sort Prop.

Ltac induct s x :=
 induction s as [|l IHl x' r IHr h]; simpl; intros;
 [|case_eq (Oeset.compare Elt x x'); intros; inv].


(** * Notations and helper lemma about pairs and triples *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Notation "t #l" := (t_left t) (at level 9, format "t '#l'") : pair_scope.
Notation "t #b" := (t_in t) (at level 9, format "t '#b'") : pair_scope.
Notation "t #r" := (t_right t) (at level 9, format "t '#r'") : pair_scope.

Local Open Scope pair_scope.


(** * Empty set *)

Lemma empty_spec : Empty empty.
Proof.
 intro; intro.
 inversion H.
Qed.

Instance empty_ok : Ok empty.
Proof.
 auto.
Qed.

(** * Emptyness test *)

Lemma is_empty_spec : forall s, is_empty s = true <-> Empty s.
Proof.
 destruct s as [|r x l h]; simpl; auto.
 split; auto. red; red; intros; inv.
 split; auto. try discriminate. intro H; elim (H x); auto.
Qed.

(** * Membership *)

Lemma mem_impl_InT :
 forall s x, mem x s = true -> InT x s.
Proof.
intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
intros x Hx; discriminate Hx.
intros x; simpl.
case_eq (Oeset.compare Elt x e); intro H.
intros _; apply IsRoot; apply H.
intro H1; apply InLeft; apply IHt1; apply H1.
intro H2; apply InRight; apply IHt2; apply H2.
Qed.

Lemma mem_spec : forall s x, Ok s -> (mem x s = true <-> InT x s).
Proof.
 split.
 induct s x; auto; try discriminate.
 rewrite H1 in H0; apply InLeft; apply IHl; assumption.
 rewrite H1 in H0; apply InRight; apply IHr; assumption.
 induct s x; intuition_in; order.
 rewrite H1 in H; discriminate H.
 rewrite lt_gt_elt in H1; rewrite H1; discriminate.
 rewrite H1 in H; discriminate H.
 rewrite H1; discriminate.
Qed.


(** * Singleton set *)

Lemma singleton_spec : forall x y, InT y (singleton x) <-> eq_elt y x.
Proof.
 unfold singleton; intuition_in.
 Qed.

Instance singleton_ok x : Ok (singleton x).
Proof.
 unfold singleton; auto.
Qed.

(** * Helper functions *)

Lemma create_spec :
 forall l x r y,  InT y (create l x r) <-> eq_elt y x \/ InT y l \/ InT y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Instance create_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (create l x r).
Proof.
 unfold create; auto.
Qed.

Lemma bal_spec : forall l x r y,
 InT y (bal l x r) <-> Oeset.compare Elt y x = Eq \/ InT y l \/ InT y r.
Proof.
 intros l x r; functional induction bal l x r; intros; try clear e0;
 rewrite !create_spec; intuition_in.
Qed.

Instance bal_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (bal l x r).
Proof.
 functional induction bal l x r; intros;
 inv; repeat apply create_ok; auto; unfold create;
 (apply lt_tree_node || apply gt_tree_node); auto;
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
Qed.


(** * Insertion *)

Lemma add_spec' : forall s x y,
 InT y (add x s) <-> eq_elt y x \/ InT y s.
Proof.
 induct s x; try rewrite ?bal_spec, ?IHl, ?IHr; intuition_in.
 apply IsRoot.
 apply (Oeset.compare_eq_trans Elt _ _ _ H1 H).
Qed.

Lemma add_spec : forall s x y `{Ok s},
 InT y (add x s) <-> eq_elt y x \/ InT y s.
Proof. intros; apply add_spec'. Qed.

Instance add_ok s x `(Ok s) : Ok (add x s).
Proof.
 induct s x; auto; apply bal_ok; auto;
 intros y; rewrite add_spec'; intuition; order.
 apply Oeset.compare_eq_lt_trans with x; assumption.
 apply Oeset.compare_lt_eq_trans with x; trivial.
 rewrite Oeset.compare_lt_gt, H0; apply refl_equal.
 rewrite Oeset.compare_lt_gt, H5; apply refl_equal.
Qed.

Open Scope Int_scope.

(** * Join *)

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac l :=
 intro l; induction l as [| ll _ lx lr Hlr lh];
   [ | intros x r; induction r as [| rl Hrl rx rr _ rh]; unfold join;
     [ | destruct (gt_le_dec lh (rh+2));
       [ match goal with |- context b [ bal ?a ?b ?c] =>
           replace (bal a b c)
           with (bal ll lx (join lr x (Node rl rx rr rh))); [ | auto]
         end
       | destruct (gt_le_dec rh (lh+2));
         [ match goal with |- context b [ bal ?a ?b ?c] =>
             replace (bal a b c)
             with (bal (join (Node ll lx lr lh) x rl) rx rr); [ | auto]
           end
         | ] ] ] ]; intros.

Lemma join_spec : forall l x r y,
 InT y (join l x r) <-> Oeset.compare Elt y x = Eq \/ InT y l \/ InT y r.
Proof.
 join_tac l.
 simpl.
 rewrite add_spec'; intuition_in.
 rewrite add_spec'; intuition_in.
 rewrite bal_spec, Hlr; clear Hlr Hrl; intuition_in.
 rewrite bal_spec, Hrl; clear Hlr Hrl; intuition_in.
 apply create_spec.
Qed.

Instance join_ok : forall l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r),
 Ok (join l x r).
Proof.
 join_tac l; auto with *; inv; apply bal_ok; auto;
 clear Hrl Hlr; intro; intros; rewrite join_spec in *.
 intuition; eauto.
 intuition; eauto.
Qed.


(** * Extraction of minimum element *)

Lemma remove_min_spec : forall l x r h y,
 InT y (Node l x r h) <->
  Oeset.compare Elt y (remove_min l x r)#2 = Eq \/ InT y (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl in *; intros.
 intuition_in.
 rewrite bal_spec, In_node_iff, IHp, e0; simpl; intuition.
Qed.

Instance remove_min_ok l x r : forall h `(Ok (Node l x r h)),
 Ok (remove_min l x r)#1.
Proof.
 functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node ll lx lr _x)) by (inv; auto).
 assert (L : lt_tree x (Node ll lx lr _x)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; auto; simpl in *.
 apply bal_ok; auto.
 inv; auto.
 intro y; specialize (L y).
 rewrite remove_min_spec, e0 in L; simpl in L; intuition.
 inv; auto.
Qed.

Lemma remove_min_gt_tree : forall l x r h `{Ok (Node l x r h)},
 gt_tree (remove_min l x r)#2 (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node ll lx lr _x)) by (inv; auto).
 assert (L : lt_tree x (Node ll lx lr _x)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; simpl in IHp.
 intro y; rewrite bal_spec; intuition;
  specialize (L m); rewrite remove_min_spec, e0 in L; simpl in L; [  | inv]; eauto.
Qed.
Local Hint Resolve remove_min_gt_tree.



(** * Merging two trees *)

Lemma merge_spec : forall s1 s2 y,
 InT y (merge s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros;
 try factornode _x _x0 _x1 _x2 as s1.
 intuition_in.
 intuition_in.
 rewrite bal_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance merge_ok s1 s2 : forall `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> Oeset.compare Elt y1 y2 = Lt),
 Ok (merge s1 s2).
Proof.
 functional induction (merge s1 s2); intros; auto;
 try factornode _x _x0 _x1 _x2 as s1.
 apply bal_ok; auto.
 change s2' with ((s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** * Deletion *)

Lemma remove_spec : forall s x y `{Ok s},
 (InT y (remove x s) <-> InT y s /\ ~ eq_elt y x).
Proof.
 induct s x.
 intuition_in.
 rewrite merge_spec; intuition; [order|order|intuition_in].
 rewrite (proper_e_e_lt_elt H (Oeset.compare_eq_sym _ _ _ H0)), Oeset.compare_eq_refl; discriminate.
 rewrite Oeset.compare_lt_gt, (Oeset.compare_eq_trans Elt y x x' H H0); discriminate.
 apply False_rec; apply H6; apply (Oeset.compare_eq_trans Elt) with x'; auto.
 rewrite bal_spec, IHl; clear IHl IHr; intuition; [order|order|intuition_in].
 assert (K : Oeset.compare Elt x x' = Eq).
 apply Oeset.compare_eq_trans with y; auto.
 rewrite K in H0; discriminate H0.
  assert (K : Oeset.compare Elt y x' = Lt).
 apply Oeset.compare_eq_lt_trans with x; auto.
 rewrite Oeset.compare_lt_gt, K; discriminate.
 rewrite bal_spec, IHr; clear IHl IHr; intuition; [order|order|intuition_in].
 assert (K : Oeset.compare Elt x x' = Eq).
 apply Oeset.compare_eq_trans with y; auto.
 rewrite K in H0; discriminate H0.
 assert (K : Oeset.compare Elt x' y = Lt).
 apply Oeset.compare_lt_eq_trans with x; auto.
 rewrite Oeset.compare_lt_gt, H0; apply refl_equal.
 rewrite Oeset.compare_lt_gt, K; discriminate.
Qed.

Instance remove_ok s x `(Ok s) : Ok (remove x s).
Proof.
  induct s x.
 auto.
 (* EQ *)
 apply merge_ok; eauto.
 (* LT *)
 apply bal_ok; auto.
 intro z; rewrite remove_spec; auto; destruct 1; eauto.
 (* GT *)
 apply bal_ok; auto.
 intro z; rewrite remove_spec; auto; destruct 1; eauto.
Qed.


(** * Minimum element *)

Lemma min_elt_spec1 : forall s x, min_elt s = Some x -> InT x s.
Proof.
 intro s; functional induction (min_elt s); auto; inversion 1; auto.
Qed.

Lemma min_elt_spec2 : forall s x y `{Ok s},
 min_elt s = Some x -> InT y s -> ~ Oeset.compare Elt y x = Lt.
Proof.
 intro s; functional induction (min_elt s);
 try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
 discriminate.
 intros x y0 U V W.
 inversion V; clear V; subst.
 inv; order.
 rewrite H; discriminate.
 rewrite lt_gt_elt; intro K; rewrite K; discriminate.
 intros; inv; auto.
 assert (lt_elt x y) by (apply H4; apply min_elt_spec1; auto).
 rewrite Oeset.compare_lt_gt.
 assert (K : Oeset.compare Elt x y0 = Lt).
 apply Oeset.compare_lt_eq_trans with y; auto.
 rewrite K; discriminate.
 assert (lt_elt x1 y) by auto.
 assert (~lt_elt x1 x) by auto.
 order.
 intros K1 K2.
 assert (K3 := Oeset.compare_lt_trans Elt _ _ _ K1 K2).
 assert (K4 := Oeset.compare_lt_trans Elt _ _ _ H1 K3).
 apply False_rec; apply H9; assumption.
Qed.

Lemma min_elt_spec3 : forall s, min_elt s = None -> Empty s.
Proof.
 intro s; functional induction (min_elt s).
 red; red; inversion 2.
 inversion 1.
 intro H0.
 destruct (IHo H0 _x2); auto.
Qed.



(** * Maximum element *)

Lemma max_elt_spec1 : forall s x, max_elt s = Some x -> InT x s.
Proof.
 intro s; functional induction (max_elt s); auto; inversion 1; auto.
Qed.

Lemma max_elt_spec2 : forall s x y `{Ok s},
 max_elt s = Some x -> InT y s -> ~ Oeset.compare Elt x y = Lt.
Proof.
 intro s; functional induction (max_elt s);
 try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
 discriminate.
 intros x y0 U V W.
 inversion V; clear V; subst.
 inversion U; subst.
 intro H; inversion W; subst.
 rewrite (Oeset.compare_lt_gt Elt), H1 in H; discriminate H.
 generalize (H5 y0 H1); rewrite (Oeset.compare_lt_gt Elt), H; discriminate.
 inversion H1.
 intros; inv; auto.
 assert (Oeset.compare Elt y x1 = Lt) by auto.
 assert (~Oeset.compare Elt x x1 = Lt) by auto.
 intro K; apply H9.
 apply Oeset.compare_lt_trans with y; [ | assumption].
 apply Oeset.compare_lt_eq_trans with y0; trivial.
 assert (Oeset.compare Elt y x = Lt) by (apply H5; apply max_elt_spec1; auto).
 intro K.
 generalize (H4 y0 H3).
 rewrite Oeset.compare_lt_gt.
 rewrite (Oeset.compare_lt_trans Elt _ _ _ H1 K); discriminate.
Qed.

Lemma max_elt_spec3 : forall s, max_elt s = None -> Empty s.
Proof.
 intro s; functional induction (max_elt s).
 red; auto.
 inversion 1.
 intros H0; destruct (IHo H0 _x2); auto.
Qed.



(** * Any element *)

Lemma choose_spec1 : forall s x, choose s = Some x -> InT x s.
Proof.
 exact min_elt_spec1.
Qed.

Lemma choose_spec2 : forall s, choose s = None -> Empty s.
Proof.
 exact min_elt_spec3.
Qed.

Lemma choose_spec3 : forall s s' x x' `{Ok s, Ok s'},
  choose s = Some x -> choose s' = Some x' ->
  Equal s s' -> Oeset.compare Elt x x' = Eq.
Proof.
 unfold choose, Equal; intros s s' x x' Hb Hb' Hx Hx' H.
 assert (~Oeset.compare Elt x x' = Lt).
  apply min_elt_spec2 with s'; auto.
  rewrite <-H; auto using min_elt_spec1.
 assert (~Oeset.compare Elt x' x = Lt).
  apply min_elt_spec2 with s; auto.
  rewrite H; auto using min_elt_spec1.
  rewrite (Oeset.compare_lt_gt Elt) in H1.
  case_eq (Oeset.compare Elt x x'); intuition.
  rewrite H2 in H1; apply False_rec; apply H1; apply refl_equal.
Qed.


(** * Concatenation *)

Lemma concat_spec : forall s1 s2 y,
 InT y (concat s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (concat s1 s2); intros;
 try factornode _x _x0 _x1 _x2 as s1.
 intuition_in.
 intuition_in.
 rewrite join_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance concat_ok s1 s2 : forall `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> lt_elt y1 y2),
 Ok (concat s1 s2).
Proof.
 functional induction (concat s1 s2); intros; auto;
 try factornode _x _x0 _x1 _x2 as s1.
 apply join_ok; auto.
 change (Ok (s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** * Splitting *)

Lemma split_spec1 : forall s x y `{Ok s},
 (InT y (split x s)#l <-> InT y s /\ lt_elt y x).
Proof.
 induction s as [ | l IHl a r IHr h].
 intuition_in.
 inversion H0.
 simpl; intros x y.
 case_eq (Oeset.compare Elt x a); intro Cxa.
 (* 1/3 *)
 intuition_in; order.
 intro; apply Oeset.compare_lt_eq_trans with a; auto.
 assert (K : Oeset.compare Elt y x = Eq).
 apply Oeset.compare_eq_trans with a; auto.
 rewrite K in H2; discriminate H2.
 intro H1;  assert (K : Oeset.compare Elt x a = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff.
 apply Oeset.compare_lt_trans with y; auto.
 rewrite K in Cxa; discriminate Cxa.
 (* 1/2 *)
 intro H; inversion H; subst.
 specialize (IHl x y).
 destruct (split x l); simpl in *. rewrite IHl; intuition.
 inversion H3; subst.
 (* 1/4 *)
 assert (K : Oeset.compare Elt x a = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff.
 apply Oeset.compare_eq_lt_trans with y; auto.
 rewrite K in Cxa; discriminate Cxa.
 (* 1/3 *)
 assumption.
 (* 1/2 *)
 generalize (H7 _ H9).
 rewrite Oeset.compare_lt_gt, (Oeset.compare_lt_trans Elt _ _ _ H8 Cxa); discriminate.
 (* 1/1 *)
 intro H; inversion H; subst.
 specialize (IHr x y).
 destruct (split x r); simpl in *. rewrite join_spec, IHr; intuition_in; order.
 apply Oeset.compare_eq_lt_trans with a; auto.
 rewrite Oeset.compare_lt_gt, Cxa; apply refl_equal.
 intros Cya _; apply Oeset.compare_lt_trans with a; auto.
 rewrite Oeset.compare_lt_gt, Cxa; apply refl_equal.
Qed.

Lemma split_spec2 : forall s x y `{Ok s},
 (InT y (split x s)#r <-> InT y s /\ lt_elt x y).
Proof.
 induction s as [ | l IHl a r IHr h].
 intuition_in.
 inversion H0.
 simpl; intros x y.
 case_eq (Oeset.compare Elt x a); intro Cxa.
 (* 1/3 *)
 intro H; inversion H; subst.
 intuition_in; order.
 intros Cya _; apply Oeset.compare_eq_lt_trans with a; auto.
 assert (Cxy : Oeset.compare Elt x y = Eq).
 apply Oeset.compare_eq_trans with a; auto.
 rewrite Cxy in H2; discriminate H2.
 intros Cya _; assert (Cxy : Oeset.compare Elt x y = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff.
 apply Oeset.compare_lt_eq_trans with a; auto.
 rewrite Cxy in H2; discriminate H2.
 (* 1/2 *)
 intro H; inversion H; subst.
 specialize (IHl x y).
 destruct (split x l); simpl in *. rewrite join_spec, IHl; intuition.
 (* 1/4 *)
 apply Oeset.compare_lt_eq_trans with a; auto.
 (* 1/3 *)
 generalize (H7 _ H2); apply (Oeset.compare_lt_trans Elt _ _ _ Cxa).
 (* 1/2 *)
 inversion H3; subst; intuition.
 (* 1/1 *)
 intro H; inversion H; subst.
 specialize (IHr x y).
 destruct (split x r); simpl in *. rewrite IHr; intuition_in; order.
 assert (Cxy : Oeset.compare Elt x y = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff in Cxa; simpl in Cxa.
 rewrite Oeset.compare_lt_gt, CompOpp_iff.
 apply Oeset.compare_eq_lt_trans with a; auto.
 rewrite Cxy in H8; discriminate H8.
 intros Cya _.
  assert (Dxa : Oeset.compare Elt x a = Lt).
 apply Oeset.compare_lt_trans with y; auto.
 rewrite Dxa in Cxa; discriminate Cxa.
Qed.

Lemma split_spec3 : forall s x `{Ok s},
 ((split x s)#b = true <-> InT x s).
Proof.
 induction s as [ | l IHl a r IHr h].
 intuition_in.
 inversion H0.
 simpl; intros x H.
 case_eq (Oeset.compare Elt x a); intro Cxa.
 (* 1/3 *)
 intuition_in.
 (* 1/2 *)
 specialize (IHl x).
 destruct (split x l); simpl in *. rewrite IHl; intuition_in; order.
 (* 1/3 *)
 rewrite Cxa in H; discriminate H.
 (* 1/2 *)
 rewrite Oeset.compare_lt_gt, Cxa; discriminate.
 (* 1/1 *)
 specialize (IHr x).
 destruct (split x r); simpl in *. rewrite IHr; intuition_in; order.
 (* 1/2 *)
 rewrite Cxa in H; discriminate H.
 (* 1/1 *)
 rewrite Cxa; discriminate.
Qed.

Lemma split_ok : forall s x `{Ok s}, Ok (split x s)#l /\ Ok (split x s)#r.
Proof.
 induction s as [ | l IHl a r IHr h].
 intuition_in.
 simpl; intros x H; inversion H; subst.
 case_eq (Oeset.compare Elt x a); intro Cxa.
 split; auto.
 specialize (IHl x).
 generalize (fun y => @split_spec2 l x y H4).
 destruct (split x l); simpl in *; intuition. apply join_ok; auto.
  intros y; rewrite H0; intuition.
 specialize (IHr x).
 generalize (fun y => @split_spec1 r x y H5).
 destruct (split x r); simpl in *; intuition. apply join_ok; auto.
 intros y; rewrite H0; intuition.
Qed.

Instance split_ok1 s x `(Ok s) : Ok (split x s)#l.
Proof. intros; destruct (@split_ok s x); auto. Qed.

Instance split_ok2 s x `(Ok s) : Ok (split x s)#r.
Proof. intros; destruct (@split_ok s x); auto. Qed.


(** * Intersection *)

Ltac destruct_split := match goal with
 | H : split ?x ?s = << ?u, ?v, ?w >> |- _ =>
   assert ((split x s)#l = u) by (rewrite H; auto);
   assert ((split x s)#b = v) by (rewrite H; auto);
   assert ((split x s)#r = w) by (rewrite H; auto);
   clear H; subst u w
 end.

Lemma inter_spec_ok : forall s1 s2 `{Ok s1, Ok s2},
 Ok (inter s1 s2) /\ (forall y, InT y (inter s1 s2) <-> InT y s1 /\ InT y s2).
Proof.
 intros s1 s2; functional induction inter s1 s2 as 
   [| | H1 H2 l1 x1 r1 h1 H3 l2 x2 r2 h2 H4 l2' H5 r2' H6 H7 IHt1 IHt2 
   | H1 H2 l1 x1 r1 h1 H3 l2 x2 r2 h2 H4 l2' H5 r2' H6 H7 IHt1 IHt2]; 
   intros B1 B2;  [intuition_in | intuition_in | | ];
 factornode l2 x2 r2 h2 as s2; destruct_split; inv;
 destruct IHt1 as (IHo1,IHi1), IHt2 as (IHo2,IHi2); auto with *;
 split; intros.
 (* Ok join *)
 apply join_ok; auto with *; intro y; rewrite ?IHi1, ?IHi2; intuition.
 (* InT join *)
 rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
 rewrite (eq_elt_InT_compat H5).
 rewrite <- split_spec3; auto.
(* Ok concat *)
 apply concat_ok; auto with *; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 do 2 intro; apply (Oeset.compare_lt_trans Elt y1 x1 y2); assumption.
 (* InT concat *)
 rewrite concat_spec, IHi1, IHi2, split_spec1, split_spec2; auto.
 intuition_in.
 absurd (InT x1 s2).
  rewrite <- split_spec3; auto; congruence.
  rewrite <- (eq_elt_InT_compat H4); assumption.
Qed.

Lemma inter_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (inter s1 s2) <-> InT y s1 /\ InT y s2).
Proof. intros; destruct (@inter_spec_ok s1 s2); auto. Qed.

Instance inter_ok s1 s2 `(Ok s1, Ok s2) : Ok (inter s1 s2).
Proof. intros; destruct (@inter_spec_ok s1 s2); auto. Qed.


(** * Difference *)

Lemma diff_spec_ok : forall s1 s2 `{Ok s1, Ok s2},
 Ok (diff s1 s2) /\ (forall y, InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof.
 intros s1 s2; functional induction diff s1 s2 as 
   [| | H1 H2 l1 x1 r1 h1 H3 l2 x2 r2 h2 H4 l2' H5 r2' H6 H7 IHt1 IHt2 
   | H1 H2 l1 x1 r1 h1 H3 l2 x2 r2 h2 H4 l2' H5 r2' H6 H7 IHt1 IHt2]; 
   intros B1 B2;  [intuition_in | intuition_in | | ];
 factornode l2 x2 r2 h2 as s2; destruct_split; inv;
 destruct IHt1 as (IHo1,IHi1), IHt2 as (IHo2,IHi2); auto with *;
 split; intros.
 (* Ok concat *)
 apply concat_ok; auto; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 do 2 intro; apply (Oeset.compare_lt_trans Elt y1 x1 y2); assumption.
 (* InT concat *)
 rewrite concat_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
 absurd (InT x1 s2).
 rewrite <- (eq_elt_InT_compat H4); assumption.
  rewrite <- split_spec3; auto; congruence.
 (* Ok join *)
 apply join_ok; auto; intro y; rewrite ?IHi1, ?IHi2; intuition.
 (* InT join *)
 rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; auto with *.
 intuition_in.
 absurd (InT x1 s2); auto.
  rewrite <- split_spec3; auto; congruence.
  rewrite <- (eq_elt_InT_compat H5); assumption.
Qed.

Lemma diff_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.

Instance diff_ok s1 s2 `(Ok s1, Ok s2) : Ok (diff s1 s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.


(** * Union *)

Lemma union_spec : forall s1 s2 y, Ok s1 -> Ok s2 ->
 ((InT y (union s1 s2) <-> InT y s1 \/ InT y s2)).
Proof.
 intros s1 s2; functional induction union s1 s2 as 
   [|  | H1 H2 l1 x1 r1 h1 H3 l2 x2 r2 h2 H4 l2' H5 b H6 IHt1 IHt2]; intros y B1 B2.
 intuition_in.
 intuition_in.
 factornode  l2 x2 r2 h2 as s2.
 destruct_split.
 inv.
 rewrite join_spec, IHt1, IHt2, split_spec1, split_spec2; auto with *.
 case_eq (Oeset.compare Elt y x1); intro Cyx1; intuition_in.
 discriminate.
 rewrite H4 in Cyx1; discriminate.
 discriminate.
  rewrite H4 in Cyx1; discriminate.
  do 3 right; split; [ | rewrite (Oeset.compare_lt_gt Elt), CompOpp_iff]; assumption.
Qed.

Instance union_ok s1 s2 : forall `(Ok s1, Ok s2), Ok (union s1 s2).
Proof.
 functional induction union s1 s2; intros B1 B2; auto.
 factornode _x0 _x1 _x2 _x3 as s2; destruct_split; inv.
 apply join_ok; auto with *.
 intro y; rewrite union_spec, split_spec1; intuition_in.
 intro y; rewrite union_spec, split_spec2; intuition_in.
Qed.


(** * Elements *)

Lemma elements_spec1' : forall s acc x,
 InA eq_elt x (elements_aux acc s) <-> InT x s \/ InA eq_elt x acc.
Proof.
 induction s as [ | l Hl x r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
Qed.

Lemma elements_spec1 : forall s x, InA eq_elt x (elements s) <-> InT x s.
Proof.
 intros; generalize (elements_spec1' s nil x); intuition.
 inversion_clear H0.
Qed.

Lemma elements_spec2' : forall s acc `{Ok s}, sort lt_elt acc ->
 (forall x y : elt, InA eq_elt x acc -> InT y s -> lt_elt y x) ->
 sort lt_elt (elements_aux acc s).
Proof.
 induction s as [ | l Hl y r Hr h]; simpl; intuition.
 inv.
 apply Hl; auto.
 constructor.
 apply Hr; auto.
 assert (E := equiv_eq_elt).
 apply (InA_InfA E (ltA := fun x y => Oeset.compare Elt x y = Lt)).
 intros.
 destruct (elements_spec1' r acc y0); intuition.
 intros.
 inversion_clear H.
 order.
 intro; apply Oeset.compare_lt_eq_trans with y; auto.
 rewrite (elements_spec1' r acc x) in H7; destruct H7 as [H7 | H7].
 generalize (H5 _ H7).
 apply (Oeset.compare_lt_trans Elt); apply (H4 _ H6).
 apply H1; [ | apply InLeft]; assumption.
Qed.

Lemma elements_spec2 : forall s `(Ok s), sort lt_elt (elements s).
Proof.
 intros; unfold elements; apply elements_spec2'; auto.
 intros; inversion H0.
Qed.
Local Hint Resolve elements_spec2.

Lemma elements_spec2w : forall s `(Ok s), NoDupA eq_elt (elements s).
Proof.
 intros. eapply SortA_NoDupA; eauto with *.
 apply equiv_eq_elt.
 apply st_ord_lt_elt.
 apply proper_e_e_lt_elt.
Qed.

Lemma elements_aux_cardinal :
 forall s acc, (length acc + cardinal s)%nat = length (elements_aux acc s).
Proof.
 simple induction s; simpl in |- *; intuition.
 rewrite <- H.
 simpl in |- *.
 rewrite <- H0; omega.
Qed.

Lemma elements_cardinal : forall s : tree, cardinal s = length (elements s).
Proof.
 exact (fun s => elements_aux_cardinal s nil).
Qed.

Definition cardinal_spec (s : tree)(Hs : Ok s) := elements_cardinal s.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold elements; simpl.
 rewrite 2 IHs1, IHs2, <- !app_nil_end, !app_ass; auto.
Qed.

Lemma elements_node :
 forall l x r h acc,
 elements l ++ x :: elements r ++ acc =
 elements (Node l x r h) ++ acc.
Proof.
 unfold elements; simpl; intros; auto.
 rewrite !elements_app, <- !app_nil_end, !app_ass; auto.
Qed.


(** * Filter *)

Lemma filter_spec' : forall s x acc f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') ->
 (InT x (filter_acc f acc s) <-> InT x acc \/ InT x s /\ f x = true).
Proof.
  intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
  (* 1/2 *)
  intros x acc f Hf; simpl; split.
  intro H; left; exact H.
  intros [H | [H _]]; [exact H | inversion H].
  (* 1/1 *)
  intros x acc f Hf; simpl; split.
  (* 1/2 *)
  intro H; rewrite IHt2 in H.
  rewrite IHt1 in H.
  destruct H as [[H | H] | H].
  case_eq (f e); intro He; rewrite He in H.
  rewrite add_spec' in H; destruct H as [H | H].
  right; split; [apply (IsRoot _ _ _ H) | ].
  rewrite (Hf x e); [apply He | apply (IsRoot _ _ _ H) | apply H].
  left; assumption.
  left; assumption.
  right; split; [apply InLeft; apply (proj1 H) | apply (proj2 H)].
  right; split; [apply InRight; apply (proj1 H) | apply (proj2 H)].
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
  (* 1/1 *)
  intro H; rewrite IHt2.
  rewrite IHt1.
  destruct H as [H | [H1 H2]].
  do 2 left; case (f e); [rewrite add_spec'; right | ]; apply H.
  rewrite In_node_iff in H1.
  destruct H1 as [H1 | [H1 | H1]].
  left; right; split; assumption.
  do 2 left.
  rewrite <- (Hf x e); [rewrite H2, add_spec'; left | apply IsRoot| ]; apply H1.
  right; split; assumption.
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
Qed.

Lemma filter_spec2' : 
  forall s x acc f, InT x (filter_acc f acc s) -> InT x acc \/ InT x s.
Proof.
intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
(* 1/2 *)
intros x acc f H.
left; apply H.
(* 1/1 *)
intros x acc f H; simpl in H.
(* 1/2 *)
destruct (IHt2 _ _ _ H) as [H1 | H1].
destruct (IHt1 _ _ _ H1) as [H2 | H2].
revert H2; case (f e).
rewrite add_spec'; intros [H2 | H2].
right; apply IsRoot; apply H2.
left; assumption.
intro H2; left; assumption.
right; apply InLeft; assumption.
right; apply InRight; assumption.
Qed.

Instance filter_ok' : forall s acc f `(Ok s, Ok acc),
 Ok (filter_acc f acc s).
Proof.
 induction s; simpl; auto.
 intros. inv.
 destruct (f e); auto with *.
Qed.

Lemma filter_spec : forall s x f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') ->
 (InT x (filter f s) <-> InT x s /\ f x = true).
Proof.
 unfold filter; intros; rewrite filter_spec'; intuition_in.
Qed.

Lemma filter_spec2 : forall s x f, InT x (filter f s) -> InT x s.
Proof.
 unfold filter; intros s x f H.
 destruct (filter_spec2' _ _ _ H) as [K | K].
 inversion K.
 exact K.
Qed.

Instance filter_ok s f `(Ok s) : Ok (filter f s).
Proof.
 unfold filter; intros; apply filter_ok'; auto.
Qed.

Lemma bal_spec' : forall x e t1 t2,
  List.In x (elements (bal t1 e t2)) <-> 
  (List.In x (elements t1) \/ x = e \/ List.In x (elements t2)).
Proof.
intros x e t1 t2; unfold bal.
case (gt_le_dec (height t1) (height t2 + 2)).
- intros _; destruct t1 as [ | ll lc lr lh]; simpl.
  + split.
    * intros [H | H].
      right; left; apply sym_eq; apply H.
      do 2 right; apply H.
    * intros [H | [H | H]].
      contradiction H.
      left; apply sym_eq; apply H.
      right; apply H.
  + case (ge_lt_dec (height ll) (height lr)).
    * intros _; unfold create, elements; simpl.
      rewrite elements_app; simpl.
      {
        split; intro H.
        destruct (in_app_or _ _ _ H) as [K | K].
        - left; rewrite elements_app.
          apply in_or_app; left; apply K.
        - simpl in K; destruct K as [K | K].
          + left; rewrite elements_app.
            apply in_or_app; right; left; assumption.
          + rewrite elements_app in K.
            destruct (in_app_or _ _ _ K) as [K1 | K1].
            * left; rewrite elements_app.
              apply in_or_app; do 2 right; apply K1.
            * simpl in K1; destruct K1 as [K1 | K1].
              right; left; apply sym_eq; assumption.
              do 2 right; assumption.
        - destruct H as [H | [H | H]].
          + rewrite elements_app in H.
            destruct (in_app_or _ _ _ H) as [K | K].
            * apply in_or_app; left; assumption.
            * {
                simpl in K; destruct K as [K | K].
                - apply in_or_app; right; left; assumption.
                - apply in_or_app; do 2 right.
                  rewrite elements_app.
                  apply in_or_app; left; assumption.
              } 
          + apply in_or_app; right.
            right; rewrite elements_app.
            apply in_or_app; right; left; apply sym_eq; assumption.
          + apply in_or_app; right.
            right.
            rewrite elements_app.
            apply in_or_app; do 2 right; assumption.
      }
    * intros _; unfold create, elements; simpl.
      {
        destruct lr as [ | lrl lrx lrr lrh]; simpl.
        - rewrite elements_app; simpl.
          rewrite (elements_app ll (lc :: nil)).
          split; intro H.
          destruct (in_app_or _ _ _ H) as [K | K].
          + left; apply in_or_app; left; apply K.
          + simpl in K; destruct K as [K | [K | K]].
            * left; apply in_or_app; right; left; assumption.
            * right; left; apply sym_eq; assumption.
            * do 2 right; assumption.
          + destruct H as [H | [H | H]].
            * {
                destruct (in_app_or _ _ _ H) as [K | K].
                - apply in_or_app; left; assumption.
                - simpl in K; destruct K as [K | K].
                  + apply in_or_app; right; left; assumption.
                  + contradiction K.
              } 
            * apply in_or_app; right.
              right; left; apply sym_eq; assumption.
            * apply in_or_app; right.
              do 2 right.
              assumption.
        - rewrite elements_app; simpl.
          rewrite (elements_app lrl).
          rewrite (elements_app lrr).
          rewrite (elements_app ll).
          rewrite (elements_app lrl).
          split; intro H.
          destruct (in_app_or _ _ _ H) as [K | K].
          + left; apply in_or_app; left; apply K.
          + simpl in K; destruct K as [K | K].
            * left; apply in_or_app; right; left; assumption.
            * {
                destruct (in_app_or _ _ _ K) as [K1 | K1].
                - left; apply in_or_app; right.
                  simpl; right.
                  apply in_or_app; left; assumption.
                - simpl in K1; destruct K1 as [K1 | K1].
                  + left; apply in_or_app; right.
                    simpl; right.
                    apply in_or_app; right; left; assumption.
                  + destruct (in_app_or _ _ _ K1) as [K2 | K2].
                    * left; apply in_or_app; right.
                      simpl; right.
                      apply in_or_app; right.
                      right; assumption.
                    * simpl in K2; destruct K2 as [K2 | K2].
                      right; left; apply sym_eq; assumption.
                      do 2 right; assumption.
              } 
          + destruct H as [H | [H | H]].
            * {
                destruct (in_app_or _ _ _ H) as [K | K].
                - apply in_or_app; left; apply K.
                - simpl in K; destruct K as [K | K].
                  + apply in_or_app; right; left; assumption.
                  + destruct (in_app_or _ _ _ K) as [K1 | K1].
                    * apply in_or_app; right.
                      right; apply in_or_app; left; assumption.
                    * {
                        simpl in K1; destruct K1 as [K1 | K1].
                        - apply in_or_app; right.
                          simpl; right.
                          apply in_or_app; right; left; assumption.
                        - apply in_or_app; right.
                          simpl; right.
                          apply in_or_app; right.
                          simpl; right.
                          apply in_or_app; left; assumption.
                      }
              }
            * apply in_or_app; right.
              simpl; right.
              apply in_or_app; right.
              simpl; right.
              apply in_or_app; right; left; apply sym_eq; assumption.
            * apply in_or_app; right.
              simpl; right.
              apply in_or_app; right.
              simpl; right.
              apply in_or_app; do 2 right; assumption.
      }
- intros _; case (gt_le_dec (height t2) (height t1 + 2)).
  + intros _; unfold create, elements; simpl.
    destruct t2 as [ | rl rx rr rh]; simpl.
    * { 
        split; intro H.
        - rewrite elements_app in H.
          destruct (in_app_or _ _ _ H) as [K | K].
          + left; assumption.
          + simpl in K; destruct K as [K | K].
            * right; left; apply sym_eq; assumption.
            * contradiction K.
        - rewrite elements_app.
          destruct H as [H | [H | H]].
          + apply in_or_app; left; assumption.
          + apply in_or_app; right; left; apply sym_eq; assumption.
          + contradiction H.
      } 
    * {
        case (ge_lt_dec (height rr) (height rl)).
        - intros _; simpl.
          rewrite (elements_app rl).
          rewrite (elements_app t1).
          split; intro H.
          + destruct (in_app_or _ _ _ H) as [K | K].
            * left; assumption.
            * {
                simpl in K; destruct K as [K | K].
                - right; left; apply sym_eq; assumption.
                - destruct (in_app_or _ _ _ K) as [K1 | K1].
                  + do 2 right.
                    apply in_or_app; left; assumption.
                  + simpl in K1; destruct K1 as [K1 | K1].
                    * do 2 right.
                      apply in_or_app; right; left; assumption.
                    * do 2 right.
                      apply in_or_app; do 2 right; assumption.
              }
          + destruct H as [H | [H | H]].
            * apply in_or_app; left; assumption.
            * apply in_or_app; right; left; apply sym_eq; assumption.
            * {
                destruct (in_app_or _ _ _ H) as [K | K].
                - apply in_or_app; right.
                  simpl; right.
                  apply in_or_app; left; assumption.
                - simpl in K; destruct K as [K | K].
                  + apply in_or_app; right.
                    simpl; right.
                    apply in_or_app; right; left; assumption.
                  + apply in_or_app; right.
                    simpl; right.
                    apply in_or_app; right.
                    simpl; right; assumption.
              } 
        - intros _.
          destruct rl as [ | rll rlx rlr rlh]; simpl.
          + rewrite (elements_app t1).
            split; intro H.
            destruct (in_app_or _ _ _ H) as [K | K].
            * left; assumption.
            * {
                simpl in K; destruct K as [K | [K | K]].
                - right; left; apply sym_eq; assumption.
                - do 2 right; left; assumption.
                - do 3 right; assumption.
              } 
            * {
                destruct H as [H | [H | [H | H]]].
                - apply in_or_app; left; assumption.
                - apply in_or_app; right; left; apply sym_eq; assumption.
                - apply in_or_app; do 2 right; left; assumption.
                - apply in_or_app; do 3 right; assumption.
              } 
          + rewrite (elements_app t1).
            rewrite (elements_app rlr).
            rewrite (elements_app rll).
            split; intro H.
            destruct (in_app_or _ _ _ H) as [K | K].
            * left; assumption.
            * {
                simpl in K; destruct K as [K | K].
                - right; left; apply sym_eq; assumption.
                - do 2 right; assumption.
              }
            * {
                destruct H as [H | [H | H]].
                - apply in_or_app; left; assumption.
                - apply in_or_app; right; left; apply sym_eq; assumption.
                - apply in_or_app; do 2 right; assumption.
              } 
      }
  + intros; unfold create, elements; simpl.
    rewrite (elements_app t1).
    split; intro H.
    * {
        destruct (in_app_or _ _ _ H) as [K | K].
        - left; assumption.
        - simpl in K; destruct K as [K | K].
          + right; left; apply sym_eq; assumption.
          + do 2 right; assumption.
      }
    * {
        destruct H as [H | [H | H]].
        - apply in_or_app; left; assumption.
        - apply in_or_app; right; left; apply sym_eq; assumption.
        - apply in_or_app; do 2 right; assumption.
      } 
Qed.

Lemma add_spec'' : 
  forall e s, ~InT e s -> 
   (forall x, List.In x (elements (add e s)) <-> (e = x \/ List.In x (elements s))).
Proof.
intros e s; unfold elements.
induction s as [ | t1 IHt1 e1 t2 IHt2 h]; intros H x; simpl.
- split; exact (fun h => h).
- case_eq (Oeset.compare Elt e e1); intro K.
  + apply False_rec; apply H.
    apply IsRoot; apply K.
  + rewrite bal_spec', IHt1.
    * {
        split; intro J.
        - destruct J as [[J | J] | [J | J]].
          + left; assumption.
          + right; rewrite elements_app.
            apply in_or_app; left; assumption.
          + right; rewrite elements_app.
            apply in_or_app; right; left; apply sym_eq; assumption.
          + right; rewrite elements_app.
            apply in_or_app; do 2 right; assumption.
        - rewrite elements_app in J.
          destruct J as [J | J].
          + do 2 left; assumption.
          + destruct (in_app_or _ _ _ J) as [J1 | J1].
            * left; right; assumption.
            * {
                simpl in J1; destruct J1 as [J1 | J1].
                - right; left; apply sym_eq; assumption.
                - do 2 right; assumption.
              } 
      }
    * intro He; apply H.
      apply InLeft; assumption.
  + rewrite bal_spec', IHt2.
    * {
        split; intro J.
        - destruct J as [J | [J | [J | J]]].
          + right; rewrite elements_app.
            apply in_or_app; left; assumption.
          + right; rewrite elements_app.
            apply in_or_app; right; left; apply sym_eq; assumption.
          + left; assumption.
          + right; rewrite elements_app.
            apply in_or_app; do 2 right; assumption.
        - destruct J as [J | J].
          + do 2 right; left; assumption.
          + rewrite elements_app in J.
            destruct (in_app_or _ _ _ J) as [J1 | J1].
            * left; assumption.
            * {
                simpl in J1; destruct J1 as [J1 | J1].
                - right; left; apply sym_eq; assumption.
                - do 3 right; assumption.
              }
      }
    * intro He; apply H.
      apply InRight; assumption.
Qed.

Lemma filter_spec3' : 
  forall s x acc f, 
    Ok s -> Ok acc -> (forall e, InT e s -> InT e acc -> False) ->
    ((List.In x (elements (filter_acc f acc s))) <->
     ((List.In x (elements s) /\ f x = true) \/ List.In x (elements acc))).
Proof.
intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
- (* 1/2 *)
  intros x acc f _ _ _; simpl; split; intro H.
  + right; assumption.
  + destruct H as [[H _] | H].
    * contradiction H.
    * apply H.
- (* 1/1 *)
  intros x acc f OKs OKa Hsa.
  inversion OKs; subst.
  assert (OK1  := bst_Ok H3).
  assert (OK2  := bst_Ok H4).
  assert (OKa1 : Ok (if f e then add e acc else acc)).
  {
    case (f e).
    - apply add_ok; apply OKa.
    - apply OKa.
  }
  assert (Hsa1 : forall x, InT x t1 -> 
                           InT x (if f e then add e acc else acc) -> False).
  {
    intros a Ha Ka.
    case_eq (f e); intro He; rewrite He in Ka.
    - rewrite (@add_spec _ _ _ OKa) in Ka.
      destruct Ka as [Ka | Ka].
      + apply (lt_tree_not_in H5).
        apply (In_1 Ka Ha).
      + apply (Hsa a); [ | assumption].
        apply InLeft; apply Ha.
    - apply (Hsa a); [ | assumption].
      apply InLeft; apply Ha.
  }
  assert (OKa2 : Ok (filter_acc f (if f e then add e acc else acc) t1)).
  {
    apply filter_ok'.
    - apply OK1.
    - apply OKa1.
  }
  assert (Hsa2 : 
            forall x, InT x t2 ->
             InT x (filter_acc f (if f e then add e acc else acc) t1) -> False).
  {
    intros a Ha Ka.
    destruct (filter_spec2' _ _ _ Ka) as [Ja | Ja].
    - case_eq (f e); intro He; rewrite He in Ja.
      + rewrite add_spec in Ja; [ | apply OKa].
        destruct Ja as [Ja | Ja].
        * apply (gt_tree_not_in H6).
          apply (In_1 Ja Ha).
        * apply (Hsa a); [ | assumption].
          apply InRight; apply Ha.
      + apply (Hsa a); [ | assumption].
        apply InRight; apply Ha.
    - generalize (H5 a Ja); rewrite Oeset.compare_lt_gt, (H6 a Ha).
      discriminate.
  }
  simpl; split; intro H; simpl in H.
  + (* 1/2 *)
    rewrite (IHt2 _ _ _ OK2 OKa2 Hsa2) in H.
    destruct H as [H | H].
    * destruct H as [H1 H2].
      left; split; [ | apply H2].
      unfold elements; simpl.
      rewrite elements_app; apply in_or_app.
      do 2 right; rewrite elements_app, <- app_nil_end.
      apply H1.
    * rewrite (IHt1 _ _ _ OK1 OKa1 Hsa1) in H.
      {
        destruct H as [H | H].
        - destruct H as [H1 H2].
          left; split; [ | apply H2].
          unfold elements; simpl.
          rewrite elements_app; apply in_or_app.
          left; apply H1.
        - case_eq (f e); intro He; rewrite He in H.
          + unfold elements in H; simpl in H.
            assert (Ke : ~InT e acc).
            {
              intro Ke.
              apply (Hsa e).
              - apply IsRoot; apply Oeset.compare_eq_refl.
              - apply Ke.
            } 
            rewrite (add_spec'' Ke) in H.
            destruct H as [H | H].
            * subst x; left; split; [ | assumption].
              unfold elements; simpl.
              rewrite elements_app.
              apply in_or_app; right; left; apply refl_equal.
            * right; assumption.
          + right; assumption.
      }
  + destruct H as [H | H].
    * destruct H as [H1 H2].
      unfold elements in H1.
      simpl in H1.
      rewrite elements_app in H1.
      {
        destruct (in_app_or _ _ _ H1) as [K | K].
        - rewrite IHt2.
          + right.
            rewrite IHt1.
            * left; split; assumption.
            * assumption.
            * assumption.
            * assumption.
          + assumption.
          + assumption.
          + assumption.
        - rewrite IHt2.
          simpl in K; destruct K as [K | K].
          + subst x; right.
            rewrite IHt1, H2.
            * right.
              rewrite add_spec''; [left; apply refl_equal | ].
              intro He; apply (Hsa e).
              apply IsRoot; apply Oeset.compare_eq_refl.
              assumption.
            * assumption.
            * assumption.
            * assumption.
          + left; split; assumption.
          + assumption.
          + assumption.
          + assumption.
      }
    * {
        rewrite IHt2.
         - right.
           rewrite IHt1.
           + right.
             case (f e); [ | assumption].
             rewrite add_spec''; [right; assumption | ].
             intro He; apply (Hsa e); [ | assumption].
             apply IsRoot; apply Oeset.compare_eq_refl.
           + assumption.
           + assumption.
           + assumption.
         - assumption.
         - assumption.
         - assumption.
      }
Qed.

(** * Partition *)

Lemma partition_spec1' : forall s acc f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') -> forall x : elt,
 InT x (partition_acc f acc s)#1 <->
 InT x acc#1 \/ InT x s /\ f x = true.
Proof.
  intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
  (* 1/2 *)
  intros [acc1 acc2] f Hf x; simpl; split.
  intro H; left; exact H.
  intros [H | [H _]]; [exact H | inversion H].
  (* 1/1 *)
  intros [acc1 acc2] f Hf x; simpl; split.
  (* 1/2 *)
  intro H; rewrite IHt2 in H.
  rewrite IHt1 in H.
  destruct H as [[H | H] | H].
  case_eq (f e); intro He; rewrite He in H.
  simpl in H; rewrite add_spec' in H; destruct H as [H | H].
  right; split; [apply (IsRoot _ _ _ H) | ].
  rewrite (Hf x e); [apply He | apply (IsRoot _ _ _ H) | apply H].
  left; assumption.
  left; assumption.
  right; split; [apply InLeft; apply (proj1 H) | apply (proj2 H)].
  right; split; [apply InRight; apply (proj1 H) | apply (proj2 H)].
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
  (* 1/1 *)
  intro H; rewrite IHt2.
  rewrite IHt1.
  destruct H as [H | [H1 H2]].
  do 2 left; case (f e); [simpl; rewrite add_spec'; right | ]; apply H.
  rewrite In_node_iff in H1.
  destruct H1 as [H1 | [H1 | H1]].
  left; right; split; assumption.
  do 2 left.
  rewrite <- (Hf x e); [rewrite H2; simpl; rewrite add_spec'; left | apply IsRoot| ]; apply H1.
  right; split; assumption.
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
Qed.

Lemma partition_spec2' : forall s acc f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') -> forall x : elt,
 InT x (partition_acc f acc s)#2 <->
 InT x acc#2 \/ InT x s /\ f x = false.
Proof.
  intro s; induction s as [ | t1 IHt1 e t2 IHt2 h].
  (* 1/2 *)
  intros [acc1 acc2] f Hf x; simpl; split.
  intro H; left; exact H.
  intros [H | [H _]]; [exact H | inversion H].
  (* 1/1 *)
  intros [acc1 acc2] f Hf x; simpl; split.
  (* 1/2 *)
  intro H; rewrite IHt2 in H.
  rewrite IHt1 in H.
  destruct H as [[H | H] | H].
  case_eq (f e); intro He; rewrite He in H.
  left; apply H.
  simpl in H; rewrite add_spec' in H; destruct H as [H | H].
  right; split; [apply (IsRoot _ _ _ H) | ].
  rewrite (Hf x e); [apply He | apply (IsRoot _ _ _ H) | apply H].
  left; assumption.
  right; split; [apply InLeft; apply (proj1 H) | apply (proj2 H)].
  right; split; [apply InRight; apply (proj1 H) | apply (proj2 H)].
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
  (* 1/1 *)
  intro H; rewrite IHt2.
  rewrite IHt1.
  destruct H as [H | [H1 H2]].
  case (f e); simpl; do 2 left; [ | rewrite add_spec'; right]; apply H.
  rewrite In_node_iff in H1.
  destruct H1 as [H1 | [H1 | H1]].
  left; right; split; assumption.
  do 2 left.
  rewrite <- (Hf x e); [rewrite H2; simpl; rewrite add_spec'; left | apply IsRoot| ]; apply H1.
  right; split; assumption.
  intros e1 e2 He; apply Hf; apply InLeft; assumption.
  intros e1 e2 He; apply Hf; apply InRight; assumption.
Qed.

Lemma partition_spec1 : forall s f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
 Equal (partition f s)#1 (filter f s).
Proof.
 unfold partition; intros s f P x.
 rewrite partition_spec1', filter_spec; simpl; intuition_in.
Qed.

Lemma partition_spec2 : forall s f,
 (forall e e', InT e s -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
 Equal (partition f s)#2 (filter (fun x => negb (f x)) s).
Proof.
 unfold partition; intros s f P x.
 rewrite partition_spec2', filter_spec; simpl; intuition_in.
 rewrite H1; auto.
 right; split; auto.
 rewrite negb_true_iff in H1; auto.
 apply f_equal; apply P; auto.
Qed.

Instance partition_ok1' : forall s acc f `(Ok s, Ok acc#1),
 Ok (partition_acc f acc s)#1.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros. inv.
 destruct (f e); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto with *.
Qed.

Instance partition_ok2' : forall s acc f `(Ok s, Ok acc#2),
 Ok (partition_acc f acc s)#2.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros. inv.
 destruct (f e); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto with *.
Qed.

Instance partition_ok1 s f `(Ok s) : Ok (partition f s)#1.
Proof. apply partition_ok1'; auto. Qed.

Instance partition_ok2 s f `(Ok s) : Ok (partition f s)#2.
Proof. apply partition_ok2'; auto. Qed.
  
(** * [for_all] and [exists] *)

Lemma for_all_spec : forall s f, Proper (eq_elt==>eq) f ->
 (for_all f s = true <-> For_all (fun x => f x = true) s).
Proof.
 split.
 induction s; simpl; auto; intros; red; intros; inv.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); eauto.
 apply IHs1; auto.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); auto.
 apply IHs2; auto.
 destruct (andb_prop _ _ H0); auto.
 (* <- *)
 induction s; simpl; auto.
 intros. red in H0.
 rewrite IHs1; try red; auto.
 rewrite IHs2; try red; auto.
 generalize (H0 e).
 destruct (f e); simpl; auto.
Qed.

Lemma exists_spec : forall s f, Proper (eq_elt==>eq) f ->
 (exists_ f s = true <-> Exists (fun x => f x = true) s).
Proof.
 split.
 induction s; simpl; intros; rewrite <- ?orb_lazy_alt in *.
 discriminate.
 destruct (orb_true_elim _ _ H0) as [H1|H1].
 destruct (orb_true_elim _ _ H1) as [H2|H2].
 exists e; auto.
 destruct (IHs1 H2); auto; exists x; intuition.
 destruct (IHs2 H1); auto; exists x; intuition.
 (* <- *)
 induction s; simpl; destruct 1 as (x,(U,V)); inv; rewrite <- ?orb_lazy_alt.
 rewrite (H _ _ (Oeset.compare_eq_sym Elt _ _ H0)); rewrite V; auto.
 apply orb_true_intro; left.
 apply orb_true_intro; right; apply IHs1; auto; exists x; auto.
 apply orb_true_intro; right; apply IHs2; auto; exists x; auto.
Qed.


(** * Fold *)

Lemma fold_spec' :
 forall (A : Type) (f : elt -> A -> A) (s : tree) (i : A) (acc : list elt),
 fold_left (flip f) (elements_aux acc s) i = fold_left (flip f) acc (fold f s i).
Proof.
 induction s as [|l IHl x r IHr h]; simpl; intros; auto.
 rewrite IHl.
 simpl. unfold flip at 2.
 apply IHr.
Qed.

Lemma fold_spec :
 forall (s : tree) (A : Type) (i : A) (f : elt -> A -> A),
 fold f s i = fold_left (flip f) (elements s) i.
Proof.
 unfold elements.
 induction s as [|l IHl x r IHr h]; simpl; intros; auto.
 rewrite fold_spec'.
 rewrite IHr.
 simpl; auto.
Qed.


(** * Subset *)

Lemma subsetl_spec : forall subset_l1 l1 x1 h1 s2
 `{Ok (Node l1 x1 Leaf h1), Ok s2},
 (forall s `{Ok s}, (subset_l1 s = true <-> Subset l1 s)) ->
 (subsetl subset_l1 x1 s2 = true <-> Subset (Node l1 x1 Leaf h1) s2 ).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 case_eq (Oeset.compare Elt x1 x2); intro.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (eq_elt a x2).
 apply (Oeset.compare_eq_trans Elt _ _ _ H10 H).
 intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 intro Cax1; assert (Dax1 : Oeset.compare Elt a x1 = Eq).
 apply Oeset.compare_eq_trans with x2; auto.
 rewrite Dax1 in Cax1; discriminate Cax1.
 intros Cax2 Cax1; assert (Dax1 : Oeset.compare Elt a x1 = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 apply Oeset.compare_eq_lt_trans with x2; auto.
 rewrite Dax1 in Cax1; discriminate Cax1.

 rewrite IHl2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (K := H6 a (IsRoot _ _ _ H10)); inversion K; subst.
 assert (Cx : Oeset.compare Elt x1 x2 = Eq).
 apply Oeset.compare_eq_trans with a; auto.
 rewrite Cx in H; discriminate H.
 assumption.
 generalize (H5 _ H11).
 intro Cx2a.
 assert (Cx : Oeset.compare Elt a x1 = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 apply Oeset.compare_lt_trans with x2; auto.
 rewrite Cx in H10; discriminate H10.
 generalize (H7 _ H10).
 intro Cax1.
 assert (K := H6 a (InLeft _ _ _ H10)); inversion K; subst.
 assert (Cax2 : Oeset.compare Elt a x2 = Lt).
 apply Oeset.compare_lt_trans with x1; auto.
 rewrite Cax2 in H11; discriminate H11.
 assumption.
 assert (Cx2a := H5 _ H11). 
 assert (Cx : Oeset.compare Elt x1 x2 = Gt).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 apply Oeset.compare_lt_trans with a; auto.
 rewrite Cx in H; discriminate H.

 unfold Subset. intuition_in.
 constructor 3. 
 rewrite <- andb_lazy_alt, Bool.andb_true_iff, mem_spec in H11.
 rewrite (eq_elt_InT_compat H14); apply H11.
 assumption.
 rewrite <- andb_lazy_alt, Bool.andb_true_iff in H11; destruct H11 as [_ H11]; rewrite H1 in H11.
 apply H11; assumption.
 constructor; trivial.
 rewrite <- andb_lazy_alt, Bool.andb_true_iff; split.
 assert (K := H11 x1 (IsRoot _ _ _ (Oeset.compare_eq_refl Elt x1))).
 inversion K; subst.
 rewrite H14 in H; discriminate H.
 generalize (H4 _ H14); rewrite H; discriminate.
 rewrite mem_spec; assumption.
 rewrite H1.
 intros y Hy; apply H11; apply InLeft; assumption.
 constructor; trivial.
Qed.


Lemma subsetr_spec : forall subset_r1 r1 x1 h1 s2,
 bst (Node Leaf x1 r1 h1) -> bst s2 ->
 (forall s, bst s -> (subset_r1 s = true <-> Subset r1 s)) ->
 (subsetr subset_r1 x1 s2 = true <-> Subset (Node Leaf x1 r1 h1) s2).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 case_eq (Oeset.compare Elt x1 x2); intro.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 apply IsRoot; apply (Oeset.compare_eq_trans Elt _ _ _ H10 H).
 assert (K := H1 a (InRight _ _ _ H9)); inversion K; subst.
  generalize (H8 _ H9).
  rewrite Oeset.compare_lt_gt, CompOpp_iff in H11; simpl in H11.
  rewrite (Oeset.compare_eq_trans Elt _ _ _ H H11); discriminate.
  generalize (Oeset.compare_lt_trans _ _ _ _ (H8 _ H9) (H4 _ H11)); rewrite H; discriminate.
  assumption.

 rewrite <- andb_lazy_alt, andb_true_iff, H1 by auto;  clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 constructor 2. rewrite (eq_elt_InT_compat H11); rewrite <- mem_spec; auto.
 assert (K := H1 x1 (IsRoot _ _ _ (Oeset.compare_eq_refl Elt x1))); inversion K; subst.
 rewrite H in H10; discriminate H10.
 rewrite mem_spec; assumption.
 generalize (H5 _ H10); rewrite lt_gt_elt, H; discriminate.

 rewrite IHr2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (K := H1 a (IsRoot _ _ _ H10)).
 inversion K; subst.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
 rewrite (Oeset.compare_eq_trans _ _ _ _ H10 H11) in H; discriminate H.
 generalize (H4 _ H11).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H; simpl in H.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
 rewrite (Oeset.compare_lt_eq_trans _ _ _ _ H H10); discriminate.
 assumption.
 assert (K := H1 a (InRight _ _ _ H10)).
 inversion K; subst.
 generalize (H8 _ H10).
  rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H; simpl in H.
  rewrite (Oeset.compare_eq_lt_trans _ _ _ _ H11 H); discriminate.
 generalize (Oeset.compare_lt_trans _ _ _ _ (H8 _ H10) (H4 _ H11)); rewrite H; discriminate.
 assumption.
Qed.

Lemma subset_spec : forall s1 s2, Ok s1 -> Ok s2 ->
 ((subset s1 s2 = true <-> Subset s1 s2)).
Proof.
 induction s1 as [|l1 IHl1 x1 r1 IHr1 h1]; simpl; intros.
 unfold Subset; intuition_in.
 destruct s2 as [|l2 x2 r2 h2]; simpl; intros.
 unfold Subset; intuition_in; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 inv.
 case_eq (Oeset.compare Elt x1 x2); intro; intuition.
 (* 1/6 *)
 rewrite <- andb_lazy_alt, andb_true_iff, IHl1, IHr1 in H8 by auto.
 intros y K; inversion K; clear K; subst.
 apply IsRoot; apply Oeset.compare_eq_trans with x1; trivial.
 apply InLeft; apply (proj1 H8); assumption.
 apply InRight; apply (proj2 H8); assumption.
 (* 1/5 *)
 rewrite <- andb_lazy_alt, andb_true_iff, IHl1, IHr1 by auto.
 split; intros y K.
 assert (J := H8 _ (InLeft _ _ _ K)); inversion J; subst.
 generalize (H6 _ K).
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H; simpl in H.
 rewrite (Oeset.compare_eq_trans Elt _ _ _ H10 H); discriminate.
 assumption.
 generalize (Oeset.compare_lt_trans _ _ _ _  (H4 _ H10) (H6 _ K)); rewrite lt_gt_elt, H; discriminate.
 assert (J := H8 _ (InRight _ _ _ K)); inversion J; subst.
 generalize (H7 _ K).
  rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
 rewrite (Oeset.compare_eq_trans Elt _ _ _ H H10); discriminate.
 generalize (Oeset.compare_lt_trans _ _ _ _  (H7 _ K) (H3 _ H10)); rewrite H; discriminate.
 assumption.
 (* 1/4 *)
 rewrite <- andb_lazy_alt, andb_true_iff, (@subsetl_spec (subset l1) l1 x1 h1) in H8; auto.
 unfold Subset; intuition_in.
 rewrite IHr1 in H10; auto.
 (* 1/3 *)
 rewrite <- andb_lazy_alt, andb_true_iff, (@subsetl_spec (subset l1) l1 x1 h1); auto.
 split.
 intros y K; assert (J : InT y (Node l2 x2 r2 h2)).
  apply (H8 y); inversion K; subst.
 apply IsRoot; trivial.
 apply InLeft; trivial.
 inversion H10.
 inversion J; subst.
 inversion K; subst.
 rewrite (Oeset.compare_eq_lt_trans Elt y x1 x2 H11 H) in H10; discriminate H10.
 generalize (H6 _ H11).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
 rewrite (Oeset.compare_lt_eq_trans Elt x1 x2 y H H10); discriminate.
 inversion H11.
 assumption.
 inversion K; subst.
 generalize (H4 _ H10).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite (Oeset.compare_eq_lt_trans Elt y x1 x2 H11 H); discriminate.
 generalize (Oeset.compare_lt_trans Elt _ _ _ (H4 _ H10) (H6 _ H11)); rewrite lt_gt_elt, H; discriminate.
 inversion H11.
 (* 1/3 *)
 rewrite IHr1 by auto; do 2 intro; apply H8; auto.
 (* 1/2 *)
 rewrite <- andb_lazy_alt, andb_true_iff, (@subsetr_spec (subset r1) r1 x1 h1), IHl1 in H8 by auto.
 intros y K; inversion K; subst.
 apply InRight; apply (proj1 H8); apply IsRoot; assumption.
 apply (proj2 H8); assumption.
 apply InRight; apply (proj1 H8); apply InRight; assumption.
 (* 1/1 *)
 rewrite <- andb_lazy_alt, andb_true_iff, (@subsetr_spec (subset r1) r1 x1 h1), IHl1 by auto; split.
 intros y K.
 assert (J : InT y (Node l1 x1 r1 h1)).
 inversion K; subst.
 apply IsRoot; assumption.
 inversion H10.
 apply InRight; assumption.
 assert (L := H8 y J).
 inversion K; subst.
 inversion L; subst.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
 rewrite (Oeset.compare_eq_trans Elt _ _ _ H10 H11) in H; discriminate H.
 generalize (H3 _ H11).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H; simpl in H.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H10; simpl in H10.
  rewrite (Oeset.compare_lt_eq_trans Elt _ _ _ H H10); discriminate.
 assumption.
 inversion H10.
 inversion L; subst.
 generalize (H7 _ H10).
 rewrite Oeset.compare_lt_gt, CompOpp_iff; simpl.
 rewrite Oeset.compare_lt_gt, CompOpp_iff in H; simpl in H.
 rewrite (Oeset.compare_eq_lt_trans Elt _ _ _ H11 H); discriminate.
 generalize (Oeset.compare_lt_trans Elt _ _ _ (H7 _ H10) (H3 _ H11)); rewrite H; discriminate.
 assumption.
 intros y K; apply H8; apply InLeft; assumption.
Qed.


(** * Comparison *)

(** ** Relations [eq] and [lt] over trees *)

Definition L := mk_oelists Elt.

Definition eq := Equal.
Instance eq_equiv : Equivalence eq.
Proof. firstorder. Qed.

Notation eq_lst := (fun l1 l2 => Oeset.compare L l1 l2 = Eq).
Notation lt_lst := (fun l1 l2 => Oeset.compare L l1 l2 = Lt).

Lemma eq_Leq : forall s s', Ok s -> Ok s' -> (eq s s' <-> eq_lst (elements s) (elements s')).
Proof.
 unfold eq, Equal; intros s s' Hs Hs'; split; intro H.
 assert (H' : forall a, InA eq_elt a (elements s) <-> InA eq_elt a (elements s')).
 intro a; rewrite 2 elements_spec1; apply H.
 assert (Ks := elements_spec2 Hs).
 assert (Ks' := elements_spec2 Hs').
 clear H; set (ss := elements s) in *; clearbody ss.
 set (ss' := elements s') in *; clearbody ss'.
 simpl.
 revert ss' H' Ks Ks'; induction ss as [ | e ss]; intros [ | e' ss'] H' Ks Ks'.
 (* 1/5 *)
 apply refl_equal.
 (* 1/4 *)
 apply False_rec.
 assert (Abs : InA eq_elt e' (e' :: ss')).
 left; apply Oeset.compare_eq_refl.
 rewrite <- H' in Abs; inversion Abs.
 (* 1/3 *)
 apply False_rec.
 assert (Abs : InA eq_elt e (e :: ss)).
 left; apply Oeset.compare_eq_refl.
 rewrite H' in Abs; inversion Abs.
 (* 1/2 *)
 assert (Aux : forall (e e' : elt) (ss ss' : list elt),
     (forall a : elt, InA eq_elt a (e :: ss) <-> InA eq_elt a (e' :: ss')) ->
     Sorted lt_elt (e :: ss) ->
     Sorted lt_elt (e' :: ss') -> InA eq_elt e ss' -> False).
 clear e e' ss ss' IHss H' Ks Ks'; intros e e' ss ss' H' Ks Ks'.
 intro Aux; assert (K : lt_elt e' e).
 inversion Ks'; subst.
 refine (@SortA_InfA_InA _ eq_elt _ lt_elt _ _ ss' _ _ _ _ _); auto.
 apply equiv_eq_elt.
 apply st_ord_lt_elt.
 apply proper_e_e_lt_elt.
 assert (H'' : InA eq_elt e' (e :: ss)).
 (* 1/4 *)
 rewrite H'; left; apply Oeset.compare_eq_refl.
 (* 1/3 *)
 inversion H''; subst.
 simpl in K; rewrite H0 in K; discriminate K.
 assert (K' : lt_elt e e').
 refine (@SortA_InfA_InA _ eq_elt _ lt_elt _ _ ss _ _ _ _ _); auto.
 apply equiv_eq_elt.
 apply st_ord_lt_elt.
 apply proper_e_e_lt_elt.
 inversion Ks; auto.
 inversion Ks; auto.
 simpl in K, K'; rewrite lt_gt_elt in K'; rewrite K' in K; discriminate.
 (* 1/2 *)
 simpl; rewrite IHss; [ | | inversion Ks; auto | inversion Ks'; auto].
 (* 1/3 *)
 clear IHss.
 assert (H : eq_elt e e'); [ | rewrite H; apply refl_equal].
 (* 1/3 *)
 assert (H : InA eq_elt e (e' :: ss')).
 (* 1/4 *)
 rewrite <- H'; left; apply Oeset.compare_eq_refl.
 (* 1/3 *)
 inversion H; subst; [assumption | ].
 apply False_rec; apply (Aux e e' ss ss' H' Ks Ks' H1).
  (* 1/2 *)
 intro a; split; intro Ha.
 assert (Ka : InA eq_elt a (e :: ss)); [right; assumption | ].
 rewrite H' in Ka; inversion Ka; subst; [ | assumption].
 apply False_rec; apply (Aux e' e ss' ss); auto.
 intro b; rewrite H'; split; exact (fun h => h).
 apply InA_eqA with a; [apply equiv_eq_elt | | ]; assumption.
 assert (Ka : InA eq_elt a (e' :: ss')); [right; assumption | ].
 rewrite <- H' in Ka; inversion Ka; subst; [ | assumption].
 apply False_rec; apply (Aux e e' ss ss'); auto.
 apply InA_eqA with a; [apply equiv_eq_elt | | ]; assumption.
 (* 1/1 *)
 intro a; rewrite <- 2 elements_spec1.
 set (ss := elements s) in *; clearbody ss.
 set (ss' := elements s') in *; clearbody ss'.
 revert ss' H; induction ss as [ | e ss]; intros [ | e' ss'] H.
 split; exact (fun h => h).
 discriminate H.
 discriminate H.
 revert H; simpl.
 case_eq (Oeset.compare Elt e e'); intros He Hss; [ | discriminate Hss | discriminate Hss].
 split; intro H; inversion H; subst.
 left; apply Oeset.compare_eq_trans with e; assumption.
 right; rewrite <- IHss; assumption.
 left; apply Oeset.compare_eq_trans with e'; [ | apply Oeset.compare_eq_sym ]; assumption.
 right; rewrite (IHss ss'); assumption.
Qed.

Definition lt (s1 s2 : tree) : Prop :=
 exists s1', exists s2', Ok s1' /\ Ok s2' /\ eq s1 s1' /\ eq s2 s2'
   /\ lt_lst (elements s1') (elements s2').

Instance lt_strorder : StrictOrder lt.
Proof.
 split.
 intros s (s1 & s2 & B1 & B2 & E1 & E2 & L).
 assert (H: eq s1 s2).
  transitivity s; [symmetry | ]; assumption.
  rewrite (eq_Leq B1 B2) in H.
  rewrite H in L; discriminate.
 intros s1 s2 s3 (s1' & s2' & B1 & B2 & E1 & E2 & L12)
                 (s2'' & s3' & B2' & B3 & E2' & E3 & L23).
 exists s1', s3'; do 4 (split; trivial).
 apply (Oeset.compare_lt_trans L) with (elements s2'); [assumption | ].
 assert (H : eq s2' s2'').
 transitivity s2; [symmetry | ]; assumption.
 rewrite eq_Leq in H; [ | apply B2 | apply B2'].
 apply (Oeset.compare_eq_lt_trans _ _ _ _ H L23).
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof.
 intros s1 s2 E12 s3 s4 E34. split.
 intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
 exists s1', s3'; do 2 (split; trivial).
  split. transitivity s1; auto. symmetry; auto.
  split; auto. transitivity s3; auto. symmetry; auto.
 intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
 exists s1', s3'; do 2 (split; trivial).
  split. transitivity s2; auto.
  split; auto. transitivity s4; auto.
Qed.


(** * Proof of the comparison algorithm *)

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)

Fixpoint flatten_e (e : enumeration) : list elt := match e with
  | End => nil
  | More x t r => x :: elements t ++ flatten_e r
 end.

Lemma flatten_e_elements :
 forall l x r h e,
 elements l ++ flatten_e (More x r e) = elements (Node l x r h) ++ flatten_e e.
Proof.
 intros; simpl; apply elements_node.
Qed.

Lemma cons_1 : forall s e,
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto; intros.
 rewrite IHs1; apply flatten_e_elements.
Qed.

(** Correctness of this comparison *)

Definition Cmp c x y := CompSpec eq_lst lt_lst x y c.

Local Hint Unfold Cmp flip.

Lemma compare_end_Cmp :
 forall e2, Cmp (compare_end e2) nil (flatten_e e2).
Proof.
 destruct e2; simpl; constructor; auto. 
Qed.

Lemma compare_more_Cmp : forall x1 cont x2 r2 e2 l,
  Cmp (cont (cons r2 e2)) l (elements r2 ++ flatten_e e2) ->
   Cmp (compare_more x1 cont (More x2 r2 e2)) (x1::l)
      (flatten_e (More x2 r2 e2)).
Proof.
 simpl; intros; unfold Cmp; simpl; case_eq (Oeset.compare Elt x1 x2); intro Cx12.
 inversion H; subst; [constructor 1 | constructor 2 | constructor 3]; simpl.
 rewrite Cx12; apply H1.
 rewrite Cx12; apply H1.
 rewrite (Oeset.compare_eq_sym Elt _ _ Cx12); apply H1.
 constructor 2; simpl; rewrite Cx12; apply refl_equal.
 constructor 3; simpl; rewrite (Oeset.compare_lt_gt Elt), CompOpp_iff in Cx12; rewrite Cx12; apply refl_equal.
Qed.

Lemma compare_cont_Cmp : forall s1 cont e2 l,
 (forall e, Cmp (cont e) l (flatten_e e)) ->
 Cmp (compare_cont s1 cont e2) (elements s1 ++ l) (flatten_e e2).
Proof.
 induction s1 as [|l1 Hl1 x1 r1 Hr1 h1]; simpl; intros; auto.
 rewrite <- elements_node; simpl.
 apply Hl1; auto. clear e2. intros [|x2 r2 e2].
 simpl; auto.
 apply compare_more_Cmp.
 rewrite <- cons_1; auto.
Qed.

Lemma compare_Cmp : forall s1 s2,
 Cmp (compare s1 s2) (elements s1) (elements s2).
Proof.
 intros; unfold compare.
 rewrite (app_nil_end (elements s1)).
 replace (elements s2) with (flatten_e (cons s2 End)) by
  (rewrite cons_1; simpl; rewrite <- app_nil_end; auto).
 apply compare_cont_Cmp; auto.
 intros.
 apply compare_end_Cmp; auto.
Qed.

Lemma compare_spec : forall s1 s2, Ok s1 -> Ok s2 ->
  (CompSpec eq lt s1 s2 (compare s1 s2)).
Proof.
 intros.
 destruct (compare_Cmp s1 s2); constructor.
 rewrite eq_Leq; auto.
 intros; exists s1, s2; repeat split; auto.
 intros; exists s2, s1; repeat split; auto.
Qed.


(** * Equality test *)

Lemma equal_spec : forall s1 s2, Ok s1 -> Ok s2 ->
 (equal s1 s2 = true <-> eq s1 s2).
Proof.
unfold equal; intros s1 s2 B1 B2.
destruct (@compare_spec s1 s2 B1 B2) as [H|H|H];
 split; intros H'; auto; try discriminate.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
Qed.

(** Encapsulation *)

Record set : Type := Mkt { this : tree; is_ok : Ok this }.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Arguments Mkt this {is_ok}.
Hint Resolve is_ok : typeclass_instances.

Definition In_ (x : elt)(s : set) := In x s.(this).
Definition Equal_ (s s' : set) := forall a : elt, In_ a s <-> In_ a s'.
Definition Subset_ (s s' : set) := forall a : elt, In_ a s -> In_ a s'.
Definition Empty_ (s : set) := forall a : elt, ~ In_ a s.
Definition For_all_ (P : elt -> Prop)(s : set) := forall x, In_ x s -> P x.
Definition Exists_ (P : elt -> Prop)(s : set) := exists x, In_ x s /\ P x.

Definition mem_ (x : elt)(s : set) := mem x s.(this).
Definition add_ (x : elt)(s : set) : set := Mkt (add x s.(this)).
Definition remove_ (x : elt)(s : set) : set := Mkt (remove x s.(this)).
Definition singleton_ (x : elt) : set := Mkt (singleton x).
Definition union_ (s s' : set) : set := Mkt (union s.(this) s'.(this)).
Definition inter_ (s s' : set) : set := Mkt (inter s.(this) s'.(this)).
Definition diff_ (s s' : set) : set := Mkt (diff s.(this) s'.(this)).
Definition equal_ (s s' : set) := equal s.(this) s'.(this).
Definition subset_ (s s' : set) := subset s.(this) s'.(this).
Definition empty_ : set := Mkt empty.
Definition is_empty_ (s : set) : bool := is_empty s.(this).
Definition elements_ (s : set) : list elt := elements s.(this).
Definition choose_ (s : set) : option elt := choose s.(this).
Definition fold_ (A : Type) (f : elt -> A -> A) (s : set) : A -> A := fold f s.(this).
Definition cardinal_ (s : set) := cardinal s.(this).
Definition filter_ (f : elt -> bool) (s : set) : set := Mkt (filter f s.(this)).
Definition for_all_ (f : elt -> bool) (s : set) := for_all f s.(this).
Definition exists__ (f : elt -> bool) (s : set) := exists_ f s.(this).
Definition partition_ (f : elt -> bool) (s : set) : set * set :=
 let p := partition f s.(this) in (Mkt (fst p), Mkt (snd p)).
Definition eq_ : set -> set -> Prop := Equal_.
Definition compare_ (s s' : set) : comparison := compare s.(this) s'.(this).

Instance eq_equiv_ : Equivalence (fun s s' : set => equal_ s s' = true).
Proof. 
unfold equal_; split.
intro s; rewrite (equal_spec s.(is_ok) s.(is_ok)); unfold eq, Equal; exact (fun _ => conj (fun h => h) (fun h => h)).
intros s1 s2;  rewrite (equal_spec s1.(is_ok) s2.(is_ok)),  (equal_spec s2.(is_ok) s1.(is_ok)); unfold eq, Equal.
intros H a; split; intro K; [rewrite H | rewrite <- H]; assumption.
intros s1 s2 s3;  rewrite (equal_spec s1.(is_ok) s2.(is_ok)),  (equal_spec s2.(is_ok) s3.(is_ok)),  (equal_spec s1.(is_ok) s3.(is_ok)); unfold eq, Equal.
intros H12 H23 a; split; intro K; [rewrite <- H23, <- H12 | rewrite  H12, H23]; assumption.
Qed.

Lemma equal_spec_ : forall s s',  equal_ s s' = true <-> (forall e : elt, mem_ e s = mem_ e s').
Proof. 
intros s s'; unfold equal_, mem_.
rewrite (equal_spec s.(is_ok) s'.(is_ok)).
unfold eq, Equal.
split.
(* 1/2 *)
intros H x.
case_eq (mem x s.(this)).
rewrite (mem_spec x s.(is_ok)); intro Hx; apply sym_eq; rewrite (mem_spec x s'.(is_ok)), <- H; assumption.
intro Hx; assert (Kx : mem x s.(this) <> true); [rewrite Hx; discriminate | ].
assert (Kx' : mem x s'.(this) <> true).
intro Jx; apply Kx.
rewrite (mem_spec x s.(is_ok)), H, <- (mem_spec x s'.(is_ok)); assumption.
revert Kx'.
case (mem x s'.(this)); [intro Abs; apply False_rec; apply Abs; apply refl_equal | exact (fun _ => refl_equal _)].
(* 1/1 *)
intros H x.
rewrite <- (mem_spec x s.(is_ok)), <- (mem_spec x s'.(is_ok)), H.
exact (conj (fun h => h) (fun h => h)).
Qed.

Lemma subset_spec_ : forall s s' : set, subset_ s s' = true <->  (forall e : elt, mem_ e s = true -> mem_ e s' = true).
Proof.
intros s s'; unfold equal_, mem_.
rewrite (subset_spec s.(is_ok) s'.(is_ok)).
unfold Subset.
split.
(* 1/2 *)
intros H x.
rewrite (mem_spec x s.(is_ok)); intro Hx; rewrite (mem_spec x s'.(is_ok)); apply H; assumption.
(* 1/1 *)
intros H x Hx.
rewrite <- (mem_spec x s'.(is_ok)); apply H; rewrite (mem_spec x s.(is_ok)); assumption.
Qed.

Lemma empty_spec_ : forall e, mem_ e empty_ = false.
Proof. intro e; apply refl_equal. Qed.

Lemma is_empty_spec_ : forall s : set, is_empty_ s = equal_ s empty_.
Proof.
intro s; unfold is_empty_, equal_, empty_; simpl.
case_eq (is_empty s.(this)); intro Hs.
rewrite (is_empty_spec s.(this)) in Hs; case_eq (s.(this)).
intros _; apply refl_equal.
intros l x r h Ks; apply False_rec; apply (Hs x); rewrite Ks; apply IsRoot; apply (Oeset.compare_eq_refl Elt).
assert (Ks : is_empty s.(this) <> true); [rewrite Hs; discriminate | ].
assert (Js : equal s.(this) empty <> true).
intro Js; apply Ks; clear Hs Ks.
rewrite (is_empty_spec s.(this)).
case_eq (s.(this)).
intros _ e He; inversion He.
intros l x r h Hs; rewrite Hs, equal_spec in Js; unfold eq, Equal in Js.
assert (Hx : InT x empty).
rewrite <- Js; apply IsRoot; apply (Oeset.compare_eq_refl Elt).
inversion Hx.
rewrite <- Hs; apply is_ok.
auto.
revert Js; case (equal s.(this) empty).
intro Abs; apply False_rec; apply Abs; apply refl_equal.
exact (fun _ => refl_equal _).
Qed.

Lemma add_spec_ : 
  forall (s : set) (x y : elt), mem_ y (add_ x s)  = match Oeset.compare Elt y x with Eq => true | _ => false end ||| mem_ y s.
Proof.
intros s x y; unfold mem_, add_; simpl.
generalize (add_spec (s := s.(this)) x y); rewrite <- mem_spec; [ | apply add_ok; apply is_ok].
case_eq (mem y (add x s.(this))); intro H.
intro K; generalize (refl_equal true); rewrite K; clear K; intro K; destruct K as [K | K].
rewrite K; apply refl_equal.
rewrite <- mem_spec in K; [rewrite K, <- orb_lazy_alt, Bool.orb_true_r; apply refl_equal | apply is_ok].
case_eq (Oeset.compare Elt y x); simpl; intros Hxy Abs.
apply False_rec; assert (Abs2 : false = true); [ | discriminate Abs2].
rewrite Abs; left; apply refl_equal.
case_eq (mem y s.(this)); [ | exact (fun _ => refl_equal _)].
rewrite Abs; intro K; right; rewrite <- mem_spec; [assumption | apply is_ok].
case_eq (mem y s.(this)); [ | exact (fun _ => refl_equal _)].
rewrite Abs; intro K; right; rewrite <- mem_spec; [assumption | apply is_ok].
Qed.

Lemma remove_spec_ : 
   forall (s : set) (x y : elt), 
      mem_ y (remove_ x s) = mem_ y s &&& negb (match Oeset.compare Elt y x with Eq => true | _ => false end).
Proof.
intros s x y; unfold mem_, remove_; simpl.
generalize (remove_spec (s := s.(this)) x y).
case_eq (Oeset.compare Elt y x); intro Hxy; simpl; intro H; [rewrite <- andb_lazy_alt, Bool.andb_false_r | rewrite <- andb_lazy_alt, andb_true_r | rewrite <- andb_lazy_alt, andb_true_r].
(* 1/3 *)
case_eq (mem y (remove x s.(this))); [ | exact (fun _ => refl_equal _)].
rewrite mem_spec; [ | apply remove_ok; apply is_ok].
rewrite H; intros [_ K]; apply False_rec; apply K; apply refl_equal.
(* 1/2 *)
case_eq (mem y (remove x (this s))); intro K.
rewrite mem_spec in K; [ | apply remove_ok; apply is_ok].
rewrite H in K; destruct K as [K _].
apply sym_eq; rewrite mem_spec; [assumption | apply is_ok].
assert (J : mem y (remove x s.(this)) <> true); [rewrite K; discriminate | ].
assert (L : mem y s.(this) <> true).
intro L; apply J.
clear K J.
rewrite mem_spec; [ | apply remove_ok; apply is_ok].
rewrite H; split; [ | discriminate].
rewrite <- mem_spec; [assumption | apply is_ok].
revert L; case (mem y s.(this)); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
(* 1/3 *)
case_eq (mem y (remove x (this s))); intro K.
rewrite mem_spec in K; [ | apply remove_ok; apply is_ok].
rewrite H in K; destruct K as [K _].
apply sym_eq; rewrite mem_spec; [assumption | apply is_ok].
assert (J : mem y (remove x s.(this)) <> true); [rewrite K; discriminate | ].
assert (L : mem y s.(this) <> true).
intro L; apply J.
clear K J.
rewrite mem_spec; [ | apply remove_ok; apply is_ok].
rewrite H; split; [ | discriminate].
rewrite <- mem_spec; [assumption | apply is_ok].
revert L; case (mem y s.(this)); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma singleton_spec_ : 
  forall x y : elt, mem_ y (singleton_ x) = match Oeset.compare Elt y x with Eq => true | _ => false end.
Proof.
intros x y; unfold mem_, singleton_; simpl; apply refl_equal.
Qed.

Lemma union_spec_ :
   forall (s s' : set) (x : elt), mem_ x (union_ s s') = mem_ x s ||| mem_ x s'.
Proof.
intros s s' x; unfold mem_, union_; simpl.
case_eq (mem x s.(this)); intro Hs.
rewrite mem_spec in Hs; [ | apply is_ok].
simpl; rewrite mem_spec; [ | apply union_ok; apply is_ok].
rewrite (union_spec x (is_ok s) (is_ok s')); left; assumption.
case_eq (mem x s'.(this)); intro Hs'.
rewrite mem_spec in Hs'; [ | apply is_ok].
simpl; rewrite mem_spec; [ | apply union_ok; apply is_ok].
rewrite (union_spec x (is_ok s) (is_ok s')); right; assumption.
simpl; assert (K : mem x (union s.(this) s'.(this)) <> true).
intro H; rewrite mem_spec in H; [ | apply union_ok; apply is_ok].
rewrite union_spec in H; [ | apply is_ok | apply is_ok].
destruct H as  [H | H]; (rewrite <- mem_spec in H; [ | apply is_ok]).
rewrite H in Hs; discriminate Hs.
rewrite H in Hs'; discriminate Hs'.
revert K; case (mem x (union s.(this) s'.(this))); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma inter_spec_ : forall (s s' : set) (x : elt), mem_ x (inter_ s s') = mem_ x s &&& mem_ x s'.
Proof.
intros s s' x; unfold mem_, inter_; simpl.
case_eq (mem x s.(this)); intro Hs.
rewrite mem_spec in Hs; [ | apply is_ok].
case_eq (mem x s'.(this)); intro Hs'.
rewrite mem_spec in Hs'; [ | apply is_ok].
simpl; rewrite mem_spec; [ | apply inter_ok; apply is_ok].
rewrite (inter_spec x); split; assumption.
assert (Ks' : mem x s'.(this) <> true); [rewrite Hs'; discriminate | ].
simpl; assert (K : mem x (inter s.(this) s'.(this)) <> true).
intro H; apply Ks'.
simpl; rewrite mem_spec in H; [ | apply inter_ok; apply is_ok].
rewrite (inter_spec x) in H.
rewrite mem_spec; [apply (proj2 H) | apply is_ok].
revert K; case (mem x (inter s.(this) s'.(this))); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
assert (Ks : mem x s.(this) <> true); [rewrite Hs; discriminate | ].
simpl; assert (K : mem x (inter s.(this) s'.(this)) <> true).
intro H; apply Ks.
simpl; rewrite mem_spec in H; [ | apply inter_ok; apply is_ok].
rewrite (inter_spec x) in H.
rewrite mem_spec; [apply (proj1 H) | apply is_ok].
revert K; case (mem x (inter s.(this) s'.(this))); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma diff_spec_ :  forall (s s' : set) (x : elt), mem_ x (diff_ s s') = mem_ x s &&& negb (mem_ x s').
Proof.
intros s s' x; unfold mem_, diff_; simpl. 
case_eq (mem x s.(this)); intro Hs.
rewrite mem_spec in Hs; [ | apply is_ok]; simpl.
case_eq (mem x s'.(this)); intro Hs'; simpl.
rewrite mem_spec in Hs'; [ | apply is_ok]; simpl.
assert (K : mem x (diff s.(this) s'.(this)) <> true).
intro H; rewrite mem_spec in H; [ | apply diff_ok; apply is_ok].
rewrite diff_spec in H; [ | apply is_ok | apply is_ok].
destruct H as [_ H]; apply H; assumption.
revert K; case (mem x (diff s.(this) s'.(this))); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
rewrite mem_spec; [ | apply diff_ok; apply is_ok].
rewrite diff_spec; [ | apply is_ok | apply is_ok].
split; [assumption | ].
intro H; rewrite <- mem_spec in H; [ | apply is_ok].
rewrite H in Hs'; discriminate Hs'.
simpl; assert (Ks : mem x s.(this) <> true); [rewrite Hs; discriminate | ].
assert (K : mem x (diff s.(this) s'.(this)) <> true).
intro K; apply Ks.
rewrite mem_spec; [ | apply is_ok].
rewrite mem_spec in K; [ | apply diff_ok; apply is_ok].
rewrite diff_spec in K; [ | apply is_ok | apply is_ok].
destruct K as [K _]; apply K.
revert K; case (mem x (diff s.(this) s'.(this))); [ | exact (fun _ => refl_equal _)].
intro Abs; apply False_rec; apply Abs; apply refl_equal.
Qed.

Lemma  fold_spec_ : 
  forall (s : set) (A : Type) (i : A) (f : elt -> A -> A), fold_ f s i = fold_left (fun (a : A) (e : elt) => f e a) (elements_ s) i. 
Proof.
intros s A i f; unfold fold_, elements_.
rewrite fold_spec; apply refl_equal.
Qed.

Lemma cardinal_spec_ : forall s : set, cardinal_ s = length (elements_ s).
Proof.
intro s; unfold cardinal_, elements_; simpl.
rewrite cardinal_spec; [apply refl_equal | apply is_ok].
Qed.

Lemma filter_spec_ :
  forall (s : set) (x : elt) (f : elt -> bool),
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> mem_ x (filter_ f s) = mem_ x s &&& f x.
Proof.
intros [s ok_s] x f Hf; unfold mem_, filter_; simpl.
case_eq (mem x (filter f s)); intro Hx.
apply sym_eq; rewrite <- andb_lazy_alt, Bool.andb_true_iff.
rewrite mem_spec in Hx; [ | apply filter_ok; apply ok_s].
rewrite (mem_spec _ ok_s); rewrite filter_spec in Hx; [apply Hx | ].
do 3 intro; apply Hf; unfold mem_; simpl; rewrite (mem_spec _ ok_s); assumption.
assert (Kx : mem x (filter f s) <> true).
rewrite Hx; discriminate.
case_eq (mem x s); intro Jx.
case_eq (f x); intro Lx.
apply False_rec; apply Kx.
rewrite mem_spec; [ | apply filter_ok; apply ok_s].
rewrite filter_spec.
split; [apply mem_impl_InT | ]; assumption.
do 3 intro; apply Hf; unfold mem_; simpl; rewrite (mem_spec _ ok_s); assumption.
apply refl_equal.
apply refl_equal.
Qed.

Lemma filter_spec2_ :
  forall (s : set) (f : elt -> bool), subset_ (filter_ f s) s = true.
Proof.
intros [s ok_s] f; unfold filter_; rewrite subset_spec_; unfold mem_; simpl.
intros x.
rewrite 2 mem_spec.
apply filter_spec2.
apply ok_s.
apply filter_ok; apply ok_s.
Qed.

Lemma filter_spec3_ :
  forall (s : set) (f : elt -> bool) x, 
    (List.In x (elements_ (filter_ f s))) <->
    (List.In x (elements_ s) /\ f x = true). 
Proof.
intros [s ok_s] f x; unfold filter_, elements_, filter; simpl.
rewrite filter_spec3'.
- split; intro H.
  + destruct H as [H | H].
    * apply H.
    * contradiction H.
  + left; apply H.
- assumption.
- left.
- intros e _ Abs; inversion Abs.
Qed.

Lemma for_all_spec_ :
  forall (s : set) (f : elt -> bool), for_all_ f s = forallb f (elements_ s).
Proof.
intros s f; unfold for_all_, elements_; simpl.
set (t := this s); clearbody t; clear s.
induction t as [ | t1 IH1 e t2 IH2 h]; simpl.
apply refl_equal.
rewrite (app_nil_end (elements (Node t1 e t2 h))), <- elements_node, <- app_nil_end.
rewrite forallb_app; simpl; rewrite IH1, IH2.
case (f e); simpl; [ | rewrite Bool.andb_false_r]; apply refl_equal.
Qed.

Lemma exists_spec_ : 
  forall (s : set) (f : elt -> bool), exists__ f s = existsb f (elements_ s).
Proof.
intros s f; unfold exists__, elements_; simpl.
set (t := this s); clearbody t; clear s.
induction t as [ | t1 IH1 e t2 IH2 h]; simpl.
apply refl_equal.
rewrite (app_nil_end (elements (Node t1 e t2 h))), <- elements_node, <- app_nil_end.
rewrite existsb_app; simpl; rewrite IH1, IH2.
case (f e); simpl; [rewrite Bool.orb_true_r | ]; apply refl_equal.
Qed.

Lemma partition_spec1_ : 
    forall f s, (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    equal_ (fst (partition_ f s)) (filter_ f s) = true.
Proof.
intros f s Hf; unfold equal_, partition_, filter_; simpl.
rewrite equal_spec; [ | apply partition_ok1; apply is_ok | apply filter_ok; apply is_ok].
unfold eq; simpl.
apply (partition_spec1 f). 
do 3 intro; apply Hf.
unfold mem_; rewrite mem_spec; [assumption | apply is_ok].
Qed.

Lemma partition_spec2_ :
    forall f s, (forall e e',  mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    equal_ (snd (partition_ f s)) (filter_ (fun x => negb (f x)) s) = true.
Proof.
intros f s Hf; unfold equal_, partition_, filter_; simpl.
rewrite equal_spec; [ | apply partition_ok2; apply is_ok | apply filter_ok; apply is_ok].
apply (partition_spec2 f). 
do 3 intro; apply Hf.
unfold mem_; rewrite mem_spec; [assumption | apply is_ok].
Qed.


Lemma choose_spec1_ : forall s x, choose_ s = Some x -> mem_ x s = true.
Proof.
intros s x; unfold choose_, mem_; simpl.
rewrite mem_spec; [ | apply is_ok].
apply choose_spec1.
Qed.

Lemma choose_spec2_ : forall s, choose_ s = None -> is_empty_ s = true.
Proof.
intros s; unfold choose_, is_empty_; simpl.
rewrite is_empty_spec.
apply choose_spec2.
Qed.

Lemma choose_spec3_ :
  forall s1 s2, equal_ s1 s2 = true ->
                match choose_ s1, choose_ s2 with
                  | None, None => True
                  | Some e1, Some e2 => Oeset.compare Elt e1 e2 = Eq
                  | _, _ => False
                end.
Proof.
intros [s1 ok1] [s2 ok2]; unfold choose_, choose; simpl; intro Hs.
assert (Ks := compare_Cmp s1 s2).
unfold equal_, equal in Hs; rewrite compare_eq_true in Hs.
simpl in Hs; rewrite Hs in Ks.
inversion Ks; clear Hs Ks.
case_eq (min_elt s1); [intros e1 Hs1 | intro Hs1];
(case_eq (min_elt s2); [intros e2 Hs2 | intro Hs2]).
- assert (He2 : InT e2 s1).
  {
    generalize (min_elt_spec1 _ Hs2).
    rewrite <- elements_spec1, InA_alt.
    intros [e [He Ke]].
    rewrite <- elements_spec1, InA_alt.
    set (l1 := elements s1) in *; clearbody l1.
    set (l2 := elements s2) in *; clearbody l2.
    revert l2 H Ke;
      induction l1 as [ | x1 l1];
      intros l2 H Ke.
    - destruct l2; [ | discriminate H].
      contradiction Ke.
    - destruct l2 as [ | x2 l2]; [discriminate H | ].
      simpl in H.
      case_eq (Oeset.compare Elt x1 x2);
        intro Hx; rewrite Hx in H; try discriminate H.
      simpl in Ke; destruct Ke as [Ke | Ke].
      + subst x2.
        exists x1; split; [ | left; apply refl_equal].
        refine (Oeset.compare_eq_trans _ _ _ _ He _).
        rewrite Oeset.compare_lt_gt, Hx; apply refl_equal.
      + destruct (IHl1 _ H Ke) as [y [Hy Ky]].
        exists y; split; [ | right]; assumption.
  }
  assert (He1 : InT e1 s2).
  {
    generalize (min_elt_spec1 _ Hs1).
    rewrite <- elements_spec1, InA_alt.
    intros [e [He Ke]].
    rewrite <- elements_spec1, InA_alt.
    set (l1 := elements s1) in *; clearbody l1.
    set (l2 := elements s2) in *; clearbody l2.
    revert l2 H Ke;
      induction l1 as [ | x1 l1];
      intros l2 H Ke.
    - contradiction Ke.
    - destruct l2 as [ | x2 l2]; [discriminate H | ].
      simpl in H.
      case_eq (Oeset.compare Elt x1 x2);
        intro Hx; rewrite Hx in H; try discriminate H.
      simpl in Ke; destruct Ke as [Ke | Ke].
      + subst x1.
        exists x2; split; [ | left; apply refl_equal].
        refine (Oeset.compare_eq_trans _ _ _ _ He Hx).
      + destruct (IHl1 _ H Ke) as [y [Hy Ky]].
        exists y; split; [ | right]; assumption.
  }
  generalize (@min_elt_spec2 s1 e1 e2 ok1 Hs1 He2).
  generalize (@min_elt_spec2 s2 e2 e1 ok2 Hs2 He1).
  rewrite (Oeset.compare_lt_gt _ e2 e1).
  destruct (Oeset.compare Elt e1 e2); trivial.
  + intro Abs; apply False_rec; apply Abs; apply refl_equal.
  + intros _ Abs; apply False_rec; apply Abs; apply refl_equal.
- generalize (min_elt_spec3 Hs2).
  unfold Empty.
  intro Abs; apply (Abs e1).
  generalize (min_elt_spec1 _ Hs1).
  rewrite <- elements_spec1, InA_alt.
  intros [e [He Ke]].
  rewrite <- elements_spec1, InA_alt.
  set (l1 := elements s1) in *; clearbody l1.
  set (l2 := elements s2) in *; clearbody l2.
  revert l2 H Ke;
    induction l1 as [ | x1 l1];
    intros l2 H Ke.
  + contradiction Ke.
  + destruct l2 as [ | x2 l2]; [discriminate H | ].
    simpl in H.
    case_eq (Oeset.compare Elt x1 x2);
        intro Hx; rewrite Hx in H; try discriminate H.
      simpl in Ke; destruct Ke as [Ke | Ke].
    * subst x1.
      exists x2; split; [ | left; apply refl_equal].
      refine (Oeset.compare_eq_trans _ _ _ _ He Hx).
    * destruct (IHl1 _ H Ke) as [y [Hy Ky]].
      exists y; split; [ | right]; assumption.
- generalize (min_elt_spec3 Hs1).
  unfold Empty.
  intro Abs; apply (Abs e2).
  generalize (min_elt_spec1 _ Hs2).
  rewrite <- elements_spec1, InA_alt.
  intros [e [He Ke]].
  rewrite <- elements_spec1, InA_alt.
  set (l1 := elements s1) in *; clearbody l1.
  set (l2 := elements s2) in *; clearbody l2.
  revert l2 H Ke;
    induction l1 as [ | x1 l1];
    intros l2 H Ke.
  + destruct l2 as [ | x2 l2]; [contradiction Ke | discriminate H].
  + destruct l2 as [ | x2 l2]; [discriminate H | ].
    simpl in H.
    case_eq (Oeset.compare Elt x1 x2);
        intro Hx; rewrite Hx in H; try discriminate H.
      simpl in Ke; destruct Ke as [Ke | Ke].
    * subst x2.
      exists x1; split; [ | left; apply refl_equal].
      refine (Oeset.compare_eq_trans _ _ _ _ He _).
      rewrite Oeset.compare_lt_gt, Hx.
      apply refl_equal.
    * destruct (IHl1 _ H Ke) as [y [Hy Ky]].
      exists y; split; [ | right]; assumption.
- exact I.
Qed.

Lemma compare_eq_trans_ : forall a1 a2 a3, compare_ a1 a2 = Eq -> compare_ a2 a3 = Eq -> compare_ a1 a3 = Eq.
Proof.
destruct lt_strorder as [HI HT].
unfold compare_.
intros s1 s2 s3.
assert (H12 := compare_spec s1.(is_ok) s2.(is_ok)).
assert (H23 := compare_spec s2.(is_ok) s3.(is_ok)).
assert (H13 := compare_spec s1.(is_ok) s3.(is_ok)).
inversion H12; [ | discriminate | discriminate].
inversion H23; [ | discriminate | discriminate].
intros _ _; inversion H13; [apply refl_equal | | ].
assert (K13 := Equivalence_Transitive (Equivalence := eq_equiv) _ _ _ H0 H2).
assert (K3 := Equivalence_Reflexive (Equivalence := eq_equiv) s3.(this)).
rewrite (lt_compat K13 K3) in H4.
apply False_rec; apply (HI _ H4).
assert (K13 := Equivalence_Transitive (Equivalence := eq_equiv) _ _ _ H0 H2).
assert (K3 := Equivalence_Reflexive (Equivalence := eq_equiv) s3.(this)).
rewrite (lt_compat K3 K13) in H4.
apply False_rec; apply (HI _ H4).
Qed.

Lemma compare_eq_lt_trans_ : forall a1 a2 a3, compare_ a1 a2 = Eq -> compare_ a2 a3 = Lt -> compare_ a1 a3 = Lt.
Proof.
destruct lt_strorder as [HI HT].
intros s1 s2 s3; unfold compare_; simpl.
assert (K12 := compare_spec s1.(is_ok) s2.(is_ok)).
inversion K12; subst; [intros _ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
assert (H23 := compare_spec s2.(is_ok) s3.(is_ok)).
inversion H23; subst.
(* 1/3 *)
intro Abs; discriminate Abs.
(* 1/2 *)
rewrite <- (lt_compat H0 (Equivalence_Reflexive (Equivalence := eq_equiv) s3.(this))) in H2.
assert (H13 := compare_spec s1.(is_ok) s3.(is_ok)).
inversion H13; subst.
(* 1/4 *)
rewrite (lt_compat H4 (Equivalence_Reflexive (Equivalence := eq_equiv) s3.(this))) in H2.
apply False_rec; apply (HI _ H2).
(* 1/3 *)
intros _; apply refl_equal.
(* 1/2 *)
apply False_rec; apply (HI s1.(this)).
apply HT with s3.(this); assumption.
(* 1/1 *)
intro Abs; discriminate Abs.
Qed.

Lemma compare_lt_eq_trans_ : forall a1 a2 a3, compare_ a1 a2 = Lt -> compare_ a2 a3 = Eq -> compare_ a1 a3 = Lt.
Proof.
destruct lt_strorder as [HI HT].
intros s1 s2 s3; unfold compare_; simpl; intros H12 H23.
assert (K12 := compare_spec s1.(is_ok) s2.(is_ok)); inversion K12; subst.
(* 1/3 *)
rewrite H12 in H; discriminate H.
clear H.
assert (K23 := compare_spec s2.(is_ok) s3.(is_ok)); inversion K23; subst.
(* 1/4 *)
clear H.
rewrite (lt_compat (Equivalence_Reflexive (Equivalence := eq_equiv) s1.(this)) H1) in H0.
assert (K13 := compare_spec s1.(is_ok) s3.(is_ok)); inversion K13; subst.
(* 1/6 *)
rewrite <- (lt_compat (Equivalence_Reflexive (Equivalence := eq_equiv) s1.(this)) H2) in H0.
apply False_rec; apply (HI _ H0).
(* 1/5 *)
apply refl_equal.
(* 1/4 *)
apply False_rec; apply (HI _ (HT _ _ _ H0 H2)).
(* 1/3 *)
rewrite H23 in H; discriminate H.
(* 1/2 *)
rewrite H23 in H; discriminate H.
(* 1/1 *)
rewrite H12 in H; discriminate H.
Qed.

Lemma compare_lt_trans_ : forall a1 a2 a3, compare_ a1 a2 = Lt -> compare_ a2 a3 = Lt -> compare_ a1 a3 = Lt.
Proof.
destruct lt_strorder as [HI HT].
intros s1 s2 s3; unfold compare_; simpl.
intros H12 H23.
assert (K12 := compare_spec s1.(is_ok) s2.(is_ok)); inversion K12.
(* 1/3 *)
rewrite H12 in H; discriminate. 
(* 1/2 *)
assert (K23 := compare_spec s2.(is_ok) s3.(is_ok)); inversion K23.
(* 1/4 *)
rewrite H23 in H1; discriminate.
(* 1/3 *)
assert (H13 := HT _ _ _ H0 H2).
assert (K13 := compare_spec s1.(is_ok) s3.(is_ok)); inversion K13.
(* 1/5 *)
rewrite (lt_compat H4 (Equivalence_Reflexive (Equivalence := eq_equiv) s3.(this))) in H13.
apply False_rec; apply (HI _ H13).
(* 1/4 *)
apply refl_equal.
(* 1/3 *)
apply False_rec; apply (HI s1.(this)); apply HT with s3.(this); assumption.
(* 1/2 *)
rewrite H23 in H1; discriminate.
(* 1/1 *)
rewrite H12 in H; discriminate.
Qed.

Lemma compare_lt_gt_ : forall a1 a2, compare_ a1 a2 = CompOpp (compare_ a2 a1).
Proof.
destruct lt_strorder as [HI HT].
intros s1 s2; unfold compare_; simpl.
assert (K12 := compare_spec s1.(is_ok) s2.(is_ok)); inversion K12.
(* 1/3 *)
assert (H21 := compare_spec s2.(is_ok) s1.(is_ok)).
inversion H21; [apply refl_equal | | ].
assert (K2 := Equivalence_Reflexive (Equivalence := eq_equiv) s2.(this)).
rewrite (lt_compat K2 H0) in H2.
apply False_rec; apply (HI _ H2).
assert (K2 := Equivalence_Reflexive (Equivalence := eq_equiv) s2.(this)).
rewrite (lt_compat H0 K2) in H2.
apply False_rec; apply (HI _ H2).
(* 1/2 *)
assert (K21 := compare_spec s2.(is_ok) s1.(is_ok)); inversion K21.
(* 1/4 *)
rewrite (lt_compat (Equivalence_Reflexive (Equivalence := eq_equiv) s1.(this)) H2) in H0.
apply False_rec; apply (HI _ H0).
(* 1/3 *)
apply False_rec; apply (HI s1.(this)); apply HT with s2.(this); assumption.
(* 1/2 *)
apply refl_equal.
(* 1/1 *)
assert (K21 := compare_spec s2.(is_ok) s1.(is_ok)); inversion K21.
(* 1/3 *)
rewrite (lt_compat H2 (Equivalence_Reflexive (Equivalence := eq_equiv) s1.(this))) in H0.
apply False_rec; apply (HI _ H0).
(* 1/2 *)
apply refl_equal.
(* 1/1 *)
apply False_rec; apply (HI s1.(this)); apply HT with s2.(this); assumption.
Qed.
  
Lemma compare_eq_refl_ : forall a, compare_ a a = Eq.
Proof.
destruct lt_strorder as [HI HT].
unfold compare_.
intros s.
assert (H := compare_spec s.(is_ok) s.(is_ok)).
inversion H; subst.
apply refl_equal.
assert (K := compare_lt_gt_ s s); unfold compare_ in K; rewrite <- H0 in K.
discriminate K.
assert (K := compare_lt_gt_ s s); unfold compare_ in K; rewrite <- H0 in K.
discriminate K.
Qed.

Lemma elements_spec1_ : 
  forall s s', equal_ s s' = true -> comparelA (Oeset.compare Elt) (elements_ s) (elements_ s') = Eq.
Proof.
intros [s ok_s] [s' ok_s'] H; unfold equal_ in H; simpl in H.
rewrite (equal_spec ok_s ok_s'), (eq_Leq ok_s ok_s') in H; simpl in H.
unfold elements_; simpl; apply H.
Qed.

Lemma elements_spec2_ : forall e s, mem_ e s = Oeset.mem_bool Elt e (elements_ s).
Proof.
intros e s; unfold mem_, elements_.
assert (Ms := mem_spec e (is_ok s)).
rewrite <- elements_spec1 in Ms.
case_eq (mem e (this s)); intro He.
(* 1/2 *)
rewrite Ms in He.
set (l := elements (this s)) in *; clearbody l; clear Ms.
apply sym_eq; induction l as [ | a l]; simpl; inversion He as [_a _l H1 H2 | _a _l H1 H2]; subst.
unfold Oeset.eq_bool; rewrite H1; apply refl_equal.
rewrite (IHl H1); unfold Oeset.eq_bool; case (Oeset.compare Elt e a); apply refl_equal.
(* 1/1 *)
assert (Ke : mem e (this s) <> true); [rewrite He; discriminate | ].
rewrite Ms in Ke.
set (l := elements (this s)) in *; clearbody l; clear Ms He.
apply sym_eq; induction l as [ | a l]; simpl.
apply refl_equal.
unfold Oeset.eq_bool; case_eq (Oeset.compare Elt e a); intro He.
apply False_rec; apply Ke; left; apply He.
apply IHl; intro Hl; apply Ke; right; apply Hl.
apply IHl; intro Hl; apply Ke; right; apply Hl.
Qed.

Lemma elements_spec3_ : forall s, Sorted (fun x y => Oeset.compare Elt x y = Lt) (elements_ s).
Proof.
intros [s ok_s]; unfold elements_.
simpl; apply elements_spec2; assumption.
Qed.

Lemma mem_cons1_ : 
  forall a1 l1 a2 l2, Sorted lt_elt (a1 :: l1) -> Sorted lt_elt (a2 :: l2) ->
  (forall x, Oeset.mem_bool Elt x (a1 :: l1) = true -> Oeset.mem_bool Elt x (a2 :: l2) = true) -> 
  ((Oeset.compare Elt a1 a2 = Eq \/ Oeset.compare Elt a1 a2 = Gt) /\
   (forall x, Oeset.mem_bool Elt x l1 = true -> Oeset.mem_bool Elt x l2 = true)).
Proof.
intros a1 l1 a2 l2 Sl1 Sl2 H.
assert (Aux : 
  ((Oeset.compare Elt a1 a2 = Eq /\
   forall x, Oeset.mem_bool Elt x l1 = true -> Oeset.mem_bool Elt x l2 = true) \/ 
   (Oeset.compare Elt a1 a2 = Gt /\
  forall x, Oeset.mem_bool Elt x l1 = true -> Oeset.mem_bool Elt x l2 = true))).
case_eq (Oeset.compare Elt a1 a2); intro Ha12.
(* 1/4 *)
left; split; [apply refl_equal | ].
intros x Hx; generalize (H x).
rewrite (Oeset.mem_bool_unfold _ _ (a1 :: l1)).
rewrite (Oeset.mem_bool_unfold _ _ (a2 :: l2)).
rewrite Hx, Bool.orb_true_r.
intro Kx; generalize (Kx (refl_equal _)); clear Kx.
case_eq (Oeset.mem_bool Elt x l2); intro Kx.
exact (fun _ => refl_equal _).
rewrite Bool.orb_false_r; intro Jx; apply False_rec.
rewrite compare_eq_true in Jx.
rewrite Oeset.mem_bool_true_iff in Hx.
destruct Hx as [x' [Hx Lx]].
generalize (Sorted_extends (Oeset.compare_lt_trans Elt) Sl1).
rewrite Forall_forall.
intro K; assert (K1 := K x' Lx).
assert (Abs : Oeset.compare Elt a1 x' = Eq).
apply Oeset.compare_eq_trans with a2; [assumption | ].
apply Oeset.compare_eq_trans with x.
rewrite Oeset.compare_lt_gt, Jx; apply refl_equal.
exact Hx.
rewrite Abs in K1; discriminate K1.
(* 1/3 *)
apply False_rec.
generalize (H a1).
rewrite (Oeset.mem_bool_unfold _ _ (a1 :: l1)), Oeset.compare_eq_refl, Bool.orb_true_l.
rewrite (Oeset.mem_bool_unfold _ _ (a2 :: l2)), Ha12, Bool.orb_false_l.
intro K; generalize (K (refl_equal _)); clear K; intro K.
rewrite Oeset.mem_bool_true_iff in K.
destruct K as [a1' [K J]].
generalize (Sorted_extends (Oeset.compare_lt_trans Elt) Sl2).
rewrite Forall_forall.
intro L; assert (L1 := L a1' J).
assert (Abs : Oeset.compare Elt a1 a1' = Lt).
apply Oeset.compare_lt_trans with a2; assumption.
simpl in K; rewrite Abs in K; discriminate K.
(* 1/2 *)
right; split; [apply refl_equal | ].
intros x Hx; generalize (H x).
rewrite (Oeset.mem_bool_unfold _ _ (a1 :: l1)), Hx, Bool.orb_true_r.
rewrite (Oeset.mem_bool_unfold _ _ (a2 :: l2)).
intro Kx; generalize (Kx (refl_equal _)); clear Kx.
case_eq (Oeset.mem_bool Elt x l2); intro Kx.
exact (fun _ => refl_equal _).
rewrite Bool.orb_false_r; intro Jx; apply False_rec.
rewrite compare_eq_true in Jx.
rewrite Oeset.mem_bool_true_iff in Hx.
destruct Hx as [x' [Hx Lx]].
generalize (Sorted_extends (Oeset.compare_lt_trans Elt) Sl1).
rewrite Forall_forall.
intro K; assert (K1 := K x' Lx).
assert (Abs : Oeset.compare Elt a1 a1 = Lt).
apply Oeset.compare_lt_trans with x'; [assumption | ].
apply Oeset.compare_eq_lt_trans with x.
rewrite Oeset.compare_lt_gt, Hx; apply refl_equal.
apply Oeset.compare_eq_lt_trans with a2; [assumption | ].
rewrite Oeset.compare_lt_gt, Ha12; apply refl_equal.
generalize (Oeset.compare_lt_gt Elt a1 a1); rewrite Abs; discriminate.
destruct Aux as [[H1 H2] | [H1 H2]].
split; [ | apply H2].
left; assumption.
split; [ | apply H2].
right; assumption.
Qed.

Lemma cardinal_eqset_ : forall s1 s2, equal_ s1 s2 = true -> cardinal_ s1 = cardinal_ s2.
Proof.
intros s1 s2 H.
rewrite 2 cardinal_spec_.
generalize (elements_spec1_ s1 s2 H).
set (l1 := elements_ s1); clearbody l1.
set (l2 := elements_ s2); clearbody l2.
revert l2; induction l1 as [ | a1 l1]; intros [ | a2 l2]; simpl.
exact (fun _ => refl_equal _).
intro Abs; discriminate Abs.
intro Abs; discriminate Abs.
case (Oeset.compare Elt a1 a2); [ | intro Abs; discriminate Abs | intro Abs; discriminate Abs].
intro Hl; rewrite (IHl1 l2 Hl); apply refl_equal.
Qed.

Lemma cardinal_subset_ : forall s1 s2, subset_ s1 s2 = true -> (cardinal_ s1 <= cardinal_ s2)%nat.
Proof.
intros s1 s2 H.
rewrite subset_spec_ in H.
assert (H' : forall e, Oeset.mem_bool Elt e (elements_ s1) = true -> Oeset.mem_bool Elt e (elements_ s2) = true).
intro e; rewrite <- 2 elements_spec2_; apply H.
clear H; rewrite 2 cardinal_spec_; unfold elements_ in *.
generalize (elements_spec2 (is_ok s1)) (elements_spec2 (is_ok s2)) (elements_spec2w (is_ok s1)) (elements_spec2w (is_ok s2)).
set (l1 := elements (this s1)) in *; clearbody l1; clear s1.
set (l2 := elements (this s2)) in *; clearbody l2; clear s2.
revert l2 H'; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; simpl.
(* 1/4 *)
exact (fun _ _ _ _ => le_n 0).
(* 1/3 *)
intros _ _ _ _; apply le_O_n.
(* 1/2 *)
intros _ _ _ _; generalize (H a1); simpl; unfold Oeset.eq_bool; rewrite Oeset.compare_eq_refl; 
intro Abs; generalize (Abs (refl_equal _)); discriminate.
(* 1/1 *)
intros Sl1 Sl2 Nl1 Nl2.
apply le_n_S; apply IHl1.
destruct (mem_cons1_ Sl1 Sl2 H) as [_ H2]; apply H2.
inversion Sl1; assumption.
inversion Sl2; assumption.
inversion Nl1; assumption.
inversion Nl2; assumption.
Qed.

Lemma compare_spec_ : forall s1 s2, compare_ s1 s2 = Eq <-> equal_ s1 s2 = true.
Proof.
intros [s1 is_ok1] [s2 is_ok2]; unfold compare_, equal_; simpl this.
rewrite equal_spec; [ | assumption | assumption].
assert (Aux := compare_spec is_ok1 is_ok2).
assert (Aux2 := lt_strorder).
inversion Aux2.
inversion Aux; split.
exact (fun _ => H0).
exact (fun _ => refl_equal _).
intro Abs; discriminate Abs.
intro H1; apply False_rec; apply (StrictOrder_Irreflexive s2).
rewrite H1 in H0; assumption.
intro Abs; discriminate Abs.
intro H1; apply False_rec; apply (StrictOrder_Irreflexive s2).
rewrite H1 in H0; assumption.
Qed.

Lemma filter_true_ : 
  forall (s : set), equal_ (filter_ (fun _ => true) s) s = true.
Proof.
intro s.
rewrite equal_spec_.
intro x.
rewrite 2 elements_spec2_, eq_iff_eq_true.
rewrite 2 Oeset.mem_bool_true_iff.
split; intros [y [H1 H2]]; (exists y; split; [assumption | ]).
- rewrite filter_spec3_ in H2; apply (proj1 H2).
- rewrite filter_spec3_; split; trivial.
Qed.

Lemma filter_and_ : 
  forall f1 f2 (s : set), 
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f1 e = f1 e') -> 
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f2 e = f2 e') -> 
    equal_ (filter_ (fun t => f1 t && f2 t) s) 
          (inter_ (filter_ (fun t => f1 t) s) (filter_ (fun t => f2 t) s)) = true.
Proof.
intros f1 f2 s H1 H2.
rewrite equal_spec_.
intro x; rewrite inter_spec_, 3 filter_spec_.
- case (mem_ x s); simpl; [ | apply refl_equal].
  case (f1 x); apply refl_equal.
- assumption.
- assumption.
- intros x1 x2 Hx H.
  rewrite (H1 _ _ Hx H), (H2 _ _ Hx H).
  apply refl_equal.
Qed.

Lemma filter_or_ : 
  forall f1 f2 (s : set), 
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f1 e = f1 e') -> 
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f2 e = f2 e') -> 
    equal_ (filter_ (fun t => f1 t || f2 t) s) (union_ (filter_ (fun t => f1 t) s) (filter_ (fun t => f2 t) s)) = true.
Proof.
intros f1 f2 s H1 H2.
rewrite equal_spec_.
intro x; rewrite union_spec_, 3 filter_spec_.
- case (mem_ x s); simpl; [ | apply refl_equal].
  case (f1 x); apply refl_equal.
- assumption.
- assumption.
- intros x1 x2 Hx H.
  rewrite (H1 _ _ Hx H), (H2 _ _ Hx H).
  apply refl_equal.
Qed.

Lemma filter_not_ : 
  forall f (s : set), 
    (forall e e', mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') -> 
    equal_ (filter_ (fun t => negb (f t)) s) (diff_ s (filter_ (fun t => f t) s)) = true.
Proof.
intros f s H.
rewrite equal_spec_.
intro x; rewrite diff_spec_, 2 filter_spec_.
- case (mem_ x s); simpl; apply refl_equal.
- apply H.
- intros x1 x2 K Hx.
  apply f_equal.
  apply H; assumption.
Qed.

Lemma partition_spec1__ :
  forall (s : set) (x : elt) (f : elt -> bool),
    (forall e e' : elt,
       mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') ->
    mem_ x (partition_ f s)#1 = mem_ x s && f x.
Proof.
intros s x f Hf.
assert (H := partition_spec1_ f s Hf).
rewrite equal_spec_ in H.
rewrite H.
apply (filter_spec_ s x f Hf).
Qed.

Lemma partition_spec2__ :
  forall (s : set) (x : elt) (f : elt -> bool),
    (forall e e' : elt,
       mem_ e s = true -> Oeset.compare Elt e e' = Eq -> f e = f e') ->
    mem_ x (partition_ f s)#2 = mem_ x s && negb (f x).
Proof.
intros s x f Hf.
assert (H := partition_spec2_ f s Hf).
rewrite equal_spec_ in H.
rewrite H.
apply (filter_spec_ s x).
intros e e' He Ke; apply f_equal.
apply Hf; assumption.
Qed.

Lemma filter_spec_weak_ : 
  forall (s : set) (x : elt) (f : elt -> bool),
    mem_ x (filter_ f s) = true -> mem_ x s = true.
Proof.
intros s x f; assert (H := filter_spec2_ s f).
rewrite subset_spec_ in H.
apply H.
Qed.

Lemma elements_empty_ : elements_ empty_ = nil.
Proof.
unfold empty_, elements_, elements; simpl; apply refl_equal.
Qed.

Lemma choose_spec3__ :
  forall s1 s2 : set,
    equal_ s1 s2 = true ->
    match choose_ s1 with
      | Some e1 =>
        match choose_ s2 with
          | Some e2 => Oeset.compare Elt e1 e2 = Eq
          | None => False
        end
      | None => choose_ s2 = None
    end.
Proof.
intros s1 s2 Hs; generalize (choose_spec3_ _ _ Hs).
case (choose_ s1); case (choose_ s2); trivial.
intros e Abs; contradiction Abs.
Qed.


Close Scope Int_scope.

End Make.

Section Sec.

Hypothesis elt : Type.
Hypothesis Elt : Oset.Rcd elt.

Definition Elt_ := oeset_of_oset Elt.

Lemma for_all_spec_alt_ :
  forall (f : elt -> bool) (s : set Elt_),
  for_all_ f s = true <-> (forall e : elt, mem_ e s = true -> f e = true).
Proof.
intros f s; rewrite for_all_spec_, forallb_forall; split; intros H e He; apply H.
- rewrite elements_spec2_, Oeset.mem_bool_true_iff in He.
  destruct He as [e' [He He']].
  unfold Elt_ in He; simpl in He.
  generalize (Oset.eq_bool_ok Elt e e'); rewrite He; intro; subst e'.
  assumption.
- rewrite elements_spec2_, Oeset.mem_bool_true_iff.
  exists e; split; [ | assumption].
  rewrite Oeset.compare_eq_refl; apply refl_equal.
Qed.

Lemma exists_spec__ :
  forall (f : elt -> bool) (s : set Elt_),
    exists__ f s = true <-> (exists e : elt, mem_ e s = true /\ f e = true).
Proof.
intros f s; rewrite exists_spec_, existsb_exists; split; 
(intros [e [He H]]; exists e; split; [ | assumption]).
- rewrite elements_spec2_, Oeset.mem_bool_true_iff.
  exists e; split; [ | assumption].
  rewrite Oeset.compare_eq_refl; apply refl_equal.
- rewrite elements_spec2_, Oeset.mem_bool_true_iff in He.
  destruct He as [e' [He He']].
  unfold Elt_ in He; simpl in He.
  generalize (Oset.eq_bool_ok Elt e e'); rewrite He; intro; subst e'.
  assumption.
Qed.

Lemma filter_spec__ :
  forall (s : set Elt_) (x : elt) (f : elt -> bool),
    mem_ x (filter_ f s) = mem_ x s && f x.
Proof.
intros s x f; apply filter_spec_.
intros e e' _ H; simpl in H.
generalize (Oset.eq_bool_ok Elt e e'); rewrite H.
apply f_equal.
Qed.

Lemma elements_spec1__ :
  forall s s' : set Elt_, equal_ s s' = true -> elements_ s = elements_ s'.
Proof.
intros s s' H1.
assert (H2 := elements_spec1_ s s' H1); simpl in H2.
assert (H3 := comparelA_eq_bool_ok (Oset.compare Elt) (elements_ s) (elements_ s')).
rewrite H2 in H3; apply H3.
intros a1 a2 _ _; apply Oset.eq_bool_ok.
Qed.

Lemma partition_spec1___ :
  forall (s : set Elt_) (x : elt) (f : elt -> bool),
  mem_ x (fst (partition_ f s)) = mem_ x s && f x.
Proof.
intros s x f.
apply partition_spec1__.
intros e1 e2 _ He; unfold Elt_ in *.
simpl in He.
assert (Aux := Oset.eq_bool_true_iff Elt e1 e2).
unfold Oset.eq_bool in Aux.
rewrite He in Aux.
apply f_equal; rewrite <- Aux.
apply refl_equal.
Qed.

Lemma partition_spec2___ :
forall (s : set Elt_) (x : elt) (f : elt -> bool),
  mem_ x (snd (partition_ f s)) = mem_ x s && negb (f x).
Proof.
intros s x f.
apply partition_spec2__.
intros e1 e2 _ He; unfold Elt_ in *.
simpl in He.
assert (Aux := Oset.eq_bool_true_iff Elt e1 e2).
unfold Oset.eq_bool in Aux.
rewrite He in Aux.
apply f_equal; rewrite <- Aux.
apply refl_equal.
Qed.

Lemma choose_spec3___ : 
  forall s1 s2 : set Elt_, equal_ s1 s2 = true -> choose_ s1 = choose_ s2.
Proof.
intros s1 s2 Hs;
generalize (choose_spec3_ _ _ Hs).
destruct (choose_ s1); destruct (choose_ s2); trivial.
- unfold Elt_; simpl.
  intro H; generalize (Oset.eq_bool_ok Elt e e0); rewrite H.
  apply f_equal.
- intros Abs; contradiction Abs.
- intros Abs; contradiction Abs.
Qed.

End Sec.
