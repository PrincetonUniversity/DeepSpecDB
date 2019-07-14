(** * btrees.v : Formal Model of BTrees  *)
From Equations Require Import Equations.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import Sorting.Sorted.
Require Import Program.Basics. (* for compose *)
Require Import Program.Combinators. (* for compose notation "∘" *)

Import ListNotations.

Definition param: nat := 8.
Definition max_depth: nat := 20.

Definition K: Type := Z.
Definition V: Type := {p: val | is_pointer_or_null p}.
Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

Instance Inhabitant_V: Inhabitant V := nullV.
Instance EqDecV: EqDec V.
Proof.
  intros [x hx] [y hy]. destruct (eq_dec x y) as [heq | hneq].
  + left. now apply exist_ext.
  + right. intro hcontr. apply hneq. inversion hcontr. reflexivity.
Qed.

(* B+tree abtract model *)
Inductive node: Z -> Type :=
| leaf: forall (records: list (K * V)) (address: val), node 0
| internal: forall {d} (ptr0: node d) (children: list (K * node d)) (address: val), node (Z.succ d).

Definition is_leaf {d} (n: node d): Prop :=
  match n with
  | leaf _ _ => True
  | _ => False
end.

Definition is_leaf_dec {d} (n: node d): {is_leaf n} + {not (is_leaf n)} :=
match n as m return {is_leaf m} + {not(is_leaf m)} with
| leaf _ _ => left I
| internal _ _ _ _ => right (fun hcontr => hcontr)
end.

Definition keys {d} (n: node d): list K := 
  match n with
  | leaf recs _ => map fst recs
  | internal _ _ children _ => map fst children
  end.

Definition address {d} (n: node d): val := 
  match n with | leaf _ p => p | internal _ _ _ p => p end.

(* number of keys in a node *)
Definition num_keys {d} (n: node d) : Z :=
match n with leaf l _ => Zlength l | internal _ _ l _ => Zlength l end.

Section node_ind.
  Variables (P: forall d, node d -> Prop) (Q : forall d, list (K * node d) -> Prop).

  Hypotheses
    (hleaf: forall l v, P 0 (leaf l v))
    (hinternal : forall d ptr0 (entries: list (K * node d)) v,
        P d ptr0 -> Q d entries -> P (Z.succ d) (internal ptr0 entries v))
    (hnil : forall d, Q d [])
    (hcons : forall d (k: K) (n: node d), P d n -> forall l: list (K * node d), Q d l -> Q d (cons (k,n) l)).

  Fixpoint general_node_ind {d} (n: node d): P d n :=
    match n as x in node d return P d x with
    | leaf l v => hleaf l v
    | internal d ptr0 l v =>
      hinternal d ptr0 l v (general_node_ind ptr0)
                (((fix l_ind (l':list (K * node d)) : Q d l' :=
                     match l' as x return Q d x with
                     | nil => hnil d
                     | cons (k1, n1) tl => hcons d k1 n1 (general_node_ind n1) tl (l_ind tl)
                     end)) l)
    end.
End node_ind.
(*
Section node_rect.
  Variables (P : node -> Type) (Q : list (K * node)-> Type).

  Hypotheses
    (hleaf: forall l v, P (leaf l v))
    (hinternal : forall ptr0 (entries:list (K * node)) v,
        P ptr0 -> Q entries -> P (internal ptr0 entries v))
    (hnil : Q [])
    (hcons : forall (k: K) (n: node), P n -> forall l: list (K * node), Q l -> Q (cons (k,n) l)).

  Fixpoint general_node_rect (n: node): P n :=
    match n as x return P x with
    | leaf l v => hleaf l v
    | internal ptr0 l v =>
      hinternal ptr0 l v (general_node_rect ptr0)
                (((fix l_ind (l':list (K * node)) : Q l' :=
                     match l' as x return Q x with
                     | nil => hnil
                     | cons (k1, n1) tl => hcons k1 n1 (general_node_rect n1) tl (l_ind tl)
                     end)) l)
    end.
End node_rect.
*)

Lemma node_ind2 (P: forall d, node d -> Prop)
        (hleaf: forall entries val, P 0 (leaf entries val))
        (hinternal : forall d ptr0 (entries:list (K * node d)) val,
            P d ptr0 -> Forall (P d ∘ snd) entries -> P (Z.succ d) (internal ptr0 entries val)):
  forall d (n: node d), P d n.
Proof.
  apply general_node_ind with (Q := fun d l => Forall (P d ∘ snd) l).
  assumption. assumption. easy. now constructor.
Qed.

(*
Definition node_rect2 (P: node -> Type)
        (hleaf: forall entries val, P (leaf entries val))
        (hinternal : forall ptr0 (entries:list (K * node)) val,
            P ptr0 -> (forall e, In e entries -> P (snd e)) -> P (internal ptr0 entries val)):
  forall n: node, P n.
Proof.
  refine (general_node_rect P (fun entries => forall e, In e entries -> P (snd e)) hleaf hinternal _ _).
  easy.
  intros k n hn l hl kn hinkn%in_inv.
  destruct (in_dec (prod_eqdec Z.eq_dec node_eq_dec) kn l) as [h|h]. apply (hl _ h).
  destruct (prod_eqdec Z.eq_dec node_eq_dec kn (k, n)) as [h'|h']. subst. easy.
  exfalso. apply h. destruct hinkn. subst; contradiction. assumption.
Qed.
*)

(* Abstracting a B+tree to an ordered list of (key,value) pairs *)
Fixpoint abs_node {d} (n: node d) : list (K * V) :=
  match n with
  | leaf le _ => le
  | internal _ ptr0 le _ => abs_node ptr0 ++ flat_map (abs_node ∘ snd) le
  end.

(* Number of records the B+tree is holding *)
Fixpoint num_records {d} (n: node d): Z :=
  match n with
  | leaf le _ => Zlength le
  | internal _ ptr0 le _ => num_records ptr0 + fold_right Z.add 0 (map (num_records ∘ snd) le)
  end.

Lemma numrec_abs_node_length {d} (n: node d): Zlength (abs_node n) = num_records n.
Proof.
  apply (node_ind2 (fun _ n => Zlength (abs_node n) = num_records n)).
  + intros. reflexivity.
  + intros * hlength hforall.
    simpl. rewrite Zlength_app, hlength, flat_map_concat_map, Zlength_concat,
    map_map. do 2 f_equal.
    apply map_ext_in.
    intros [k n']. rewrite Forall_forall in hforall.
    apply hforall.
Qed.

Inductive cursor: forall {d} (root: node d), Type :=
| leaf_cursor: forall {l p} (k: K) (ptr: V) (i: Z)
                 (hi: 0 <= i < Zlength l)
                 (h: Znth i l = (k, ptr)), cursor (leaf l p) 
| ptr0_cursor: forall {d} {ptr0: node d} {l p} (tl: cursor ptr0), cursor (internal ptr0 l p)
| le_child_cursor: forall {d ptr0 l p} (k: K) (child: node d) (i: Z)
                     (hi: 0 <= i < Zlength l)
                     (h: @Znth _ (k, child) i l = (k, child))
                  (tl: cursor child), cursor (internal ptr0 l p).
