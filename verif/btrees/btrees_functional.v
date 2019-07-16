Require Import VST.floyd.functional_base.
Require Import VST.floyd.proofauto.
Require Import VST.progs.conclib.
Require Import Program.Basics. (* for compose *)
Require Import Program.Combinators. (* for compose notation "∘" *)

Definition param: Z := 8.
Definition max_depth: Z := 20.

Lemma param_eq: param = 8. Proof. reflexivity. Qed.
Lemma max_depth_eq: max_depth = 20. Proof. reflexivity. Qed.
Opaque param. Opaque max_depth.

Hint Rewrite param_eq: rep_omega. Hint Rewrite max_depth_eq: rep_omega.

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

Unset Elimination Schemes.
Inductive node: Type :=
| leaf: forall (records: list (K * V)) (address: val), node
| internal: forall (ptr0: node) (children: list (K * node)) (address: val), node.

Inductive balanced: Z -> node -> Prop :=
| balanced_leaf: forall {l p}, balanced 0 (leaf l p)
| balanced_internal: forall {d ptr0 l p}, balanced d ptr0 -> Forall (balanced d ∘ snd) l ->
                                     balanced (Z.succ d) (internal ptr0 l p). 

Instance Inhabitant_node: Inhabitant node :=
  leaf (combine (upto (Z.to_nat param)) (Zrepeat param nullV)) nullval.

Definition is_leaf (n: node): Prop :=
  match n with
  | leaf _ _ => True
  | _ => False
  end.

Definition is_leaf_dec (n: node): {is_leaf n} + {not (is_leaf n)} :=
  match n as m return {is_leaf m} + {not(is_leaf m)} with
  | leaf _ _ => left I
  | internal _ _ _ => right (fun hcontr => hcontr)
  end.

Definition keys (n: node): list K := 
  match n with
  | leaf recs _ => map fst recs
  | internal _ children _ => map fst children
  end.

Definition node_address (n: node): val := 
  match n with | leaf _ p => p | internal _ _ p => p end.

Arguments node_address n: simpl nomatch.

Definition num_keys (n: node): Z :=
  match n with leaf l _ => Zlength l | internal _ l _ => Zlength l end.

(* Abstracting a node to an ordered list of (key,value) pairs *)
Fixpoint abs_node (n: node): list (K * V) :=
  match n with
  | leaf le _ => le
  | internal ptr0 le _ => abs_node ptr0 ++ flat_map (abs_node ∘ snd) le
  end.

Fixpoint num_records (n: node): Z :=
  match n with
  | leaf le _ => Zlength le
  | internal ptr0 le _ => num_records ptr0 + fold_right Z.add 0 (map (num_records ∘ snd) le)
  end.

Lemma node_ind (P: node -> Prop)
      (hleaf: forall l p, P (leaf l p))
      (hinternal: forall ptr0 l p, P ptr0 -> Forall (P ∘ snd) l -> P (internal ptr0 l p)) : forall n, P n.
Proof.
  fix hrec 1.
  intros [].
  apply hleaf.
  apply hinternal. apply hrec.
  induction children as [|[k n] children]. constructor.
  constructor. cbn. apply hrec. assumption.
Qed.

Lemma numrec_abs_node_length n : Zlength (abs_node n) = num_records n.
Proof.
  apply (node_ind (fun n => Zlength (abs_node n) = num_records n)).
  + intros. reflexivity.
  + intros * hlength hforall.
    simpl. rewrite Zlength_app, hlength, flat_map_concat_map, Zlength_concat,
           map_map. do 2 f_equal.
    apply map_ext_in.
    intros [k n']. rewrite Forall_forall in hforall.
    apply hforall.
Qed.

Inductive cursor: forall (root: node), Type :=
| leaf_cursor: forall {l p} (k: K) (ptr: V) (i: Z)
                 (hi: 0 <= i < Zlength l)
                 (h: Znth i l = (k, ptr)), cursor (leaf l p) 
| ptr0_cursor: forall {ptr0: node} {l p} (tl: cursor ptr0), cursor (internal ptr0 l p)
| le_child_cursor: forall {ptr0 l p} (k: K) (child: node) (i: Z)
                     (hi: 0 <= i < Zlength l)
                     (h: Znth i l = (k, child))
                     (tl: cursor child), cursor (internal ptr0 l p).
