Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.general_locks.
Require Import bst.pair_conc.
Import FashNotation.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_pair := Tstruct _Pair noattr.
Definition t_struct_pair_impl := Tstruct _PairImpl noattr.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Inductive pair_snapshot :=
| left_pair (val: Z) (version: nat)
| right_pair (val: Z) (version: nat)
| pair_snap (left_val: Z) (right_val: Z) (version: nat).

Definition pair_join (a b: pair_snapshot): option pair_snapshot :=
  match a, b with
  | left_pair c1 v1, right_pair c2 _ => Some (pair_snap c1 c2 v1)
  | right_pair c2 _, left_pair c1 v1 => Some (pair_snap c1 c2 v1)
  | _, _ => None
  end.

#[local] Instance pairJoin: sepalg.Join pair_snapshot :=
  fun p1 p2 p3 => pair_join p1 p2 = Some p3.

#[local] Instance pairPerm': sepalg.Perm_alg pair_snapshot.
Proof.
  constructor; intros; repeat red in H; try repeat red in H0.
  - destruct x, y, z, z'; simpl in H, H0; inversion H; inversion H0; subst; auto.
  - destruct a, b, d; simpl in H; inversion H; subst; simpl in H0; inversion H0.
  - do 2 red. destruct a, b, c; simpl in H; inversion H; subst; simpl; auto.
  - destruct a, a', b; inversion H; subst; simpl in H0; inversion H0.
Qed.

#[local] Instance pairPerm: sepalg.Perm_alg (option pair_snapshot).
Proof. apply psepalg.Perm_lower. apply pairPerm'. Qed.

#[local] Instance pairSep: sepalg.Sep_alg (option pair_snapshot).
Proof. apply psepalg.Sep_lower. Defined.

Definition valid_pair (a: option pair_snapshot) := a <> None.

#[local] Program Instance pairGhost: Ghost :=
  { G := option pair_snapshot;
    valid := valid_pair;
    Join_G := psepalg.Join_lower pairJoin }.
Next Obligation.
  intros. destruct a, b, x; red in H;
    unfold psepalg.Join_lower in H; inversion H; subst; auto. 1: red; auto.
Abort.
