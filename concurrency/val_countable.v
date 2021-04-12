Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Bool.Bool.
Require Import stdpp.countable.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import Flocq.IEEE754.Binary.

Instance val_eq_dec: EqDecision val := Val.eq.

Local Definition val_eq_type : Type :=
  unit + int + int64 + float + float32 + (block * ptrofs).

Local Instance ptrofs_eq_dec: EqDecision ptrofs := Ptrofs.eq_dec.
Local Instance int64_eq_dec: EqDecision int64 := Int64.eq_dec.
Local Instance int_eq_dec: EqDecision int := Int.eq_dec.

Local Definition val2val_eq (v: val) : val_eq_type :=
  match v with
  | Vundef => inl (inl (inl (inl (inl tt))))
  | Vint u => inl (inl (inl (inl (inr u))))
  | Vlong u => inl (inl (inl (inr u)))
  | Vfloat u => inl (inl (inr u))
  | Vsingle u => inl (inr u)
  | Vptr b p => inr (pair b p)
  end.

Local Definition val_eq2val (v: val_eq_type): val :=
  match v with
  | inl (inl (inl (inl (inl tt)))) => Vundef
  | inl (inl (inl (inl (inr u)))) => Vint u
  | inl (inl (inl (inr u))) => Vlong u
  | inl (inl (inr u)) => Vfloat u
  | inl (inr u) => Vsingle u
  | inr (pair b p) => Vptr b p
  end.

Local Lemma val_eq_inj: forall v, val_eq2val (val2val_eq v) = v.
Proof. intros. destruct v; simpl; easy. Qed.

Local Definition z2int (z: Z): option int :=
  match Z_lt_le_dec (-1)%Z z with
  | left m1 => match Z_lt_le_dec z Int.modulus with
               | left m2 => Some (Int.mkint z (conj m1 m2))
               | right _ => None
               end
  | right _ => None
  end.

Local Lemma z2int_int: forall x: int, z2int (Int.unsigned x) = Some x.
Proof.
  intros. destruct x as [v [? ?]]. unfold z2int. simpl.
  destruct (Z_lt_le_dec (-1) v). 2: lia.
  destruct (Z_lt_le_dec v Int.modulus). 2: lia. f_equal. f_equal.
  f_equal; apply proof_irrelevance.
Qed.

Local Instance int_countable: Countable int :=
  inj_countable Int.unsigned z2int z2int_int.

Local Definition z2int64 (z: Z): option int64 :=
  match Z_lt_le_dec (-1)%Z z with
  | left m1 => match Z_lt_le_dec z Int64.modulus with
               | left m2 => Some (Int64.mkint z (conj m1 m2))
               | right _ => None
               end
  | right _ => None
  end.

Local Lemma z2int64_int: forall x: int64, z2int64 (Int64.unsigned x) = Some x.
Proof.
  intros. destruct x as [v [? ?]]. unfold z2int64. simpl.
  destruct (Z_lt_le_dec (-1) v). 2: lia.
  destruct (Z_lt_le_dec v Int64.modulus). 2: lia. f_equal. f_equal.
  f_equal; apply proof_irrelevance.
Qed.

Local Instance int64_countable: Countable int64 :=
  inj_countable Int64.unsigned z2int64 z2int64_int.

Local Instance bin_float_eq_dec:
  forall prec emax, EqDecision (binary_float prec emax).
Proof. intros. hnf. intros. hnf. apply IEEE754_extra.Beq_dec. Qed.

Local Definition float_eq_type: Set :=
  bool + bool + (bool * positive) + (bool * positive * Z).

Local Definition float2eq (prec emax: Z)
      (v: binary_float prec emax): float_eq_type :=
  match v with
  | B754_zero b => inl (inl (inl b))
  | B754_infinity b => inl (inl (inr b))
  | B754_nan b pl _ => inl (inr (pair b pl))
  | B754_finite b m e _ => inr (pair (pair b m) e)
  end.

Local Definition eq2float (prec emax: Z) (v: float_eq_type):
  option (binary_float prec emax) :=
  match v with
  | inl (inl (inl b)) => Some (B754_zero prec emax b)
  | inl (inl (inr b)) => Some (B754_infinity prec emax b)
  | inl (inr (pair b pl)) => match (bool_dec (nan_pl prec pl) true) with
                             | left pf => Some (B754_nan prec emax b pl pf)
                             | right _ => None
                             end
  | inr (pair (pair b m) e) =>
    match (bool_dec (bounded prec emax m e) true) with
    | left pf => Some (B754_finite prec emax b m e pf)
    | right _ => None
    end
  end.

Local Lemma float2eq_float: forall prec emax (x: binary_float prec emax),
    eq2float prec emax (float2eq prec emax x) = Some x.
Proof.
  intros. destruct x; simpl; try easy.
  - destruct (bool_dec (nan_pl prec pl) true). 2: easy. f_equal.
    f_equal. apply proof_irrelevance.
  - destruct (bool_dec (bounded prec emax m e) true). 2: easy. f_equal.
    f_equal. apply proof_irrelevance.
Qed.

Local Instance float_eq_countable: Countable float_eq_type.
Proof. typeclasses eauto. Qed.

Local Instance float_countable: forall prec emax, Countable (binary_float prec emax).
Proof.
  intros.
  apply (inj_countable (float2eq prec emax) (eq2float prec emax)
                       (float2eq_float prec emax)).
Qed.

Local Definition z2ptrofs (z: Z): option ptrofs :=
  match Z_lt_le_dec (-1)%Z z with
  | left m1 => match Z_lt_le_dec z Ptrofs.modulus with
               | left m2 => Some (Ptrofs.mkint z (conj m1 m2))
               | right _ => None
               end
  | right _ => None
  end.

Local Lemma z2ptrofs_eq: forall x: ptrofs, z2ptrofs (Ptrofs.unsigned x) = Some x.
Proof.
  intros. destruct x as [v [? ?]]. unfold z2ptrofs. simpl.
  destruct (Z_lt_le_dec (-1) v). 2: lia.
  destruct (Z_lt_le_dec v Ptrofs.modulus). 2: lia. f_equal. f_equal.
  f_equal; apply proof_irrelevance.
Qed.

Local Instance ptrofs_countable: Countable ptrofs :=
  inj_countable Ptrofs.unsigned z2ptrofs z2ptrofs_eq.

Local Instance val_eq_type_countable: Countable val_eq_type.
Proof. typeclasses eauto. Qed.

Instance val_countable: Countable val :=
  inj_countable' val2val_eq val_eq2val val_eq_inj.
