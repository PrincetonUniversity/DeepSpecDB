(** * Index.v: defining indexes *)

Require Import Omega.

Inductive index: Type :=
| im: index
| ip: Z -> index.


Definition index_eqb (i1:index) (i2:index) : bool :=
  match i1 with
  | im => match i2 with
          | im => true
          | ip _ => false
          end
  | ip n1 => match i2 with
             | im => false
             | ip n2 => (Z.eqb n1 n2)
             end
  end.

Definition next_index (i:index) : index :=
  match i with
  | im => ip 0
  | ip n => ip (Z.succ n)
  end.

Definition prev_index (i:index) : index :=
  match i with
  | im => im
  | ip n => if Z_le_dec n 0 then im else ip (Z.pred n)
  end.

Definition prev_index_nat (n:Z) : index :=
  if Z_le_dec n 0 then im else ip (Z.pred n).

Definition index_leb_nat (i:index) (n:Z) : bool :=
  match i with
  | im => true
  | ip n' => (n' <=? n)%Z
  end.

Definition idx_to_Z (i:index) : Z :=
  match i with
  | im => -1
  | ip n => n
  end.

Lemma next_idx_to_Z: forall i,
    (idx_to_Z (next_index i) = (idx_to_Z i) + 1)%Z.
Proof.
  intros.
  destruct i.
  - simpl. auto.
  - simpl. omega.
Qed.
