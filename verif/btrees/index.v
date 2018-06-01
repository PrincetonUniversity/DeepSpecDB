(** * Index.v: defining indexes *)

Require Import Omega.

Inductive index: Type :=
| im: index
| ip: nat -> index.

Definition nat_to_index (n:nat) := ip n.

Definition index_eqb (i1:index) (i2:index) : bool :=
  match i1 with
  | im => match i2 with
          | im => true
          | ip _ => false
          end
  | ip n1 => match i2 with
             | im => false
             | ip n2 => (Nat.eqb n1 n2)
             end
  end.

Definition next_index (i:index) : index :=
  match i with
  | im => ip (O%nat)
  | ip n => ip (S n)
  end.

Definition prev_index (i:index) : index :=
  match i with
  | im => im
  | ip n => match n with
            | O => im
            | S ii => ip ii
            end
  end.

Definition prev_index_nat (n:nat) : index :=
  match n with
  | O => im
  | S n' => ip n'
  end.

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Lemma max_0: forall a, max_nat a 0 = a.
Proof. induction a. auto. simpl. auto. Qed.

Lemma max_refl: forall a, max_nat a a = a.
Proof.
  intros. induction a.
  apply max_0. simpl. rewrite IHa. auto.
Qed.

Theorem le_max_split_l: forall n a b,
    (n < a)%nat -> (n< max_nat a b)%nat.
Proof.
  intros.
  generalize dependent n.
  generalize dependent b.
  generalize dependent a.
  induction a; intros.
  - inversion H.
  - destruct b.
    + rewrite max_0. auto.
    + simpl. destruct n. omega.
      assert (n<a)%nat by omega. apply IHa with (b:=b) in H0. omega.
Qed.      

Theorem max_flip: forall a b, max_nat a b = max_nat b a.
Proof.
  induction a; intros.
  - simpl. rewrite max_0. auto.
  - simpl. destruct b.
    + simpl. auto.
    + simpl. rewrite IHa. auto.
Qed.    

Theorem le_max_split_r: forall n a b,
    (n < b)%nat -> (n< max_nat a b)%nat.
Proof.
  intros. rewrite max_flip. apply le_max_split_l. auto.
Qed.
  
Definition max_index (i1:index) (i2:index): index :=
  match i1 with
  | im => i2
  | ip n1 => match i2 with
            | im => i1
            | ip n2 => ip (max_nat n1 n2)
             end
  end.

Definition index_leb_nat (i:index) (n:nat) : bool :=
  match i with
  | im => true
  | ip n' => (n' <=? n)%nat
  end.

Definition idx_to_Z (i:index) : Z :=
  match i with
  | im => -1
  | ip n => Z.of_nat n
  end.

Lemma next_idx_to_Z: forall i,
    (idx_to_Z (next_index i) = (idx_to_Z i) + 1)%Z.
Proof.
  intros.
  destruct i.
  - simpl. auto.
  - simpl. rewrite Zpos_P_of_succ_nat. omega.
Qed.