(** * Index.v: defining indexes *)

Require Import Omega.

Definition index := Z.

Definition index_eqb: index -> index -> bool := Z.eqb.

Definition next_index: index -> index := Z.succ.

Definition prev_index: index -> index := Z.pred.

Definition idx_to_Z (i:index) : Z := i.

Definition im : index := (-1)%Z.
Definition ip (i: Z) : index :=  i.

Lemma next_idx_to_Z: forall i,
    (idx_to_Z (next_index i) = (idx_to_Z i) + 1)%Z.
Proof.
  intros. reflexivity.
Qed.
