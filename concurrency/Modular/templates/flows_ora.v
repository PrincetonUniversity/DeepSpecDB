From flows Require Import flows.
From iris_ora Require Export ora.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Section flows.
  Local Instance flows_order: OraOrder flowintT := fun (a b: flowintT) => a = b \/ b = intUndef.
  Lemma Increasing_flows : forall (a : flowintT ), Increasing a <-> a = ε \/ a = intUndef.
  Proof.
  split; intros Ha.
  - specialize (Ha ε).
    rewrite right_id in Ha.
    inversion Ha; auto.
  - intros ?; destruct Ha.
    + subst a. rewrite left_id; hnf; auto. 
    + hnf. subst a. right.
      by rewrite (intComp_undef_op).
  Qed.

  Definition flows_ora_mixin : DORAMixin flowintT.
  Proof. 
    split; try apply _; try done.
    - intros ???.
      rewrite Increasing_flows.
      destruct x; inversion H; auto.
    - intros ???; inversion H; hnf; auto.
    - intros ?????; inversion H; subst; eexists; split; eauto; hnf; [left|right]; auto.
    - intros ?????; inversion H0; subst; auto; hnf; auto. 
    - intros ????; inversion H; subst; hnf; [left | right]; auto; by pose proof (intComp_undef_op y). 
    - intros ????; inversion H0; subst; [auto | contradiction].
    - intros ???;
      destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      inversion H0; subst; try eauto.
      destruct (int f0 ⋅ y);  eexists; split; try done; subst; hnf; [left | right]; eauto;
      eexists.
      + rewrite (intComp_undef_op y);
        eexists; split; last first; eauto; hnf; auto.
      + inversion H0; subst. inversion H2.
      + rewrite (intComp_undef_op y).
        eexists; split; eauto; hnf; auto.
   Qed.
  
  Canonical Structure flowsR := discreteOra flowintT flows_ora_mixin.

  Global Instance flows_ora_discrete : OraDiscrete flowintT.
  Proof. apply discrete_ora_discrete. Qed.

  Canonical Structure flowintUR : uora := Uora flowintT flowint_ucmra_mixin.

End flows.
