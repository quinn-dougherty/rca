(*constructing square roots and things*)
Require Import Reals.
Require Import Lra.
Local Open Scope R_scope.

Definition lt_sqrt2 := fun x => x * x < 2.

Lemma lt_sqrt2_has_upper_bound : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2.
  intros x H.
  left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - apply Rlt_trans with (r2 := 1). apply L. lra.
  - lra.
  - assert (x*1 < x*x).
    apply Rmult_lt_compat_l.
    eapply Rlt_trans.
    apply Rlt_0_1.
    apply G.
    apply G.
    rewrite Rmult_comm, Rmult_1_l in H0.
    eapply Rlt_trans.
    apply H0.
    apply H.
Qed.

Lemma bound_sqrt2 : bound lt_sqrt2.
Proof.
  exists 2.
  apply lt_sqrt2_has_upper_bound.
Qed.

Lemma ex_lt_sqrt2 : exists x, lt_sqrt2 x.
  (*showing that the predicate is nonempty*)
Proof.
  exists 1.
  unfold lt_sqrt2.
  lra.
Qed.

Definition sqrt2 := completeness lt_sqrt2 bound_sqrt2 ex_lt_sqrt2.

Check sqrt2.
