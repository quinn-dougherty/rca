Require Import Reals.
Require Import Lra.
Require Import Psatz.
(*Require Import SeqSeries.*)
Local Open Scope R_scope.

Definition harmonic_squrd (n : nat) := 1 / (((INR n) + 1) ^ 2).

(*decreasing*)
Lemma harmonic_squrd_decreasing : Un_decreasing harmonic_squrd.
Proof.
  unfold Un_decreasing, harmonic_squrd.
  intros n.
  induction n as [| n' IHn'].
  - field_simplify; simpl; lra.
  - field_simplify.

Admitted.


Lemma harmonic_squrd_convergent : Un_cv harmonic_squrd 0.
  unfold Un_cv, harmonic_squrd.
  intros eps H.
  remember (sqrt eps) as sqrt_eps.
  (*exists nat.ceil (1 / sqrt_eps)*)
Admitted.

Ltac abs_lra :=
  unfold R_dist, Rabs; destruct Rcase_abs; try lra.

Lemma Rdist_ident :
  forall x, x >= 0 -> R_dist x 0 = x.
Proof.
  intros x H.
  unfold R_dist, Rabs.
  destruct Rcase_abs; try lra.
Qed.

Lemma sqrt_preserves_convergence_to0 : forall (Xn : nat -> R),
    (*exericse 2.3.1 in Stephen Abbott Understanding Analysis*)
    Un_cv Xn 0 -> forall k, Xn k >= 0 -> Un_cv (fun n => sqrt (Xn n)) 0.
Proof.
  intros Xn H k H'.
  unfold Un_cv in *.
  intros eps H__eps.
  assert (0<eps*eps). apply Rmult_lt_compat_r with (r:=eps) in H__eps;
                        try (rewrite Rmult_comm in H__eps;
                             rewrite Rmult_0_r in H__eps);
                        apply H__eps.
  specialize (H (eps*eps) H0).
  destruct H as [N H].
  exists N.
  intros n0 H2.
  specialize (H n0 H2).
  unfold sqrt.
  destruct Rcase_abs as [G | G].
  - abs_lra.
  - unfold Rsqrt; simpl.
    destruct Rsqrt_exists as [x0 [F1 F2]].
    abs_lra.
    inversion F1 as [F1' | F1']; try lra.
    rewrite Rminus_0_r in *.
    apply Rsqr_incrst_0; unfold Rsqr; try lra.
    unfold Rsqr in F2.
    rewrite <- F2.
    rewrite Rdist_ident in H; try lra.
Qed.
