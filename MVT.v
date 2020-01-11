Require Import Reals.
Require Import Lra.
Require Import Ensembles.
Require Import Ranalysis1.
Local Open Scope R_scope.

Definition x_squared (x : R) := x * x.

Definition closed_unit_interval := fun x => 0 <= x <= 1.
Definition open_unit_interval := fun x => 0 < x < 1.

Definition Open_Interval (a : R) (b : R) := fun x => a < x < b.

Record Interval : Type := mkinterval {a :> R; b :> R; H : a < b}.
Lemma zero_lt_one : 0 < 1. Proof. lra. Qed.
Definition zero_to_one := mkinterval 0 1 zero_lt_one.

Lemma xsquared_derivable : derivable x_squared.
Proof.
  unfold derivable, derivable_pt, derivable_pt_abs, derivable_pt_lim, x_squared.
  intros x.
  Admitted.

Definition derive_threex := derive x_squared xsquared_derivable.

Lemma conjugate_trick (a b : R) : a * a - b * b = (a - b) * (a + b).
Proof.
  lra.
Qed.

Lemma zero_numerator_equals_zero :
  forall (x y : R), x / y = 0 -> x = 0.
Proof.
  intros x y H.
  Admitted.


Theorem xsquared_continuous : continuity x_squared.
Proof.
  unfold continuity, continuity_pt, continue_in, no_cond, limit1_in, limit_in, dist, x_squared.
  simpl.
  unfold D_x.
  intros c eps H.
  exists (Rmin 1 (Rabs (eps / (2 * c + 1)))).
  split.
  - compute; destruct Rcase_abs as [| G1]; destruct Rle_dec as [| G2]; try lra.
    unfold not in G2.
    destruct G1; try lra.
    apply zero_numerator_equals_zero in H0.
    lra.
  - intros x G.
    destruct G as [G1 G2]; destruct G1 as [_ G].
    unfold R_dist, Rabs in *.
    destruct Rcase_abs as [| F] in G2;
      destruct Rcase_abs as [| E];
      destruct Rcase_abs as [| E'];
      compute in G2; destruct Rle_dec in G2;
        field_simplify; try lra.
Admitted.

Definition three_x (x : R) := 3 * x.

Theorem threex_continuous : continuity three_x.
Proof.
  unfold continuity, three_x.
  unfold continuity_pt, continue_in, limit1_in, limit_in, dist, D_x; simpl.
  intros x eps H.
  exists (eps/3).
  split; try lra.
  intros x0 G.
  unfold no_cond, R_dist in G.
  destruct G as [[_ G1] G2].
  unfold R_dist, Rabs.
  unfold Rabs in G2; destruct Rcase_abs in G2; destruct Rcase_abs; try lra.
Qed.

Lemma threex_derivable : derivable three_x.
Proof.
  unfold derivable, derivable_pt, derivable_pt_abs, derivable_pt_lim, three_x.
  intros x.
  simpl.
  Admitted.

Check derive.

Lemma threex_has_mean_value_property_on_0_1 :
  exists (c : R),
    0 < c < 1 /\ derive three_x threex_derivable c = (three_x 1 - three_x 0) / (1 - 0).
Proof.
  exists (1/2). (*any c in (0,1) will do.*)
  split; try lra.
  unfold derive, derive_pt, three_x.
  destruct threex_derivable as [c  G].
  unfold derivable_pt_abs, derivable_pt_lim in G.
  simpl.
  specialize (G 1).
  destruct G as [delt G]; try lra.
  unfold three_x in G.
  unfold Rabs in G.
  specialize (G 1).
  destruct Rcase_abs in G; try lra.
  assert (H : 1 <> 0). lra.
  specialize (G H).
  destruct Rcase_abs in G; try lra.
  destruct delt as [delt delt_pos].









Lemma xsquared_has_mean_value_property_on_minus1_1 :
    exists (c : R),
      (-1) < c < 1 ->
      derive x_squared xsquared_derivable c = (x_squared 1 - x_squared (-1)) / (1 - (-1)).
Proof.
  exists 0.
  intros H.
  unfold x_squared in *.
  unfold derive, derive_pt.
  rewrite conjugate_trick; field_simplify.
  destruct xsquared_derivable as [x G].
  unfold derivable_pt_abs, derivable_pt_lim in G.
  simpl.
  Admitted.


Theorem mean_value_theorem {a b : R}
        (f : R -> R) (H : derivable f) (A : Open_Interval a b) :
  exists (c : R), A c -> derive f H c = (f b - f a) / (b - a).
