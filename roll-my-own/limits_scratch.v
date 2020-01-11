Require Import Reals.
(*Require Import Rlimit.*)
Require Import Lra.
Require Import preservation_of_compactness.
Require Import Ensembles.
Local Open Scope R_scope.

Definition open_unit_interval := fun x => 0 < x < 1.

Definition limit_relation_topological (f : R -> R) (c : R) :=
  fun l =>
    forall (eps : R), exists (delt : R),
        eps > 0 -> delt > 0 ->
        forall (x : R), x<>c -> neighborhood delt c x -> neighborhood eps l (f x).



Definition limit_relation (f : R -> R) (c : R) :=
  fun l =>
    forall eps, exists delt,
        eps > 0 -> delt > 0 ->
        forall x,
          R_dist x c < delt ->
          R_dist (f x) l < eps.

Lemma limit_threex_as_x_approaches_one : limit_relation three_x 1 3.
Proof.
  unfold limit_relation, three_x.
  intros eps.
  exists (eps/3).
  intros H1 H2 x G.
  unfold R_dist, Rabs; destruct Rcase_abs;
    unfold R_dist, Rabs in G;
    destruct Rcase_abs in G;
    lra.
Qed.

Definition differentiable_at_point (f : R -> R) (c : R) :=
  exists (l : R),
    limit_relation (fun x => (f x - f c) / (x - c)) c l.

Definition differentiable (f : R -> R) (A : Ensemble R) :=
  forall (c : R), A c -> differentiable_at_point f c.

Lemma threex_differentiable_open_unit_interval : differentiable three_x open_unit_interval.
Proof.
  unfold differentiable, open_unit_interval, three_x, differentiable_at_point, limit_relation.
  intros c H.
  exists (3 * c).
  intros eps.
  exists (-1).
  lra.
Qed.


Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Definition neighborhood' (eps : posreal) (point : R) :=
  fun x => point - eps < x < point + eps.


Definition limit_relation_topological' (f : R -> R) (c : R) :=
  fun l =>
    forall (eps : posreal), exists (delt : posreal),
        forall (x : R), x<>c -> neighborhood' delt c x -> neighborhood' eps l (f x).

Definition three_pos := mkposreal 3.

Lemma H : 0 < 3.
Proof. lra. Qed.

Check mkposreal 3 H.

Require Import Rlimit.
Require Import Rderiv.

Lemma limit_of_threex_as_x_goes_to_one : limit_in R_met R_met three_x open_unit_interval 1 3.
Proof.
  unfold limit_in. intros eps H.
  exists (eps / 3). split; try lra.
  intros x G. destruct G as [G1 G2].
  unfold three_x, open_unit_interval in *.
  unfold dist, R_met, R_dist, Rabs. destruct Rcase_abs.
  unfold dist, R_met, R_dist, Rabs in G2; destruct Rcase_abs in G2; try lra.
  field_simplify. lra.
Qed.

Definition const_3 (x : R) := 3.

Lemma derivative_of_threex_is_constant_3 : D_in three_x const_3 open_unit_interval 3.
Proof.
  unfold D_in, three_x, const_3, open_unit_interval.
  unfold limit1_in, limit_in.
  intros eps H.
  exists 1.
  split; try lra.
  intros x G.
  destruct G as [G1 G2].
  unfold D_x in G1; destruct G1 as [G11 G12].
  unfold dist, R_met, R_dist, Rabs. unfold dist, R_met, R_dist, Rabs in G2.
  destruct Rcase_abs in G2; destruct Rcase_abs; field_simplify; lra.
Qed.

Lemma threex_continuous_in_openunitinterval : continue_in three_x open_unit_interval 3.
Proof.
  unfold continue_in, three_x, open_unit_interval.
  unfold limit1_in, limit_in.
  intros eps H.
  exists 1.
  split; try lra.
  intros x G.
  destruct G as [G1 G2].
  destruct G1 as [G11 G12].
  unfold dist, R_met, R_dist, Rabs in *.
  destruct Rcase_abs in G2; destruct Rcase_abs; field_simplify; try lra.
Qed.

Require Import Ranalysis1.

Lemma threex_continuous : continuity three_x.
Proof.
  unfold continuity, continuity_pt, continue_in, no_cond, limit1_in, limit_in, three_x.
  intros x eps H.
  exists (eps/3).
  split; try lra.
  intros x0 G.
  destruct G as [G1 G2].
  unfold D_x in G1; destruct G1 as [_ G12].
  unfold dist, R_met, R_dist, Rabs in *. destruct Rcase_abs in G2; destruct Rcase_abs; try lra.
Qed.
