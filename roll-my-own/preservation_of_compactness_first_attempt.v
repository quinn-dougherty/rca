Require Import Reals.
Require Import Lra.
Require Import Omega.
Local Open Scope R_scope.



Definition three_x (x : R) := 3 * x.

Definition neighborhood (eps : R) (point : R) :=
  fun x => point - eps < x < point + eps.

Definition continuous_c (f : R -> R) (c : R) :=
  forall (eps : R), exists (delt : R),
      eps > 0 -> delt > 0 ->
      forall x, neighborhood delt c x -> neighborhood eps (f c) (f x).

Theorem three_x_continuous_at_0 : continuous_c three_x 0.
Proof.
  unfold continuous_c.
  intros. exists (eps / 3). intros.
  unfold neighborhood.
  split; unfold three_x; unfold neighborhood in H1; lra.
Qed.

Definition continuous (f : R -> R) :=
  forall (c : R), continuous_c f c.

Theorem three_x_continuous : continuous three_x.
  unfold continuous.
  intros; unfold continuous_c; intros.
  exists (eps / 3).
  intros; unfold neighborhood; unfold three_x.
  unfold neighborhood in H1.
  lra.
Qed.

Definition uniformly_continuous' (f : R -> R) :=
  forall (eps : R), exists (delt : R),
      eps > 0 -> delt > 0 ->
      forall (x y : R), Rabs (x - y) < delt -> Rabs (f x - f y) < eps.

Definition uniformly_continuous (f : R -> R) :=
  forall (eps : R), exists (delt : R),
      eps > 0 -> delt > 0 ->
      forall (x y : R), neighborhood delt x y -> neighborhood eps (f x) (f y).

Theorem three_x_uniformly_continuous : uniformly_continuous three_x.
Proof.
  unfold uniformly_continuous.
  intros eps.
  exists (eps / 3).
  intros H1 H2 x y G1.
  unfold neighborhood. unfold neighborhood in G1.
  unfold three_x.
  lra.
Qed.

Check neighborhood 1 1.


(*compactness*)
Definition closed_unit_interval (x : R) := 0 <= x <= 1.

Definition limit_point (A : R -> Prop) (x : R) :=
  forall eps, exists x', eps > 0 /\ neighborhood eps x x' /\ A x' /\ x <> x'.

Definition closed' (A : R -> Prop) :=
  forall x, limit_point A x -> A x.

Definition complement (A : R -> Prop) :=
  fun (x : R) => ~ (A x).

Definition open (A : R -> Prop) :=
  forall x, A x -> exists eps, eps > 0 /\ (forall x', neighborhood eps x x' -> A x').

Definition closed (A : R -> Prop) :=
  open A -> forall x, complement A x.

Theorem closed_unit_interval_is_closed : closed closed_unit_interval.
Proof.
  unfold closed.
  intros H x.
  unfold complement; unfold not; intro G.
  unfold open in H.
  assert (E : closed_unit_interval 1). { unfold closed_unit_interval; lra. }
  destruct (H 1 E) as [eps1 H'].
  destruct H' as [H1' H2'].
  unfold neighborhood in H2'.
  destruct (H2' (1 + eps1 / 2)).
  - lra.
  - lra.
Qed.

Definition is_upper_bound (A : R -> Prop) (b : R) := forall x, A x -> x <= b.

Definition is_lower_bound (A : R -> Prop) (b : R) := forall x, A x -> x >= b.

Definition bounded (A : R -> Prop) := (exists m, is_upper_bound A m) /\ (exists b, is_lower_bound A b).

Ltac show_boundedness b is_bound A :=
  exists b; unfold is_bound; intros x H; unfold A in H; lra.

Theorem closed_unit_interval_is_bounded : bounded closed_unit_interval.
Proof.
  unfold bounded.
  split.
  - show_boundedness 2 is_upper_bound closed_unit_interval.
  - show_boundedness (0-1) is_lower_bound closed_unit_interval.
Qed.

Definition compact (A : R -> Prop) := closed A /\ bounded A.

Theorem closed_unit_interval_is_compact : compact closed_unit_interval.
Proof.
  unfold compact.
  split.
  - apply closed_unit_interval_is_closed.
  - apply closed_unit_interval_is_bounded.
Qed.

(**Preservation of compactness*)

Definition empty (x : R) := x < 5 /\ x > 6.

Definition image' (f : R -> R) (A : R -> Prop) (B : R -> Prop) := forall x, A x -> B (f x).
(*I really want image to land in R -> Prop *)

Check image' three_x closed_unit_interval.

Theorem image'_test1 : image' three_x closed_unit_interval (fun x => 0 <= x <= 3).
Proof.
  unfold image'.
  intros x H.
  unfold three_x.
  unfold closed_unit_interval in H.
  lra.
Qed.

Theorem image'_test2 : image' three_x empty empty.
Proof.
  unfold image'.
  intros x H.
  unfold three_x.
  unfold empty in H.
  unfold empty.
  lra.
Qed.
(*Now that i have image as a relation between two sets, i want image as a function R -> Prop *)
