(*this time w the ensembles library*)
Require Import Reals.
Require Import Lra.
Require Import Ensembles.
Require Image.
Local Open Scope R_scope.
Definition Image (A : Ensemble R) (f : R -> R) : Ensemble R :=
  Image.Im R R A f.


Definition closed_unit_interval : Ensemble R :=
  fun x => 0 <= x <= 1.

Definition three_x : R -> R := fun x => 3*x.
(*continuity*)
Definition neighborhood (eps : R) (point : R) : Ensemble R :=
  fun x =>
    point - eps <= x <= point + eps.

Check In R (neighborhood 1 1).



Definition continuous_c (f : R -> R) (c : R) : Prop :=
  forall (eps : R), exists (delt : R),
      eps > 0 -> delt > 0 ->
      forall x, (neighborhood delt c) x ->
           (neighborhood eps (f c)) (f x).

Definition continuous (f : R -> R) (A : Ensemble R) : Prop :=
  forall (c : R), A c -> continuous_c f c.

Theorem three_x_continuous : continuous three_x closed_unit_interval.
Proof.
  unfold continuous, continuous_c; intros.
  exists (eps / 3). intros. unfold three_x.
  unfold neighborhood in *.
  lra.
Qed.

(*compactness*)
Definition open (A : Ensemble R) : Prop :=
  forall x, exists eps,
      A x -> eps > 0 ->
      Included R (neighborhood eps x) A.

Definition closed (A : Ensemble R) : Prop :=
  open (Complement R A).

Theorem closed_unit_interval_closed : closed closed_unit_interval.
Proof.
  unfold closed, open, Complement, closed_unit_interval; intros.
  assert (G : closed_unit_interval 1). { unfold closed_unit_interval. lra. }
  exists 0.
  unfold not, included, neighborhood, Included, In; intros.
  lra.
Qed.


Definition bounded_above (A : Ensemble R) : Prop :=
  exists (b : R), forall x, A x -> x <= b.

Definition bounded_below (A : Ensemble R) : Prop :=
  exists (b : R), forall x, A x -> b <= x.

Definition bounded (A : Ensemble R) : Prop :=
  bounded_above A /\ bounded_below A.

Ltac show_boundedness bounded_side A x :=
  unfold bounded_side, A; exists x; intros; lra.

Theorem closed_unit_interval_bounded : bounded closed_unit_interval.
Proof.
  unfold bounded; split.
  - show_boundedness bounded_above closed_unit_interval 1.
  - show_boundedness bounded_below closed_unit_interval 0.
Qed.

Definition compact (A : Ensemble R) : Prop :=
  closed A /\ bounded A.

Theorem closed_unit_interval_compact : compact closed_unit_interval.
Proof.
  unfold compact; split.
  - apply closed_unit_interval_closed.
  - apply closed_unit_interval_bounded.
Qed.

(*preservation*)
Definition compact_image (f : R -> R) (A : Ensemble R) : Prop :=
  (*won't be provable if f isn't continuous or A isn't compact*)
  compact (Image A f).

Theorem three_x_preserves_compactness : compact_image three_x closed_unit_interval.
Proof.
  unfold compact_image.
  unfold compact.
  split.
  { unfold closed.
    unfold open, Complement.
    intro x.
    exists 0.
    intros H1 H2.
    lra.
  }
  { unfold bounded.
    split.
    - unfold bounded_above; exists 3; intros x H; unfold closed_unit_interval, three_x in H.
      destruct H. unfold In in H. lra.
    - unfold bounded_below; exists 0; intros x H; unfold closed_unit_interval, three_x in H.
      destruct H. unfold In in H. lra.
  }
Qed.



Definition f_attains_max_and_min (f : R -> R) (A : Ensemble R) : Prop :=
  continuous f A -> compact A ->
  exists (fmin fmax : R), forall (y : R), Image A f y -> fmin <= y <= fmax.

Theorem three_x_attains_max_and_min :
  f_attains_max_and_min three_x closed_unit_interval.
  unfold f_attains_max_and_min.
  intros H1 H2.
  exists 0, 3;
    intros.
    inversion H;
    unfold In, closed_unit_interval in H0;
    unfold three_x in H3;
    lra.
Qed.

Theorem preservation_of_compactness :
  forall (f : R -> R) (A : Ensemble R),
    continuous f A -> compact A ->
    compact_image f A.
Proof.
  intros f A H G.
  unfold compact_image.
  unfold compact.
  split.
  { unfold closed, open, Complement.
    intros x.
    exists 0.
    intros F E.
    lra.
  }
  { assert (J : f_attains_max_and_min f A).
    { unfold f_attains_max_and_min.
      intros _ _.
      unfold compact, bounded in G; destruct G as [G1 [G2 G3]].
      destruct G2 as [b__up G2].
      destruct G3 as [b__low G3].





      eexists. eexists.
      intros y F.
      split.
      - remember (y-1) as fmin.
        assert (J1 : fmin <= y). lra.
        give_up.
      - give_up.
    }
    unfold f_attains_max_and_min in J.
    specialize (J H G).
    destruct J as [fmin [fmax J']].
    unfold compact, bounded in G; destruct G as [G1 [G2 G3]].
    destruct G2 as [b__up G2].
    destruct G3 as [b__low G3].
    split.
    { unfold bounded_above;
        exists fmax;
        intros y F;
        inversion F as [x' F1 y' F2 F3];
        unfold In in F1.
      destruct (J' y) as [J'1 J'2]. apply F.
      apply J'2.
    }
    { unfold bounded_below;
        exists fmin;
        intros y F;
        inversion F as [x' F1 y' F2 F3];
        unfold In in F1.
      destruct (J' y) as [J'1 J'2]. apply F.
      apply J'1.
    }
  }
