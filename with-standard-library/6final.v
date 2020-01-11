Require Import Reals.
Require Import Psatz.
Require Import Ensembles.
Local Open Scope R.

Definition continuous_on_set (AUTO : Ensemble R) (f : {x : R | A x} -> R) :=
  forall x, continuity_pt f x.


Definition D (x : R) :=
  0 <= x <= 1 \/ x = 2 \/ 3 <= x < 4.

Check {x : R | D x} -> R.

Theorem continuous_at_2 : forall (f : {x : R | D x} -> R), continuous_on_set f D.
Proof.
  intros f.
  unfold continuous_on_set.
  intros x H.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps H__eps.
  unfold D in H.
  unfold D_x.
