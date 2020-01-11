Require Import Reals.
Require Import Ensembles.
Local Open Scope R.

Record Aset (A : Ensemble R) : Type := mkset {x :> R; inA : A x}.

Definition bounded_above (A : Ensemble R) :=
  exists (b : R), forall (a : Aset A), a <= b.



Definition is_upper_bound (An : nat -> R) :=
