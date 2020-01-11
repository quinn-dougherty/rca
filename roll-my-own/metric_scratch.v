Require Import Reals.
Local Open Scope R_scope.

Record Metric_Space : Type :=
  {Base: Type;
   dist : Base -> Base -> R;
   dist_pos : forall (x y : Base), dist x y >= 0;
   dist_sym : forall (x y : Base), dist x y = dist y x;
   dist_refl : forall (x y : Base), dist x y = 0 <-> x = y;
   dist_tri : forall (x y z : Base), dist x y <= dist x z + dist z y
  }.

Definition R_met : Metric_Space :=
  Build_Metric_Space R R_dist R_dist_pos R_dist_sym R_dist_refl R_dist_tri.
