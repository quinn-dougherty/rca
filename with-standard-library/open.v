Require Import Reals.
Require Import Lra.
Require Import Rtopology.
Require Import Rminmax.
Require Import Ensembles.
Local Open Scope R_scope.

Ltac rabs_delta F Heqdelt :=
  unfold Rabs; destruct Rcase_abs;
  unfold Rabs in F; destruct Rcase_abs in F;
  unfold Rmin in Heqdelt; destruct Rle_dec in Heqdelt;
  try lra.


Theorem intersection_open_sets_is_open (A B : Ensemble R) :
  open_set A -> open_set B -> open_set (Intersection R A B).
Proof.
  intros H1 H2.
  unfold open_set in *.
  intros x G.
  destruct G as [x G1 G2]; unfold In in *.
  unfold included.
  specialize (H1 x G1); destruct H1 as [[delt1 delt1pos] H1].
  specialize (H2 x G2); destruct H2 as [[delt2 delt2pos] H2].
  unfold included, disc, included in H1; simpl in H1.
  unfold included, disc, included in H2; simpl in H2.
  remember (Rmin delt1 delt2) as delt; assert (deltpos : delt > 0).
  { rewrite Heqdelt.
    compute; destruct Rle_dec.
    - apply delt1pos.
    - apply delt2pos.
  }
  exists (mkposreal delt deltpos).
  unfold included, disc; intros x' F; simpl in F.

  apply Intersection_intro; unfold In.
  - apply H1; rabs_delta F Heqdelt.
  - apply H2; rabs_delta F Heqdelt.
Qed.
