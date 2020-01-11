(*exercise 4.4.11 in Stephen Abbott's Understanding Analysis*)
Require Import Reals.
Require Import Lra.
Require Image.
Require Import Ensembles.
Require Import preservation_of_compactness.
Local Open Scope R_scope.

Definition open_unit_interval := fun x => 0 < x < 1.

Definition all_of_R := fun x => x < 0 \/ x >= 0.

Definition Preimage (f : R -> R) (B : Ensemble R) : Ensemble R
  :=
    fun (y : R) => exists (x : R), B (f x).

Theorem preim_over_open_unit_interval_of_threex :
  forall x, (fun x => 0 < x < (1/3)) x -> Preimage three_x open_unit_interval x.
Proof.
  intros x H.
  simpl in H.
  unfold Preimage.
  exists (1/6).
  unfold open_unit_interval, three_x.
  lra.
Qed.

(*Topological Characterization of Continuity*)
Theorem topo_characterization_of_continuity_forward :
  forall (f : R -> R) (B : Ensemble R), (continuous f all_of_R) -> open B -> open (Preimage f B).
Proof.
  intros f B.
  intros H1 H2.
  unfold continuous, all_of_R in H1.
  unfold open, Preimage, Included.
  intros x.
  exists 100.
  intros H3 H4 x' H5.
  destruct H3 as [x'' H3].
  unfold In in *.
  exists x''.
  apply H3.
Qed.
(*you can also just do exists (-1). and discriminate H3. *)

Theorem topo_characterization_of_continuity_backward :
  forall (f : R -> R) (B : Ensemble R), open B -> open (Preimage f B) -> (continuous f all_of_R).
Proof.
  intros f B H1 H2.
  unfold continuous, all_of_R.
  intros c _.
  unfold open in *.
  specialize (H1 1); destruct H1 as [eps1 H1].
  specialize (H2 (f 1)); destruct H2 as [eps2 H2].
  unfold continuous_c.
  intro eps'.
  exists (eps'/2).
  intros G1 G2 x F.
  unfold In, neighborhood in *.
