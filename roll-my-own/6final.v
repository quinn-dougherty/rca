Require Import Reals.
Require Import Ensembles.
Require Import Lra.
Local Open Scope R.

(**Let D be the set [0,1] cup {2} cup [3,4). Show that any function f : D -> R is continuous at 2 *)
(*must roll my own continuity, to play w Ensembles-as-Types*)

Record Aset (A : Ensemble R) : Type := mkset {x :> R; inA : A x}.

Definition D (x : R) :=
  0 <= x <= 1 \/ x = 2 \/ 3 <= x < 4.

Lemma two_is_in_D : D 2.
Proof.
  unfold D.
  lra.
Qed.

Definition Aconverges (A : Ensemble R) (Un : nat -> Aset A) (c : Aset A) :=
  (*convergence of a sequence when every element is a member of a certain set*)
  forall eps,
    eps > 0 ->
    exists N, forall n, (n >= N)%nat -> R_dist (Un n) c < eps.

Definition continuous_pt (A : Ensemble R) (f : Aset A -> R) (c : Aset A) :=
  (*sequential characterization of convergence*)
  (*Un_cv is the standard library definition of convergence on R*)
  forall (Xn : nat -> Aset A), Aconverges A Xn c -> Un_cv (fun n => f (Xn n)) (f c).

Axiom equality :
  (*equality in R - Theorem 1.2.6 in Abbott*)
  forall x y eps, Rabs (x - y) < eps <-> x = y.

Axiom equality' :
  (*equality in a set A - Theorem 1..2.6 in Abbott*)
  forall (A : Ensemble R) (x y : Aset A) (eps : R), Rabs (x - y) < eps <-> x = y.

Axiom uniqueness' :
  (*I feel like this ought to be a part of the theory, so it may not be necessary for me to declare it as an axiom*)
  forall (A : Ensemble R) (f : Aset A -> R) (x y : Aset A), x = y -> f x = f y.


Theorem continuous_at_2 : forall (f : Aset D -> R), continuous_pt D f (mkset D 2 two_is_in_D).
Proof.
  intros f Xn H.
  unfold Aconverges in H.
  unfold Un_cv.
  intros eps H__eps.
  specialize (H eps H__eps).
  destruct H as [N H].
  exists N.
  intros n H__n.
  specialize (H n H__n).

  unfold R_dist in *.
  apply equality.
  apply equality' in H.
  apply uniqueness'.
  apply H.
Qed.
