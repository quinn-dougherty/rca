Require Import Reals.
Require Import Psatz.
Require Import Ensembles.
Local Open Scope R.

(** *)
(**Let D be the set [0,1] cup {2} cup [3,4). Show that any function f : D -> R is continuous at 2 *)
(***)
(*must roll my own continuity, to play w Ensembles-as-Types*)

Record Aset (A : Ensemble R) : Type := mkset {x :> R; inA : A x}.

Definition continuous_pt (A : Ensemble R) (f : Aset A -> R) (c : Aset A) :=
  A c ->
  forall eps, eps > 0 ->
         exists (delt : posreal), forall (x : Aset A),
             Rabs (x - c) < delt -> Rabs (f x - f c) < eps.

Definition D (x : R) :=
  0 <= x <= 1 \/ x = 2 \/ 3 <= x < 4.

Lemma two_is_in_D : D 2.
Proof.
  unfold D.
  lra.
Qed.

Theorem continuous_at_2 : forall (f : Aset D -> R), continuous_pt D f (mkset D 2 two_is_in_D).
Proof.
  intros f.
  unfold continuous_pt.
  intros H eps H__eps; simpl in H.
  destruct two_is_in_D as [D' | [D' | D']]; try (exfalso; lra).
  assert (H100 : 100*eps > 0). lra.
  exists (mkposreal (100*eps) H100).
  intros x0 H1.
  destruct x0.
  simpl in H1.
  destruct inA0 as [inA' | [inA' | inA']];
    unfold Rabs in H1;
    destruct Rcase_abs as [H1' | H1'] in H1;
    unfold Rabs;
    destruct Rcase_abs as [H2' | H2'];
    try rewrite Ropp_minus_distr;
    try apply Rminus_lt in H2';
    try rewrite Ropp_minus_distr in H1;
    try lra;
    give_up.
Admitted.

Print Un_cv.

Definition Aconverges (A : Ensemble R) (Un : nat -> Aset A) (c : Aset A) :=
  (*convergence of a sequence when every element is a member of a certain set*)
  forall eps,
    eps > 0 ->
    exists N, forall n, (n >= N)%nat -> R_dist (Un n) c < eps.

Definition continuous_pt' (A : Ensemble R) (f : Aset A -> R) (c : Aset A) :=
  forall (Xn : nat -> Aset A), Aconverges A Xn c -> Un_cv (fun n => f (Xn n)) (f c).

Theorem continuous_at_2' : forall (f : Aset D -> R), continuous_pt' D f (mkset D 2 two_is_in_D).
Proof.
  intros f Xn H.
  unfold Aconverges in H.
  unfold Un_cv.
  intros eps H__eps.
  assert (H__eps100 : 100*eps > 0). lra.
  specialize (H (100*eps) H__eps100).
  destruct H as [N H].
  exists N.
  intros n H__n.
  specialize (H n H__n).
  unfold R_dist, Rabs in *.
  destruct Rcase_abs as [H' | H'] in H;
    destruct Rcase_abs as [G' | G'];
    destruct two_is_in_D as [D' | [D' | D']];
    try (exfalso; lra);
    simpl in H; simpl in H'; simpl in G'.
  - give_up.
  - give_up.
  - give_up.
  - give_up.
Admitted.
