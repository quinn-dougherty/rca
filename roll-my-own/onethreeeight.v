Require Import Reals.
Require Import Ensembles.
Require Import Lra.
Local Open Scope R.

Record Aset (A : Ensemble R) : Type := mkset {x :> R; inA : A x}.

Definition bounded_above (A : Ensemble R) :=
  exists (b : R), forall (a : Aset A), a <= b.

Definition lt_sqrt2 := fun x => x * x < 2.

Definition lt_5 := fun x => x < 5.

Lemma lt_5_is_bounded_above :
  bounded_above lt_5.
Proof.
  unfold bounded_above.
  exists 6.
  intros a.
  induction a; simpl.
  unfold lt_5 in inA0.
  lra.
Qed.

Check has_ub.

Definition is_upper_bound (A : Ensemble R) (b : R) :=
  forall (a : Aset A), a <= b.

Definition is_lub (A : Ensemble R) (s : R) :=
  is_upper_bound A s /\ (forall b, is_upper_bound A b -> s <= b).

Theorem one_three_eight
        (A : Ensemble R)
        (nonempty : exists x, A x)
        (s : R)
        (H : is_upper_bound A s)
  :
    is_lub A s <-> forall (eps : posreal), exists (a : Aset A), s - eps < a.
Proof.
  split.
  { intros G eps.
    destruct eps as [eps H__eps]; simpl.
    destruct nonempty as [x H__x].
    unfold is_lub in G.
    destruct G as [G1 G2].
    unfold is_upper_bound in *.
    assert (s - eps < s). lra.
    assert (not (is_upper_bound A (s - eps))).
    { unfold not.
      intros H'.
      unfold is_upper_bound in H'.
      specialize (H' (mkset A x H__x)); simpl in H'.
      give_up.

    }
