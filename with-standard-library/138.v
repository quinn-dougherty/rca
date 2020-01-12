Require Import Reals.
Require Import Psatz.
Open Local Scope R.
(**Lemma 1.3.8 in Abbott Understanding Analysis. *)
(** Assume s in R is an upper bound for a set A in R. *)
(** then, s = supA iff forall eps > 0 exists a in A s.t. s - eps < a*)


Axiom equality :
  (*equality in R - Theorem 1.2.6 in Abbott*)
  forall x y eps, Rabs (x - y) < eps <-> x = y.

Lemma if_not_ub_then_exists (An : nat -> R) (x : R) :
  not (is_upper_bound (EUn An) x) -> exists a, (EUn An) a /\ x < a.
Proof.
  intros H.
  unfold not in H.

  Admitted.

Lemma Rle_plus_nonneg_forward (x y : R) :
  exists (eps : nonnegreal),
  x <= y -> x = y - eps.
Proof.
Admitted.

Theorem one_three_eight
      (An : nat -> R)
      (s : R)
      (s_is_ub : is_upper_bound (EUn An) s)
      (An_has_ub : has_ub An)
  :
    s = lub An An_has_ub <->
    forall (eps : posreal), exists (a : R), (EUn An) a /\ s - eps < a.
Proof.
  split.
  { intros H eps.
    destruct eps as [eps H__eps]; simpl.
    unfold is_upper_bound in s_is_ub.
    assert (An_has_ub' : has_ub An). apply An_has_ub.
    unfold has_ub, bound, is_upper_bound in An_has_ub';
      destruct An_has_ub' as [m An_has_ub'].
    unfold lub in H; destruct ub_to_lub as [x H'].
    unfold is_lub in H'; destruct H' as [H'1 H'2].
    unfold is_upper_bound in H'1.
    assert (G : not (is_upper_bound (EUn An) (s - eps))).
    { unfold not.
      intros G'.
      specialize (H'2 (s - eps) G').
      rewrite H in H'2.
      lra.
    }

    specialize (H'2 (s - eps)).
    rewrite H in H'2.
    apply if_not_ub_then_exists in G.
    destruct G as [a [G1 G2]]; simpl in G2.
    exists a.
    split.
    - apply G1.
    - apply G2.
  }
  { intros H.
    assert (G : forall (eps : posreal), not (is_upper_bound (EUn An) (s - eps))).
    { unfold not.
      intros eps H'.
      specialize (H eps); destruct H as [a [H1 H2]].
      give_up.
    }
    assert (eps0 : exists (eps : posreal), eps = eps). give_up.
    destruct eps0 as [[eps H__eps] _].
    remember (s - eps) as b.
    specialize (G (mkposreal eps H__eps)); simpl in G.

    unfold lub;
      destruct ub_to_lub as [b' F];
      unfold is_lub in F;
      destruct F as [F1 F2];
      specialize (F2 s s_is_ub).

    destruct F2 as [F2' | F2'].
    - exfalso.
      apply G.
      unfold is_upper_bound in *.
      intros x H__x.
      specialize (s_is_ub x H__x).
      specialize (F1 x H__x).
      specialize (H (mkposreal eps H__eps)); destruct H as [a [H1 H2]]; simpl in H2.
      right.
      remember (Rle_plus_nonneg_forward x s) as E.
      destruct E as [eps' E].
      assert (E' : x <= s -> x = s - eps'). apply E.
      specialize (E' s_is_ub).
      destruct eps' as [eps' H__eps'].
      assert (H0 : eps' = eps). give_up.
      rewrite <- H0.
      simpl in E'.
      apply E'.
    - rewrite F2'. reflexivity.
  }
Admitted.
