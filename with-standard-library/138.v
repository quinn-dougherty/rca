Require Import Reals.
Require Import Psatz.
Open Local Scope R.
(**Lemma 1.3.8 in Abbott Understanding Analysis. *)
(** Assume s in R is an upper bound for a set A in R. *)
(** then, s = supA iff forall eps > 0 exists a in A s.t. s - eps < a*)

Check is_upper_bound.
Check lub.
Check completeness.

Lemma if_not_ub_then_exists (An : nat -> R) (x : R) :
  not (is_upper_bound (EUn An) x) -> exists a, (EUn An) a /\ x < a.
Proof.
  intros H.
  unfold not in H.

  Admitted.

Lemma one_three_eight
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
    assert (H0 : 1 > 0). lra.
    specialize (H (mkposreal 1 H0));
      destruct H as [a [H1 H2]];
      simpl in H2.
    unfold lub;
      destruct ub_to_lub as [x G];
      unfold is_lub in G;
      destruct G as [G1 G2].
    assert (G2' : forall b, is_upper_bound (EUn An) b -> x <= b). apply G2.
    specialize (G2 s s_is_ub).
    specialize (G2' x G1).

    unfold is_upper_bound in G1.
    specialize (G1 simpl).

    unfold is_upper_bound in s_is_ub.
    specialize (s_is_ub a H1).
    unfold has_ub, bound in An_has_ub;
      destruct An_has_ub as [m An_has_ub'];
      unfold is_upper_bound in An_has_ub'.
    specialize (An_has_ub' a H1).
    unfold is_upper_bound in G1.





  }
