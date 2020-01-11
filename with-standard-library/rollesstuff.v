Require Import Reals.
Require Import Lra.
Require Import FunctionalExtensionality.
Local Open Scope R_scope.

Definition three (x : R) := 3.

Definition threex (x : R) := 3 * x.

Lemma derivable_three : derivable three.
Proof.
  unfold derivable, derivable_pt, derivable_pt_abs, derivable_pt_lim, three.
  intros x.
  exists 0.
  intros eps H.
  assert (deltpos : (eps) > 0). lra.
  exists (mkposreal (eps) deltpos).
  intros h H' G.
  simpl in G.
  unfold Rabs in *;
    destruct Rcase_abs in G;
    destruct Rcase_abs;
    field_simplify;
    try lra.
Qed.

Lemma derivable_threex : derivable threex.
Proof.
  unfold derivable, derivable_pt, derivable_pt_abs, derivable_pt_lim, threex.
  intros x.
  exists 3.
  intros eps H.
  assert (deltpos : (eps) > 0). lra.
  exists (mkposreal (eps) deltpos).
  intros h H' G.
  simpl in G.
  unfold Rabs in *;
    destruct Rcase_abs in G;
    destruct Rcase_abs;
    field_simplify;
    try lra.
Qed.


Lemma constant_three : constant three.
Proof.
  unfold constant, three; intros; reflexivity.
Qed.

Check derivable_threex.

Lemma Rcomm_0_1 : forall x y, x + y - x = y.
Proof.
  intros x y.
  lra.
Qed.

Lemma Rdiv_inv : forall x y, y <> 0 -> y * x / y = x.
Proof.
  intros x y H.
  field.
  apply H.
Qed.


Lemma deriv_threex_is_three : derive threex derivable_threex = three.
Proof.
  unfold derive, threex, three.
  apply functional_extensionality.
  intros x.
  unfold derive_pt, proj1_sig.
  destruct derivable_threex as [c H].
  unfold derivable_pt_abs, derivable_pt_lim in H.
  assert (H0 : 1 > 0). lra.
  specialize (H 1 H0).
  destruct H as [[delt deltpos] H].
  unfold threex in H; simpl in H.
  assert (H00 : (delt/2) <> 0). lra.
  assert (H000 : Rabs (delt/2) < delt). unfold Rabs; destruct Rcase_abs; lra.
  specialize (H (delt/2) H00 H000).
  unfold Rabs in H000; destruct Rcase_abs as [H000' | H000'] in H000; try lra.
  rewrite Rmult_comm in H.
  rewrite Rmult_plus_distr_r in H.
  rewrite Rmult_comm in H.
  rewrite Rcomm_0_1 in H.
  rewrite Rdiv_inv in H; try lra.


  unfold Rabs in H; destruct Rcase_abs as [H' | H']; try lra.
  - apply Rminus_lt in H'.
    assert (G : 3 < c < 4). lra.
    rewrite Ropp_minus_distr in H.
    give_up.
  - simpl.
    destruct H' as [H' | H'].
    + give_up.
    + lra.
Admitted.


Lemma constant_threex_deriv : constant (derive threex derivable_threex).
Proof.
  unfold constant, derive, threex; intros x y.
  destruct (derivable_threex x) as [x' H]; destruct (derivable_threex y) as [y' G].
  unfold derive_pt, proj1_sig.
  unfold derivable_pt_abs, derivable_pt_lim in *.
  assert (0 < (1/3)). lra.
  specialize (H (1/3) H0). specialize (G (1/3) H0).
  destruct H as [[delt1 delt1pos] H].
  destruct G as [[delt2 delt2pos] G].
  assert (delt1 / 2 <> 0). lra.
  assert (delt2 / 2 <> 0). lra.
  assert (Rabs (delt1 / 2) < delt1). unfold Rabs; destruct Rcase_abs; lra.
  assert (Rabs (delt2 / 2) < delt2). unfold Rabs; destruct Rcase_abs; lra.
  specialize (H (delt1 / 2) H1 H3).
  specialize (G (delt2 / 2) H2 H4).

  unfold threex in *. simpl in H. simpl in G.
  rewrite Rmult_comm with (r1:=3) (r2:=x + (delt1/2)) in H;
    rewrite Rmult_plus_distr_r with (r1:=x) (r2:= (delt1/2)) in H.
  rewrite Rmult_comm with (r1:=3) (r2:=y + (delt2/2)) in G;
    rewrite Rmult_plus_distr_r with (r1:=y) (r2:= (delt2/2)) in G.
  rewrite <- Rmult_comm with (r1:=3) (r2:=x) in H;
    rewrite <- Rmult_comm with (r1:=3) (r2:=y) in G.
  rewrite Rcomm_0_1 with (x := 3*x) in H;
    rewrite Rdiv_inv in H;
    try apply H1.
  rewrite Rcomm_0_1 with (x := 3*y) in G;
    rewrite Rdiv_inv in G;
    try apply H2.


  unfold Rabs in H;
    unfold Rabs in G;
    destruct Rcase_abs as [H' | H'] in H;
    destruct Rcase_abs as [G' | G'] in G.
  - assert (F1 : 3 < x' < (10/3)). lra.
    assert (F2 : 3 < y' < (10/3)). lra.

    remember (Rtotal_order x' y') as E.
    destruct E as [E1 | [E2 | E3]]; try lra.




 


  Admitted.

Lemma derivable_implies_continuity :
  forall (f : R -> R), derivable f -> continuity f.
Proof.
  intros f H.
  unfold derivable in H.
  unfold continuity.
  intros x.
  specialize (H x).
  unfold derivable_pt in H; destruct H as [c H].
  unfold derivable_pt_abs, derivable_pt_lim in H.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps H__eps.
  specialize (H eps H__eps).
  destruct H as [[delt deltpos] H].
  exists delt.
  split; try lra.
  intros x' G.
  destruct G as [G1 G2].
  unfold dist in *; simpl in *; unfold R_dist, Rabs in *.
  unfold D_x, no_cond in G1; destruct G1 as [_ G1].
  assert (F : (delt/2) <> 0). lra. assert (F' : (delt/2) < delt). lra.
  specialize (H (delt/2) F).
  destruct Rcase_abs in H; try lra.
  specialize (H F').
  destruct Rcase_abs as [G2' | G2'] in G2.
  - destruct Rcase_abs.
    + destruct Rcase_abs.
      * simpl.

  Admitted.

Compute IVT.

Lemma shifted_IVT :
  forall (f : R -> R) (x y : R),
    continuity f -> x < y ->
    forall c,
      f x < c < f y -> {z : R | x < z < y /\ f z = c}.
Proof.
  intros f x y H1 H2 c H.
  remember (fun x => f x - c) as g.
  assert (G : g x < 0 < g y). rewrite Heqg. lra.
  exists ((x + y)/2).
  split.
  - simpl.



  Admitted.
Compute constant.
Compute derivable_continuous.

Ltac unpack_derivative :=
  fun H diff n H0 delt deltpos =>
    unfold derive, derive_pt, derivable_pt_abs, derivable_pt_lim, proj1_sig in H;
    destruct diff as [x1 H'] in H;
    unfold derivable_pt_abs, derivable_pt_lim in H';
    specialize (H' n H0);
    destruct H' as [[delt deltpos] H'].


(*final: #10*)
Theorem number10 :
  forall (f : R -> R) (diff : derivable f) (a b c' : R),
    a < c' < b -> (derive f diff c') = 0 -> forall x y, a < x < b -> a < y < b -> f x = f y.
Proof.
  intros f diff a b c' H__ab H x y H__x H__y.
  assert (E0 : a < b). lra.
  assert (E1 : f a = f b). give_up.
  remember (derivable_continuous f diff) as diff'.

  assert (1 > 0). lra.
  unpack_derivative H diff 1 H0 delt1 delt1pos.
  simpl in H'.

  assert (pr : forall x, a < x < b -> derivable_pt f x).
  { intros x0 pr'.
    assert (diff'' : derivable f). apply diff.
    unfold derivable in diff''.
    specialize (diff'' x0).
    apply diff''.
  }
  assert (pr' : forall x', a <= x' <= b -> continuity_pt f x').
  { intros x' H''.
    assert (diff'' : continuity f). apply diff'.
    unfold continuity in diff''.
    specialize (diff'' x').
    apply diff''.
  }

  remember (Rolle f a b pr pr' E0 E1) as F.
  destruct F as [c [H__c F]].
  assert (F' : derive_pt f c (pr c H__c) = 0). apply F.
  destruct (pr c H__c) as [x0 F0] in F'; simpl in F'.
  rewrite F' in F0.

  unfold derivable_pt_abs, derivable_pt_lim in F0.

  specialize (F0 1 H0).
  destruct F0 as [[delt2 delt2pos] F0].
  assert (delt2/2 <> 0). lra.
  assert (Rabs (delt2/2) < delt2). unfold Rabs; destruct Rcase_abs; lra.
  simpl in F0. specialize (F0 (delt2/2) H1 H2).

  unfold Rabs in F0;
    destruct Rcase_abs as [F0' | F0'] in F0;
    field_simplify in F0;
    field_simplify in F0';
    try lra.
