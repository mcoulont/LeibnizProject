
Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Lemma eq_mathcomp_equivalent {T : eqType} (m n : T) :
  m == n = true <-> m = n.
Proof.
  split; intro; by apply/eqP.
Qed.

Definition pair {T : eqType} (x y : T) : pred T :=
  fun (t : T) => (t == x) || (t == y).

Lemma pair_fst {T : eqType} (x y : T) :
  pair x y x.
Proof.
  unfold pair. rewrite eq_refl. apply orTb.
Qed.

Lemma pair_snd {T : eqType} (x y : T) :
  pair x y y.
Proof.
  unfold pair. rewrite eq_refl. apply orbT.
Qed.

Lemma pair_closure {T : eqType} {x y z : T} (Hx : z <> x) (Hy : z <> y) :
  ~ pair x y z.
Proof.
  unfold pair. intro.
  unfold orb in H.
  destruct (z == x) eqn:Ezx.
  { apply Hx. apply/eqP. rewrite Ezx. intuition. }
  { apply Hy. apply/eqP. exact H. }
Qed.

Lemma pair_symmetric {T : eqType} (x y : T) :
  pair x y = pair y x.
Proof.
  unfold pair.
  apply functional_extensionality. intro.
  rewrite orbC. reflexivity.
Qed.

Definition triple {T : eqType} (x y z : T) : pred T :=
  fun (t : T) => (t == x) || (t == y) || (t == z).

Lemma triple_closure {T : eqType} {x y z t : T} (t_in : triple x y z t) :
  t = x \/ t = y \/ t = z.
Proof.
  unfold triple in t_in.
  destruct (t == x) eqn:Etx.
  { left. by apply/eqP. }
  {
    right.
    destruct (t == y) eqn:Ety.
    { left. by apply/eqP. }
    {
      right.
      destruct (t == z) eqn:Etz.
      { by apply/eqP. }
      { inversion t_in. }
    }
  }
Qed.

Lemma triple_fst {T : eqType} (x y z : T) :
  triple x y z x.
Proof.
  unfold triple. rewrite eq_refl. apply orTb.
Qed.

Lemma pair_subpred_triple {T : eqType} (x y z : T) :
  subpred (pair x y) (triple x y z).
Proof.
  unfold subpred. unfold pair. unfold triple.
  intros.
  apply Bool.orb_true_intro.
  left. exact H.
Qed.

Lemma pair_subpred_triple' {T : eqType} (x y z : T) :
  subpred (pair x z) (triple x y z).
Proof.
  unfold subpred. unfold pair. unfold triple.
  intros.
  apply Bool.orb_true_intro. apply Bool.orb_prop in H.
  destruct H.
  {
    left. apply Bool.orb_true_intro.
    left. exact H.
  }
  { right. exact H. }
Qed.

Lemma pair_subpred_triple'' {T : eqType} (x y z : T) :
  subpred (pair y z) (triple x y z).
Proof.
  unfold subpred. unfold pair. unfold triple.
  intros.
  apply Bool.orb_true_intro. apply Bool.orb_prop in H.
  destruct H.
  {
    left. apply Bool.orb_true_intro.
    right. exact H.
  }
  { right. exact H. }
Qed.
