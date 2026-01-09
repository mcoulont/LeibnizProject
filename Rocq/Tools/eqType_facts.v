
Require Import Classical.
Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Lemma eq_bool_equivalent {T : eqType} (m n : T) :
  m == n = true <-> m = n.
Proof.
  split; intro; by apply/eqP.
Qed.

Lemma eq_bool_equivalent_not {T : eqType} (m n : T) :
  m == n = false <-> m <> n.
Proof.
  split.
  {
    intro fal. unfold not. intro tru.
    rewrite tru in fal. rewrite eq_refl in fal.
    inversion fal.
  }
  {
    intro ne.
    unfold not in ne.
    rewrite <- eq_bool_equivalent in ne.
    destruct (m == n).
    { exfalso. apply ne. reflexivity. }
    { reflexivity. }
  }
Qed.

Definition replace {A: eqType} {B : A -> Type}
(before_replace : forall a : A, B a) (a0 : A) (b0 : B a0) :
  forall a : A, B a.
Proof.
  intro.
  pose proof (eq_comparable a0 a).
  unfold decidable in H.
  destruct H.
  - rewrite <- e. exact b0.
  - exact (before_replace a).
Defined.

Lemma replace_changes {A: eqType} {B : A -> Type}
(before_replace : forall a : A, B a) (a0 : A) (b0 : B a0) :
  replace before_replace a0 b0 a0 = b0.
Proof.
  unfold replace.
  destruct (eq_comparable (T:=A) a0 a0).
  - rewrite <- eq_rect_eq. reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma replace_unchanges {A: eqType} {B : A -> Type} {a a' : A}
(before_replace : forall a : A, B a) (b : B a) (ne_aa' : a <> a') :
  replace before_replace a b a' = before_replace a'.
Proof.
  unfold replace.
  destruct (eq_comparable (T:=A) a a').
  - tauto.
  - reflexivity.
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
