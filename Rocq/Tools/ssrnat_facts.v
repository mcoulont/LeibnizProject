
Require Import Logic.Epsilon.
From mathcomp Require Import all_ssreflect.

Lemma add1_lt (m n : nat) :
  m < n <-> m.+1 < n.+1.
Proof.
  intuition.
Qed.

Lemma lt_mathcomp_equivalent (m n : nat) :
  m < n = true <-> (m < n)%coq_nat.
Proof.
  generalize dependent m.
  induction n.
  { split; intro; inversion H. }
  {
    intro.
    destruct m.
    { intuition. }
    {
      specialize (IHn m).
      specialize (add1_lt m n). intro.
      assert ((m < n)%coq_nat <-> (m.+1 < n.+1)%coq_nat).
      { intuition. }
      rewrite <- H0. rewrite <- H.
      exact IHn.
    }
  }
Qed.

Lemma lt_mathcomp_equivalent_not (m n : nat) :
  m < n = false <-> ~ (m < n)%coq_nat.
Proof.
  rewrite <- lt_mathcomp_equivalent. unfold not.
  destruct (m < n).
  {
    split.
    { intros. discriminate H. }
    { intros. exfalso. apply H. reflexivity. }
  }
  {
    split.
    { intros. discriminate H0. }
    { intros. reflexivity. }
  }
Qed.

Lemma le_mathcomp_equivalent (m n : nat) :
  m <= n = true <-> (m <= n)%coq_nat.
Proof.
  generalize dependent n.
  induction m.
  {
    intro.
    rewrite leq0n.
    split.
    { intro. apply PeanoNat.Nat.le_0_l. }
    { intro. reflexivity. }
  }
  {
    destruct n.
    {
      rewrite ltn0.
      split.
      { intro. inversion H. }
      { intro. exfalso. apply (PeanoNat.Nat.nle_succ_0 m). exact H. }
    }
    {
      specialize (IHm n).
      specialize (add1_lt m n). intro.
      assert ((m <= n)%coq_nat <-> (m.+1 <= n.+1)%coq_nat).
      { intuition. }
      unfold leq. rewrite subSS.
      rewrite <- H0.
      exact IHm.
    }
  }
Qed.
