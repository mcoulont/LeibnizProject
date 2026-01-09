
Require Import Setoid.
Require Import Nat.
From mathcomp Require Import all_ssreflect fintype.

Require Import nat_facts.
Require Import ssrnat_facts.

Lemma add_sums {T : finType} (f g : T -> nat) :
  \sum_i (f i) + \sum_i (g i) = \sum_i (f i + g i).
Proof.
  assert (forall t, true -> f t <= f t + g t).
  { intros. apply leq_addr. }
  pose proof (sumnB (index_enum T) H).
  simpl in H0.
  assert (forall i, f i <= f i).
  { auto. }
  assert (forall i, f i + g i - f i = g i).
  {
    intro.
    induction (g i).
    {
      rewrite <- plus_n_O.
      induction (f i).
      { reflexivity. }
      { rewrite subSS. exact IHn. }
    }
    {
      rewrite addnS.
      rewrite <- IHn at 2.
      rewrite subSn.
      { reflexivity. }
      { apply leq_addr. }
    }
  }
  revert H0.
  under eq_bigr do rewrite H2. intro.
  simpl in H0.
  rewrite H0.
  rewrite addnBA.
  2: {
    apply leq_sum.
    intros. auto.
  }
  {
    unfold addn. rewrite add_comm.
    rewrite <- addnBA.
    2: {
      apply leq_sum.
      intros. auto.
    }
    {
      assert (\big[add/0]_i  f i - \big[add/0]_i  f i = 0).
      { rewrite sub_n_n_0. reflexivity. }
      rewrite H3.
      unfold addn. rewrite add_comm.
      reflexivity.
    }
  }
Qed.
