
Require Import Logic.Classical_Pred_Type.
Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Require Import ethics_first_steps.
Require Import objective_ethics_no_disapproval_iff_same_ethic.
Require Import more_resrtictive_ethics_diminish_conflicts.

Definition Action : eqType := ethics_first_steps.Action.

Definition Individual : finType :=
  more_resrtictive_ethics_diminish_conflicts.Individual.
Definition feasible : State -> ActionProfile -> bool :=
  more_resrtictive_ethics_diminish_conflicts.feasible.

Definition generalized_whole_society (e : IndividualEthic) : EthicalProfile :=
  fun (i : Individual) => e.

Definition altruist (e : IndividualEthic) (state : State) : Prop :=
  exists (ap : ActionProfile), no_conflict (generalized_whole_society e) ap state.

Definition bipartite_contest (state : State) (i j : Individual)
(a_i a_j b_i b_j : Action) : Prop :=
  i <> j /\
  (
    forall (ap : ActionProfile),
      ap i = a_i ->
      ap j = a_j ->
      feasible state ap = false
  ) /\ (
    exists (ap : ActionProfile),
      ap i = a_i /\
      ap j = b_j /\
      feasible state ap = true
  ) /\ (
    exists (ap : ActionProfile),
      ap i = b_i /\
      ap j = a_j /\
      feasible state ap = true
  ).

Proposition unanimous_altruism_not_enough_to_avoid_conflicts (state : State) :
  (
    exists (i j : Individual) (a_i a_j b_i b_j : Action),
      bipartite_contest state i j a_i a_j b_i b_j
  ) -> (
    exists (ep : EthicalProfile) (ap : ActionProfile),
      conflict ep ap state /\
      forall (k : Individual), altruist (ep k) state
  ).
Proof.
  intro.
  destruct H as [i]. destruct H as [j]. destruct H as [a_i]. destruct H as [a_j].
  destruct H as [b_i]. destruct H as [b_j].
  exists (
    fun (k : Individual) =>
    fun (subj_state : SubjectiveState) =>
    fun (action : Action) =>
    if (k == i) then (
      if (subj_state.(individual) == i) then (
        if (action == a_i) then true else
        if (action == b_i) then true else
        false
      ) else if (subj_state.(individual) == j) then (
        if (action == b_j) then true else false
      ) else true
    )
    else (
      if (subj_state.(individual) == j) then (
        if (action == a_j) then true else
        if (action == b_j) then true else
        false
      ) else if (subj_state.(individual) == i) then (
        if (action == b_i) then true else false
      ) else true
    )
  ).
  exists (
    fun (k : Individual) =>
    if (k == i) then a_i else a_j
  ).
  split.
  {
    unfold conflict.
    split.
    {
      unfold bipartite_contest in H.
      destruct H. unfold not in H.
      assert ((i == j) = false).
      { by apply/eqP. }
      destruct H0.
      apply H0.
      { rewrite eq_refl. reflexivity. }
      { rewrite eq_sym. rewrite H1. reflexivity. }
    }
    {
      unfold everyone_follows_its_ethic.
      intro.
      destruct (i0 == i) eqn:Di0i.
      {
        rewrite Di0i.
        rewrite eq_refl.
        reflexivity.
      }
      {
        rewrite Di0i.
        rewrite eq_refl.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == j) eqn:Di0j ; rewrite Di0j ; reflexivity.
      }
    }
  }
  {
    intro.
    unfold altruist.
    unfold bipartite_contest in H.
    destruct H. destruct H0. destruct H1.
    destruct (k == i) eqn:Dki.
    {
      destruct H1 as [ap].
      exists (
        fun (k : Individual) =>
        if (k == i) then a_i else
        if (k == j) then b_j else
        ap k
      ).
      unfold no_conflict.
      destruct H1. destruct H3.
      split.
      {
        rewrite <- H1. rewrite <- H3.
        assert (
          (fun k0 : Individual => if k0 == i then ap i else if k0 == j then ap j else ap k0) = ap
        ).
        {
          apply functional_extensionality. intro.
          destruct (x == i) eqn:Dxi.
          {
            assert (x = i).
            { by apply/eqP. }
            rewrite H5. reflexivity.
          }
          {
            destruct (x == j) eqn:Dxj.
            {
              assert (x = j).
              { by apply/eqP. }
              rewrite H5. reflexivity.
            }
            reflexivity.
          }
        }
        rewrite H5.
        apply H4.
      }
      {
        unfold everyone_follows_its_ethic. intro.
        unfold generalized_whole_society.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == i) eqn: Di0i.
        {
          rewrite Di0i.
          rewrite eq_refl.
          reflexivity.
        }
        {
          rewrite Di0i.
          destruct (i0 == j) eqn: Di0j.
          {
            rewrite Di0j.
            rewrite eq_refl.
            reflexivity.
          }
          {
            rewrite Di0j.
            reflexivity.
          }
        }
      }
    }
    {
      destruct H2 as [ap].
      exists (
        fun (k : Individual) =>
        if (k == i) then b_i else
        if (k == j) then a_j else
        ap k
      ).
      unfold no_conflict.
      destruct H2. destruct H3.
      split.
      {
        rewrite <- H2. rewrite <- H3.
        assert (
          (fun k0 : Individual => if k0 == i then ap i else if k0 == j then ap j else ap k0) = ap
        ).
        {
          apply functional_extensionality. intro.
          destruct (x == i) eqn:Dxi.
          {
            assert (x = i).
            { by apply/eqP. }
            rewrite H5. reflexivity.
          }
          {
            destruct (x == j) eqn:Dxj.
            {
              assert (x = j).
              { by apply/eqP. }
              rewrite H5. reflexivity.
            }
            reflexivity.
          }
        }
        rewrite H5.
        apply H4.
      }
      {
        unfold everyone_follows_its_ethic. intro.
        unfold generalized_whole_society.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == i) eqn: Di0i.
        {
          rewrite Di0i.
          rewrite eq_refl.
          destruct (i0 == j) eqn: Di0j.
          {
            assert (i0 = i).
            { by apply/eqP. }
            assert (i0 = j).
            { by apply/eqP. }
            assert (i = j).
            {
              rewrite <- H5. rewrite <- H6.
              reflexivity.
            }
            exfalso.
            apply H in H7. inversion H7.
          }
          {
            rewrite Di0j.
            reflexivity.
          }
        }
        {
          rewrite Di0i.
          destruct (i0 == j) eqn: Di0j.
          {
            rewrite Di0j.
            rewrite eq_refl.
            reflexivity.
          }
          {
            rewrite Di0j.
            reflexivity.
          }
        }
      }
    }
  }
Qed.
